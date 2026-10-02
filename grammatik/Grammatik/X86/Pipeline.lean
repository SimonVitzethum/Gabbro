/-
  File:      Grammatik/X86/Pipeline.lean
  Subject:   The first complete end-to-end pipeline in Lean, over a selected
             fragment: typed Gabbro source block -> certified optimiser ->
             direct lowering to the 14 pilot instructions -> canonical bytes
             in a code region -> byte-level fetch/decode/execute, with a
             validator that RECOMPUTES the bytes from the source and ONE
             closing theorem (`pipeline_correct`) over the REAL `execBlock`
             of the ORIGINAL (unoptimised) block.

             WIDENED (2026-10-02): values are arbitrary-depth `lit`/`var`/
             `weiter`/`add`/`sub`/`neg` trees over a scratch-register stack
             (`PipeCfg.frei`, `ExpressionLoweringDeep.senkTief`); checks
             compare two arbitrary-depth operands
             (`ExpressionLoweringDeep.senkVergleich`) under the decided
             signed-window side condition; `Stmt.ite` over such a
             comparison lowers to `cmp` + `jcc` over the then-block + `jmp`
             over the else-block, both branches in the fragment
             recursively, with every displacement recomputed and checked.
             The original fragment is a special case with identical bytes
             (`senkWert_als_tief`, `senkBed_als_tief`).

  Reused, not duplicated:
    - optimiser: `OptimizationRules.applyPipeline`/`applyPipeline_sound`
      (`BlockEquiv`), `constInt?`/`constInt?_sound` for constant indices;
    - expression lowering: `ExpressionLowering.senkFrag`/`senkAtom`,
      `senkung_korrekt`, `senkAtom_korrekt`, `EnvRepr`, `Frisch`,
      `intWort_sint`; `SourceAssignmentLowering.intWort_zahlWort`;
      `ExpressionLoweringDeep.senkTief`/`IstTief`/`istTief_korrekt`,
      `senkVergleich`/`IstVergleich`/`istVergleich_von_senkVergleich`,
      `FrischListe` and its `frischListe_*` lemmas;
    - source/target representation: `SourceMemory.repOk`, `RepSlot`,
      `zahlWort`, `schreibSlot_hit`/`schreibSlot_fremd_*`;
    - machine: `Codec.encode`/`decode`/`roundtrip`, `Ausfuehrung.schritt`/
      `lauf`, `Byteschritt.byteschritt`/`laufBytes`/
      `kanonisch_schritt_ueberein`, `Speicher.write64`/`read64` frames;
    - flags: `FlagBeweis` (`sub64_sint`, `sub64_of_iff`, `bmod_*`).
  No second IR, no second source interpreter, no per-program rule. The
  instruction type is reached only through `encode`, `schritt` and the
  shape class `gerade`, so a later unified ISA can replace `Befehl` at
  these three points (see CUTS).

  The joint witness program and the poison probes live in
  `Grammatik/X86/PipelineWitnesses.lean`.
-/
import Grammatik.X86.OptimizationRules
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.ExpressionLoweringDeep

namespace Gabbro.Grammatik.X86.Pipeline

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules

/-! ## 1. Code regions and the byte-level fetch bridge

    A lowered program is a list of pilot instructions; its bytes are the
    concatenation of the canonical encodings. `CodeAt` says that the code
    region holds exactly these bytes, is executable and is NOT writable
    (W^X): a successful store can then never change a code byte, which is
    what keeps fetch stable along the whole run. -/

/-- The canonical decoded form of an instruction (the one `lauf` runs). -/
def kanon (b : Befehl) : Decodiert := ⟨b, (encode b).length⟩

/-- The bytes of a lowered program: the canonical encodings, in order. -/
def encodeAll (P : List Befehl) : List Byte := (P.map encode).flatten

theorem encodeAll_nil : encodeAll [] = [] := rfl

theorem encodeAll_cons (b : Befehl) (P : List Befehl) :
    encodeAll (b :: P) = encode b ++ encodeAll P := by
  simp [encodeAll]

theorem encodeAll_append (P Q : List Befehl) :
    encodeAll (P ++ Q) = encodeAll P ++ encodeAll Q := by
  simp [encodeAll]

/-- The code region at `cs` holds `flat`: executable, not writable, and
    byte for byte the given list. -/
def CodeAt (m : Speicher) (cs : Adresse) (flat : List Byte) : Prop :=
  ∀ (i : Nat) (b : Byte), flat[i]? = some b →
    m.ausfuehrbar (addrOff cs i) = true ∧ m.schreibbar (addrOff cs i) = false ∧
      m.bytes (addrOff cs i) = b

/-- Byte offsets compose. -/
theorem addrOff_addrOff (a : Adresse) (i j : Nat) :
    addrOff (addrOff a i) j = addrOff a (i + j) := by
  unfold addrOff
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `ripNach` is a byte offset. -/
theorem ripNach_addrOff (a : Adresse) (l : Nat) : ripNach a l = addrOff a l := rfl

/-- The fetch window starts with any executable list it finds in memory. -/
theorem holeFetchAux_praefix (m : Speicher) (a : Adresse) :
    ∀ (l : List Byte) (off cap : Nat), l.length ≤ cap →
      (∀ (j : Nat) (b : Byte), l[j]? = some b →
        m.ausfuehrbar (addrOff a (off + j)) = true ∧ m.bytes (addrOff a (off + j)) = b) →
      holeFetchAux m a off cap = l ++ holeFetchAux m a (off + l.length) (cap - l.length)
  | [], off, cap, _, _ => by simp
  | x :: xs, off, cap, hlen, h => by
    obtain ⟨c, rfl⟩ : ∃ c, cap = c + 1 := ⟨cap - 1, by simp at hlen; omega⟩
    have h0 := h 0 x rfl
    simp only [Nat.add_zero] at h0
    have ih := holeFetchAux_praefix m a xs (off + 1) c (by simp at hlen; omega)
      (fun j b hj => by
        have := h (j + 1) b (by simpa using hj)
        rwa [show off + (j + 1) = off + 1 + j by omega] at this)
    simp only [holeFetchAux, h0.1, if_true, h0.2, ih, List.cons_append, List.length_cons,
      Nat.add_sub_add_right]
    rw [show off + 1 + xs.length = off + (xs.length + 1) by omega]

/-- Execute permission of a prefix from per-byte permission. -/
theorem ausfuehrbarN_von (m : Speicher) (a : Adresse) :
    ∀ (n : Nat), (∀ j, j < n → m.ausfuehrbar (addrOff a j) = true) →
      ausfuehrbarN m a n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [ausfuehrbarN, Bool.and_eq_true]
    exact ⟨ausfuehrbarN_von m a n (fun j hj => h j (by omega)), h n (by omega)⟩

/-- FETCH IN THE CODE REGION: at an instruction boundary of a code region,
    the byte step runs exactly `schritt` on the canonical instruction
    (decoder round trip + actual-memory fetch, `kanonisch_schritt_ueberein`). -/
theorem byteschritt_im_code (s : Zustand) (cs : Adresse) (flat pre post : List Byte)
    (b : Befehl) (hc : CodeAt s.speicher cs flat) (hf : flat = pre ++ encode b ++ post)
    (hrip : s.rip = addrOff cs pre.length) :
    byteschritt s = match schritt (kanon b) s with
      | none => .verweigert
      | some s' => .weiter s' := by
  have hlen := encode_len b
  have hbyte : ∀ (j : Nat) (x : Byte), (encode b)[j]? = some x →
      s.speicher.ausfuehrbar (addrOff s.rip (0 + j)) = true ∧
        s.speicher.bytes (addrOff s.rip (0 + j)) = x := by
    intro j x hj
    obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hj
    have hflat : flat[pre.length + j]? = some x := by
      rw [hf, List.append_assoc, List.getElem?_append_right (by omega)]
      rw [show pre.length + j - pre.length = j by omega, List.getElem?_append_left hjl]
      exact hj
    obtain ⟨hx, -, hb⟩ := hc _ _ hflat
    rw [hrip, Nat.zero_add, addrOff_addrOff]
    exact ⟨hx, hb⟩
  have hwin : geholt s = encode b ++ holeFetchAux s.speicher s.rip (0 + (encode b).length)
      (fetchCap - (encode b).length) :=
    holeFetchAux_praefix s.speicher s.rip (encode b) 0 fetchCap (by
      unfold fetchCap; omega) hbyte
  have hexe : ausfuehrbarN s.speicher s.rip (encode b).length = true :=
    ausfuehrbarN_von _ _ _ (fun j hj => by
      have hx : (encode b)[j]? = some ((encode b)[j]) := List.getElem?_eq_getElem hj
      have := (hbyte j _ hx).1
      rwa [Nat.zero_add] at this)
  exact (kanonisch_schritt_ueberein b s _ hwin hexe).2

/-- Straight-line pilot forms: they fall through to the next instruction
    and touch memory only by a permission-checked store. -/
def gerade : Befehl → Bool
  | .movImm64 _ _ | .movReg64 _ _ | .addReg64 _ _ | .subReg64 _ _
  | .xorReg64 _ _ | .cmpReg64 _ _ | .load64 _ _ _ | .store64 _ _ _ => true
  | _ => false

/-- A successful 8-byte write had write permission on all eight bytes. -/
theorem write64_schreibbar (m m' : Speicher) (a : Adresse) (v : Wort)
    (h : write64 m a v = some m') : schreibbar8 m a = true := by
  unfold write64 at h
  by_cases hc : schreibbar8 m a = true
  · exact hc
  · rw [if_neg hc] at h; cases h

/-- Write permission of the eight footprint bytes. -/
theorem schreibbar8_byte (m : Speicher) (a : Adresse) (h : schreibbar8 m a = true)
    (k : Nat) (hk : k < 8) : m.schreibbar (addrOff a k) = true := by
  unfold schreibbar8 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | k + 8, hk => exact absurd hk (by omega)

/-- A store never changes a non-writable byte. -/
theorem write64_nicht_schreibbar (m m' : Speicher) (a : Adresse) (v : Wort)
    (h : write64 m a v = some m') (x : Adresse) (hx : m.schreibbar x = false) :
    m'.bytes x = m.bytes x := by
  apply write64_rahmen m m' a x v h
  intro k hk he
  have := schreibbar8_byte m a (write64_schreibbar m m' a v h) k hk
  rw [← he, hx] at this
  cases this

/-- FRAME OF A STRAIGHT STEP: the instruction pointer moves past the
    instruction, permissions are unchanged, and a non-writable byte keeps
    its value. -/
theorem schritt_gerade (b : Befehl) (s s' : Zustand) (hg : gerade b = true)
    (h : schritt (kanon b) s = some s') :
    s'.rip = addrOff s.rip (encode b).length ∧
      s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar ∧
      s'.speicher.lesbar = s.speicher.lesbar ∧
      (∀ x, s.speicher.schreibbar x = false → s'.speicher.bytes x = s.speicher.bytes x) := by
  have hok : laengeOk (kanon b).laenge = true := laengeOk_encode b
  unfold schritt at h
  rw [hok] at h
  cases b with
  | movImm64 dst v =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | movReg64 dst src =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | addReg64 dst src =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | subReg64 dst src =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | xorReg64 dst src =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cmpReg64 lhs rhs =>
    simp only [kanon, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | load64 dst base disp =>
    simp only [kanon] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · cases h
  | store64 base src disp =>
    simp only [kanon] at h
    split at h
    · rename_i m hw
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hs, hx⟩ := write64_erhaelt_berechtigungen _ _ _ _ hw
      exact ⟨rfl, hx, hs, hl, fun x hx' => write64_nicht_schreibbar _ _ _ _ hw x hx'⟩
    · cases h
  | jump32 _ => simp [gerade] at hg
  | jumpIf32 _ _ => simp [gerade] at hg
  | call32 _ => simp [gerade] at hg
  | push64 _ => simp [gerade] at hg
  | pop64 _ => simp [gerade] at hg
  | ret => simp [gerade] at hg

/-- The code region survives every step that keeps permissions and every
    non-writable byte. -/
theorem codeAt_erhalten (m m' : Speicher) (cs : Adresse) (flat : List Byte)
    (hc : CodeAt m cs flat) (hx : m'.ausfuehrbar = m.ausfuehrbar)
    (hs : m'.schreibbar = m.schreibbar)
    (hb : ∀ x, m.schreibbar x = false → m'.bytes x = m.bytes x) :
    CodeAt m' cs flat := by
  intro i b hi
  obtain ⟨h1, h2, h3⟩ := hc i b hi
  refine ⟨by rw [hx]; exact h1, by rw [hs]; exact h2, ?_⟩
  rw [hb _ h2, h3]

/-- Byte runs compose. -/
theorem laufBytes_add : ∀ (n k : Nat) (s s1 : Zustand), laufBytes n s = .weiter s1 →
    laufBytes (n + k) s = laufBytes k s1
  | 0, k, s, s1, h => by
    simp only [laufBytes] at h; cases h; simp
  | n + 1, k, s, s1, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [laufBytes] at h ⊢
    cases hb : byteschritt s with
    | verweigert => rw [hb] at h; cases h
    | weiter s2 =>
      rw [hb] at h
      exact laufBytes_add n k s2 s1 h

/-- THE LAUF-TO-BYTES BRIDGE: a straight-line canonical run whose bytes sit
    at the instruction pointer of a W^X code region is the same run when
    every instruction is FETCHED from actual memory and decoded. -/
theorem lauf_zu_laufBytes (cs : Adresse) (flat : List Byte) :
    ∀ (P : List Befehl) (pre post : List Byte) (s s' : Zustand),
      P.all gerade = true → lauf (P.map kanon) s = some s' →
      CodeAt s.speicher cs flat → flat = pre ++ encodeAll P ++ post →
      s.rip = addrOff cs pre.length →
      laufBytes P.length s = .weiter s' ∧
        s'.rip = addrOff cs (pre.length + (encodeAll P).length) ∧
        CodeAt s'.speicher cs flat ∧
        s'.speicher.lesbar = s.speicher.lesbar ∧
        s'.speicher.schreibbar = s.speicher.schreibbar
  | [], pre, post, s, s', _, hl, hc, _, hrip => by
    simp only [List.map_nil, lauf, Option.some.injEq] at hl
    subst hl
    exact ⟨rfl, by simp [encodeAll, hrip], hc, rfl, rfl⟩
  | b :: P, pre, post, s, s', hg, hl, hc, hf, hrip => by
    simp only [List.all_cons, Bool.and_eq_true] at hg
    simp only [List.map_cons, lauf] at hl
    cases hs : schritt (kanon b) s with
    | none => rw [hs] at hl; cases hl
    | some s1 =>
      rw [hs] at hl
      obtain ⟨hrip1, hx1, hs1, hl1, hb1⟩ := schritt_gerade b s s1 hg.1 hs
      have hc1 : CodeAt s1.speicher cs flat := codeAt_erhalten _ _ _ _ hc hx1 hs1 hb1
      have hf1 : flat = (pre ++ encode b) ++ encodeAll P ++ post := by
        rw [hf, encodeAll_cons]; simp
      have hrip1' : s1.rip = addrOff cs (pre ++ encode b).length := by
        rw [hrip1, hrip, addrOff_addrOff, List.length_append]
      obtain ⟨hb', hr', hc', hl', hs'⟩ :=
        lauf_zu_laufBytes cs flat P (pre ++ encode b) post s1 s' hg.2 hl hc1 hf1 hrip1'
      have hbs : byteschritt s = .weiter s1 := by
        rw [byteschritt_im_code s cs flat pre (encodeAll P ++ post) b hc
          (by rw [hf, encodeAll_cons]; simp) hrip, hs]
      refine ⟨?_, ?_, hc', by rw [hl', hl1], by rw [hs', hs1]⟩
      · simp only [List.length_cons, laufBytes, hbs]
        exact hb'
      · rw [hr', encodeAll_cons]
        simp only [List.length_append]
        congr 1
        omega

/-! ## 2. The world representation over a slot layout

    A layout places some source slots `(t, k, f)` at byte addresses. The
    world representation says: every placed slot is an admitted integer
    slot (`repOk`, reused from `SourceMemory`), its eight bytes are
    readable and writable, and its word is the source value (`RepSlot`).
    `LayoutSep` says two placed slots are the same slot or have disjoint
    eight-byte footprints. -/

variable {D : Deklaration}

/-- A slot layout: where each placed source slot lives. -/
structure Layout (D : Deklaration) where
  loc : (t : D.Tab) → Int → D.Feld t → Option Nat

/-- The target memory represents the source world on every placed slot. -/
def WorldRep (L : Layout D) (m : Speicher) (σ : World D) : Prop :=
  ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat), L.loc t k f = some a →
    repOk (D.typ t f) a 8 0 = true ∧ lesbar8 m (natAdresse a) = true ∧
      schreibbar8 m (natAdresse a) = true ∧
      ∀ (lo hi : Int) (hT : D.typ t f = .int lo hi), RepSlot t k f lo hi hT (natAdresse a) m σ

/-- Two placed slots are the same slot or have disjoint footprints. -/
def LayoutSep (L : Layout D) : Prop :=
  ∀ (t1 : D.Tab) (k1 : Int) (f1 : D.Feld t1) (a1 : Nat)
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2) (a2 : Nat),
    L.loc t1 k1 f1 = some a1 → L.loc t2 k2 f2 = some a2 →
      (t1 = t2 ∧ k1 = k2 ∧ HEq f1 f2) ∨ (a1 + 8 ≤ a2 ∨ a2 + 8 ≤ a1)

/-- Reading only logs trace events: the representation is untouched. -/
theorem worldRep_lese (L : Layout D) (m : Speicher) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) : WorldRep L m (σ.lese Λ o) ↔ WorldRep L m σ :=
  Iff.rfl

/-- An admitted slot type is an integer range with the word bounds. -/
theorem repOk_int (ty : Ty) (a : Nat) (h : repOk ty a 8 0 = true) :
    ∃ lo hi, ty = .int lo hi ∧ 0 ≤ lo ∧ hi < 2 ^ 64 ∧ a + 8 ≤ 2 ^ 64 := by
  cases ty with
  | int lo hi =>
    obtain ⟨h1, h2, -, h4⟩ := repOk_klingt h
    exact ⟨lo, hi, rfl, h1, h2, by omega⟩
  | _ => simp [repOk] at h

/-- An admitted address does not wrap. -/
theorem natAdresse_ohneUmbruch (a : Nat) (h : a + 8 ≤ 2 ^ 64) :
    OhneUmbruch (natAdresse a) := by
  unfold OhneUmbruch natAdresse
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

theorem natAdresse_toNat (a : Nat) (h : a + 8 ≤ 2 ^ 64) : (natAdresse a).toNat = a := by
  unfold natAdresse
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- STORE PRESERVATION: one source slot write together with the matching
    target word write keeps the representation of EVERY placed slot: the
    written one reads back the new value, every other one is untouched on
    both sides (disjoint footprint, other carrier). -/
theorem worldRep_store (L : Layout D) (hsep : LayoutSep L) (m m' : Speicher)
    (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat)
    (hloc : L.loc t k f = some a) (hW : WorldRep L m σ)
    (lo hi : Int) (hT : D.typ t f = .int lo hi) (w : Wert D (D.typ t f))
    (hw : write64 m (natAdresse a)
      (zahlWort (cast (congrArg (Wert D) hT) w : Wert D (.int lo hi))) = some m')
    (Λ : List (Res D)) :
    WorldRep L m' (σ.schreibSlot t Λ k f w) := by
  obtain ⟨hok, hrd, -, -⟩ := hW t k f a hloc
  intro t2 k2 f2 a2 hloc2
  obtain ⟨hok2, hrd2, hwr2, hrep2⟩ := hW t2 k2 f2 a2 hloc2
  refine ⟨hok2, by rw [lesbar8_nach_schreiben m m' _ _ _ hw]; exact hrd2,
    by rw [schreibbar8_nach_schreiben m m' _ _ _ hw]; exact hwr2, ?_⟩
  intro lo2 hi2 hT2
  rcases hsep t k f a t2 k2 f2 a2 hloc hloc2 with ⟨rfl, rfl, hf⟩ | hdis
  · cases hf
    rw [hloc] at hloc2
    cases hloc2
    have hlh : lo2 = lo ∧ hi2 = hi := by
      rw [hT] at hT2
      cases hT2
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hlh
    unfold RepSlot
    rw [schreibSlot_hit]
    exact read64_nach_write64 m m' _ _ hw hrd
  · obtain ⟨lo1, hi1, -, -, -, hA⟩ := repOk_int _ a hok
    obtain ⟨-, -, -, -, -, hA2⟩ := repOk_int _ a2 hok2
    have hdisj : Disjunkt (natAdresse a) (natAdresse a2) :=
      disjunkt_von_intervallen _ _ (natAdresse_ohneUmbruch a hA)
        (natAdresse_ohneUmbruch a2 hA2)
        (by rw [natAdresse_toNat a hA, natAdresse_toNat a2 hA2]; exact hdis)
    have hslot : (σ.schreibSlot t Λ k f w).slots t2 k2 f2 = σ.slots t2 k2 f2 := by
      by_cases ht : t2 = t
      · subst ht
        by_cases hk : k2 = k
        · subst hk
          by_cases hf : f2 = f
          · subst hf
            rw [hloc] at hloc2
            cases hloc2
            omega
          · exact schreibSlot_fremd_feld σ t2 Λ k2 f w k2 f2 rfl hf
        · exact schreibSlot_fremd_schluessel σ t2 Λ k f w k2 f2 hk
      · exact schreibSlot_fremd_tab σ t Λ k f w t2 k2 f2 ht
    have hrep := hrep2 lo2 hi2 hT2
    unfold RepSlot at hrep ⊢
    rw [hslot, read64_rahmen m m' _ _ _ hw hdisj]
    exact hrep

/-! ## 3. Signed comparison through `cmp` flags

    The pilot `cmpReg64` sets the SUB flags; the jump conditions read them.
    These are the generic facts the check lowering consumes. -/

/-- SIGNED LESS: `l` after `cmp x y` is exactly `sint x < sint y`, for
    every pair of words (overflow included). -/
theorem bedingung_l_sub64 (x y : Wort) :
    bedingung .l (sub64 x y).2 = decide (sint x < sint y) := by
  have hx := sint_mem x
  have hy := sint_mem y
  have hsf : (sub64 x y).2.sf = decide ((sint x - sint y).bmod (2 ^ 64) < 0) := by
    rw [sub64_sf_sint, sub64_sint]
  rw [bedingung_l, hsf]
  by_cases hlo : sint x - sint y < -(2 ^ 63 : Int)
  · have hof : (sub64 x y).2.of = true := (sub64_of_iff x y).mpr (Or.inl hlo)
    rw [hof, bmod_low _ (by omega) hlo]
    have h2 : sint x < sint y := by omega
    simp [h2]
    omega
  · by_cases hhi : (2 ^ 63 : Int) ≤ sint x - sint y
    · have hof : (sub64 x y).2.of = true := (sub64_of_iff x y).mpr (Or.inr hhi)
      rw [hof, bmod_high _ hhi (by omega)]
      have h2 : ¬ sint x < sint y := by omega
      simp [h2]
      omega
    · have hof : (sub64 x y).2.of = false := by
        cases hc : (sub64 x y).2.of with
        | false => rfl
        | true =>
          rcases (sub64_of_iff x y).mp hc with h | h
          · exact absurd h hlo
          · exact absurd h hhi
      rw [hof, bmod_in_range _ (by omega) (by omega)]
      by_cases h3 : sint x < sint y
      · have h4 : sint x - sint y < 0 := by omega
        simp [h3, h4]
      · have h4 : ¬ sint x - sint y < 0 := by omega
        simp [h3, h4]

/-- ZERO: `zf` after `cmp x y` is word equality. -/
theorem sub64_zf_eq (x y : Wort) : (sub64 x y).2.zf = decide (x = y) := by
  rw [sub64_zf]
  unfold zfTest
  by_cases h : x = y
  · subst h; simp
  · have hne : ¬ (x - y = 0#64) := fun he => h (
      calc x = x - y + y := (BitVec.sub_add_cancel x y).symm
        _ = 0#64 + y := by rw [he]
        _ = y := BitVec.zero_add y)
    simp [h, hne]

/-- Signed reading is injective on words. -/
theorem sint_inj (x y : Wort) : sint x = sint y ↔ x = y :=
  ⟨fun h => BitVec.eq_of_toInt_eq h, fun h => h ▸ rfl⟩

/-- `ge` after `cmp`: not signed-less. -/
theorem bedingung_ge_sub64 (x y : Wort) :
    bedingung .ge (sub64 x y).2 = !decide (sint x < sint y) := by
  rw [← bedingung_l_sub64, bedingung_ge, bedingung_l]
  cases (sub64 x y).2.sf <;> cases (sub64 x y).2.of <;> rfl

/-- `g` after `cmp`: signed-greater. -/
theorem bedingung_g_sub64 (x y : Wort) :
    bedingung .g (sub64 x y).2 = decide (sint y < sint x) := by
  have hl := bedingung_l_sub64 x y
  rw [bedingung_l] at hl
  rw [bedingung_g, sub64_zf_eq]
  have hge : ((sub64 x y).2.sf == (sub64 x y).2.of) =
      !((sub64 x y).2.sf != (sub64 x y).2.of) := by
    cases (sub64 x y).2.sf <;> cases (sub64 x y).2.of <;> rfl
  rw [hge, hl]
  by_cases he : x = y
  · subst he; simp
  · have hne : sint x ≠ sint y := fun h => he ((sint_inj x y).mp h)
    by_cases hlt : sint x < sint y
    · have : ¬ sint y < sint x := by omega
      simp [he, hlt, this]
    · have : sint y < sint x := by omega
      simp [he, hlt, this]

/-- `ne` after `cmp`: word inequality. -/
theorem bedingung_ne_sub64 (x y : Wort) :
    bedingung .ne (sub64 x y).2 = !decide (x = y) := by
  rw [bedingung_ne, sub64_zf_eq]

/-! ## 4. Configuration, register map and freshness

    Every target choice of the lowering is DATA in `PipeCfg`, and the
    freshness facts the correctness proof needs are DECIDED by `cfgOk`:
    the three working registers are pairwise distinct, none of them is
    `rsp`, and no source variable lives in one of them. -/

/-- The target configuration of one lowering. -/
structure PipeCfg where
  /-- Register of the `i`-th context variable. -/
  regs : List Register
  /-- Value register. -/
  dst : Register
  /-- Scratch register. -/
  tmp : Register
  /-- Address register for slot stores. -/
  adr : Register
  /-- First code byte. -/
  codeBase : Nat
  /-- Refusal exits: reason `r` exits at `exitBase + exitStride * r`
      (`exitAdr`). -/
  exitBase : Nat
  /-- Distance between the refusal exits of consecutive reasons. The
      default `1` is the original layout (`exitBase + r`); an image with a
      stub per reason needs a stride of at least the stub length plus one
      (`PipelineImage`). -/
  exitStride : Nat := 1
  /-- Further scratch registers for arbitrary-depth values and checks
      (`ExpressionLoweringDeep.senkTief`): the deep lowering works over the
      register stack `tmp :: frei`. The default `[]` keeps exactly the
      original one-level fragment's register budget (`tmp` alone). -/
  frei : List Register := []
  deriving DecidableEq, Repr

/-- The refusal exit of reason `g`. -/
def exitAdr (c : PipeCfg) (g : Nat) : Nat := c.exitBase + c.exitStride * g

/-- With the default stride the exits are the original `exitBase + g`. -/
theorem exitAdr_eins (c : PipeCfg) (h : c.exitStride = 1) (g : Nat) :
    exitAdr c g = c.exitBase + g := by
  unfold exitAdr
  rw [h, Nat.one_mul]

/-- Distinct reasons have exits at least one stride apart. -/
theorem exitAdr_abstand (c : PipeCfg) (g g' : Nat) (h : g < g') :
    exitAdr c g + c.exitStride ≤ exitAdr c g' := by
  unfold exitAdr
  have : c.exitStride * g + c.exitStride ≤ c.exitStride * g' := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ h
  omega

/-- Position of a variable in its context. -/
def varIdx : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .hier => 0
  | _, _, .dort x => varIdx x + 1

/-- The register map: the `i`-th variable lives in `regs[i]` (`rsp` past
    the list, which the freshness check keeps apart from every working
    register). -/
def abbOf (c : PipeCfg) {Γ : Ctx} : ∀ (τ : Ty), Var Γ τ → Register :=
  fun _ x => c.regs.getD (varIdx x) .rsp

/-- The decided freshness check. -/
def cfgOk (c : PipeCfg) : Bool :=
  decide (c.dst ∉ c.regs ∧ c.tmp ∉ c.regs ∧ c.adr ∉ c.regs ∧ c.dst ≠ c.tmp ∧
    c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧ c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧ c.adr ≠ .rsp ∧
    c.frei.Nodup ∧ ∀ r ∈ c.frei, r ∉ c.regs ∧ r ≠ c.dst ∧ r ≠ c.tmp ∧ r ≠ c.adr ∧ r ≠ .rsp)

/-- A mapped variable register is listed or `rsp`. -/
theorem abbOf_mem (c : PipeCfg) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    abbOf c τ x ∈ c.regs ∨ abbOf c τ x = .rsp := by
  unfold abbOf
  rw [List.getD_eq_getElem?_getD]
  cases h : c.regs[varIdx x]? with
  | none => exact Or.inr rfl
  | some r => exact Or.inl (List.mem_of_getElem? h)

/-- The checked configuration is fresh: no variable lives in a working
    register. -/
theorem cfgOk_frei (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    abbOf c τ x ≠ c.dst ∧ abbOf c τ x ≠ c.tmp ∧ abbOf c τ x ≠ c.adr := by
  unfold cfgOk at hc
  simp only [decide_eq_true_eq] at hc
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, -⟩ := hc
  rcases abbOf_mem c x with hm | hm
  · exact ⟨fun e => h1 (e ▸ hm), fun e => h2 (e ▸ hm), fun e => h3 (e ▸ hm)⟩
  · rw [hm]
    exact ⟨Ne.symm h7, Ne.symm h8, Ne.symm h9⟩

/-- The working registers are pairwise distinct and none is `rsp`. -/
theorem cfgOk_regs (c : PipeCfg) (hc : cfgOk c = true) :
    c.dst ≠ c.tmp ∧ c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧ c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧
      c.adr ≠ .rsp := by
  unfold cfgOk at hc
  simp only [decide_eq_true_eq] at hc
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, -⟩ := hc
  exact ⟨h4, h5, h6, h7, h8, h9⟩

/-- The accepted `Frisch` premise of `senkung_korrekt`, derived. -/
theorem cfgOk_frisch (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} :
    Frisch (abbOf c (Γ := Γ)) c.dst c.tmp :=
  ⟨fun _ x => ⟨(cfgOk_frei c hc x).1, (cfgOk_frei c hc x).2.1⟩, (cfgOk_regs c hc).1⟩

/-- The environment survives a register change outside the variable map. -/
theorem envRepr_fremd {Γ : Ctx} (ρ : Env D Γ) (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (r r' : Register → Wort) (h : EnvRepr ρ r abb)
    (hr : ∀ (τ : Ty) (x : Var Γ τ), r' (abb τ x) = r (abb τ x)) : EnvRepr ρ r' abb := by
  intro lo hi x
  rw [hr, h]

/-- The scratch facts the checked configuration decides. -/
theorem cfgOk_frei_liste (c : PipeCfg) (hc : cfgOk c = true) :
    c.frei.Nodup ∧ ∀ r ∈ c.frei, r ∉ c.regs ∧ r ≠ c.dst ∧ r ≠ c.tmp ∧ r ≠ c.adr ∧ r ≠ .rsp := by
  unfold cfgOk at hc
  simp only [decide_eq_true_eq] at hc
  exact hc.2.2.2.2.2.2.2.2.2

/-- The checked configuration is LIST-fresh for the deep lowering
    (`ExpressionLoweringDeep.FrischListe`): no variable lives in `dst` or
    on the scratch stack `tmp :: frei`, `dst` is not on the stack, and the
    stack has no duplicate. -/
theorem cfgOk_frischListe (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} :
    FrischListe (abbOf c (Γ := Γ)) c.dst (c.tmp :: c.frei) := by
  obtain ⟨hnd, hfr⟩ := cfgOk_frei_liste c hc
  obtain ⟨hdt, -, -, -, -, -⟩ := cfgOk_regs c hc
  refine ⟨fun τ x => ⟨(cfgOk_frei c hc x).1, ?_⟩, ?_, ?_⟩
  · intro hin
    rcases List.mem_cons.mp hin with he | he
    · exact (cfgOk_frei c hc x).2.1 he
    · rcases abbOf_mem c x with hm | hm
      · exact (hfr _ he).1 hm
      · exact (hfr _ he).2.2.2.2 hm
  · intro hin
    rcases List.mem_cons.mp hin with he | he
    · exact hdt he
    · exact (hfr _ he).2.1 rfl
  · exact List.nodup_cons.mpr ⟨fun hin => (hfr _ hin).2.2.1 rfl, hnd⟩

/-- `rsp` is neither the value register nor on the scratch stack. -/
theorem cfgOk_rsp (c : PipeCfg) (hc : cfgOk c = true) :
    c.dst ≠ .rsp ∧ Register.rsp ∉ c.tmp :: c.frei := by
  obtain ⟨-, hfr⟩ := cfgOk_frei_liste c hc
  obtain ⟨-, -, -, hdr, htr, -⟩ := cfgOk_regs c hc
  refine ⟨hdr, fun hin => ?_⟩
  rcases List.mem_cons.mp hin with he | he
  · exact htr he.symm
  · exact (hfr _ he).2.2.2.2 rfl

/-- A variable register is off the scratch stack (so the deep code keeps
    the environment). -/
theorem cfgOk_var_frei (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    abbOf c τ x ≠ c.dst ∧ abbOf c τ x ∉ c.tmp :: c.frei :=
  (cfgOk_frischListe c hc).1 τ x

/-! ## 5. Value lowering: the accepted fragment plus widening

    The optimiser's integer fold produces `weiter (lit v)` (the literal
    widened back to the slot type, `OptimizationRules.foldInt`). `weiter`
    keeps the number, so its code is the code of the widened operand; every
    other value goes to the accepted `senkFrag` unchanged. -/

/-- Value lowering: strip one `weiter`, then the accepted fragment. -/
def senkWert {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp : Register) : Option (List Befehl) :=
  match e with
  | .weiter _ _ e' => senkFrag abb e' dst tmp
  | _ => senkFrag abb e dst tmp

/-- Shape of a lowered value (inversion substitutes the expression). -/
inductive IstWert {Γ : Ctx} {Λ : List (Res D)} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) : ∀ {τ : Ty}, Expr D Γ Λ τ → List Befehl → Prop where
  | frag {τ : Ty} (e : Expr D Γ Λ τ) (p : List Befehl) (h : senkFrag abb e dst tmp = some p) :
      IstWert abb dst tmp e p
  | weiter {lo hi lo' hi' : Int} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (e : Expr D Γ Λ (.int lo hi))
      (p : List Befehl) (h : senkFrag abb e dst tmp = some p) :
      IstWert abb dst tmp (.weiter h1 h2 e) p

theorem istWert_von {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (p : List Befehl) (h : senkWert abb e dst tmp = some p) : IstWert abb dst tmp e p := by
  cases e with
  | weiter h1 h2 e' => exact .weiter h1 h2 e' p h
  | _ => exact .frag _ p h

/-- Every lowered atom is straight-line code. -/
theorem senkAtom_gerade {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (a : Expr D Γ Λ τ) (dst : Register)
    (pa : List Befehl) (ha : senkAtom abb a dst = some pa) : pa.all gerade = true := by
  cases istAtom_von_senkAtom abb a dst pa ha with
  | lit n => simp only [senkAtom, Option.some.injEq] at ha; subst ha; rfl
  | var x => simp only [senkAtom, Option.some.injEq] at ha; subst ha; rfl

/-- Every lowered fragment is straight-line code. -/
theorem senkFrag_gerade {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (p : List Befehl) (h : senkFrag abb e dst tmp = some p) : p.all gerade = true := by
  cases istFrag_von_senkFrag abb e dst tmp p h with
  | lit n => rfl
  | var x => rfl
  | add a b pa pb ha hb =>
    simp [List.all_append, senkAtom_gerade abb a dst pa ha, senkAtom_gerade abb b tmp pb hb,
      gerade]
  | sub a b pa pb ha hb =>
    simp [List.all_append, senkAtom_gerade abb a dst pa ha, senkAtom_gerade abb b tmp pb hb,
      gerade]

theorem senkWert_gerade {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (p : List Befehl) (h : senkWert abb e dst tmp = some p) : p.all gerade = true := by
  cases istWert_von abb e dst tmp p h with
  | frag e p h => exact senkFrag_gerade abb e dst tmp p h
  | weiter h1 h2 e p h => exact senkFrag_gerade abb e dst tmp p h

/-- VALUE CORRECTNESS: the lowered value code leaves the modular word of
    the exact source value in `dst`, keeps memory and every register but
    the two working ones. Stated at a general type index with the
    equation `τ = .int lo hi`, so it applies at the stuck slot type
    `D.typ t f`. -/
theorem senkWert_korrekt {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {lo hi : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (hτ : τ = .int lo hi)
    (dst tmp : Register) (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hrenv : EnvRepr ρ s.register abb) (p : List Befehl)
    (h : senkWert abb e dst tmp = some p) :
    ∃ s', lauf (p.map kanon) s = some s' ∧
      s'.register dst = intWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) :
        Wert D (.int lo hi)).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) := by
  subst hτ
  cases istWert_von abb e dst tmp p h with
  | frag e p h =>
    obtain ⟨s', hrun, hval, hmem, hreg, -⟩ :=
      senkung_korrekt abb e dst tmp ρ σ₀ σ s hfr hrsp hrenv p h
    exact ⟨s', hrun, hval, hmem, hreg⟩
  | weiter h1 h2 e p h =>
    obtain ⟨s', hrun, hval, hmem, hreg, -⟩ :=
      senkung_korrekt abb e dst tmp ρ σ₀ σ s hfr hrsp hrenv p h
    exact ⟨s', hrun, hval, hmem, hreg⟩

/-! ## 5a. Deep values: arbitrary-depth trees over the scratch stack

    The widened value lowering is `ExpressionLoweringDeep.senkTief` over
    the register stack `tmp :: frei` of the configuration: `lit`/`var`/
    `weiter`/`add`/`sub`/`neg` trees of any depth, refused (`none`) on every
    other form and on stack exhaustion. The original fragment is a special
    case: what `senkWert` lowers, `senkTief` lowers to the SAME code for
    every scratch tail (`senkWert_als_tief`), so the old programs keep their
    bytes. -/

/-- The widened value lowering of a configuration. -/
def senkWertT (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Option (List Befehl) :=
  senkTief (abbOf c) e c.dst (c.tmp :: c.frei)

/-- An atom lowers to the same code under the deep lowering, whatever the
    scratch stack. -/
theorem senkAtom_als_tief {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (a : Expr D Γ Λ τ) (dst : Register)
    (frei : List Register) (pa : List Befehl) (ha : senkAtom abb a dst = some pa) :
    senkTief abb a dst frei = some pa := by
  cases istAtom_von_senkAtom abb a dst pa ha with
  | lit n => exact ha
  | var x => exact ha

/-- THE ORIGINAL FRAGMENT IS A SPECIAL CASE: whatever `senkWert` lowers,
    the deep lowering lowers to exactly the same instructions, for every
    scratch tail. -/
theorem senkWert_als_tief {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (rest : List Register) (p : List Befehl) (h : senkWert abb e dst tmp = some p) :
    senkTief abb e dst (tmp :: rest) = some p := by
  have frag : ∀ {τ' : Ty} (e' : Expr D Γ Λ τ') (p' : List Befehl),
      senkFrag abb e' dst tmp = some p' → senkTief abb e' dst (tmp :: rest) = some p' := by
    intro τ' e' p' h'
    cases istFrag_von_senkFrag abb e' dst tmp p' h' with
    | lit n => exact h'
    | var x => exact h'
    | add a b pa pb ha hb =>
      simp [senkTief, senkAtom_als_tief abb a dst rest pa ha, senkAtom_als_tief abb b tmp rest pb hb]
    | sub a b pa pb ha hb =>
      simp [senkTief, senkAtom_als_tief abb a dst rest pa ha, senkAtom_als_tief abb b tmp rest pb hb]
  cases istWert_von abb e dst tmp p h with
  | frag e p h => exact frag e p h
  | weiter h1 h2 e p h => exact frag e p h

/-- Every deep lowering is straight-line code. -/
theorem istTief_gerade {Γ : Ctx} {Λ : List (Res D)} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    {τ : Ty} {e : Expr D Γ Λ τ} {dst : Register} {frei : List Register} {p : List Befehl}
    (h : IstTief abb e dst frei p) : p.all gerade = true := by
  induction h with
  | lit => rfl
  | var => rfl
  | weiter _ _ _ _ _ _ _ ih => exact ih
  | add _ _ _ _ _ _ _ _ _ iha ihb => simp [List.all_append, iha, ihb, gerade]
  | sub _ _ _ _ _ _ _ _ _ iha ihb => simp [List.all_append, iha, ihb, gerade]
  | neg _ _ _ _ _ _ iha => simp [List.all_append, iha, gerade]

theorem senkWertT_gerade (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (p : List Befehl) (h : senkWertT c e = some p) : p.all gerade = true :=
  istTief_gerade _ (istTief_von_senkTief _ e _ _ p h)

/-- DEEP VALUE CORRECTNESS: the widened value code leaves the modular word
    of the exact source value in `dst`, keeps memory, and keeps every
    register off the stack `dst :: tmp :: frei` (in particular every
    variable register). Stated at a general type index with `τ = .int lo hi`
    (the stuck slot type `D.typ t f`). -/
theorem senkWertT_korrekt (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {lo hi : Int} (e : Expr D Γ Λ τ) (hτ : τ = .int lo hi)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand) (hE : EnvRepr ρ s.register (abbOf c))
    (p : List Befehl) (h : senkWertT c e = some p) :
    ∃ s', lauf (p.map kanon) s = some s' ∧
      s'.register c.dst = intWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) :
        Wert D (.int lo hi)).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ c.dst → q ∉ c.tmp :: c.frei → s'.register q = s.register q) := by
  subst hτ
  obtain ⟨s', hrun, hval, hmem, hreg, -⟩ := istTief_korrekt (abbOf c) e c.dst (c.tmp :: c.frei) p
    (istTief_von_senkTief _ e _ _ p h) ρ σ₀ σ s (cfgOk_frischListe c hc) (cfgOk_rsp c hc) hE
  exact ⟨s', hrun, hval, hmem, hreg⟩

/-- The environment survives deep code. -/
theorem envRepr_tief (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} (ρ : Env D Γ)
    (r r' : Register → Wort) (h : EnvRepr ρ r (abbOf c))
    (hr : ∀ q, q ≠ c.dst → q ∉ c.tmp :: c.frei → r' q = r q) : EnvRepr ρ r' (abbOf c) :=
  envRepr_fremd ρ _ _ _ h (fun _ x => hr _ (cfgOk_var_frei c hc x).1 (cfgOk_var_frei c hc x).2)

/-! ## 6. Check lowering: `cmp` plus a conditional jump to a refusal exit

    A `pruefung` over a signed comparison of two atoms lowers to the two
    atom loads, `cmpReg64 dst tmp`, and `jumpIf32` on the NEGATED condition
    to the refusal exit of its reason. The literal condition `true` (what
    the optimiser's condition fold leaves) lowers to no code. -/

/-- The signed 64-bit window of an integer range. -/
def imSigned (lo hi : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ lo ∧ hi < 2 ^ 63)

/-- Compare two atoms; `j` is the jump-to-refusal condition. -/
def vergleich {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) (dst tmp : Register)
    (j : Bedingung) : Option (List Befehl × Bedingung) :=
  if imSigned l1 h1 && imSigned l2 h2 then
    match senkAtom abb a dst, senkAtom abb b tmp with
    | some pa, some pb => some (pa ++ pb ++ [.cmpReg64 dst tmp], j)
    | _, _ => none
  else none

/-- Condition lowering: `<`, `<=`, `=` over atoms; everything else refuses. -/
def senkBed {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp : Register) : Option (List Befehl × Bedingung) :=
  match e with
  | .lt a b => vergleich abb a b dst tmp .ge
  | .le a b => vergleich abb a b dst tmp .g
  | .eq a b => vergleich abb a b dst tmp .ne
  | _ => none

/-- The literal `true`. -/
def istWahr {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : Bool :=
  match e with
  | .wahr => true
  | _ => false

theorem istWahr_wahr {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (h : istWahr e = true) (σ₀ σ : World D) (ρ : Env D Γ) :
    boolOf τ (eval σ₀ e σ ρ) = some true := by
  cases e with
  | wahr => rfl
  | _ => simp [istWahr] at h

/-- Shape of a lowered condition. -/
inductive IstBed {Γ : Ctx} {Λ : List (Res D)} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) : ∀ {τ : Ty}, Expr D Γ Λ τ → List Befehl → Bedingung → Prop where
  | lt {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (pa pb : List Befehl) (hs1 : imSigned l1 h1 = true) (hs2 : imSigned l2 h2 = true)
      (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
      IstBed abb dst tmp (.lt a b) (pa ++ pb ++ [.cmpReg64 dst tmp]) .ge
  | le {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (pa pb : List Befehl) (hs1 : imSigned l1 h1 = true) (hs2 : imSigned l2 h2 = true)
      (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
      IstBed abb dst tmp (.le a b) (pa ++ pb ++ [.cmpReg64 dst tmp]) .g
  | eq {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (pa pb : List Befehl) (hs1 : imSigned l1 h1 = true) (hs2 : imSigned l2 h2 = true)
      (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
      IstBed abb dst tmp (.eq a b) (pa ++ pb ++ [.cmpReg64 dst tmp]) .ne

theorem vergleich_inv {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) (dst tmp : Register)
    (j j' : Bedingung) (code : List Befehl)
    (h : vergleich abb a b dst tmp j = some (code, j')) :
    imSigned l1 h1 = true ∧ imSigned l2 h2 = true ∧ j' = j ∧
      ∃ pa pb, senkAtom abb a dst = some pa ∧ senkAtom abb b tmp = some pb ∧
        code = pa ++ pb ++ [.cmpReg64 dst tmp] := by
  unfold vergleich at h
  by_cases hs : (imSigned l1 h1 && imSigned l2 h2) = true
  · rw [if_pos hs] at h
    simp only [Bool.and_eq_true] at hs
    cases ha : senkAtom abb a dst with
    | none => rw [ha] at h; cases h
    | some pa =>
      cases hb : senkAtom abb b tmp with
      | none => rw [ha, hb] at h; cases h
      | some pb =>
        rw [ha, hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨hs.1, hs.2, h.2.symm, pa, pb, rfl, rfl, h.1.symm⟩
  · rw [if_neg hs] at h; cases h

theorem istBed_von {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (code : List Befehl) (j : Bedingung) (h : senkBed abb e dst tmp = some (code, j)) :
    IstBed abb dst tmp e code j := by
  cases e with
  | lt a b =>
    obtain ⟨h1, h2, rfl, pa, pb, ha, hb, rfl⟩ := vergleich_inv abb a b dst tmp _ _ _ h
    exact .lt a b pa pb h1 h2 ha hb
  | le a b =>
    obtain ⟨h1, h2, rfl, pa, pb, ha, hb, rfl⟩ := vergleich_inv abb a b dst tmp _ _ _ h
    exact .le a b pa pb h1 h2 ha hb
  | eq a b =>
    obtain ⟨h1, h2, rfl, pa, pb, ha, hb, rfl⟩ := vergleich_inv abb a b dst tmp _ _ _ h
    exact .eq a b pa pb h1 h2 ha hb
  | _ => simp [senkBed] at h

/-- The canonical decoded list of a lowered list is the one the accepted
    lowering lemmas run. -/
theorem map_kanon (P : List Befehl) :
    P.map kanon = P.map fun b => (⟨b, (encode b).length⟩ : Decodiert) := rfl

/-- COMPARE RUN: the two atom loads and the `cmp` leave the SUB flags of
    the two exact source words; memory and every other register stay. -/
theorem vergleich_lauf {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) (dst tmp : Register)
    (pa pb : List Befehl) (ha : senkAtom abb a dst = some pa)
    (hb : senkAtom abb b tmp = some pb)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hE : EnvRepr ρ s.register abb) :
    ∃ s', lauf ((pa ++ pb ++ [Befehl.cmpReg64 dst tmp]).map kanon) s = some s' ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) ∧
      s'.flags = (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2 := by
  obtain ⟨hneu, hne⟩ := hfr
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1, -⟩ := senkAtom_korrekt abb a dst ρ σ₀ σ s hE pa ha
  have hE1 : EnvRepr ρ s1.register abb :=
    envRepr_fremd ρ abb _ _ hE (fun τ x => hreg1 _ (hneu τ x).1)
  obtain ⟨s2, hrun2, hval2, hmem2, hreg2, -⟩ := senkAtom_korrekt abb b tmp ρ σ₀ σ s1 hE1 pb hb
  have hd2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by rw [hreg2 dst hne, hval1]
  have hcmp := schritt_cmpReg64 (kanon (.cmpReg64 dst tmp)) s2 dst tmp
    (laengeOk_encode _) rfl
  let s3 : Zustand := { s2 with rip := ripNach s2.rip (kanon (Befehl.cmpReg64 dst tmp)).laenge, flags := (sub64 (s2.register dst) (s2.register tmp)).2 }
  refine ⟨s3, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, map_kanon, map_kanon,
      List.append_assoc, lauf_anhang _ _ _ _ hrun1, lauf_anhang _ _ _ _ hrun2]
    simp only [List.map_cons, List.map_nil, lauf]
    rw [hcmp]
  · show s2.speicher = s.speicher
    rw [hmem2, hmem1]
  · intro q hq1 hq2
    show s2.register q = s.register q
    rw [hreg2 q hq2, hreg1 q hq1]
  · show (sub64 (s2.register dst) (s2.register tmp)).2 = _
    rw [hd2, hval2]

/-- The signed reading of an in-window source number is the number. -/
theorem intWort_sint_zahl {lo hi : Int} (v : Zahl lo hi) (h : imSigned lo hi = true) :
    sint (intWort v.n) = v.n := by
  unfold imSigned at h
  simp only [decide_eq_true_eq] at h
  have := v.lo_le
  have := v.le_hi
  exact intWort_sint _ (by omega) (by omega)

/-- CHECK CORRECTNESS: the lowered condition code runs, keeps memory and
    every register but the working ones, and the jump-to-refusal
    condition holds EXACTLY when the source condition is false. -/
theorem senkBed_korrekt {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (e : Expr D Γ Λ τ) (dst tmp : Register)
    (code : List Befehl) (j : Bedingung) (h : senkBed abb e dst tmp = some (code, j))
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hE : EnvRepr ρ s.register abb) :
    code.all gerade = true ∧
      ∃ s', lauf (code.map kanon) s = some s' ∧ s'.speicher = s.speicher ∧
        (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) ∧
        boolOf τ (eval σ₀ e σ ρ) = some (!bedingung j s'.flags) := by
  cases istBed_von abb e dst tmp code j h with
  | lt a b pa pb hs1 hs2 ha hb =>
    refine ⟨by simp [List.all_append, senkAtom_gerade abb a dst pa ha,
      senkAtom_gerade abb b tmp pb hb, gerade], ?_⟩
    obtain ⟨s', hrun, hmem, hreg, hfl⟩ := vergleich_lauf abb a b dst tmp pa pb ha hb ρ σ₀ σ s hfr hE
    refine ⟨s', hrun, hmem, hreg, ?_⟩
    rw [hfl, bedingung_ge_sub64, intWort_sint_zahl (eval σ₀ a σ ρ) hs1,
      intWort_sint_zahl (eval σ₀ b σ ρ) hs2]
    simp [boolOf, eval]
  | le a b pa pb hs1 hs2 ha hb =>
    refine ⟨by simp [List.all_append, senkAtom_gerade abb a dst pa ha,
      senkAtom_gerade abb b tmp pb hb, gerade], ?_⟩
    obtain ⟨s', hrun, hmem, hreg, hfl⟩ := vergleich_lauf abb a b dst tmp pa pb ha hb ρ σ₀ σ s hfr hE
    refine ⟨s', hrun, hmem, hreg, ?_⟩
    rw [hfl, bedingung_g_sub64, intWort_sint_zahl (eval σ₀ a σ ρ) hs1,
      intWort_sint_zahl (eval σ₀ b σ ρ) hs2]
    simp only [boolOf, eval, Option.some.injEq]
    by_cases hc : (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n
    · have : ¬ (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n := by omega
      simp [hc, this]
    · have : (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n := by omega
      simp [hc, this]
  | eq a b pa pb hs1 hs2 ha hb =>
    refine ⟨by simp [List.all_append, senkAtom_gerade abb a dst pa ha,
      senkAtom_gerade abb b tmp pb hb, gerade], ?_⟩
    obtain ⟨s', hrun, hmem, hreg, hfl⟩ := vergleich_lauf abb a b dst tmp pa pb ha hb ρ σ₀ σ s hfr hE
    refine ⟨s', hrun, hmem, hreg, ?_⟩
    rw [hfl, bedingung_ne_sub64]
    have hiff : intWort (eval σ₀ a σ ρ).n = intWort (eval σ₀ b σ ρ).n ↔
        (eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n := by
      rw [← sint_inj, intWort_sint_zahl (eval σ₀ a σ ρ) hs1,
        intWort_sint_zahl (eval σ₀ b σ ρ) hs2]
    simp only [boolOf, eval, Option.some.injEq, Bool.not_not]
    by_cases hc : (eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n
    · simp [hc]
    · have : ¬ intWort (eval σ₀ a σ ρ).n = intWort (eval σ₀ b σ ρ).n := fun h' => hc (hiff.mp h')
      simp [hc, this]

/-! ## 6a. Deep checks: arbitrary-depth operands through `senkVergleich`

    A comparison `<`/`<=`/`=` whose two operands are arbitrary-depth
    `senkTief` trees is lowered by `ExpressionLoweringDeep.senkVergleich`
    over the stack `tmp :: frei`; the jump condition is the x86 NEGATION
    (`negBed`) of the condition `senkVergleich` names for "true". The
    decided range side condition is the one the original fragment already
    used: both operand TYPES lie in the signed 64-bit window (`imSigned`).
    That is enough at any depth: the operand registers hold the modular
    word of the exact value (`istTief_korrekt`), the exact value lies in
    its type range, so the signed reading is the exact value, and the
    flag facts `bedingung_*_sub64` hold for EVERY pair of words (overflow
    of the `cmp` subtraction included). No subtree bound is needed. -/

/-- The x86 negation of a condition code. -/
def negBed : Bedingung → Bedingung
  | .o => .no | .no => .o | .b => .ae | .ae => .b | .e => .ne | .ne => .e
  | .be => .a | .a => .be | .s => .ns | .ns => .s | .p => .np | .np => .p
  | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- The negated condition is the Boolean negation, on every flag state. -/
theorem bedingung_negBed (j : Bedingung) (f : Flags) :
    bedingung (negBed j) f = !bedingung j f := by
  cases f with
  | mk cf pf af zf sf of =>
    cases j <;> simp only [negBed, bedingung, Bool.not_not] <;>
      cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of <;> rfl

/-- The decided range side condition of a comparison: both operand types
    in the signed 64-bit window; every other form is refused. -/
def imFensterB {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : Bool :=
  match e with
  | .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ => imSigned l1 h1 && imSigned l2 h2
  | .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ => imSigned l1 h1 && imSigned l2 h2
  | .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ => imSigned l1 h1 && imSigned l2 h2
  | _ => false

/-- Deep check lowering: the comparison code and the jump-to-refusal (or
    jump-to-else) condition, i.e. the negation of the truth condition. -/
def senkBedT (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Option (List Befehl × Bedingung) :=
  if imFensterB e then
    match senkVergleich (abbOf c) e c.dst (c.tmp :: c.frei) with
    | some (code, j) => some (code, negBed j)
    | none => none
  else none

/-- DEEP COMPARE RUN: the two deep operand codes and the `cmp` leave the
    SUB flags of the two exact source words; memory and every register off
    the stack stay. (The register-stack argument of
    `ExpressionLoweringDeep.istVergleich_korrekt`, stopped at the flags.) -/
theorem vergleichT_lauf {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) (dst tmp : Register)
    (rest : List Register) (pa pb : List Befehl) (ha : IstTief abb a dst rest pa)
    (hb : IstTief abb b tmp rest pb) (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : FrischListe abb dst (tmp :: rest))
    (hrsp : dst ≠ Register.rsp ∧ Register.rsp ∉ tmp :: rest)
    (hE : EnvRepr ρ s.register abb) :
    ∃ s', lauf ((pa ++ pb ++ [Befehl.cmpReg64 dst tmp]).map kanon) s = some s' ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ∉ tmp :: rest → s'.register q = s.register q) ∧
      s'.flags = (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2 := by
  have hfrA := frischListe_tail abb dst tmp rest hfr
  have hfrB := frischListe_kopf abb dst tmp rest hfr
  have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
  have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
  have hrspTmp : tmp ≠ Register.rsp := by
    intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1, -⟩ :=
    istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hE
  have hE1 : EnvRepr ρ s1.register abb := by
    intro lo' hi' x
    have hx := hfr.1 _ x
    rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
    exact hE lo' hi' x
  obtain ⟨s2, hrun2, hval2, hmem2, hreg2, -⟩ :=
    istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hE1
  have hd2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
    rw [hreg2 dst hdstTmp (fun hin => hfr.2.1 (List.mem_cons_of_mem _ hin))]
    exact hval1
  have hcmp := schritt_cmpReg64 (kanon (.cmpReg64 dst tmp)) s2 dst tmp (laengeOk_encode _) rfl
  let s3 : Zustand := { s2 with rip := ripNach s2.rip (kanon (Befehl.cmpReg64 dst tmp)).laenge, flags := (sub64 (s2.register dst) (s2.register tmp)).2 }
  refine ⟨s3, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, map_kanon, map_kanon,
      List.append_assoc, lauf_anhang _ _ _ _ hrun1, lauf_anhang _ _ _ _ hrun2]
    simp only [List.map_cons, List.map_nil, lauf]
    rw [hcmp]
  · show s2.speicher = s.speicher
    rw [hmem2, hmem1]
  · intro q hq1 hq2
    have hqt : q ≠ tmp := fun he => hq2 (he ▸ List.mem_cons_self)
    have hqr : q ∉ rest := fun hin => hq2 (List.mem_cons_of_mem _ hin)
    show s2.register q = s.register q
    rw [hreg2 q hqt hqr, hreg1 q hq1 hqr]
  · show (sub64 (s2.register dst) (s2.register tmp)).2 = _
    rw [hd2, hval2]

/-- DEEP CHECK CORRECTNESS: the lowered condition code is straight-line,
    runs, keeps memory and every register off the stack, and the jump
    condition holds EXACTLY when the source condition is false. -/
theorem senkBedT_korrekt (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) (code : List Befehl) (j : Bedingung)
    (h : senkBedT c e = some (code, j)) (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hE : EnvRepr ρ s.register (abbOf c)) :
    code.all gerade = true ∧
      ∃ s', lauf (code.map kanon) s = some s' ∧ s'.speicher = s.speicher ∧
        (∀ q, q ≠ c.dst → q ∉ c.tmp :: c.frei → s'.register q = s.register q) ∧
        wahr? (eval σ₀ e σ ρ) = !bedingung j s'.flags := by
  unfold senkBedT at h
  by_cases hf : imFensterB e = true
  · rw [if_pos hf] at h
    cases hv : senkVergleich (abbOf c) e c.dst (c.tmp :: c.frei) with
    | none => rw [hv] at h; cases h
    | some cj =>
      obtain ⟨code', j'⟩ := cj
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfr := cfgOk_frischListe c hc (Γ := Γ)
      have hrsp := cfgOk_rsp c hc
      cases istVergleich_von_senkVergleich _ e _ _ _ _ hv with
      | lt a b dst tmp rest pa pb ha hb =>
        simp only [imFensterB, Bool.and_eq_true] at hf
        refine ⟨by simp [List.all_append, istTief_gerade _ ha, istTief_gerade _ hb, gerade], ?_⟩
        obtain ⟨s', hrun, hmem, hreg, hfl⟩ :=
          vergleichT_lauf _ a b _ _ _ pa pb ha hb ρ σ₀ σ s hfr hrsp hE
        refine ⟨s', hrun, hmem, hreg, ?_⟩
        rw [bedingung_negBed, Bool.not_not, hfl, bedingung_l_sub64,
          intWort_sint_zahl (eval σ₀ a σ ρ) hf.1, intWort_sint_zahl (eval σ₀ b σ ρ) hf.2]
        rfl
      | le a b dst tmp rest pa pb ha hb =>
        simp only [imFensterB, Bool.and_eq_true] at hf
        refine ⟨by simp [List.all_append, istTief_gerade _ ha, istTief_gerade _ hb, gerade], ?_⟩
        obtain ⟨s', hrun, hmem, hreg, hfl⟩ :=
          vergleichT_lauf _ a b _ _ _ pa pb ha hb ρ σ₀ σ s hfr hrsp hE
        refine ⟨s', hrun, hmem, hreg, ?_⟩
        rw [show negBed .le = .g from rfl, hfl, bedingung_g_sub64,
          intWort_sint_zahl (eval σ₀ a σ ρ) hf.1, intWort_sint_zahl (eval σ₀ b σ ρ) hf.2]
        show decide ((eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n) = _
        by_cases hc' : (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n
        · have : ¬ (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n := by omega
          simp [hc', this]
        · have : (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n := by omega
          simp [hc', this]
      | eq a b dst tmp rest pa pb ha hb =>
        simp only [imFensterB, Bool.and_eq_true] at hf
        refine ⟨by simp [List.all_append, istTief_gerade _ ha, istTief_gerade _ hb, gerade], ?_⟩
        obtain ⟨s', hrun, hmem, hreg, hfl⟩ :=
          vergleichT_lauf _ a b _ _ _ pa pb ha hb ρ σ₀ σ s hfr hrsp hE
        refine ⟨s', hrun, hmem, hreg, ?_⟩
        rw [show negBed .e = .ne from rfl, hfl, bedingung_ne_sub64]
        have hiff : intWort (eval σ₀ a σ ρ).n = intWort (eval σ₀ b σ ρ).n ↔
            (eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n := by
          rw [← sint_inj, intWort_sint_zahl (eval σ₀ a σ ρ) hf.1,
            intWort_sint_zahl (eval σ₀ b σ ρ) hf.2]
        show decide ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) = _
        by_cases hc' : (eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n
        · simp [hc']
        · have : ¬ intWort (eval σ₀ a σ ρ).n = intWort (eval σ₀ b σ ρ).n :=
            fun h' => hc' (hiff.mp h')
          simp [hc', this]
  · rw [if_neg hf] at h; cases h

/-- THE ORIGINAL CHECK FRAGMENT IS A SPECIAL CASE: what `senkBed` lowers
    (atoms, signed window) the deep check lowers to the SAME code and the
    SAME jump condition, for every scratch tail. -/
theorem senkBed_als_tief (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (code : List Befehl) (j : Bedingung)
    (h : senkBed (abbOf c) e c.dst c.tmp = some (code, j)) : senkBedT c e = some (code, j) := by
  cases istBed_von (abbOf c) e c.dst c.tmp code j h with
  | lt a b pa pb hs1 hs2 ha hb =>
    simp [senkBedT, imFensterB, hs1, hs2, senkVergleich,
      senkAtom_als_tief _ a _ c.frei pa ha, senkAtom_als_tief _ b _ c.frei pb hb, negBed]
  | le a b pa pb hs1 hs2 ha hb =>
    simp [senkBedT, imFensterB, hs1, hs2, senkVergleich,
      senkAtom_als_tief _ a _ c.frei pa ha, senkAtom_als_tief _ b _ c.frei pb hb, negBed]
  | eq a b pa pb hs1 hs2 ha hb =>
    simp [senkBedT, imFensterB, hs1, hs2, senkVergleich,
      senkAtom_als_tief _ a _ c.frei pa ha, senkAtom_als_tief _ b _ c.frei pb hb, negBed]

/-! ## 7. Assignment chunk: value, address, store

    `T.slots[k].f = e` with a CONSTANT index `k` (recomputed by the
    optimiser's own `constInt?`) at a placed slot lowers to the value code,
    `movImm64 adr A` and `store64 adr dst 0`. -/

/-- ASSIGNMENT RUN: the chunk writes the representation word of the exact
    source value at the slot address, and keeps every variable register. -/
theorem assign_lauf (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) {lo hi : Int} (hτ : τ = .int lo hi) (hlo : 0 ≤ lo)
    (hhi : hi < 2 ^ 64) (pv : List Befehl)
    (hp : senkWert (abbOf c) e c.dst c.tmp = some pv) (A : Nat)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand) (hE : EnvRepr ρ s.register (abbOf c))
    (hwr : schreibbar8 s.speicher (natAdresse A) = true) :
    ∃ s', lauf ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).map kanon) s = some s' ∧
      write64 s.speicher (natAdresse A)
        (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
        some s'.speicher ∧
      EnvRepr ρ s'.register (abbOf c) := by
  obtain ⟨hdt, hda, hta, hdr, htr, -⟩ := cfgOk_regs c hc
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1⟩ :=
    senkWert_korrekt (abbOf c) e hτ c.dst c.tmp ρ σ₀ σ s (cfgOk_frisch c hc) ⟨hdr, htr⟩ hE pv hp
  have hword : s1.register c.dst =
      zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi)) := by
    rw [hval1]
    exact intWort_zahlWort _ hlo hhi
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse A))) s1 c.adr
    (natAdresse A) (laengeOk_encode _) rfl
  let s2 := schrittRegister s1 (ripNach s1.rip (kanon (.movImm64 c.adr (natAdresse A))).laenge)
    s1.flags c.adr (natAdresse A)
  have hs2d : s2.register c.dst = s1.register c.dst := regSet_fremd _ _ _ _ hda
  have hs2a : s2.register c.adr = natAdresse A := regSet_gleich _ _ _
  have heff : effAddr s2 c.adr (BitVec.ofNat 32 0) = natAdresse A := by
    rw [effAddr_null, hs2a]
  let w : Wort := zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))
  let m' : Speicher := { s.speicher with bytes := writeBytes s.speicher (natAdresse A) w }
  have hw : write64 s.speicher (natAdresse A)
      (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
      some m' := by
    unfold write64
    rw [if_pos hwr]
  have hw2 : write64 s2.speicher (effAddr s2 c.adr (BitVec.ofNat 32 0)) (s2.register c.dst) =
      some m' := by
    rw [heff, hs2d, hword]
    show write64 s1.speicher _ _ = _
    rw [hmem1]
    exact hw
  have hst := schritt_store64_erfolg (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))) s2
    c.adr c.dst (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw2
  let r3 : Adresse := ripNach s2.rip (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))).laenge
  refine ⟨{ s2 with speicher := m', rip := r3 }, ?_, hw, ?_⟩
  · rw [List.map_append, lauf_anhang _ _ _ _ hrun1]
    simp only [List.map_cons, List.map_nil, lauf]
    rw [hmi]
    simp only
    rw [hst]
  · apply envRepr_fremd ρ (abbOf c) s.register _ hE
    intro τ' x
    obtain ⟨h1, h2, h3⟩ := cfgOk_frei c hc x
    show regSet s1.register c.adr (natAdresse A) (abbOf c τ' x) = s.register (abbOf c τ' x)
    rw [regSet_fremd _ _ _ _ h3, hreg1 _ h1 h2]

/-- DEEP ASSIGNMENT RUN (the widened value lowering): the chunk writes the representation word of the exact
    source value at the slot address, and keeps every variable register. -/
theorem assignT_lauf (c : PipeCfg) (hc : cfgOk c = true) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) {lo hi : Int} (hτ : τ = .int lo hi) (hlo : 0 ≤ lo)
    (hhi : hi < 2 ^ 64) (pv : List Befehl)
    (hp : senkWertT c e = some pv) (A : Nat)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand) (hE : EnvRepr ρ s.register (abbOf c))
    (hwr : schreibbar8 s.speicher (natAdresse A) = true) :
    ∃ s', lauf ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).map kanon) s = some s' ∧
      write64 s.speicher (natAdresse A)
        (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
        some s'.speicher ∧
      EnvRepr ρ s'.register (abbOf c) := by
  obtain ⟨hdt, hda, hta, hdr, htr, -⟩ := cfgOk_regs c hc
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1⟩ :=
    senkWertT_korrekt c hc e hτ ρ σ₀ σ s hE pv hp
  have hword : s1.register c.dst =
      zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi)) := by
    rw [hval1]
    exact intWort_zahlWort _ hlo hhi
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse A))) s1 c.adr
    (natAdresse A) (laengeOk_encode _) rfl
  let s2 := schrittRegister s1 (ripNach s1.rip (kanon (.movImm64 c.adr (natAdresse A))).laenge)
    s1.flags c.adr (natAdresse A)
  have hs2d : s2.register c.dst = s1.register c.dst := regSet_fremd _ _ _ _ hda
  have hs2a : s2.register c.adr = natAdresse A := regSet_gleich _ _ _
  have heff : effAddr s2 c.adr (BitVec.ofNat 32 0) = natAdresse A := by
    rw [effAddr_null, hs2a]
  let w : Wort := zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))
  let m' : Speicher := { s.speicher with bytes := writeBytes s.speicher (natAdresse A) w }
  have hw : write64 s.speicher (natAdresse A)
      (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
      some m' := by
    unfold write64
    rw [if_pos hwr]
  have hw2 : write64 s2.speicher (effAddr s2 c.adr (BitVec.ofNat 32 0)) (s2.register c.dst) =
      some m' := by
    rw [heff, hs2d, hword]
    show write64 s1.speicher _ _ = _
    rw [hmem1]
    exact hw
  have hst := schritt_store64_erfolg (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))) s2
    c.adr c.dst (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw2
  let r3 : Adresse := ripNach s2.rip (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))).laenge
  refine ⟨{ s2 with speicher := m', rip := r3 }, ?_, hw, ?_⟩
  · rw [List.map_append, lauf_anhang _ _ _ _ hrun1]
    simp only [List.map_cons, List.map_nil, lauf]
    rw [hmi]
    simp only
    rw [hst]
  · apply envRepr_fremd ρ (abbOf c) s.register _ hE
    intro τ' x
    obtain ⟨-, -, h3⟩ := cfgOk_frei c hc x
    obtain ⟨h1, h2⟩ := cfgOk_var_frei c hc x
    show regSet s1.register c.adr (natAdresse A) (abbOf c τ' x) = s.register (abbOf c τ' x)
    rw [regSet_fremd _ _ _ _ h3, hreg1 _ h1 h2]

/-! ## 8. The lowering of a block, and its correctness

    `senkBlock` walks the REAL block: `cons` of an admitted assignment
    (deep value, `senkWertT`), `cons` of an `ite` whose condition is a deep
    comparison (`senkBedT`) and whose two branches are lowered blocks in
    the same fragment (recursively), `pruefung` with a lowered condition
    and a reason exit, `nil`. Every other constructor and every other
    statement is refused (`none`). Every jump displacement is computed and
    then RE-CHECKED against its target (`sprungOk` for the forward jumps of
    an `ite`, the address equation for a refusal exit), so the lowering
    itself refuses an unreachable target. -/

section Block
variable {V : Vertrag D}

/-- Statement lowering: an assignment to a placed integer slot at a
    constant index, with a deep value. -/
def senkStmt (c : PipeCfg) (L : Layout D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Option (List Befehl) :=
  match s with
  | .assignSlot t f i e _ _ =>
    match constInt? i with
    | some k =>
      match L.loc t k f with
      | some A =>
        if repOk (D.typ t f) A 8 0 then
          (senkWertT c e).map (fun p => p ++
            [.movImm64 c.adr (natAdresse A), .store64 c.adr c.dst (BitVec.ofNat 32 0)])
        else none
      | none => none
    | none => none
  | _ => none

/-- The jump displacement from the end of the jump at `posJ` to `ziel`. -/
def sprungDisp (c : PipeCfg) (posJ ziel : Nat) : BitVec 32 :=
  BitVec.ofInt 32 ((ziel : Int) - ((c.codeBase + posJ + 6 : Nat) : Int))

/-- Check lowering: the (deep) condition code, then the jump to the exit of
    the reason; the literal `true` lowers to nothing. -/
def senkPruef (c : PipeCfg) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (pos : Nat)
    (cnd : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ) : Option (List Befehl) :=
  match sonst with
  | .retGrund r _ =>
    if istWahr cnd then some [] else
    match senkBedT c cnd with
    | some (code, j) =>
      let posJ := pos + (encodeAll code).length
      let disp := sprungDisp c posJ (exitAdr c r.val)
      if addrOff (natAdresse c.codeBase) (posJ + (encode (.jumpIf32 j disp)).length) +
          dispWort disp = natAdresse (exitAdr c r.val) then
        some (code ++ [.jumpIf32 j disp])
      else none
    | none => none
  | _ => none

/-- A forward jump over `k` bytes is representable: the 32-bit
    displacement `k` sign-extends back to `k` (decided, i.e. `k < 2^31`). -/
def sprungOk (k : Nat) : Bool := decide (dispWort (BitVec.ofNat 32 k) = BitVec.ofNat 64 k)

/-- A checked forward jump lands `k` bytes further. -/
theorem sprungOk_addr (a : Adresse) (n k : Nat) (h : sprungOk k = true) :
    addrOff a n + dispWort (BitVec.ofNat 32 k) = addrOff a (n + k) := by
  unfold sprungOk at h
  rw [of_decide_eq_true h, ← addrOff_addrOff]
  rfl

/-- The pilot conditional jump is six bytes, the unconditional one five. -/
theorem encode_jumpIf32_len (j : Bedingung) (d : BitVec 32) :
    (encode (.jumpIf32 j d)).length = 6 := by
  cases j <;> rfl

theorem encode_jump32_len (d : BitVec 32) : (encode (.jump32 d)).length = 5 := rfl

/-- The jump over the then-block (to the else-block) of an `ite`. -/
def iteSprung (j : Bedingung) (pt : List Befehl) : Befehl :=
  .jumpIf32 j (BitVec.ofNat 32 ((encodeAll pt).length + 5))

/-- The jump over the else-block (to the end) of an `ite`. -/
def iteEnde (pe : List Befehl) : Befehl :=
  .jump32 (BitVec.ofNat 32 (encodeAll pe).length)

/-- The code of an `ite`: condition, jump on the NEGATED condition over the
    then-block, then-block, jump over the else-block, else-block. -/
def iteCode (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) : List Befehl :=
  code ++ [iteSprung j pt] ++ pt ++ [iteEnde pe] ++ pe

theorem encodeAll_iteCode (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) :
    encodeAll (iteCode code j pt pe) = encodeAll code ++ encode (iteSprung j pt) ++
      encodeAll pt ++ encode (iteEnde pe) ++ encodeAll pe := by
  simp [iteCode, encodeAll_append, encodeAll_cons]

theorem encodeAll_iteCode_len (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) :
    (encodeAll (iteCode code j pt pe)).length = (encodeAll code).length + 6 +
      (encodeAll pt).length + 5 + (encodeAll pe).length := by
  rw [encodeAll_iteCode]
  simp only [List.length_append, iteSprung, iteEnde, encode_jumpIf32_len, encode_jump32_len]

/-- Block lowering from byte position `pos` of the code region. -/
def senkBlock (c : PipeCfg) (L : Layout D) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Nat → Block D V l Γ Λ Λ' →
      Option (List Befehl)
  | _, _, _, _, _, .nil => some []
  | _, _, _, _, pos, .cons (.ite cnd t e) rest =>
    match senkBedT c cnd with
    | some (code, j) =>
      match senkBlock c L (pos + (encodeAll code).length + 6) t with
      | some pt =>
        match senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e with
        | some pe =>
          if sprungOk ((encodeAll pt).length + 5) && sprungOk (encodeAll pe).length then
            (senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length) rest).map
              (iteCode code j pt pe ++ ·)
          else none
        | none => none
      | none => none
    | none => none
  | _, _, _, _, pos, .cons s rest =>
    match senkStmt c L s with
    | some p => (senkBlock c L (pos + (encodeAll p).length) rest).map (p ++ ·)
    | none => none
  | _, _, _, _, pos, .pruefung cnd sonst rest =>
    match senkPruef c pos cnd sonst with
    | some p => (senkBlock c L (pos + (encodeAll p).length) rest).map (p ++ ·)
    | none => none
  | _, _, _, _, _, _ => none

/-- The lowering equation of an assignment. -/
theorem senkBlock_assign (c : PipeCfg) (L : Layout D) {l : Bool} {Γ : Ctx}
    {Λ Λ'' : List (Res D)} (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (rest : Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos (.cons (.assignSlot t f i e hw hL) rest) =
      match senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) with
      | some p => (senkBlock c L (pos + (encodeAll p).length) rest).map (p ++ ·)
      | none => none := rfl

/-- Inversion of an accepted `ite`. -/
theorem senkBlock_ite_inv (c : PipeCfg) (L : Layout D) {l : Bool} {Γ : Ctx}
    {Λ Λ' Λ'' : List (Res D)} (cnd : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (pos : Nat) (prog : List Befehl)
    (h : senkBlock c L pos (.cons (.ite cnd t e) rest) = some prog) :
    ∃ code j pt pe q, senkBedT c cnd = some (code, j) ∧
      senkBlock c L (pos + (encodeAll code).length + 6) t = some pt ∧
      senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e = some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length) rest = some q ∧
      prog = iteCode code j pt pe ++ q := by
  have h' : (match senkBedT c cnd with
    | some (code, j) =>
      match senkBlock c L (pos + (encodeAll code).length + 6) t with
      | some pt =>
        match senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e with
        | some pe =>
          if sprungOk ((encodeAll pt).length + 5) && sprungOk (encodeAll pe).length then
            (senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length) rest).map
              (iteCode code j pt pe ++ ·)
          else none
        | none => none
      | none => none
    | none => none) = some prog := h
  cases hb : senkBedT c cnd with
  | none => simp [hb] at h'
  | some cj =>
    obtain ⟨code, j⟩ := cj
    simp only [hb] at h'
    cases ht : senkBlock c L (pos + (encodeAll code).length + 6) t with
    | none => simp [ht] at h'
    | some pt =>
      simp only [ht] at h'
      cases he : senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e with
      | none => simp [he] at h'
      | some pe =>
        simp only [he] at h'
        by_cases hk : (sprungOk ((encodeAll pt).length + 5) && sprungOk (encodeAll pe).length) = true
        · simp only [hk, if_true] at h'
          simp only [Bool.and_eq_true] at hk
          cases hr : senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length) rest with
          | none => simp [hr] at h'
          | some q =>
            simp only [hr] at h'
            simp only [Option.map_some, Option.some.injEq] at h'
            exact ⟨code, j, pt, pe, q, rfl, ht, he, hk.1, hk.2, hr, h'.symm⟩
        · simp [hk] at h'

/-- What a target end state must show for a source outcome: a normal
    outcome ends at the end of the code with world and environment
    represented; a reason outcome ends at the reason's refusal exit with
    the world represented; NO other outcome is admitted. -/
def Entspricht (c : PipeCfg) (L : Layout D) (endA : Adresse) {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Zustand → Prop
  | .ok σ' ρ', s' => s'.rip = endA ∧ WorldRep L s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf c)
  | .grund σ' r, s' => s'.rip = natAdresse (exitAdr c r.val) ∧ WorldRep L s'.speicher σ'
  | _, _ => False

/-- A statement that ends normally continues with the rest of the block. -/
theorem execBlock_cons_stmtOk (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    execBlock O passes R (.cons s rest) σ ρ = execBlock O passes R rest σ' ρ' := by
  simp only [execBlock, h]

/-- A statement that ends with a reason ends the block with it. -/
theorem execBlock_cons_stmtGrund (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ σ' : World D) (ρ : Env D Γ) (r : Fin V.gruende)
    (h : execStmt O passes R s σ ρ = .grund σ' r) :
    execBlock O passes R (.cons s rest) σ ρ = .grund σ' r := by
  simp only [execBlock, h]

/-- The source step of an `ite` (the real `execStmt` equation). -/
theorem execStmt_ite (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (cnd : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (.ite cnd t e) σ ρ =
      if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
      then execBlock O passes R t (σ.lese Λ cnd.orte) ρ
      else execBlock O passes R e (σ.lese Λ cnd.orte) ρ := rfl

/-- BLOCK LOWERING CORRECTNESS, with the code region carried along: for
    every lowered block, every source world and environment represented by
    a target state whose code region holds the lowered bytes at its
    instruction pointer, the FETCHED byte run reaches a state, whose code
    region still holds the bytes, that corresponds to the REAL `execBlock`
    outcome. Proved by recursion on the block (into both branches of an
    `ite`); the chunks are `assignT_lauf` and `senkBedT_korrekt` lifted to
    bytes by `lauf_zu_laufBytes`, and the jumps are fetched by
    `byteschritt_im_code`. -/
theorem senkBlock_korrektC (c : PipeCfg) (L : Layout D) (hc : cfgOk c = true)
    (hsep : LayoutSep L) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (flat : List Byte)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
    (pre post : List Byte) (prog : List Befehl)
    (h : senkBlock c L pre.length b = some prog)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll prog ++ post)
    (hrip : s.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c)) :
    ∃ n s', laufBytes n s = .weiter s' ∧ CodeAt s'.speicher (natAdresse c.codeBase) flat ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (pre.length + (encodeAll prog).length))
        (execBlock O passes R b σ ρ) s' := by
  generalize hb0 : b = b0 at h
  cases b0 with
  | nil =>
    simp only [senkBlock, Option.some.injEq] at h
    subst h
    refine ⟨0, s, rfl, hcode, ?_, hW, hE⟩
    rw [hrip]
    rfl
  | cons st rest =>
    cases st with
    | assignSlot t f i e hw hL =>
      rw [senkBlock_assign] at h
      cases hs : senkStmt c L (Stmt.assignSlot (V := V) t f i e hw hL) with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        dsimp only at h
        cases hq : senkBlock c L (pre.length + (encodeAll p).length) rest with
        | none => simp [hq] at h
        | some q =>
          simp only [hq] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          simp only [senkStmt] at hs
          cases hk : constInt? i with
          | none => simp [hk] at hs
          | some k =>
            simp only [hk] at hs
            cases hA : L.loc t k f with
            | none => simp [hA] at hs
            | some A =>
              simp only [hA] at hs
              by_cases hok : repOk (D.typ t f) A 8 0 = true
              · rw [if_pos hok] at hs
                cases hv : senkWertT c e with
                | none => simp [hv] at hs
                | some pv =>
                  simp only [hv] at hs
                  simp only [Option.map_some, Option.some.injEq] at hs
                  subst hs
                  obtain ⟨lo, hi, hT, hlo, hhi, -⟩ := repOk_int _ A hok
                  -- the source step
                  let σL := σ.lese Λ (i.orte ++ e.orte)
                  have hki : (eval σL i σL ρ).n = k := by
                    have := constInt?_sound i σL σL ρ k hk
                    simpa [intOf] using this
                  have hsrc : execBlock O passes R (.cons (.assignSlot t f i e hw hL) rest) σ ρ =
                      execBlock O passes R rest
                        (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
                    rw [← hki]
                    rfl
                  -- the target chunk
                  obtain ⟨-, -, hwrA, -⟩ := hW t k f A hA
                  obtain ⟨s1, hrun1, hw1, hE1⟩ :=
                    assignT_lauf c hc e hT hlo hhi pv hv A ρ σL σL s hE hwrA
                  have hgp : (pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).all gerade = true := by
                    simp [List.all_append, senkWertT_gerade c e pv hv, gerade]
                  obtain ⟨hb1, hr1, hc1, -, -⟩ := lauf_zu_laufBytes (natAdresse c.codeBase) flat _
                    pre (encodeAll q ++ post) s s1 hgp hrun1 hcode
                    (by rw [hf, encodeAll_append]; simp) hrip
                  have hW1 : WorldRep L s1.speicher (σL.schreibSlot t Λ k f (eval σL e σL ρ)) :=
                    worldRep_store L hsep s.speicher s1.speicher σL t k f A hA hW lo hi hT _ hw1 Λ
                  have hq' : senkBlock c L (pre ++ encodeAll (pv ++
                      [Befehl.movImm64 c.adr (natAdresse A),
                      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)])).length rest = some q := by
                    rw [List.length_append]; exact hq
                  obtain ⟨n2, s2, hb2, hc2, hent⟩ := senkBlock_korrektC c L hc hsep O passes R
                    flat rest (pre ++ encodeAll (pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)])) post q hq'
                    _ ρ s1 hc1 (by rw [hf, encodeAll_append]; simp)
                    (by rw [hr1, List.length_append]) hW1 hE1
                  refine ⟨_ + n2, s2, by rw [laufBytes_add _ _ _ _ hb1]; exact hb2, hc2, ?_⟩
                  rw [hsrc]
                  have hend : pre.length + (encodeAll (pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)] ++ q)).length =
                      (pre ++ encodeAll (pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)])).length +
                      (encodeAll q).length := by
                    simp only [encodeAll_append, List.length_append]
                    omega
                  rw [hend]
                  exact hent
              · rw [if_neg hok] at hs; cases hs
    | ite cnd t e =>
      obtain ⟨code, j, pt, pe, q, hb, ht, he, hk1, hk2, hq, rfl⟩ :=
        senkBlock_ite_inv c L cnd t e rest pre.length prog h
      have hJ : (encode (iteSprung j pt)).length = 6 := encode_jumpIf32_len _ _
      have hK : (encode (iteEnde pe)).length = 5 := encode_jump32_len _
      have hsrc := execStmt_ite O passes R cnd t e σ ρ
      -- the condition
      obtain ⟨hgc, s1, hrun1, hmem1, hreg1, hval⟩ :=
        senkBedT_korrekt c hc cnd code j hb ρ (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) s hE
      have hE1 : EnvRepr ρ s1.register (abbOf c) := envRepr_tief c hc ρ _ _ hE hreg1
      have hW1 : WorldRep L s1.speicher (σ.lese Λ cnd.orte) := by rw [hmem1]; exact hW
      have hflat1 : flat = pre ++ encodeAll code ++ (encode (iteSprung j pt) ++ encodeAll pt ++
          encode (iteEnde pe) ++ encodeAll pe ++ encodeAll q ++ post) := by
        rw [hf, encodeAll_append, encodeAll_iteCode]; simp
      obtain ⟨hb1, hr1, hc1, -, -⟩ := lauf_zu_laufBytes (natAdresse c.codeBase) flat code pre
        _ s s1 hgc hrun1 hcode hflat1 hrip
      have hbs := byteschritt_im_code s1 (natAdresse c.codeBase) flat (pre ++ encodeAll code)
        (encodeAll pt ++ encode (iteEnde pe) ++ encodeAll pe ++ encodeAll q ++ post)
        (iteSprung j pt) hc1 (by rw [hflat1]; simp) (by rw [hr1, List.length_append])
      -- the lengths of the pieces
      have hRest : (pre ++ encodeAll (iteCode code j pt pe)).length =
          pre.length + (encodeAll code).length + 6 + (encodeAll pt).length + 5 +
            (encodeAll pe).length := by
        rw [List.length_append, encodeAll_iteCode_len]; omega
      have hq' : senkBlock c L (pre ++ encodeAll (iteCode code j pt pe)).length rest = some q := by
        rw [List.length_append]; exact hq
      have hflatR : flat = (pre ++ encodeAll (iteCode code j pt pe)) ++ encodeAll q ++ post := by
        rw [hf, encodeAll_append]; simp
      have hend : pre.length + (encodeAll (iteCode code j pt pe ++ q)).length =
          (pre ++ encodeAll (iteCode code j pt pe)).length + (encodeAll q).length := by
        rw [encodeAll_append, List.length_append, List.length_append]; omega
      by_cases hcj : bedingung j s1.flags = true
      · -- the jump is taken: the source condition is false, the else-block runs
        have hst := schritt_jumpIf32_genommen (kanon (iteSprung j pt)) s1 j
          (BitVec.ofNat 32 ((encodeAll pt).length + 5)) (laengeOk_encode _) rfl hcj
        rw [hst] at hbs
        have hcond : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = false := by
          rw [hval, hcj]; rfl
        rw [if_neg (by rw [hcond]; exact Bool.false_ne_true)] at hsrc
        let s2 : Zustand := { s1 with rip := ripNach s1.rip (kanon (iteSprung j pt)).laenge + dispWort (BitVec.ofNat 32 ((encodeAll pt).length + 5)) }
        have hb2 : laufBytes (code.length + 1) s = .weiter s2 := by
          rw [laufBytes_add _ _ _ _ hb1]
          simp only [laufBytes, hbs]
          rfl
        have hpreE : (pre ++ encodeAll code ++ encode (iteSprung j pt) ++ encodeAll pt ++
            encode (iteEnde pe)).length =
            pre.length + (encodeAll code).length + 6 + (encodeAll pt).length + 5 := by
          simp only [List.length_append, hJ, hK]
        have hr2 : s2.rip = addrOff (natAdresse c.codeBase) (pre ++ encodeAll code ++
            encode (iteSprung j pt) ++ encodeAll pt ++ encode (iteEnde pe)).length := by
          show ripNach s1.rip (encode (iteSprung j pt)).length + _ = _
          rw [hJ, hr1, ripNach_addrOff, addrOff_addrOff, sprungOk_addr _ _ _ hk1, hpreE]
          all_goals (congr 1 <;> omega)
        obtain ⟨n3, s3, hb3, hc3, hent3⟩ := senkBlock_korrektC c L hc hsep O passes R flat e
          (pre ++ encodeAll code ++ encode (iteSprung j pt) ++ encodeAll pt ++ encode (iteEnde pe))
          (encodeAll q ++ post) pe (by rw [hpreE]; exact he) (σ.lese Λ cnd.orte) ρ s2 hc1
          (by rw [hflat1]; simp) hr2 hW1 hE1
        have hb23 : laufBytes (code.length + 1 + n3) s = .weiter s3 := by
          rw [laufBytes_add _ _ _ _ hb2]; exact hb3
        have hendE : (pre ++ encodeAll code ++ encode (iteSprung j pt) ++ encodeAll pt ++
            encode (iteEnde pe)).length + (encodeAll pe).length =
            (pre ++ encodeAll (iteCode code j pt pe)).length := by
          rw [hpreE, hRest]
        rw [hendE] at hent3
        cases hx : execBlock O passes R e (σ.lese Λ cnd.orte) ρ with
        | ok σ' ρ' =>
          rw [hx] at hent3 hsrc
          obtain ⟨hr3, hW3, hE3⟩ := hent3
          obtain ⟨n4, s4, hb4, hc4, hent4⟩ := senkBlock_korrektC c L hc hsep O passes R flat rest
            (pre ++ encodeAll (iteCode code j pt pe)) post q hq' σ' ρ' s3 hc3 hflatR hr3 hW3 hE3
          refine ⟨code.length + 1 + n3 + n4, s4, by rw [laufBytes_add _ _ _ _ hb23]; exact hb4,
            hc4, ?_⟩
          rw [execBlock_cons_stmtOk O passes R _ rest σ ρ σ' ρ' hsrc, hend]
          exact hent4
        | grund σ' r =>
          rw [hx] at hent3 hsrc
          refine ⟨code.length + 1 + n3, s3, hb23, hc3, ?_⟩
          rw [execBlock_cons_stmtGrund O passes R _ rest σ σ' ρ r hsrc]
          exact hent3
        | zurueck _ _ => rw [hx] at hent3; exact hent3.elim
        | leave _ _ _ => rw [hx] at hent3; exact hent3.elim
        | next _ _ _ => rw [hx] at hent3; exact hent3.elim
        | logik _ => rw [hx] at hent3; exact hent3.elim
        | hardware _ => rw [hx] at hent3; exact hent3.elim
      · -- the jump falls through: the source condition is true, the then-block runs
        have hcj' : bedingung j s1.flags = false := by
          cases h' : bedingung j s1.flags
          · rfl
          · exact absurd h' hcj
        have hst := schritt_jumpIf32_nicht (kanon (iteSprung j pt)) s1 j
          (BitVec.ofNat 32 ((encodeAll pt).length + 5)) (laengeOk_encode _) rfl hcj'
        rw [hst] at hbs
        have hcond : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = true := by
          rw [hval, hcj']; rfl
        rw [if_pos hcond] at hsrc
        let s2 : Zustand := { s1 with rip := ripNach s1.rip (kanon (iteSprung j pt)).laenge }
        have hb2 : laufBytes (code.length + 1) s = .weiter s2 := by
          rw [laufBytes_add _ _ _ _ hb1]
          simp only [laufBytes, hbs]
          rfl
        have hpreT : (pre ++ encodeAll code ++ encode (iteSprung j pt)).length =
            pre.length + (encodeAll code).length + 6 := by
          simp only [List.length_append, hJ]
        have hr2 : s2.rip = addrOff (natAdresse c.codeBase)
            (pre ++ encodeAll code ++ encode (iteSprung j pt)).length := by
          show ripNach s1.rip (encode (iteSprung j pt)).length = _
          rw [hJ, hr1, ripNach_addrOff, addrOff_addrOff, hpreT]
        obtain ⟨n3, s3, hb3, hc3, hent3⟩ := senkBlock_korrektC c L hc hsep O passes R flat t
          (pre ++ encodeAll code ++ encode (iteSprung j pt))
          (encode (iteEnde pe) ++ encodeAll pe ++ encodeAll q ++ post) pt (by rw [hpreT]; exact ht)
          (σ.lese Λ cnd.orte) ρ s2 hc1 (by rw [hflat1]; simp) hr2 hW1 hE1
        have hb23 : laufBytes (code.length + 1 + n3) s = .weiter s3 := by
          rw [laufBytes_add _ _ _ _ hb2]; exact hb3
        cases hx : execBlock O passes R t (σ.lese Λ cnd.orte) ρ with
        | ok σ' ρ' =>
          rw [hx] at hent3 hsrc
          obtain ⟨hr3, hW3, hE3⟩ := hent3
          -- the jump over the else-block
          have hbsJ := byteschritt_im_code s3 (natAdresse c.codeBase) flat
            (pre ++ encodeAll code ++ encode (iteSprung j pt) ++ encodeAll pt)
            (encodeAll pe ++ encodeAll q ++ post) (iteEnde pe) hc3
            (by rw [hflat1]; simp) (by simp only [hr3, List.length_append])
          rw [schritt_jump32 (kanon (iteEnde pe)) s3 (BitVec.ofNat 32 (encodeAll pe).length)
            (laengeOk_encode _) rfl] at hbsJ
          let s4 : Zustand := { s3 with rip := ripNach s3.rip (kanon (iteEnde pe)).laenge + dispWort (BitVec.ofNat 32 (encodeAll pe).length) }
          have hr4 : s4.rip = addrOff (natAdresse c.codeBase)
              (pre ++ encodeAll (iteCode code j pt pe)).length := by
            show ripNach s3.rip (encode (iteEnde pe)).length + _ = _
            rw [hK, hr3, ripNach_addrOff, addrOff_addrOff, sprungOk_addr _ _ _ hk2, hRest,
              hpreT]
            all_goals (congr 1 <;> omega)
          obtain ⟨n4, s4', hb4, hc4, hent4⟩ := senkBlock_korrektC c L hc hsep O passes R flat rest
            (pre ++ encodeAll (iteCode code j pt pe)) post q hq' σ' ρ' s4 hc3 hflatR hr4 hW3 hE3
          refine ⟨code.length + 1 + n3 + 1 + n4, s4', ?_, hc4, ?_⟩
          · have hb34 : laufBytes (code.length + 1 + n3 + 1) s = .weiter s4 := by
              rw [laufBytes_add _ _ _ _ hb23]
              simp only [laufBytes, hbsJ]
              rfl
            rw [laufBytes_add _ _ _ _ hb34]
            exact hb4
          · rw [execBlock_cons_stmtOk O passes R _ rest σ ρ σ' ρ' hsrc, hend]
            exact hent4
        | grund σ' r =>
          rw [hx] at hent3 hsrc
          refine ⟨code.length + 1 + n3, s3, hb23, hc3, ?_⟩
          rw [execBlock_cons_stmtGrund O passes R _ rest σ σ' ρ r hsrc]
          exact hent3
        | zurueck _ _ => rw [hx] at hent3; exact hent3.elim
        | leave _ _ _ => rw [hx] at hent3; exact hent3.elim
        | next _ _ _ => rw [hx] at hent3; exact hent3.elim
        | logik _ => rw [hx] at hent3; exact hent3.elim
        | hardware _ => rw [hx] at hent3; exact hent3.elim
    | _ => simp [senkBlock, senkStmt] at h
  | pruefung cnd sonst rest =>
    simp only [senkBlock] at h
    cases hs : senkPruef c pre.length cnd sonst with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : senkBlock c L (pre.length + (encodeAll p).length) rest with
      | none => simp [hq] at h
      | some q =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        have hq' : senkBlock c L (pre ++ encodeAll p).length rest = some q := by
          rw [List.length_append]; exact hq
        cases sonst with
        | retGrund r hΛ =>
          let σL := σ.lese Λ cnd.orte
          have hsrc : execBlock O passes R (.pruefung cnd (.retGrund r hΛ) rest) σ ρ =
              if wahr? (eval σL cnd σL ρ) then execBlock O passes R rest σL ρ
              else .grund σL r := rfl
          simp only [senkPruef] at hs
          by_cases hw : istWahr cnd = true
          · rw [if_pos hw] at hs
            simp only [Option.some.injEq] at hs
            subst hs
            have hv : wahr? (eval σL cnd σL ρ) = true :=
              Option.some.inj (istWahr_wahr cnd hw σL σL ρ)
            rw [hsrc, if_pos hv]
            have hent := senkBlock_korrektC c L hc hsep O passes R flat rest pre post q
              (by simpa [encodeAll] using hq') σL ρ s hcode (by simpa [encodeAll] using hf) hrip
              hW hE
            simpa [encodeAll] using hent
          · rw [if_neg hw] at hs
            cases hb : senkBedT c cnd with
            | none => simp [hb] at hs
            | some cj =>
              obtain ⟨code, j⟩ := cj
              simp only [hb] at hs
              by_cases hj : addrOff (natAdresse c.codeBase)
                  (pre.length + (encodeAll code).length +
                    (encode (.jumpIf32 j (sprungDisp c (pre.length + (encodeAll code).length)
                      (exitAdr c r.val)))).length) +
                  dispWort (sprungDisp c (pre.length + (encodeAll code).length)
                    (exitAdr c r.val)) = natAdresse (exitAdr c r.val)
              · rw [if_pos hj] at hs
                simp only [Option.some.injEq] at hs
                subst hs
                obtain ⟨hgc, s1, hrun1, hmem1, hreg1, hval⟩ :=
                  senkBedT_korrekt c hc cnd code j hb ρ σL σL s hE
                have hE1 : EnvRepr ρ s1.register (abbOf c) := envRepr_tief c hc ρ _ _ hE hreg1
                obtain ⟨hb1, hr1, hc1, -, -⟩ := lauf_zu_laufBytes (natAdresse c.codeBase) flat
                  code pre
                  (encodeAll [Befehl.jumpIf32 j (sprungDisp c (pre.length + (encodeAll code).length)
                    (exitAdr c r.val))] ++ encodeAll q ++ post)
                  s s1 hgc hrun1 hcode
                  (by rw [hf]; simp [encodeAll]) hrip
                have hW1 : WorldRep L s1.speicher σL := by rw [hmem1]; exact hW
                have hbs := byteschritt_im_code s1 (natAdresse c.codeBase) flat
                  (pre ++ encodeAll code) (encodeAll q ++ post)
                  (.jumpIf32 j (sprungDisp c (pre.length + (encodeAll code).length)
                    (exitAdr c r.val))) hc1
                  (by rw [hf]; simp [encodeAll])
                  (by rw [hr1, List.length_append])
                by_cases hcj : bedingung j s1.flags = true
                · -- the check fails: the jump reaches the reason's exit
                  have hst := schritt_jumpIf32_genommen
                    (kanon (.jumpIf32 j (sprungDisp c (pre.length + (encodeAll code).length)
                      (exitAdr c r.val)))) s1 j _ (laengeOk_encode _) rfl hcj
                  rw [hst] at hbs
                  have hf' : wahr? (eval σL cnd σL ρ) = false := by rw [hval, hcj]; rfl
                  let rx : Adresse := ripNach s1.rip (kanon (.jumpIf32 j (sprungDisp c
                    (pre.length + (encodeAll code).length) (exitAdr c r.val)))).laenge +
                    dispWort (sprungDisp c (pre.length + (encodeAll code).length) (exitAdr c r.val))
                  refine ⟨code.length + 1, { s1 with rip := rx }, ?_, hc1, ?_⟩
                  · rw [laufBytes_add _ _ _ _ hb1]
                    simp only [laufBytes, hbs]
                    rfl
                  · rw [hsrc, if_neg (by rw [hf']; exact Bool.false_ne_true)]
                    refine ⟨?_, hW1⟩
                    show ripNach s1.rip _ + _ = _
                    rw [hr1, ripNach_addrOff, addrOff_addrOff]
                    exact hj
                · -- the check passes: fall through to the rest
                  have hcj' : bedingung j s1.flags = false := by
                    cases h' : bedingung j s1.flags
                    · rfl
                    · exact absurd h' hcj
                  have hst := schritt_jumpIf32_nicht
                    (kanon (.jumpIf32 j (sprungDisp c (pre.length + (encodeAll code).length)
                      (exitAdr c r.val)))) s1 j _ (laengeOk_encode _) rfl hcj'
                  rw [hst] at hbs
                  have ht : wahr? (eval σL cnd σL ρ) = true := by rw [hval, hcj']; rfl
                  let r2 : Adresse := ripNach s1.rip (kanon (.jumpIf32 j (sprungDisp c
                    (pre.length + (encodeAll code).length) (exitAdr c r.val)))).laenge
                  let s2 : Zustand := { s1 with rip := r2 }
                  have hent := senkBlock_korrektC c L hc hsep O passes R flat rest
                    (pre ++ encodeAll (code ++ [.jumpIf32 j (sprungDisp c
                      (pre.length + (encodeAll code).length) (exitAdr c r.val))])) post q hq'
                    σL ρ s2 hc1 (by rw [hf]; simp [encodeAll])
                    (by
                      show ripNach s1.rip _ = _
                      rw [hr1, ripNach_addrOff, addrOff_addrOff, encodeAll_append,
                        List.length_append, List.length_append, encodeAll_cons, encodeAll_nil,
                        List.append_nil]
                      rfl)
                    hW1 hE1
                  obtain ⟨n2, s3, hb3, hc3, hent3⟩ := hent
                  refine ⟨code.length + 1 + n2, s3, ?_, hc3, ?_⟩
                  · rw [Nat.add_assoc, laufBytes_add _ _ _ _ hb1,
                      laufBytes_add 1 n2 s1 s2 (by simp only [laufBytes, hbs]; rfl)]
                    exact hb3
                  · rw [hsrc, if_pos ht]
                    have hend : pre.length + (encodeAll (code ++ [Befehl.jumpIf32 j (sprungDisp c
                        (pre.length + (encodeAll code).length) (exitAdr c r.val))] ++ q)).length =
                        (pre ++ encodeAll (code ++ [Befehl.jumpIf32 j (sprungDisp c
                        (pre.length + (encodeAll code).length) (exitAdr c r.val))])).length +
                        (encodeAll q).length := by
                      simp only [encodeAll_append, List.length_append]
                      omega
                    rw [hend]
                    exact hent3
              · rw [if_neg hj] at hs; cases hs
        | _ => simp [senkPruef] at hs
  | _ => simp [senkBlock] at h
termination_by sizeOf b
decreasing_by
  all_goals
    subst hb0
    simp only [Block.cons.sizeOf_spec, Block.pruefung.sizeOf_spec, Stmt.ite.sizeOf_spec]
    omega

/-- BLOCK LOWERING CORRECTNESS: for every lowered block, every source
    world and environment represented by a target state whose code region
    holds the lowered bytes at its instruction pointer, the FETCHED byte
    run reaches a state that corresponds to the REAL `execBlock` outcome.
    (The statement of the original fragment, now over the widened
    lowering; derived from `senkBlock_korrektC`.) -/
theorem senkBlock_korrekt (c : PipeCfg) (L : Layout D) (hc : cfgOk c = true)
    (hsep : LayoutSep L) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (flat : List Byte)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
    (pre post : List Byte) (prog : List Befehl)
    (h : senkBlock c L pre.length b = some prog)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll prog ++ post)
    (hrip : s.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c)) :
    ∃ n s', laufBytes n s = .weiter s' ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (pre.length + (encodeAll prog).length))
        (execBlock O passes R b σ ρ) s' := by
  obtain ⟨n, s', hrun, -, hent⟩ :=
    senkBlock_korrektC c L hc hsep O passes R flat b pre post prog h σ ρ s hcode hf hrip hW hE
  exact ⟨n, s', hrun, hent⟩

/-- THE ACCEPTOR EXCLUDES EVERY OTHER OUTCOME: a lowered block ends
    normally or with the reason of a failed check -- never with a return,
    `leave`/`next`, a logic stop (budget, range) or a hardware stop. This is
    proved from the acceptor, not assumed; an `ite` inherits it from both
    of its lowered branches. -/
theorem senkBlock_ausgang (c : PipeCfg) (L : Layout D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (pos : Nat)
    (prog : List Befehl) (h : senkBlock c L pos b = some prog) (σ : World D) (ρ : Env D Γ) :
    (∃ σ' ρ', execBlock O passes R b σ ρ = .ok σ' ρ') ∨
      (∃ σ' r, execBlock O passes R b σ ρ = .grund σ' r) := by
  generalize hb0 : b = b0 at h
  cases b0 with
  | nil => exact Or.inl ⟨σ, ρ, rfl⟩
  | cons st rest =>
    cases st with
    | assignSlot t f i e hw hL =>
      rw [senkBlock_assign] at h
      cases hs : senkStmt c L (Stmt.assignSlot (V := V) t f i e hw hL) with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        dsimp only at h
        cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
        | none => simp [hq] at h
        | some q =>
          exact senkBlock_ausgang c L O passes R rest _ q hq _ ρ
    | ite cnd t e =>
      obtain ⟨code, j, pt, pe, q, -, ht, he, -, -, hq, -⟩ :=
        senkBlock_ite_inv c L cnd t e rest pos prog h
      have hsrc := execStmt_ite O passes R cnd t e σ ρ
      have hzweig : (∃ σ' ρ', execStmt O passes R (.ite cnd t e) σ ρ = .ok σ' ρ') ∨
          (∃ σ' r, execStmt O passes R (.ite cnd t e) σ ρ = .grund σ' r) := by
        rw [hsrc]
        split
        · exact senkBlock_ausgang c L O passes R t _ pt ht _ ρ
        · exact senkBlock_ausgang c L O passes R e _ pe he _ ρ
      rcases hzweig with ⟨σ', ρ', hx⟩ | ⟨σ', r, hx⟩
      · rw [execBlock_cons_stmtOk O passes R _ rest σ ρ σ' ρ' hx]
        exact senkBlock_ausgang c L O passes R rest _ q hq σ' ρ'
      · rw [execBlock_cons_stmtGrund O passes R _ rest σ σ' ρ r hx]
        exact Or.inr ⟨σ', r, rfl⟩
    | _ => simp [senkBlock, senkStmt] at h
  | pruefung cnd sonst rest =>
    simp only [senkBlock] at h
    cases hs : senkPruef c pos cnd sonst with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
      | none => simp [hq] at h
      | some q =>
        cases sonst with
        | retGrund r hΛ =>
          show (∃ σ' ρ', (if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
              then execBlock O passes R rest (σ.lese Λ cnd.orte) ρ
              else .grund (σ.lese Λ cnd.orte) r) = .ok σ' ρ') ∨
            (∃ σ' r', (if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
              then execBlock O passes R rest (σ.lese Λ cnd.orte) ρ
              else .grund (σ.lese Λ cnd.orte) r) = .grund σ' r')
          split
          · exact senkBlock_ausgang c L O passes R rest _ q hq _ ρ
          · exact Or.inr ⟨_, r, rfl⟩
        | _ => simp [senkPruef] at hs
  | _ => simp [senkBlock] at h
termination_by sizeOf b
decreasing_by
  all_goals
    subst hb0
    simp only [Block.cons.sizeOf_spec, Block.pruefung.sizeOf_spec, Stmt.ite.sizeOf_spec]
    omega

/-! ## 9. The pipeline: optimise, lower, encode -- and the validator

    The optimiser stage is the accepted certificate pipeline
    (`applyPipeline`); a refused certificate list falls back to the
    unchanged block (the conservative route, sound by reflexivity). The
    validator RECOMPUTES everything from the source and the certificates:
    the candidate bytes (untrusted, e.g. produced by Rust) must equal the
    Lean encoding, decode back to exactly the Lean instruction list, and
    keep every written slot out of the code region. -/

/-- The optimiser stage with its conservative fallback. -/
def optimise (certs : List (PassKind × BlockCert)) (b : Block D V l Γ Λ Λ') :
    Block D V l Γ Λ Λ' :=
  (applyPipeline certs b).getD b

/-- The optimiser stage refines its input in every outcome. -/
theorem optimise_sound (certs : List (PassKind × BlockCert)) (b : Block D V l Γ Λ Λ') :
    BlockEquiv b (optimise certs b) := by
  unfold optimise
  cases h : applyPipeline certs b with
  | none => exact BlockEquiv.refl b
  | some b' => exact applyPipeline_sound certs b b' h

/-- Optimise, then lower from the start of the code region. -/
def compileProg (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (b : Block D V l Γ Λ Λ') : Option (List Befehl) :=
  if cfgOk c then senkBlock c L 0 (optimise certs b) else none

/-- The whole compiler: source block to code bytes. -/
def compile (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (b : Block D V l Γ Λ Λ') : Option (List Byte) :=
  (compileProg c L certs b).map encodeAll

/-- Decode a whole byte list with the independent decoder. -/
def decodeAll : Nat → List Byte → Option (List Befehl)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bs =>
    match decode (b :: bs) with
    | some (d, rest) => (decodeAll fuel rest).map (d.befehl :: ·)
    | none => none

/-- Every instruction has at least one byte. -/
theorem length_le_encodeAll : ∀ (P : List Befehl), P.length ≤ (encodeAll P).length
  | [] => Nat.le_refl 0
  | b :: P => by
    rw [encodeAll_cons, List.length_append, List.length_cons]
    have := (encode_len b).1
    have := length_le_encodeAll P
    omega

/-- CODEC ROUND TRIP FOR PROGRAMS: decoding the encoded program gives the
    program back (from the per-instruction `Codec.roundtrip`). -/
theorem decodeAll_encodeAll : ∀ (P : List Befehl) (fuel : Nat), P.length ≤ fuel →
    decodeAll fuel (encodeAll P) = some P
  | [], fuel, _ => by cases fuel <;> rfl
  | b :: P, fuel, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨x, xs, hx⟩ : ∃ x xs, encode b ++ encodeAll P = x :: xs := by
      cases h : encode b ++ encodeAll P with
      | nil =>
        have := congrArg List.length h
        simp only [List.length_append, List.length_nil] at this
        have := (encode_len b).1
        omega
      | cons x xs => exact ⟨x, xs, rfl⟩
    rw [encodeAll_cons, hx]
    simp only [decodeAll]
    rw [← hx, roundtrip b (encodeAll P)]
    simp [decodeAll_encodeAll P f (by simp at hf; omega)]

/-- The slot addresses a lowered block writes. -/
def stmtAdresse (L : Layout D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Option Nat :=
  match s with
  | .assignSlot t f i _ _ _ =>
    match constInt? i with
    | some k => L.loc t k f
    | none => none
  | _ => none

def slotAdressen (L : Layout D) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → List Nat
  | _, _, _, _, .nil => []
  | _, _, _, _, .cons (.ite _ t e) rest => slotAdressen L t ++ slotAdressen L e ++ slotAdressen L rest
  | _, _, _, _, .cons s rest => (stmtAdresse L s).toList ++ slotAdressen L rest
  | _, _, _, _, .pruefung _ _ rest => slotAdressen L rest
  | _, _, _, _, _ => []

/-- Is the statement an `ite`? -/
def istIte {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : Bool :=
  match s with
  | .ite _ _ _ => true
  | _ => false

/-- The written slots of a non-`ite` statement and its rest. -/
theorem slotAdressen_cons_eq (L : Layout D) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (hs : istIte s = false) :
    slotAdressen L (.cons s rest) = (stmtAdresse L s).toList ++ slotAdressen L rest := by
  cases s <;> first | rfl | simp [istIte] at hs

/-- Every written slot footprint lies outside the code region `[base, base + len)`. -/
def datenGetrennt (c : PipeCfg) (L : Layout D) (b : Block D V l Γ Λ Λ') (len : Nat) : Bool :=
  (slotAdressen L b).all (fun A => decide (A + 8 ≤ c.codeBase ∨ c.codeBase + len ≤ A))

/-- THE VALIDATOR: recompute the program from the source and the
    certificates, and accept the candidate bytes only if they ARE its
    encoding, decode back to it, and the written data stays off the code. -/
def validate (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  match compileProg c L certs src with
  | some prog =>
    decide (bytes = encodeAll prog) && decide (decodeAll bytes.length bytes = some prog) &&
      datenGetrennt c L (optimise certs src) bytes.length
  | none => false

/-- What an accepted candidate is: the Lean recomputation, decoded back. -/
theorem validate_sound (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : validate c L certs src bytes = true) :
    ∃ prog, cfgOk c = true ∧ senkBlock c L 0 (optimise certs src) = some prog ∧
      bytes = encodeAll prog ∧ decodeAll bytes.length bytes = some prog ∧
      compile c L certs src = some bytes := by
  unfold validate at h
  cases hp : compileProg c L certs src with
  | none => rw [hp] at h; cases h
  | some prog =>
    rw [hp] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, hd⟩, -⟩ := h
    unfold compileProg at hp
    by_cases hc : cfgOk c = true
    · rw [if_pos hc] at hp
      refine ⟨prog, hc, hp, hb, hd, ?_⟩
      unfold compile compileProg
      rw [if_pos hc, hp, hb]
      rfl
    · rw [if_neg hc] at hp; cases hp

/-- The compiler's own output always validates once its written data is
    off the code (completeness of the validator on honest candidates). -/
theorem validate_compile (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte) (h : compile c L certs src = some bytes)
    (hd : datenGetrennt c L (optimise certs src) bytes.length = true) :
    validate c L certs src bytes = true := by
  unfold compile at h
  cases hp : compileProg c L certs src with
  | none => rw [hp] at h; cases h
  | some prog =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    unfold validate
    rw [hp]
    simp [decodeAll_encodeAll prog _ (length_le_encodeAll prog), hd]

/-- A code region start offset by its length. -/
theorem addrOff_natAdresse (a n : Nat) : addrOff (natAdresse a) n = natAdresse (a + n) := by
  unfold addrOff natAdresse
  rw [BitVec.ofNat_add]

/-! ## 10. THE CLOSING THEOREM -/

/-- **PIPELINE CORRECTNESS.** If the validator accepts candidate bytes for
    a source block and optimiser certificates, then from ANY target state
    whose code region holds those bytes (executable, not writable) at the
    instruction pointer, whose placed slots represent the source world
    (`WorldRep`, over a separated layout) and whose variable registers
    represent the environment (`EnvRepr`), and for every source run of the
    ORIGINAL, UNOPTIMISED block through the REAL `execBlock` that ends
    normally in `σ'`, `ρ'`: fetching, decoding and executing the bytes from
    memory terminates at the end of the code region in a state that
    represents `σ'` and `ρ'`.

    Composed from: optimiser soundness (`applyPipeline_sound` via
    `optimise_sound`, `BlockEquiv`), lowering correctness
    (`senkBlock_korrekt`: `senkung_korrekt`, `rep_*`/`RepSlot`, the `cmp`
    flag facts), the codec round trip and fetch (`kanonisch_schritt_ueberein`
    through `lauf_zu_laufBytes`), and the recomputing validator
    (`validate_sound`). -/
theorem pipeline_correct (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (σ' : World D) (ρ' : Env D Γ) (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    ∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) := by
  obtain ⟨prog, hc, hlow, hb, -, -⟩ := validate_sound c L certs src bytes hval
  obtain ⟨n, s', hrun, hent⟩ := senkBlock_korrekt c L hc hsep O passes R bytes
    (optimise certs src) [] [] prog hlow σ ρ s hcode (by simp [hb])
    (by rw [hrip]; exact (addrOff_null _).symm) hW hE
  rw [optimise_sound certs src O passes R σ ρ, hsrc] at hent
  obtain ⟨hr, hw, he⟩ := hent
  refine ⟨n, s', hrun, ?_, hw, he⟩
  rw [hr, addrOff_natAdresse, hb]
  simp

/-- **PIPELINE REFUSAL CORRESPONDENCE.** The same chain for a source run
    that stops at a failed check with reason `r`: the fetched run reaches
    the refusal exit of `r` with the world of the failed check represented. -/
theorem pipeline_refuses (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (σ' : World D) (r : Fin V.gruende) (hsrc : execBlock O passes R src σ ρ = .grund σ' r) :
    ∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (exitAdr c r.val) ∧ WorldRep L s'.speicher σ' := by
  obtain ⟨prog, hc, hlow, hb, -, -⟩ := validate_sound c L certs src bytes hval
  obtain ⟨n, s', hrun, hent⟩ := senkBlock_korrekt c L hc hsep O passes R bytes
    (optimise certs src) [] [] prog hlow σ ρ s hcode (by simp [hb])
    (by rw [hrip]; exact (addrOff_null _).symm) hW hE
  rw [optimise_sound certs src O passes R σ ρ, hsrc] at hent
  exact ⟨n, s', hrun, hent⟩

/-- The refusal correspondence in its ORIGINAL form (exit at
    `exitBase + r`), for the default stride `1`: the general theorem
    specialised, nothing assumed beyond the stride. -/
theorem pipeline_refuses_eins (c : PipeCfg) (hst : c.exitStride = 1) (L : Layout D)
    (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (σ' : World D) (r : Fin V.gruende) (hsrc : execBlock O passes R src σ ρ = .grund σ' r) :
    ∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (c.exitBase + r.val) ∧ WorldRep L s'.speicher σ' := by
  rw [← exitAdr_eins c hst]
  exact pipeline_refuses c L certs src bytes hval hsep O passes R σ ρ s hcode hrip hW hE σ' r hsrc

/-- **NO OTHER OUTCOME.** An accepted source block, run through the real
    `execBlock`, ends normally or at a failed check -- for every world,
    environment, oracle, budget and callee table. -/
theorem pipeline_ausgang (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c L certs src bytes = true)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) :
    (∃ σ' ρ', execBlock O passes R src σ ρ = .ok σ' ρ') ∨
      (∃ σ' r, execBlock O passes R src σ ρ = .grund σ' r) := by
  obtain ⟨prog, -, hlow, -, -, -⟩ := validate_sound c L certs src bytes hval
  rw [← optimise_sound certs src O passes R σ ρ]
  exact senkBlock_ausgang c L O passes R _ 0 prog hlow σ ρ

end Block

/- CUTS (exactly what is NOT proved here):

   Fragment. Accepted, and nothing else (every other form answers `none`):
   - `Block.nil`;
   - `Block.cons` of `Stmt.assignSlot t f i e` where the index `i` is a
     constant recomputed by `constInt?`, the slot `(t, k, f)` is placed by
     the layout at an address passing `repOk` (integer field, `0 <= lo`,
     `hi < 2^64`, no wrap), and the value `e` is an arbitrary-depth
     `senkTief` tree (`lit`/`var`/`weiter`/`add`/`sub`/`neg`) that fits the
     scratch stack `tmp :: frei` (one register per binary/`neg` level on
     the left spine, no spilling);
   - `Block.cons` of `Stmt.ite c t e` where `c` is `<`/`<=`/`=` over two
     arbitrary-depth `senkTief` operands that fit the stack and whose TYPE
     ranges lie in the signed 64-bit window (`imFensterB`), and BOTH `t`
     and `e` are blocks of this fragment (recursively), with both forward
     displacements below `2^31` (`sprungOk`, decided);
   - `Block.pruefung c (retGrund r) rest` with `c` the literal `true`, or a
     comparison as for `ite`, lowered to `cmp` + `jumpIf32` on the negated
     condition (`negBed`) to the refusal exit.
   The original one-level fragment is a special case with IDENTICAL code
   (`senkWert_als_tief`, `senkBed_als_tief`); the original lemmas
   (`senkWert_korrekt`, `senkBed_korrekt`, `assign_lauf`) stay proved over
   the original definitions and are no longer used by the block lowering.
   NOT covered: variable or computed indices (no scaled addressing),
   `mul`/`div`/bitwise/memory reads in values, conditions other than one
   comparison (`und`/`oder`/`nicht`, a bare boolean variable, a literal in
   an `ite`), register spilling, every other statement (`assignVar`,
   `assignGlob`, loops, `locks`, calls, byte writes, ...), every other
   block form (`bind`, `narrow`, calls, gates, floats, ...), `else` blocks
   other than a bare reason (`ret`, `leave`/`next`, statements in `else`),
   boolean, sum, float or pointer slots, a check folded to literal
   `false`. The read trace of a condition (`World.lese` over `c.orte`) is
   not represented in the target (`WorldRep` ignores the trace), so no
   read-free restriction is needed and none is claimed: the trace is
   simply not part of the correspondence.

   Refusal exit. A failed check jumps to `exitAdr c r = exitBase +
   exitStride * r` (stride `1` by default, which is the original
   `exitBase + r`, re-derived as `pipeline_refuses_eins`); the run is
   followed exactly to that address with the world represented
   (`pipeline_refuses`). No code AT the exit is generated, validated or
   executed: returning the reason to a caller, the ABI and the
   register/flag state at the exit are OPEN.

   Memory and image. `CodeAt` (code bytes at the instruction pointer,
   executable, NOT writable), `WorldRep` (placed slots readable, writable,
   holding the source values) and `LayoutSep` (placed slots pairwise equal
   or disjoint) are PREMISES on the start state and the layout. `validate`
   checks the bytes, their decoding and that every WRITTEN slot lies off
   the code region; it cannot check `LayoutSep` for an arbitrary layout
   function. The connection to a loaded image (`ValidatorSkeleton.valX86`,
   `LoadedExecution.bildZustand`, relocation) is NOT made here. Slots the
   layout does not place are not represented and not claimed.

   Outcome. Only `Ausgang.ok` and `Ausgang.grund` are reachable for an
   accepted block (`senkBlock_ausgang`, proved, through both branches of
   every `ite`). After a normal end the variable registers, the world on
   placed slots and the end address are claimed; flags, the three working
   registers and the scratch registers `frei` are NOT.

   Optimiser. Whatever `applyPipeline` accepts, with its own CUTS
   (`OptimizationRules.lean`); a refused certificate list falls back to the
   unchanged block. Rewrites whose output the lowering cannot take (e.g. a
   condition folded to `false`) make the compile refuse, never guess.

   Machine. Pilot ISA only (`Befehl`, `Codec.encode`/`decode`,
   `Ausfuehrung.schritt`). The instruction type is used at four points --
   `encode`, `schritt` (through `kanon`), the shape class `gerade`, and the
   accepted lowerings `senkAtom`/`senkFrag`/`senkTief`/`senkVergleich` and
   the two jump forms of an `ite` -- so a unified ISA can replace
   it there; `ISA.lean` is not used or edited. Sequential single-core runs
   only (`laufBytes`): no TSO, no concurrency, no machine-G/GX transfer
   (a check the optimiser drops removes a G step, `BlockEquiv`). No time or
   budget transfer: the step count `n` is not related to any source
   budget. No hardware claim: memory is the model `Speicher`.
-/

#print axioms addrOff_addrOff
#print axioms holeFetchAux_praefix
#print axioms ausfuehrbarN_von
#print axioms byteschritt_im_code
#print axioms write64_schreibbar
#print axioms schreibbar8_byte
#print axioms write64_nicht_schreibbar
#print axioms schritt_gerade
#print axioms codeAt_erhalten
#print axioms laufBytes_add
#print axioms lauf_zu_laufBytes
#print axioms worldRep_lese
#print axioms repOk_int
#print axioms natAdresse_ohneUmbruch
#print axioms natAdresse_toNat
#print axioms worldRep_store
#print axioms bedingung_l_sub64
#print axioms sub64_zf_eq
#print axioms sint_inj
#print axioms bedingung_ge_sub64
#print axioms bedingung_g_sub64
#print axioms bedingung_ne_sub64
#print axioms abbOf_mem
#print axioms cfgOk_frei
#print axioms cfgOk_regs
#print axioms cfgOk_frisch
#print axioms envRepr_fremd
#print axioms istWert_von
#print axioms senkAtom_gerade
#print axioms senkFrag_gerade
#print axioms senkWert_gerade
#print axioms senkWert_korrekt
#print axioms istWahr_wahr
#print axioms vergleich_inv
#print axioms istBed_von
#print axioms vergleich_lauf
#print axioms intWort_sint_zahl
#print axioms senkBed_korrekt
#print axioms assign_lauf
#print axioms senkBlock_korrekt
#print axioms senkBlock_ausgang
#print axioms optimise_sound
#print axioms length_le_encodeAll
#print axioms decodeAll_encodeAll
#print axioms validate_sound
#print axioms validate_compile
#print axioms addrOff_natAdresse
#print axioms pipeline_correct
#print axioms pipeline_refuses
#print axioms pipeline_refuses_eins
#print axioms exitAdr_eins
#print axioms exitAdr_abstand
#print axioms pipeline_ausgang
#print axioms cfgOk_frei_liste
#print axioms cfgOk_frischListe
#print axioms cfgOk_rsp
#print axioms cfgOk_var_frei
#print axioms senkAtom_als_tief
#print axioms senkWert_als_tief
#print axioms istTief_gerade
#print axioms senkWertT_gerade
#print axioms senkWertT_korrekt
#print axioms envRepr_tief
#print axioms bedingung_negBed
#print axioms vergleichT_lauf
#print axioms senkBedT_korrekt
#print axioms senkBed_als_tief
#print axioms assignT_lauf
#print axioms sprungOk_addr
#print axioms encode_jumpIf32_len
#print axioms encode_jump32_len
#print axioms encodeAll_iteCode
#print axioms encodeAll_iteCode_len
#print axioms senkBlock_assign
#print axioms senkBlock_ite_inv
#print axioms execBlock_cons_stmtOk
#print axioms execBlock_cons_stmtGrund
#print axioms execStmt_ite
#print axioms senkBlock_korrektC
#print axioms slotAdressen_cons_eq

end Gabbro.Grammatik.X86.Pipeline
