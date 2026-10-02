/-
  File:      Grammatik/X86/Pipeline.lean
  Subject:   The first complete end-to-end pipeline in Lean, over a selected
             fragment: typed Gabbro source block -> certified optimiser ->
             direct lowering to the 14 pilot instructions -> canonical bytes
             in a code region -> byte-level fetch/decode/execute, with a
             validator that RECOMPUTES the bytes from the source and ONE
             closing theorem (`pipeline_correct`) over the REAL `execBlock`
             of the ORIGINAL (unoptimised) block.

  Reused, not duplicated:
    - optimiser: `OptimizationRules.applyPipeline`/`applyPipeline_sound`
      (`BlockEquiv`), `constInt?`/`constInt?_sound` for constant indices;
    - expression lowering: `ExpressionLowering.senkFrag`/`senkAtom`,
      `senkung_korrekt`, `senkAtom_korrekt`, `EnvRepr`, `Frisch`,
      `intWort_sint`; `SourceAssignmentLowering.intWort_zahlWort`;
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
  /-- Refusal exits: reason `r` exits at `exitBase + r`. -/
  exitBase : Nat
  deriving DecidableEq, Repr

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
    c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧ c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧ c.adr ≠ .rsp)

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
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9⟩ := hc
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
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9⟩ := hc
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

end Gabbro.Grammatik.X86.Pipeline
