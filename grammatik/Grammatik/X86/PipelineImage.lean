/-
  File:      Grammatik/X86/PipelineImage.lean
  Subject:   The loaded image and the refusal exit of the end-to-end pipeline
             (`Pipeline.lean`): the start-state premises `CodeAt`, `WorldRep`
             and `LayoutSep` of `pipeline_correct` are DERIVED from a decided
             image check over the existing loader (`Bild.geladen`,
             `LoadedExecution.bildZustand`), and a refusal no longer ends at a
             bare address: a fixed exit stub per reason, placed in the image
             and checked, loads the reason into `rax`, after which the byte
             machine stops at a defined address.

  Reused, not duplicated:
    - pipeline: `Pipeline.validate`/`validate_sound`, `pipeline_correct`,
      `pipeline_refuses`, `senkBlock`, `optimise`/`optimise_sound`,
      `CodeAt`, `WorldRep`, `LayoutSep`, `Layout`, `codeAt_erhalten`,
      `byteschritt_im_code`, `write64_nicht_schreibbar`, `laufBytes_add`,
      `kanon`, `addrOff_natAdresse`;
    - image and loader: `Bild`, `Abschnitt`, `geladen`, `effBias`,
      `LoadedExecution.bildZustand`, `ValidatorSkeleton.valX86`,
      `TableLayout.TabLayout`/`layoutOk`/`alsRegion`, `Regionen.Region`/
      `regionDisjunkt`;
    - representation: `SourceMemory.repOk`, `RepSlot`, `zahlWort`;
    - machine: `Codec.encode`, `Ausfuehrung.schritt`/`schritt_movImm64`,
      `Byteschritt.byteschritt`/`laufBytes`/`fetchDekodiert`,
      `Speicher.write64_erhaelt_berechtigungen`.
  No second loader, no second machine, no second source interpreter, no
  per-program rule.

  THE EXIT ABI (the smallest honest one under the fixed exit addresses of
  `Pipeline.lean`, where a failed check of reason `r` jumps to
  `exitBase + r`): at `exitBase + r` the image holds exactly the canonical
  bytes of `mov rax, r` (`movImm64 .rax (intWort r)`, 10 bytes), executable
  and not writable; the byte right after it, `exitBase + r + 10`, is NOT
  executable in the image. So a refusal ends with `rax = r` at the defined
  stop address `exitBase + r + 10`, where the byte machine stops
  (`byteschritt = .verweigert`, a fetch without execute permission).
  Why not `ret` or a jump to one common sequence: the pipeline gives NO
  register facts at the exit (only the address and the world), so a stub
  must not depend on `rsp` or any register; `mov imm` is the only pilot
  form that does not. Why one stub per USED reason: exits are one byte
  apart, a 10-byte stub cannot exist for every reason of a contract;
  stubs are generated for the reasons the lowered block can actually
  reach (`grundListe`), and the image check refuses overlapping stubs
  (see CUTS).

  The normal end is a defined stop too: the image check demands that the
  byte right after the code is not executable.

  The joint witness and the poison probes live in
  `Grammatik/X86/PipelineImageWitnesses.lean`.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.LoadedExecution
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86.PipelineImage

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline

variable {D : Deklaration}

/-! ## 1. A finite slot layout: placements

    The pipeline's `Layout` is an arbitrary function; nothing about it can
    be decided. A placement list is the finite, checkable form: each entry
    places one source slot `(t, k, f)` at a byte address. Its layout looks
    the slot up (first hit). -/

/-- One placed source slot. -/
structure Platz (D : Deklaration) where
  t : D.Tab
  k : Int
  f : D.Feld t
  a : Nat

/-- A placement names the slot `(t, k, f)`. -/
def Platz.trifft (p : Platz D) (t : D.Tab) (k : Int) (f : D.Feld t) : Bool :=
  if h : p.t = t then decide (p.k = k) && decide (cast (congrArg D.Feld h) p.f = f)
  else false

/-- The layout of a placement list: the address of the first placement
    that names the slot. -/
def layoutVon (ps : List (Platz D)) : Layout D where
  loc := fun t k f => (ps.find? (fun p => p.trifft t k f)).map Platz.a

/-- A hit names exactly that slot. -/
theorem trifft_inv (p : Platz D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (h : p.trifft t k f = true) :
    ∃ ht : p.t = t, p.k = k ∧ cast (congrArg D.Feld ht) p.f = f := by
  unfold Platz.trifft at h
  by_cases ht : p.t = t
  · rw [dif_pos ht] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ht, h.1, h.2⟩
  · rw [dif_neg ht] at h; cases h

/-- A placed slot comes from a member placement that names it. -/
theorem layoutVon_loc (ps : List (Platz D)) (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat)
    (h : (layoutVon ps).loc t k f = some a) :
    ∃ p ∈ ps, p.trifft t k f = true ∧ p.a = a := by
  unfold layoutVon at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have h3 : p.trifft t k f = true := List.find?_some (p := fun (q : Platz D) => q.trifft t k f) hp
  exact ⟨p, List.mem_of_find?_eq_some hp, h3, rfl⟩

/-- A member placement that names its own slot is found (possibly at an
    earlier placement of the same slot). -/
theorem layoutVon_some (ps : List (Platz D)) (t : D.Tab) (k : Int) (f : D.Feld t)
    (p : Platz D) (hp : p ∈ ps) (h : p.trifft t k f = true) :
    ∃ a, (layoutVon ps).loc t k f = some a := by
  unfold layoutVon
  cases hf : ps.find? (fun p => p.trifft t k f) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    rw [h] at this
    exact absurd rfl this
  | some q => exact ⟨q.a, by simp [hf]⟩

/-! ## 2. Decided layout separation -/

/-- Two placements name the same slot. -/
def gleicherSchluessel (p q : Platz D) : Bool :=
  if h : p.t = q.t then decide (p.k = q.k) && decide (cast (congrArg D.Feld h) p.f = q.f)
  else false

/-- Every two placements name the same slot or have disjoint footprints. -/
def sepB (ps : List (Platz D)) : Bool :=
  ps.all fun p => ps.all fun q =>
    gleicherSchluessel p q || decide (p.a + 8 ≤ q.a ∨ q.a + 8 ≤ p.a)

/-- SEPARATION FROM THE CHECK: the decided `sepB` gives the pipeline's
    `LayoutSep` for the placement layout. -/
theorem sepB_sound (ps : List (Platz D)) (h : sepB ps = true) : LayoutSep (layoutVon ps) := by
  intro t1 k1 f1 a1 t2 k2 f2 a2 h1 h2
  obtain ⟨p, hp, htp, rfl⟩ := layoutVon_loc ps t1 k1 f1 a1 h1
  obtain ⟨q, hq, htq, rfl⟩ := layoutVon_loc ps t2 k2 f2 a2 h2
  have hpq := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hpq
  rcases hpq with hs | hd
  · left
    obtain ⟨pt, pk, pf, pa⟩ := p
    obtain ⟨qt, qk, qf, qa⟩ := q
    obtain ⟨ht1, hk1, hf1⟩ := trifft_inv _ _ _ _ htp
    obtain ⟨ht2, hk2, hf2⟩ := trifft_inv _ _ _ _ htq
    simp only at ht1 hk1 hf1 ht2 hk2 hf2
    subst ht1 ht2 hk1 hk2 hf1 hf2
    unfold gleicherSchluessel at hs
    simp only at hs
    by_cases hpq : pt = qt
    · subst hpq
      rw [dif_pos rfl] at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨rfl, hf⟩ := hs
      simp only [cast_eq] at hf
      subst hf
      exact ⟨rfl, rfl, HEq.rfl⟩
    · rw [dif_neg hpq] at hs; cases hs
  · right; exact hd

/-! ## 3. Decided code region and world representation over a memory -/

/-- DECIDED `CodeAt`: every byte of `flat` sits at its offset from `cs`,
    executable and not writable. -/
def codeAtB (m : Speicher) (cs : Adresse) (flat : List Byte) : Bool :=
  (List.range flat.length).all fun i =>
    m.ausfuehrbar (addrOff cs i) && !m.schreibbar (addrOff cs i) &&
      decide (m.bytes (addrOff cs i) = flat.getD i 0)

theorem codeAtB_sound (m : Speicher) (cs : Adresse) (flat : List Byte)
    (h : codeAtB m cs flat = true) : CodeAt m cs flat := by
  intro i b hi
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
  have hc := List.all_eq_true.mp h i (List.mem_range.mpr hlt)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨h1, h2, ?_⟩
  rw [h3, List.getD_eq_getElem?_getD, hi]
  rfl

/-- The word of a slot value: the representation word of an integer
    slot, zero for every other type (no representation, see CUTS). -/
def slotWort : (ty : Ty) → Wert D ty → Wort
  | .int _ _, v => zahlWort v
  | _, _ => 0

theorem slotWort_cast {ty : Ty} {lo hi : Int} (v : Wert D ty) (hT : ty = .int lo hi) :
    slotWort ty v = zahlWort (cast (congrArg (Wert D) hT) v : Wert D (.int lo hi)) := by
  subst hT
  rfl

/-- DECIDED PLACEMENT ADMISSION over a memory: every placement is an
    admitted integer slot (`repOk`), readable and writable for its eight
    bytes. -/
def platzOkB (m : Speicher) (ps : List (Platz D)) : Bool :=
  ps.all fun p => repOk (D.typ p.t p.f) p.a 8 0 && lesbar8 m (natAdresse p.a) &&
    schreibbar8 m (natAdresse p.a)

/-- DECIDED WORLD CHECK over a memory: every placed slot reads back the
    representation word of the source value. -/
def weltB (m : Speicher) (ps : List (Platz D)) (σ : World D) : Bool :=
  ps.all fun p => decide (read64 m (natAdresse p.a) = some (slotWort _ (σ.slots p.t p.k p.f)))

/-- REPRESENTATION FROM THE CHECKS: admission and the world check give
    the pipeline's `WorldRep` for the placement layout. -/
theorem worldRep_von (m : Speicher) (ps : List (Platz D)) (σ : World D)
    (hp : platzOkB m ps = true) (hw : weltB m ps σ = true) :
    WorldRep (layoutVon ps) m σ := by
  intro t k f a hloc
  obtain ⟨p, hmem, htr, rfl⟩ := layoutVon_loc ps t k f a hloc
  have h1 := List.all_eq_true.mp hp p hmem
  have h2 := List.all_eq_true.mp hw p hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  obtain ⟨pt, pk, pf, pa⟩ := p
  obtain ⟨ht, hk, hf⟩ := trifft_inv _ _ _ _ htr
  simp only at ht hk hf h1 h2 ⊢
  subst ht hk hf
  simp only [cast_eq] at *
  obtain ⟨⟨hrep, hrd⟩, hwr⟩ := h1
  refine ⟨by simpa using hrep, hrd, hwr, fun lo hi hT => ?_⟩
  unfold RepSlot
  rw [h2, slotWort_cast _ hT]

/-! ## 4. The memory frame of every byte step

    Whatever instruction runs, a byte step keeps every permission and
    every byte that is not writable. Proved for EVERY pilot form (the
    stores, pushes and calls write through the permission-checked
    `write64`), so it holds of any byte run, independent of what the
    lowered code is. -/

/-- The frame of a memory change. -/
def ByteRahmen (m m' : Speicher) : Prop :=
  m'.ausfuehrbar = m.ausfuehrbar ∧ m'.schreibbar = m.schreibbar ∧ m'.lesbar = m.lesbar ∧
    ∀ x, m.schreibbar x = false → m'.bytes x = m.bytes x

theorem byteRahmen_refl (m : Speicher) : ByteRahmen m m := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem byteRahmen_trans {m1 m2 m3 : Speicher} (h1 : ByteRahmen m1 m2) (h2 : ByteRahmen m2 m3) :
    ByteRahmen m1 m3 := by
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun x hx => ?_⟩
  rw [d2 x (by rw [b1]; exact hx), d1 x hx]

theorem byteRahmen_write64 {m m' : Speicher} {a : Adresse} {v : Wort} (h : write64 m a v = some m') :
    ByteRahmen m m' := by
  obtain ⟨hl, hs, hx⟩ := write64_erhaelt_berechtigungen _ _ _ _ h
  exact ⟨hx, hs, hl, fun x hx' => write64_nicht_schreibbar _ _ _ _ h x hx'⟩

/-- STEP FRAME: every successful pilot step keeps the frame. -/
theorem schritt_rahmen (d : Decodiert) (s s' : Zustand) (h : schritt d s = some s') :
    ByteRahmen s.speicher s'.speicher := by
  unfold schritt at h
  split at h
  · cases h
  · rename_i hok
    cases hb : d.befehl with
    | movImm64 dst v =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | movReg64 dst src =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | addReg64 dst src =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | subReg64 dst src =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | xorReg64 dst src =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | cmpReg64 lhs rhs =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | load64 dst base disp =>
      rw [hb] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
      · cases h
    | store64 base src disp =>
      rw [hb] at h
      simp only at h
      split at h
      · rename_i m hw
        simp only [Option.some.injEq] at h; subst h; exact byteRahmen_write64 hw
      · cases h
    | jump32 disp =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | jumpIf32 cond disp =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
    | call32 disp =>
      rw [hb] at h
      simp only at h
      split at h
      · rename_i m hw
        simp only [Option.some.injEq] at h; subst h; exact byteRahmen_write64 hw
      · cases h
    | push64 src =>
      rw [hb] at h
      simp only at h
      split at h
      · rename_i m hw
        simp only [Option.some.injEq] at h; subst h; exact byteRahmen_write64 hw
      · cases h
    | pop64 dst =>
      rw [hb] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        split <;> exact byteRahmen_refl _
      · cases h
    | ret =>
      rw [hb] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact byteRahmen_refl _
      · cases h

/-- BYTE-STEP FRAME. -/
theorem byteschritt_rahmen (s s' : Zustand) (h : byteschritt s = .weiter s') :
    ByteRahmen s.speicher s'.speicher := by
  unfold byteschritt at h
  cases hf : fetchDekodiert s with
  | none => rw [hf] at h; cases h
  | some dr =>
    obtain ⟨d, rest⟩ := dr
    rw [hf] at h
    simp only at h
    cases hs : schritt d s with
    | none => rw [hs] at h; cases h
    | some s2 =>
      rw [hs] at h
      injection h with h
      subst h
      exact schritt_rahmen d s _ hs

/-- RUN FRAME: a whole byte run keeps the frame. -/
theorem laufBytes_rahmen : ∀ (n : Nat) (s s' : Zustand), laufBytes n s = .weiter s' →
    ByteRahmen s.speicher s'.speicher
  | 0, s, s', h => by
    simp only [laufBytes] at h; cases h; exact byteRahmen_refl _
  | n + 1, s, s', h => by
    simp only [laufBytes] at h
    cases hb : byteschritt s with
    | verweigert => rw [hb] at h; cases h
    | weiter s2 =>
      rw [hb] at h
      exact byteRahmen_trans (byteschritt_rahmen s s2 hb) (laufBytes_rahmen n s2 s' h)

/-- A code region survives every byte run. -/
theorem codeAt_lauf (n : Nat) (s s' : Zustand) (h : laufBytes n s = .weiter s')
    (cs : Adresse) (flat : List Byte) (hc : CodeAt s.speicher cs flat) :
    CodeAt s'.speicher cs flat := by
  obtain ⟨hx, hs, -, hb⟩ := laufBytes_rahmen n s s' h
  exact codeAt_erhalten _ _ cs flat hc hx hs hb

/-- THE STOP: the byte machine stops where the instruction pointer has no
    execute permission (an empty fetch decodes to nothing). -/
theorem byteschritt_stop (s : Zustand) (h : s.speicher.ausfuehrbar s.rip = false) :
    byteschritt s = .verweigert := by
  apply byteschritt_verweigert_ohne_fetch
  have hg : geholt s = [] := by
    unfold geholt fetchCap
    simp only [holeFetchAux, addrOff_null, h]
    rfl
  unfold fetchDekodiert
  rw [hg]
  rfl


/-! ## 5. The refusal exits a lowered block can reach

    `grundListe` collects the reason of every check of a block; a lowered
    block that ends with a reason ends with one of them. Proved from the
    acceptor (`senkBlock`), mirroring `senkBlock_ausgang`. -/

section Gruende
variable {V : Vertrag D}

/-- The reasons of the checks of a block, in order. -/
def grundListe :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → List Nat
  | _, _, _, _, .nil => []
  | _, _, _, _, .cons _ rest => grundListe rest
  | _, _, _, _, .pruefung _ (.retGrund r _) rest => r.val :: grundListe rest
  | _, _, _, _, .pruefung _ _ rest => grundListe rest
  | _, _, _, _, _ => []

/-- A REACHED REASON IS LISTED: a lowered block that ends with reason `r`
    ends at one of its own checks. -/
theorem grund_mem (c : PipeCfg) (L : Layout D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (pos : Nat)
    (prog : List Befehl) (h : senkBlock c L pos b = some prog) (σ : World D) (ρ : Env D Γ)
    (σ' : World D) (r : Fin V.gruende) (hx : execBlock O passes R b σ ρ = .grund σ' r) :
    r.val ∈ grundListe b := by
  generalize hb0 : b = b0 at h hx
  cases b0 with
  | nil => cases hx
  | cons st rest =>
    simp only [senkBlock] at h
    cases hs : senkStmt c L st with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
      | none => simp [hq] at h
      | some q =>
        cases st with
        | assignSlot t f i e hw hL =>
          exact grund_mem c L O passes R rest _ q hq _ ρ σ' r hx
        | _ => simp [senkStmt] at hs
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
        | retGrund r0 hΛ =>
          change (if wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ)
              then execBlock O passes R rest (σ.lese Λ cnd.orte) ρ
              else .grund (σ.lese Λ cnd.orte) r0) = .grund σ' r at hx
          show r.val ∈ r0.val :: grundListe rest
          split at hx
          · exact List.mem_cons_of_mem _ (grund_mem c L O passes R rest _ q hq _ ρ σ' r hx)
          · have hr : r0 = r := by injection hx
            subst hr
            exact List.mem_cons_self
        | _ => simp [senkPruef] at hs
  | _ => simp [senkBlock] at h
termination_by sizeOf b
decreasing_by
  all_goals
    subst hb0
    simp only [Block.cons.sizeOf_spec, Block.pruefung.sizeOf_spec]
    omega

end Gruende

/-! ## 6. The exit stubs and the image constructor

    The image is built from the pipeline output: the code section holds
    the validated bytes (`compile`), one stub section per reachable reason
    holds `mov rax, r`, and one data section per checked table extent
    (`TableLayout.TabLayout`) holds the representation bytes of the
    initial world on the placed slots. The constructor is a convenience
    for an honest producer: it is NOT trusted. The theorems below take any
    image and demand only the decided `imageOk`. -/

/-- The exit register of the refusal ABI. -/
def exitReg : Register := .rax

/-- The exit stub of reason `g`: `mov rax, g` (10 canonical bytes). -/
def stubBefehl (g : Nat) : Befehl := .movImm64 exitReg (intWort g)

def stubBytes (g : Nat) : List Byte := encode (stubBefehl g)

theorem stubBytes_length (g : Nat) : (stubBytes g).length = 10 := rfl

/-- The byte of the initial world at address `x`: the representation
    byte of the first placement covering `x`, else zero. -/
def slotByte (ps : List (Platz D)) (σ : World D) (x : Nat) : Byte :=
  match ps.find? (fun p => decide (p.a ≤ x ∧ x < p.a + 8)) with
  | some p => wortByte (slotWort _ (σ.slots p.t p.k p.f)) (x - p.a)
  | none => 0

/-- The code section: the entry sequence `pro` (possibly empty) followed
    by the code bytes, placed so that the code starts exactly at
    `codeBase`; readable, executable, never writable. -/
def codeAbschnittP (c : PipeCfg) (pro bytes : List Byte) : Abschnitt :=
  { dateiOff := 0, dateiLen := pro.length + bytes.length, vaddr := c.codeBase - pro.length,
    memLen := pro.length + bytes.length, lesbar := true, schreibbar := false,
    ausfuehrbar := true, ausr := 1 }

/-- The code section without an entry sequence. -/
def codeAbschnitt (c : PipeCfg) (bytes : List Byte) : Abschnitt := codeAbschnittP c [] bytes

/-- One stub section per reason, from file offset `off`, at the reason's
    exit address `exitAdr c g`. -/
def stubAbschnitte (c : PipeCfg) : Nat → List Nat → List Abschnitt
  | _, [] => []
  | off, g :: gs =>
    { dateiOff := off, dateiLen := 10, vaddr := exitAdr c g, memLen := 10,
      lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 } ::
      stubAbschnitte c (off + 10) gs

/-- One data section per table extent, from file offset `off`. -/
def datenAbschnitte : Nat → List TabLayout → List Abschnitt
  | _, [] => []
  | off, e :: es =>
    { dateiOff := off, dateiLen := e.len, vaddr := e.basis, memLen := e.len,
      lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := e.ausr } ::
      datenAbschnitte (off + e.len) es

/-- The initial-world bytes of one table extent. -/
def datenChunk (ps : List (Platz D)) (σ : World D) (e : TabLayout) : List Byte :=
  (List.range e.len).map fun i => slotByte ps σ (e.basis + i)

/-- The file bytes of the data sections. -/
def datenDatei (ps : List (Platz D)) (σ : World D) (es : List TabLayout) : List Byte :=
  (es.map (datenChunk ps σ)).flatten

/-- THE IMAGE CONSTRUCTOR with an entry sequence `pro` in front of the
    code (the entry is `codeBase - |pro|`; `codeBase` stays listed). -/
def baueBildP (c : PipeCfg) (pro bytes : List Byte) (gs : List Nat) (ps : List (Platz D))
    (σ : World D) (es : List TabLayout) : Bild :=
  { datei := pro ++ bytes ++ (gs.map stubBytes).flatten ++ datenDatei ps σ es
    abschnitte := codeAbschnittP c pro bytes :: stubAbschnitte c (pro.length + bytes.length) gs ++
      datenAbschnitte (pro.length + bytes.length + 10 * gs.length) es
    reloks := []
    eintraege := [c.codeBase - pro.length, c.codeBase]
    modus := .fest }

/-- THE IMAGE CONSTRUCTOR from the pipeline output (no entry sequence). -/
def baueBild (c : PipeCfg) (bytes : List Byte) (gs : List Nat) (ps : List (Platz D))
    (σ : World D) (es : List TabLayout) : Bild :=
  baueBildP c [] bytes gs ps σ es

/-- The reason list without duplicates (the last occurrence is kept):
    one stub per reason, never two sections at one exit. -/
def ohneDoppel : List Nat → List Nat
  | [] => []
  | g :: gs => if g ∈ gs then ohneDoppel gs else g :: ohneDoppel gs

theorem mem_ohneDoppel : ∀ (gs : List Nat) (g : Nat), g ∈ ohneDoppel gs ↔ g ∈ gs
  | [], g => by simp [ohneDoppel]
  | x :: xs, g => by
    unfold ohneDoppel
    by_cases hx : x ∈ xs
    · rw [if_pos hx, mem_ohneDoppel xs g]
      constructor
      · exact List.mem_cons_of_mem _
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hx
        · exact h
    · rw [if_neg hx, List.mem_cons, List.mem_cons, mem_ohneDoppel xs g]

theorem ohneDoppel_nodup : ∀ (gs : List Nat), (ohneDoppel gs).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    unfold ohneDoppel
    by_cases hx : x ∈ xs
    · rw [if_pos hx]; exact ohneDoppel_nodup xs
    · rw [if_neg hx]
      exact List.nodup_cons.mpr ⟨fun h => hx ((mem_ohneDoppel xs x).mp h), ohneDoppel_nodup xs⟩

/-- The image of a compiled block: one stub for each of its reachable
    reasons. -/
def bildFuer {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : PipeCfg)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (ps : List (Platz D)) (σ : World D) (es : List TabLayout) : Bild :=
  baueBild c bytes (ohneDoppel (grundListe (optimise certs src))) ps σ es

/-- The image of a compiled block with the entry sequence `pro` in front. -/
def bildFuerP {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : PipeCfg)
    (pro : List Byte) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (ps : List (Platz D)) (σ : World D) (es : List TabLayout) : Bild :=
  baueBildP c pro bytes (ohneDoppel (grundListe (optimise certs src))) ps σ es

/-! ## 7. The decided image check -/

/-- The loaded memory of an image (the existing loader, at its own bias). -/
def ladung (bild : Bild) : Speicher := geladen bild (effBias bild.modus)

/-- The code region as a target region. -/
def codeRegion (c : PipeCfg) (bytes : List Byte) : Region :=
  { basis := c.codeBase, len := bytes.length, lesbar := true, schreibbar := false,
    ausfuehrbar := true }

/-- The stub region of reason `g` as a target region. -/
def stubRegion (c : PipeCfg) (g : Nat) : Region :=
  { basis := exitAdr c g, len := 10, lesbar := true, schreibbar := false,
    ausfuehrbar := true }

/-- THE IMAGE CHECK. Everything is RE-DECIDED from the candidate image,
    the configuration, the placements, the table layout and the source:
    1. `valX86` (checked mapping incl. W^X and disjoint sections, decode
       coverage of every executable section);
    2. `layoutOk` of the table extents; every placement inside one extent;
       code and every stub region `regionDisjunkt` from every extent;
    3. the loaded memory holds the code bytes at `codeBase` (executable,
       not writable), and the byte after the code is not executable;
    4. for every reachable reason `g` of the optimised block, the loaded
       memory holds the stub of `g` at `exitBase + g` (executable, not
       writable), and the byte after the stub is not executable;
    5. placements: decided separation, and every placed slot admitted
       (`repOk`), readable and writable in the loaded memory;
    6. the code start is a listed entry. -/
def imageOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (p : Profil)
    (bild : Bild) (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ') (bytes : List Byte) :
    Bool :=
  let m := ladung bild
  let gs := grundListe (optimise certs src)
  valX86 p bild &&
  layoutOk es &&
  ps.all (fun q => es.any fun e => decide (e.basis ≤ q.a ∧ q.a + 8 ≤ e.basis + e.len)) &&
  es.all (fun e => regionDisjunkt (codeRegion c bytes) (alsRegion e) &&
    gs.all fun g => regionDisjunkt (stubRegion c g) (alsRegion e)) &&
  codeAtB m (natAdresse c.codeBase) bytes &&
  !m.ausfuehrbar (natAdresse (c.codeBase + bytes.length)) &&
  gs.all (fun g => codeAtB m (natAdresse (exitAdr c g)) (stubBytes g) &&
    !m.ausfuehrbar (natAdresse (exitAdr c g + 10))) &&
  sepB ps &&
  platzOkB m ps &&
  bild.eintraege.contains c.codeBase

/-- THE INITIAL-WORLD CHECK: the loaded image represents `σ` on every
    placed slot. -/
def weltOk (bild : Bild) (ps : List (Platz D)) (σ : World D) : Bool :=
  weltB (ladung bild) ps σ

section Folgerungen
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- Unpacking the image check. -/
theorem imageOk_teile (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true) :
    valX86 p bild = true ∧ layoutOk es = true ∧
    (∀ q ∈ ps, ∃ e ∈ es, e.basis ≤ q.a ∧ q.a + 8 ≤ e.basis + e.len) ∧
    (∀ e ∈ es, regionDisjunkt (codeRegion c bytes) (alsRegion e) = true ∧
      ∀ g ∈ grundListe (optimise certs src),
        regionDisjunkt (stubRegion c g) (alsRegion e) = true) ∧
    codeAtB (ladung bild) (natAdresse c.codeBase) bytes = true ∧
    (ladung bild).ausfuehrbar (natAdresse (c.codeBase + bytes.length)) = false ∧
    (∀ g ∈ grundListe (optimise certs src),
      codeAtB (ladung bild) (natAdresse (exitAdr c g)) (stubBytes g) = true ∧
      (ladung bild).ausfuehrbar (natAdresse (exitAdr c g + 10)) = false) ∧
    sepB ps = true ∧ platzOkB (ladung bild) ps = true ∧
    c.codeBase ∈ bild.eintraege := by
  unfold imageOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, fun e he => ⟨(h4 e he).1, (h4 e he).2⟩, h5, h6,
    fun g hg => ⟨(h7 g hg).1, (h7 g hg).2⟩, h8, h9, h10⟩

/-- LOADED CODE: an accepted image holds the code bytes at `codeBase`,
    executable and not writable -- the `CodeAt` premise of the pipeline. -/
theorem imageOk_codeAt (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true) :
    CodeAt (ladung bild) (natAdresse c.codeBase) bytes :=
  codeAtB_sound _ _ _ (imageOk_teile p bild c ps es certs src bytes h).2.2.2.2.1

/-- LOADED SEPARATION: the `LayoutSep` premise of the pipeline. -/
theorem imageOk_layoutSep (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true) :
    LayoutSep (layoutVon ps) :=
  sepB_sound ps (imageOk_teile p bild c ps es certs src bytes h).2.2.2.2.2.2.2.1

/-- LOADED WORLD: the `WorldRep` premise of the pipeline, for the initial
    world the image was checked against. -/
theorem imageOk_worldRep (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true) (σ : World D)
    (hw : weltOk bild ps σ = true) :
    WorldRep (layoutVon ps) (ladung bild) σ :=
  worldRep_von _ ps σ (imageOk_teile p bild c ps es certs src bytes h).2.2.2.2.2.2.2.2.1 hw

/-- The image check implies the existing skeleton validator and the
    checked mapping (W^X, disjoint sections, entries in executable code). -/
theorem imageOk_valX86 (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true) :
    valX86 p bild = true ∧ wohlgeformt p bild = true ∧ c.codeBase ∈ bild.eintraege :=
  have ht := imageOk_teile p bild c ps es certs src bytes h
  ⟨ht.1, valX86_wohlgeformt p bild ht.1, ht.2.2.2.2.2.2.2.2.2⟩

/-- DATA OFF CODE AND STUBS: every placed slot footprint lies inside a
    checked table extent, and that extent is disjoint from the code region
    and from every stub region. -/
theorem imageOk_daten_getrennt (p : Profil) (bild : Bild) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (h : imageOk p bild c ps es certs src bytes = true)
    (q : Platz D) (hq : q ∈ ps) :
    (q.a + 8 ≤ c.codeBase ∨ c.codeBase + bytes.length ≤ q.a) ∧
      ∀ g ∈ grundListe (optimise certs src),
        q.a + 8 ≤ exitAdr c g ∨ exitAdr c g + 10 ≤ q.a := by
  obtain ⟨-, -, hin, hdis, -⟩ := imageOk_teile p bild c ps es certs src bytes h
  obtain ⟨e, he, hlo, hhi⟩ := hin q hq
  obtain ⟨hc, hs⟩ := hdis e he
  unfold regionDisjunkt codeRegion alsRegion at hc
  simp only [decide_eq_true_eq] at hc
  refine ⟨by omega, fun g hg => ?_⟩
  have := hs g hg
  unfold regionDisjunkt stubRegion alsRegion at this
  simp only [decide_eq_true_eq] at this
  omega

end Folgerungen

/-! ## 8. The closing theorems over the loaded image -/

section Schluss
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The loaded start state: the existing loader's state at the code
    start, with the entry registers and flags. -/
def startZustand (bild : Bild) (c : PipeCfg) (reg : Register → Wort) (fl : Flags) : Zustand :=
  bildZustand bild (effBias bild.modus) (natAdresse c.codeBase) reg fl

/-- **PIPELINE CORRECTNESS OVER THE LOADED IMAGE.** Premises are only:
    the code validator (`validate`), the image check (`imageOk`), the
    initial-world check (`weltOk`), the entry registers representing the
    source environment (`EnvRepr`), and the source run of the ORIGINAL
    block through the REAL `execBlock`. The start state is the existing
    loader's (`bildZustand` over `geladen`). Conclusion: the fetched byte
    run reaches the end of the code with world and environment
    represented, and the machine STOPS there. -/
theorem pipeline_correct_loaded (p : Profil) (bild : Bild) (c : PipeCfg)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ) (hE : EnvRepr ρ reg (abbOf c))
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (ρ' : Env D Γ) (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    ∃ n s', laufBytes n (startZustand bild c reg fl) = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      byteschritt s' = .verweigert ∧
      laufBytes (n + 1) (startZustand bild c reg fl) = .verweigert := by
  have ht := imageOk_teile p bild c ps es certs src bytes himg
  obtain ⟨n, s', hrun, hrip, hW, hE'⟩ := pipeline_correct c (layoutVon ps) certs src bytes hval
    (imageOk_layoutSep p bild c ps es certs src bytes himg) O passes R σ ρ
    (startZustand bild c reg fl) (imageOk_codeAt p bild c ps es certs src bytes himg) rfl
    (imageOk_worldRep p bild c ps es certs src bytes himg σ hwelt) hE σ' ρ' hsrc
  have hstop : byteschritt s' = .verweigert := by
    apply byteschritt_stop
    obtain ⟨hx, -⟩ := laufBytes_rahmen n _ s' hrun
    rw [hx, hrip]
    exact ht.2.2.2.2.2.1
  refine ⟨n, s', hrun, hrip, hW, hE', hstop, ?_⟩
  rw [laufBytes_add n 1 _ s' hrun]
  simp only [laufBytes, hstop]

/-- **PIPELINE REFUSAL OVER THE LOADED IMAGE, THROUGH THE EXIT STUB.** For
    a source run of the ORIGINAL block that stops at a failed check with
    reason `r`: the fetched byte run reaches the exit of `r`, executes the
    checked stub there, and ends at the defined stop address
    `exitBase + r + 10` with the reason in the exit register `rax` and the
    world of the failed check represented; the machine STOPS there. -/
theorem pipeline_refuses_loaded (p : Profil) (bild : Bild) (c : PipeCfg)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ) (hE : EnvRepr ρ reg (abbOf c))
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (r : Fin V.gruende) (hsrc : execBlock O passes R src σ ρ = .grund σ' r) :
    ∃ n s1 s', laufBytes n (startZustand bild c reg fl) = .weiter s1 ∧
      s1.rip = natAdresse (exitAdr c r.val) ∧
      byteschritt s1 = .weiter s' ∧
      s'.rip = natAdresse (exitAdr c r.val + 10) ∧
      s'.register exitReg = intWort r.val ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧
      laufBytes (n + 1) (startZustand bild c reg fl) = .weiter s' ∧
      byteschritt s' = .verweigert ∧
      laufBytes (n + 2) (startZustand bild c reg fl) = .verweigert := by
  have ht := imageOk_teile p bild c ps es certs src bytes himg
  obtain ⟨prog, -, hlow, -, -, -⟩ := validate_sound c (layoutVon ps) certs src bytes hval
  have hmem : r.val ∈ grundListe (optimise certs src) := by
    apply grund_mem c (layoutVon ps) O passes R (optimise certs src) 0 prog hlow σ ρ σ' r
    rw [optimise_sound certs src O passes R σ ρ]
    exact hsrc
  obtain ⟨hstubB, hstopB⟩ := ht.2.2.2.2.2.2.1 r.val hmem
  obtain ⟨n, s1, hrun, hrip, hW⟩ := pipeline_refuses c (layoutVon ps) certs src bytes hval
    (imageOk_layoutSep p bild c ps es certs src bytes himg) O passes R σ ρ
    (startZustand bild c reg fl) (imageOk_codeAt p bild c ps es certs src bytes himg) rfl
    (imageOk_worldRep p bild c ps es certs src bytes himg σ hwelt) hE σ' r hsrc
  -- the stub is still in memory at the exit (it is never writable)
  have hstub : CodeAt s1.speicher (natAdresse (exitAdr c r.val)) (stubBytes r.val) :=
    codeAt_lauf n _ s1 hrun _ _ (codeAtB_sound _ _ _ hstubB)
  have hbs := byteschritt_im_code s1 (natAdresse (exitAdr c r.val)) (stubBytes r.val) [] []
    (stubBefehl r.val) hstub (by simp [stubBytes]) (by rw [hrip]; exact (addrOff_null _).symm)
  rw [schritt_movImm64 (kanon (stubBefehl r.val)) s1 exitReg (intWort r.val)
    (laengeOk_encode _) rfl] at hbs
  let s' := schrittRegister s1 (ripNach s1.rip (kanon (stubBefehl r.val)).laenge) s1.flags
    exitReg (intWort r.val)
  have hrip' : s'.rip = natAdresse (exitAdr c r.val + 10) := by
    show ripNach s1.rip 10 = _
    rw [hrip, ripNach_addrOff, addrOff_natAdresse]
  have hstop : byteschritt s' = .verweigert := by
    apply byteschritt_stop
    obtain ⟨hx, -⟩ := laufBytes_rahmen n _ s1 hrun
    show s1.speicher.ausfuehrbar s'.rip = false
    rw [hx, hrip']
    exact hstopB
  have hrun1 : laufBytes (n + 1) (startZustand bild c reg fl) = .weiter s' := by
    rw [laufBytes_add n 1 _ s1 hrun]
    simp only [laufBytes, hbs]
    rfl
  refine ⟨n, s1, s', hrun, hrip, hbs, hrip',
    regSet_gleich s1.register exitReg (intWort r.val), hW, hrun1, hstop, ?_⟩
  rw [laufBytes_add (n + 1) 1 _ s' hrun1]
  simp only [laufBytes, hstop]

/-- **NO OTHER OUTCOME, LOADED.** From the loaded start state an accepted
    block either stops at the code end or at the stub stop of its reason,
    for every source run (the source side is `pipeline_ausgang`). -/
theorem pipeline_loaded_ausgang (p : Profil) (bild : Bild) (c : PipeCfg)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ) (hE : EnvRepr ρ reg (abbOf c))
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    ∃ n s', laufBytes n (startZustand bild c reg fl) = .weiter s' ∧
      byteschritt s' = .verweigert ∧
      ((s'.rip = natAdresse (c.codeBase + bytes.length) ∧
          ∃ σ' ρ', execBlock O passes R src σ ρ = .ok σ' ρ' ∧
            WorldRep (layoutVon ps) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c)) ∨
        (∃ σ' r, execBlock O passes R src σ ρ = .grund σ' r ∧
          s'.rip = natAdresse (exitAdr c r.val + 10) ∧
          s'.register exitReg = intWort r.val ∧
          WorldRep (layoutVon ps) s'.speicher σ')) := by
  rcases pipeline_ausgang c (layoutVon ps) certs src bytes hval O passes R σ ρ with
    ⟨σ', ρ', hsrc⟩ | ⟨σ', r, hsrc⟩
  · obtain ⟨n, s', hrun, hrip, hW, hE', hstop, -⟩ := pipeline_correct_loaded p bild c ps es
      certs src bytes hval himg σ hwelt reg fl ρ hE O passes R σ' ρ' hsrc
    exact ⟨n, s', hrun, hstop, Or.inl ⟨hrip, σ', ρ', hsrc, hW, hE'⟩⟩
  · obtain ⟨n, -, s', -, -, -, hrip, hreg, hW, hrun, hstop, -⟩ := pipeline_refuses_loaded p bild
      c ps es certs src bytes hval himg σ hwelt reg fl ρ hE O passes R σ' r hsrc
    exact ⟨n + 1, s', hrun, hstop, Or.inr ⟨σ', r, hsrc, hrip, hreg, hW⟩⟩

end Schluss

-- BEGIN SEC9
/-! ## 9. Completeness of the image builder

    The constructor `baueBildP` (and so `bildFuer`/`bildFuerP`) of a
    compiled block passes `imageOk` and `weltOk` IN GENERAL, under the
    decided LAYOUT side conditions `bauOk`: code, stubs and table extents
    lie in the low canonical half and pairwise apart, the exit stride is at
    least eleven (a stub of ten bytes plus its stop byte), placements lie
    inside extents and strictly apart, and every placed slot type is
    admitted. `bauOk` reads no loaded memory; everything about the loaded
    image is PROVED from it over the existing loader (`geladen`). -/

section Bau

/-- Two intervals `[a1, a1 + l1)` and `[a2, a2 + l2)` are apart. -/
def apartB (a1 l1 a2 l2 : Nat) : Bool := decide (a1 + l1 ≤ a2 ∨ a2 + l2 ≤ a1)

/-- The low canonical half of a profile. -/
def halbe (p : Profil) : Nat := 2 ^ (p.breite - 1)

theorem halbe_le (p : Profil) : halbe p ≤ 2 ^ 64 := by cases p <;> decide

/-- Placements strictly apart: no two share a byte, none is listed twice. -/
def platzGetrennt (ps : List (Platz D)) : Bool :=
  decide (ps.Pairwise fun p q => p.a + 8 ≤ q.a ∨ q.a + 8 ≤ p.a)

/-- THE LAYOUT SIDE CONDITIONS of the image builder, decided over the
    configuration, the entry sequence, the code, the reason list, the
    placements and the table extents (never over a loaded memory). -/
def bauOk (p : Profil) (c : PipeCfg) (pro bytes : List Byte) (gs : List Nat)
    (ps : List (Platz D)) (es : List TabLayout) : Bool :=
  decide (0 < bytes.length) && decide (pro.length ≤ c.codeBase) &&
  decide (11 ≤ c.exitStride) &&
  decide (c.codeBase + bytes.length + 1 ≤ halbe p) &&
  gs.all (fun g => decide (exitAdr c g + c.exitStride ≤ halbe p) &&
    apartB (exitAdr c g) c.exitStride (c.codeBase - pro.length) (pro.length + bytes.length + 1) &&
    es.all fun e => apartB (exitAdr c g) c.exitStride e.basis e.len) &&
  es.all (fun e => decide (e.basis + e.len ≤ halbe p) &&
    apartB (c.codeBase - pro.length) (pro.length + bytes.length) e.basis e.len) &&
  layoutOk es &&
  ps.all (fun q => es.any fun e => decide (e.basis ≤ q.a ∧ q.a + 8 ≤ e.basis + e.len)) &&
  platzGetrennt ps &&
  ps.all (fun q => repOk (D.typ q.t q.f) q.a 8 0)

/-- The side conditions, unpacked. -/
structure BauFakten (p : Profil) (c : PipeCfg) (pro bytes : List Byte) (gs : List Nat)
    (ps : List (Platz D)) (es : List TabLayout) : Prop where
  lang : 0 < bytes.length
  pro_le : pro.length ≤ c.codeBase
  stride : 11 ≤ c.exitStride
  code_halb : c.codeBase + bytes.length + 1 ≤ halbe p
  stub_halb : ∀ g ∈ gs, exitAdr c g + c.exitStride ≤ halbe p
  stub_code : ∀ g ∈ gs, exitAdr c g + c.exitStride ≤ c.codeBase - pro.length ∨
    c.codeBase - pro.length + (pro.length + bytes.length + 1) ≤ exitAdr c g
  stub_daten : ∀ g ∈ gs, ∀ e ∈ es,
    exitAdr c g + c.exitStride ≤ e.basis ∨ e.basis + e.len ≤ exitAdr c g
  daten_halb : ∀ e ∈ es, e.basis + e.len ≤ halbe p
  daten_code : ∀ e ∈ es, c.codeBase - pro.length + (pro.length + bytes.length) ≤ e.basis ∨
    e.basis + e.len ≤ c.codeBase - pro.length
  layout : layoutOk es = true
  platz_in : ∀ q ∈ ps, ∃ e ∈ es, e.basis ≤ q.a ∧ q.a + 8 ≤ e.basis + e.len
  platz_getrennt : ps.Pairwise fun p q => p.a + 8 ≤ q.a ∨ q.a + 8 ≤ p.a
  platz_rep : ∀ q ∈ ps, repOk (D.typ q.t q.f) q.a 8 0 = true

theorem bauOk_fakten (p : Profil) (c : PipeCfg) (pro bytes : List Byte) (gs : List Nat)
    (ps : List (Platz D)) (es : List TabLayout) (h : bauOk p c pro bytes gs ps es = true) :
    BauFakten p c pro bytes gs ps es := by
  unfold bauOk apartB platzGetrennt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, fun g hg => (h5 g hg).1.1, fun g hg => (h5 g hg).1.2,
    fun g hg => (h5 g hg).2, fun e he => (h6 e he).1, fun e he => (h6 e he).2, h7, h8, h9, h10⟩

/-! ### Generic facts about lists, sections and the loader -/

/-- Two members of a pairwise-related list are equal or related. -/
theorem pairwise_drei {α : Type _} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => by simp at ha
  | x :: r, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (h.1 b hb'))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inr (h.1 a ha'))
      · exact pairwise_drei h.2 ha' hb'

theorem take_drop_mitte (P X Q : List Byte) : ((P ++ X ++ Q).drop P.length).take X.length = X := by
  simp

theorem getD_von_take_drop (l X : List Byte) (o n i : Nat) (d : Byte)
    (h : (l.drop o).take n = X) (hi : i < n) : l.getD (o + i) d = X.getD i d := by
  subst h
  simp [List.getD_eq_getElem?_getD, hi, List.getElem?_drop]

/-- Two sections occupy disjoint virtual ranges (at bias zero). -/
def VGetrennt (s t : Abschnitt) : Prop :=
  s.vaddr + s.memLen ≤ t.vaddr ∨ t.vaddr + t.memLen ≤ s.vaddr

/-- Two sections occupy disjoint file ranges. -/
def FGetrennt (s t : Abschnitt) : Prop :=
  s.dateiOff + s.dateiLen ≤ t.dateiOff ∨ t.dateiOff + t.dateiLen ≤ s.dateiOff

/-- The decided pairwise check from pairwise disjoint intervals. -/
theorem paarweise_von (f : Abschnitt → Nat × Nat) : ∀ (l : List Abschnitt),
    l.Pairwise (fun s t => (f s).2 ≤ (f t).1 ∨ (f t).2 ≤ (f s).1) → paarweise f l = true
  | [], _ => rfl
  | s :: r, h => by
    rw [List.pairwise_cons] at h
    simp only [paarweise, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun t ht => ?_, paarweise_von f r h.2⟩
    have := h.1 t ht
    show disjunktPaar (f s).1 (f s).2 (f t).1 (f t).2 = true
    simp [disjunktPaar, this]

/-- With pairwise disjoint sections, the loader finds THE section that
    holds an address. -/
theorem abteilFinden_eindeutig : ∀ (secs : List Abschnitt), secs.Pairwise VGetrennt →
    ∀ (s : Abschnitt), s ∈ secs → ∀ (a : Nat), s.vaddr ≤ a → a < s.vaddr + s.memLen →
      abteilFinden secs 0 a = some s
  | [], _, s, hs, _, _, _ => by simp at hs
  | t :: r, hp, s, hs, a, h1, h2 => by
    rw [List.pairwise_cons] at hp
    simp only [abteilFinden, Nat.zero_add]
    rcases List.mem_cons.mp hs with rfl | hs'
    · rw [if_pos ⟨h1, h2⟩]
    · have hd := hp.1 s hs'
      have hn : ¬ (t.vaddr ≤ a ∧ a < t.vaddr + t.memLen) := by
        intro hh
        unfold VGetrennt at hd
        omega
      rw [if_neg hn]
      exact abteilFinden_eindeutig r hp.2 s hs' a h1 h2

/-- What the loader finds is a member that holds the address. -/
theorem abteilFinden_mem : ∀ (secs : List Abschnitt) (a : Nat) (s : Abschnitt),
    abteilFinden secs 0 a = some s → s ∈ secs ∧ s.vaddr ≤ a ∧ a < s.vaddr + s.memLen
  | [], _, _, h => by simp [abteilFinden] at h
  | t :: r, a, s, h => by
    simp only [abteilFinden, Nat.zero_add] at h
    by_cases ht : t.vaddr ≤ a ∧ a < t.vaddr + t.memLen
    · rw [if_pos ht] at h
      cases h
      exact ⟨List.mem_cons_self, ht⟩
    · rw [if_neg ht] at h
      obtain ⟨h1, h2⟩ := abteilFinden_mem r a s h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- An address that no executable section holds is not executable. -/
theorem ladenAusfuehrbar_aus (bild : Bild) (a : Nat)
    (h : ∀ s ∈ bild.abschnitte, s.vaddr ≤ a → a < s.vaddr + s.memLen → s.ausfuehrbar = false) :
    ladenAusfuehrbar bild 0 a = false := by
  unfold ladenAusfuehrbar
  cases hf : abteilFinden bild.abschnitte 0 a with
  | none => rfl
  | some s =>
    obtain ⟨hm, h1, h2⟩ := abteilFinden_mem _ a s hf
    exact h s hm h1 h2

theorem natAdresse_toNat_lt (a : Nat) (h : a < 2 ^ 64) : (natAdresse a).toNat = a := by
  unfold natAdresse
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem addrOff_toNat (b i : Nat) (h : b + i < 2 ^ 64) :
    (addrOff (natAdresse b) i).toNat = b + i := by
  rw [addrOff_natAdresse]
  exact natAdresse_toNat_lt _ h

/-- A loaded file-backed byte. -/
theorem ladenByte_in (bild : Bild) (hpw : bild.abschnitte.Pairwise VGetrennt) (s : Abschnitt)
    (hs : s ∈ bild.abschnitte) (hdm : s.dateiLen ≤ s.memLen) (i : Nat) (hi : i < s.dateiLen) :
    ladenByte bild 0 (s.vaddr + i) = bild.datei.getD (s.dateiOff + i) (BitVec.ofNat 8 0) := by
  have hf := abteilFinden_eindeutig _ hpw s hs (s.vaddr + i) (by omega) (by omega)
  unfold ladenByte
  rw [hf]
  simp only [Nat.zero_add]
  rw [if_pos (by omega), show s.vaddr + i - s.vaddr = i by omega]
  rfl

/-- DECIDED CODE FROM A SECTION: bytes that a non-writable executable
    section carries at offset `o` pass `codeAtB` at their address. -/
theorem codeAtB_von (bild : Bild) (hmod : bild.modus = .fest)
    (hpw : bild.abschnitte.Pairwise VGetrennt) (s : Abschnitt) (hs : s ∈ bild.abschnitte)
    (hdm : s.dateiLen ≤ s.memLen) (hx : s.ausfuehrbar = true) (hw : s.schreibbar = false)
    (o : Nat) (flat : List Byte) (hlen : o + flat.length ≤ s.dateiLen)
    (hb : (bild.datei.drop (s.dateiOff + o)).take flat.length = flat)
    (hwrap : s.vaddr + o + flat.length ≤ 2 ^ 64) :
    codeAtB (ladung bild) (natAdresse (s.vaddr + o)) flat = true := by
  unfold codeAtB
  apply List.all_eq_true.mpr
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : (addrOff (natAdresse (s.vaddr + o)) i).toNat = s.vaddr + (o + i) := by
    rw [addrOff_toNat _ _ (by omega)]
    omega
  have hf := abteilFinden_eindeutig _ hpw s hs (s.vaddr + (o + i)) (by omega) (by omega)
  have hbyte := ladenByte_in bild hpw s hs hdm (o + i) (by omega)
  have hget := getD_von_take_drop bild.datei flat (s.dateiOff + o) flat.length i
    (BitVec.ofNat 8 0) hb hi'
  simp only [ladung, hmod, effBias, geladen, ha, ladenAusfuehrbar, ladenSchreibbar, hf, hx, hw,
    hbyte, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  rw [← Nat.add_assoc, hget]
  rfl

/-! ### The sections of the built image -/

/-- Every stub section is the stub of a listed reason. -/
theorem stub_mem_v (c : PipeCfg) : ∀ (gs : List Nat) (off : Nat) (t : Abschnitt),
    t ∈ stubAbschnitte c off gs → ∃ g ∈ gs, t.vaddr = exitAdr c g ∧ t.memLen = 10 ∧
      t.dateiLen = 10 ∧ t.lesbar = true ∧ t.schreibbar = false ∧ t.ausfuehrbar = true ∧
      t.ausr = 1
  | [], _, t, ht => by simp [stubAbschnitte] at ht
  | g :: gs, off, t, ht => by
    simp only [stubAbschnitte] at ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨g, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨g', hg', h⟩ := stub_mem_v c gs (off + 10) t ht'
      exact ⟨g', List.mem_cons_of_mem _ hg', h⟩

/-- Every listed reason has its stub section, carrying its stub bytes. -/
theorem stub_vorhanden (c : PipeCfg) : ∀ (gs : List Nat) (P Q : List Byte) (g : Nat), g ∈ gs →
    ∃ t ∈ stubAbschnitte c P.length gs, t.vaddr = exitAdr c g ∧ t.memLen = 10 ∧
      t.dateiLen = 10 ∧ t.schreibbar = false ∧ t.ausfuehrbar = true ∧
      ((P ++ (gs.map stubBytes).flatten ++ Q).drop t.dateiOff).take 10 = stubBytes g
  | [], _, _, g, hg => by simp at hg
  | x :: gs, P, Q, g, hg => by
    by_cases hx : g = x
    · subst hx
      refine ⟨_, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, ?_⟩
      have := take_drop_mitte P (stubBytes g) ((gs.map stubBytes).flatten ++ Q)
      simpa [List.append_assoc, stubBytes_length] using this
    · have hg' : g ∈ gs := by
        rcases List.mem_cons.mp hg with h | h
        · exact absurd h hx
        · exact h
      obtain ⟨t, ht, h⟩ := stub_vorhanden c gs (P ++ stubBytes x) Q g hg'
      have hl : (P ++ stubBytes x).length = P.length + 10 := by simp [stubBytes_length]
      rw [hl] at ht
      refine ⟨t, ?_, ?_⟩
      · simp only [stubAbschnitte]
        exact List.mem_cons_of_mem _ ht
      · simpa [List.append_assoc] using h

/-- The file bytes a stub section owns are a stub's bytes. -/
theorem stub_bytes (c : PipeCfg) : ∀ (gs : List Nat) (P Q : List Byte) (t : Abschnitt),
    t ∈ stubAbschnitte c P.length gs → ∃ g ∈ gs,
      ((P ++ (gs.map stubBytes).flatten ++ Q).drop t.dateiOff).take 10 = stubBytes g
  | [], _, _, t, ht => by simp [stubAbschnitte] at ht
  | x :: gs, P, Q, t, ht => by
    simp only [stubAbschnitte] at ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · refine ⟨x, List.mem_cons_self, ?_⟩
      have := take_drop_mitte P (stubBytes x) ((gs.map stubBytes).flatten ++ Q)
      simpa [List.append_assoc, stubBytes_length] using this
    · have hl : P.length + 10 = (P ++ stubBytes x).length := by simp [stubBytes_length]
      rw [hl] at ht'
      obtain ⟨g', hg', h⟩ := stub_bytes c gs (P ++ stubBytes x) Q t ht'
      exact ⟨g', List.mem_cons_of_mem _ hg', by simpa [List.append_assoc] using h⟩

/-- Every data section is the section of a listed extent. -/
theorem daten_mem_v : ∀ (es : List TabLayout) (off : Nat) (t : Abschnitt),
    t ∈ datenAbschnitte off es → ∃ e ∈ es, t.vaddr = e.basis ∧ t.memLen = e.len ∧
      t.dateiLen = e.len ∧ t.lesbar = true ∧ t.schreibbar = true ∧ t.ausfuehrbar = false ∧
      t.ausr = e.ausr
  | [], _, t, ht => by simp [datenAbschnitte] at ht
  | e :: es, off, t, ht => by
    simp only [datenAbschnitte] at ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨e, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨e', he', h⟩ := daten_mem_v es (off + e.len) t ht'
      exact ⟨e', List.mem_cons_of_mem _ he', h⟩

theorem datenChunk_length (ps : List (Platz D)) (σ : World D) (e : TabLayout) :
    (datenChunk ps σ e).length = e.len := by
  simp [datenChunk]

/-- Every listed extent has its data section, carrying its world bytes. -/
theorem daten_vorhanden (ps : List (Platz D)) (σ : World D) : ∀ (es : List TabLayout)
    (P : List Byte) (e : TabLayout), e ∈ es →
    ∃ t ∈ datenAbschnitte P.length es, t.vaddr = e.basis ∧ t.memLen = e.len ∧
      t.dateiLen = e.len ∧ t.lesbar = true ∧ t.schreibbar = true ∧
      ((P ++ datenDatei ps σ es).drop t.dateiOff).take e.len = datenChunk ps σ e
  | [], _, e, he => by simp at he
  | x :: es, P, e, he => by
    by_cases hx : e = x
    · subst hx
      refine ⟨_, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, ?_⟩
      have := take_drop_mitte P (datenChunk ps σ e) (datenDatei ps σ es)
      rw [datenChunk_length] at this
      simpa [datenDatei, List.append_assoc] using this
    · have he' : e ∈ es := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h hx
        · exact h
      obtain ⟨t, ht, h⟩ := daten_vorhanden ps σ es (P ++ datenChunk ps σ x) e he'
      have hl : (P ++ datenChunk ps σ x).length = P.length + x.len := by
        simp [datenChunk_length]
      rw [hl] at ht
      refine ⟨t, ?_, ?_⟩
      · simp only [datenAbschnitte]
        exact List.mem_cons_of_mem _ ht
      · simpa [datenDatei, List.append_assoc] using h

/-! ### File positions: a contiguous chain -/

/-- Sections laid out contiguously in the file from `a` to `b`. -/
def KetteE : Nat → List Abschnitt → Nat → Prop
  | a, [], b => a = b
  | a, s :: r, b => s.dateiOff = a ∧ KetteE (a + s.dateiLen) r b

theorem ketteE_append : ∀ (A B : List Abschnitt) (a b e : Nat), KetteE a A b → KetteE b B e →
    KetteE a (A ++ B) e
  | [], B, a, b, e, hA, hB => by
    simp only [KetteE] at hA
    subst hA
    exact hB
  | s :: r, B, a, b, e, hA, hB => ⟨hA.1, ketteE_append r B _ b e hA.2 hB⟩

theorem ketteE_le : ∀ (l : List Abschnitt) (a b : Nat), KetteE a l b → a ≤ b
  | [], a, b, h => by simp only [KetteE] at h; omega
  | s :: r, a, b, h => by have := ketteE_le r _ b h.2; omega

theorem ketteE_mem : ∀ (l : List Abschnitt) (a b : Nat), KetteE a l b →
    ∀ t ∈ l, a ≤ t.dateiOff ∧ t.dateiOff + t.dateiLen ≤ b
  | [], _, _, _, t, ht => by simp at ht
  | s :: r, a, b, h, t, ht => by
    have h1 := h.1
    rcases List.mem_cons.mp ht with rfl | ht'
    · have := ketteE_le r _ b h.2
      omega
    · have := ketteE_mem r _ b h.2 t ht'
      omega

theorem ketteE_pairwise : ∀ (l : List Abschnitt) (a b : Nat), KetteE a l b →
    l.Pairwise FGetrennt
  | [], _, _, _ => List.Pairwise.nil
  | s :: r, a, b, h => by
    refine List.pairwise_cons.mpr ⟨fun t ht => ?_, ketteE_pairwise r _ b h.2⟩
    have := ketteE_mem r _ b h.2 t ht
    have h1 := h.1
    unfold FGetrennt
    omega

theorem ketteE_stubs (c : PipeCfg) : ∀ (gs : List Nat) (off : Nat),
    KetteE off (stubAbschnitte c off gs) (off + 10 * gs.length)
  | [], off => by simp [stubAbschnitte, KetteE]
  | g :: gs, off => by
    refine ⟨rfl, ?_⟩
    have := ketteE_stubs c gs (off + 10)
    simp only [List.length_cons]
    rw [show off + 10 * (gs.length + 1) = off + 10 + 10 * gs.length by omega]
    exact this

theorem ketteE_daten (ps : List (Platz D)) (σ : World D) : ∀ (es : List TabLayout) (off : Nat),
    KetteE off (datenAbschnitte off es) (off + (datenDatei ps σ es).length)
  | [], off => by simp [datenAbschnitte, datenDatei, KetteE]
  | e :: es, off => by
    refine ⟨rfl, ?_⟩
    have := ketteE_daten ps σ es (off + e.len)
    have hl : (datenDatei ps σ (e :: es)).length = e.len + (datenDatei ps σ es).length := by
      simp [datenDatei, datenChunk_length]
    rw [hl, ← Nat.add_assoc]
    exact this

theorem stubs_flatten_length : ∀ (gs : List Nat), ((gs.map stubBytes).flatten).length = 10 * gs.length
  | [] => rfl
  | g :: gs => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, stubBytes_length,
      stubs_flatten_length gs, List.length_cons]
    omega

/-! ### Decode coverage of canonical code -/

/-- The fuel traversal decodes a canonical program completely. -/
theorem decodeFuel_encodeAll : ∀ (P : List Befehl) (k : Nat), P.length ≤ k →
    decodeFuel (k + 1) (encodeAll P) = some (P.map kanon, [])
  | [], k, _ => rfl
  | b :: P, k, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    obtain ⟨x, xs, hx⟩ : ∃ x xs, encode b ++ encodeAll P = x :: xs := by
      cases hc : encode b ++ encodeAll P with
      | nil =>
        have := congrArg List.length hc
        simp only [List.length_append, List.length_nil] at this
        have := (encode_len b).1
        omega
      | cons x xs => exact ⟨x, xs, rfl⟩
    rw [encodeAll_cons, hx, decodeFuel_cons_eq, ← hx, roundtrip b (encodeAll P)]
    have hlen : ((encode b).length + (encodeAll P).length == (encode b ++ encodeAll P).length &&
        laengeOk (encode b).length) = true := by
      simp [laengeOk_encode]
    simp only [hlen, if_true]
    rw [decodeFuel_encodeAll P k' (by simp at h; omega)]
    rfl

theorem validAllFuel_encodeAll (P : List Befehl) (k : Nat) (h : P.length ≤ k) :
    validAllFuel (k + 1) (encodeAll P) = true := by
  unfold validAllFuel
  rw [decodeFuel_encodeAll P k h]

/-! ### The loaded image of the builder -/

/-! ### Separation of the stub and data sections -/

theorem stubs_pairwise (c : PipeCfg) (hst : 10 ≤ c.exitStride) : ∀ (gs : List Nat) (off : Nat),
    gs.Nodup → (stubAbschnitte c off gs).Pairwise VGetrennt
  | [], _, _ => List.Pairwise.nil
  | g :: gs, off, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [stubAbschnitte]
    refine List.pairwise_cons.mpr ⟨fun t ht => ?_, stubs_pairwise c hst gs (off + 10) hnd.2⟩
    obtain ⟨g', hg', hv, hm, -⟩ := stub_mem_v c gs (off + 10) t ht
    have hne : g ≠ g' := fun h => hnd.1 (h ▸ hg')
    unfold VGetrennt
    rw [hv, hm]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := exitAdr_abstand c g g' h
      exact Or.inl (by simp only; omega)
    · have := exitAdr_abstand c g' g h
      exact Or.inr (by simp only; omega)

theorem daten_pairwise : ∀ (es : List TabLayout) (off : Nat), paarOk es = true →
    (datenAbschnitte off es).Pairwise VGetrennt
  | [], _, _ => List.Pairwise.nil
  | e :: es, off, h => by
    simp only [paarOk, Bool.and_eq_true, List.all_eq_true] at h
    simp only [datenAbschnitte]
    refine List.pairwise_cons.mpr ⟨fun t ht => ?_, daten_pairwise es (off + e.len) h.2⟩
    obtain ⟨e', he', hv, hm, -⟩ := daten_mem_v es (off + e.len) t ht
    have := h.1 e' he'
    unfold regionDisjunkt alsRegion at this
    simp only [decide_eq_true_eq] at this
    unfold VGetrennt
    rw [hv, hm]
    exact this

theorem datenChunk_getD (ps : List (Platz D)) (σ : World D) (e : TabLayout) (i : Nat)
    (hi : i < e.len) : (datenChunk ps σ e).getD i (BitVec.ofNat 8 0) = slotByte ps σ (e.basis + i) := by
  simp [datenChunk, List.getD_eq_getElem?_getD, hi]

/-! ### Words from bytes -/

theorem lesbar8_von (m : Speicher) (a : Adresse)
    (h : ∀ k, k < 8 → m.lesbar (addrOff a k) = true) : lesbar8 m a = true := by
  unfold lesbar8
  simp [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem schreibbar8_von (m : Speicher) (a : Adresse)
    (h : ∀ k, k < 8 → m.schreibbar (addrOff a k) = true) : schreibbar8 m a = true := by
  unfold schreibbar8
  simp [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem read64_von (m : Speicher) (a : Adresse) (w : Wort) (hl : lesbar8 m a = true)
    (hb : ∀ k, k < 8 → m.bytes (addrOff a k) = wortByte w k) : read64 m a = some w := by
  unfold read64
  rw [if_pos hl]
  have : readBytes m a = fun i => wortByte w i.val := by
    funext i
    exact hb i.val i.isLt
  rw [this, bytesWort_wortByte]

/-- The initial-world byte inside a placement is that placement's word
    byte (placements strictly apart). -/
theorem slotByte_von (ps : List (Platz D)) (σ : World D)
    (hsep : ps.Pairwise fun p q => p.a + 8 ≤ q.a ∨ q.a + 8 ≤ p.a)
    (p : Platz D) (hp : p ∈ ps) (k : Nat) (hk : k < 8) :
    slotByte ps σ (p.a + k) = wortByte (slotWort _ (σ.slots p.t p.k p.f)) k := by
  unfold slotByte
  cases hf : ps.find? (fun q => decide (q.a ≤ p.a + k ∧ p.a + k < q.a + 8)) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    simp only [decide_eq_true_eq] at this
    omega
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hpr := List.find?_some hf
    simp only [decide_eq_true_eq] at hpr
    rcases pairwise_drei hsep hq hp with rfl | h | h
    · simp
    · omega
    · omega

section Geladen
variable (p : Profil) (c : PipeCfg) (proP prog : List Befehl) (gs : List Nat)
  (ps : List (Platz D)) (σ : World D) (es : List TabLayout)

/-- Every section of the built image is the code section, a stub section
    or a data section. -/
theorem baueBildP_sek (s : Abschnitt)
    (hs : s ∈ (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte) :
    s = codeAbschnittP c (encodeAll proP) (encodeAll prog) ∨
    (∃ g ∈ gs, s.vaddr = exitAdr c g ∧ s.memLen = 10 ∧ s.dateiLen = 10 ∧ s.lesbar = true ∧
      s.schreibbar = false ∧ s.ausfuehrbar = true ∧ s.ausr = 1) ∨
    (∃ e ∈ es, s.vaddr = e.basis ∧ s.memLen = e.len ∧ s.dateiLen = e.len ∧ s.lesbar = true ∧
      s.schreibbar = true ∧ s.ausfuehrbar = false ∧ s.ausr = e.ausr) := by
  simp only [baueBildP, List.mem_cons, List.mem_append] at hs
  rcases hs with (rfl | hs) | hs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (stub_mem_v c gs _ s hs))
  · exact Or.inr (Or.inr (daten_mem_v es _ s hs))

/-- The file layout of the built image is one contiguous chain. -/
theorem baueBildP_kette :
    KetteE 0 (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte
      (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).datei.length := by
  simp only [baueBildP]
  have h1 := ketteE_stubs c gs ((encodeAll proP).length + (encodeAll prog).length)
  have h2 := ketteE_daten ps σ es
    ((encodeAll proP).length + (encodeAll prog).length + 10 * gs.length)
  have h12 := ketteE_append _ _ _ _ _ h1 h2
  refine ⟨rfl, ?_⟩
  simp only [codeAbschnittP, Nat.zero_add, List.length_append, stubs_flatten_length] at h12 ⊢
  exact h12


/-- Every section of the built image lies in the low canonical half. -/
theorem baueBildP_halb (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es) (s : Abschnitt)
    (hs : s ∈ (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte) :
    s.vaddr + s.memLen ≤ halbe p := by
  have h1 := F.pro_le
  have h2 := F.code_halb
  have h3 := F.stride
  rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g, hg, hv, hm, -⟩ | ⟨e, he, hv, hm, -⟩
  · simp only [codeAbschnittP]
    omega
  · have := F.stub_halb g hg
    rw [hv, hm]
    omega
  · have := F.daten_halb e he
    rw [hv, hm]
    exact this

/-- The sections of the built image are pairwise apart in memory. -/
theorem baueBildP_pairwise (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) :
    (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte.Pairwise VGetrennt := by
  have hst := F.stride
  have hlay := F.layout
  unfold layoutOk at hlay
  simp only [Bool.and_eq_true] at hlay
  simp only [baueBildP]
  refine List.pairwise_cons.mpr ⟨fun t ht => ?_, List.pairwise_append.mpr
    ⟨stubs_pairwise c (by omega) gs _ hnd, daten_pairwise es _ hlay.2, ?_⟩⟩
  · rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨g, hg, hv, hm, -⟩ := stub_mem_v c gs _ t ht
      have := F.stub_code g hg
      unfold VGetrennt
      rw [hv, hm]
      simp only [codeAbschnittP]
      omega
    · obtain ⟨e, he, hv, hm, -⟩ := daten_mem_v es _ t ht
      have := F.daten_code e he
      unfold VGetrennt
      rw [hv, hm]
      simp only [codeAbschnittP]
      omega
  · intro a ha b hb
    obtain ⟨g, hg, hv, hm, -⟩ := stub_mem_v c gs _ a ha
    obtain ⟨e, he, hv', hm', -⟩ := daten_mem_v es _ b hb
    have := F.stub_daten g hg e he
    unfold VGetrennt
    rw [hv, hm, hv', hm']
    omega

/-- THE BUILT IMAGE IS WELL-FORMED (`Bild.wohlgeformt`): every mapping
    check of the existing image validator, proved from `bauOk`. -/
theorem baueBildP_wohlgeformt (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) :
    wohlgeformt p (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es) = true := by
  have hpw := baueBildP_pairwise p c proP prog gs ps σ es F hnd
  have hk := baueBildP_kette c proP prog gs ps σ es
  have hlay := F.layout
  unfold layoutOk at hlay
  simp only [Bool.and_eq_true, List.all_eq_true] at hlay
  have hhl := halbe_le p
  have hlen := F.lang
  have hpro := F.pro_le
  unfold wohlgeformt
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, rfl⟩
  · intro s hs
    unfold groesseOk
    rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g, -, -, hm, hd, -⟩ |
      ⟨e, -, -, hm, hd, -⟩
    · simp [codeAbschnittP]
    · simp [hm, hd]
    · simp [hm, hd]
  · intro s hs
    unfold dateiOk
    have := (ketteE_mem _ _ _ hk s hs).2
    simp only [decide_eq_true_eq]
    exact this
  · intro s hs
    have := baueBildP_halb p c proP prog gs ps σ es F s hs
    unfold virtuellOk
    apply decide_eq_true
    show 0 + s.vaddr + s.memLen ≤ 2 ^ 64
    omega
  · intro s hs
    have := baueBildP_halb p c proP prog gs ps σ es F s hs
    unfold kanonischBereich
    apply decide_eq_true
    left
    show 0 + s.vaddr + s.memLen ≤ 2 ^ (p.breite - 1)
    unfold halbe at this
    omega
  · intro s hs
    simp only [ausrOk, baueBildP, effBias, decide_eq_true_eq, Nat.zero_add]
    rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g, -, -, -, -, -, -, -, ha⟩ |
      ⟨e, he, hv, -, -, -, -, -, ha⟩
    · simp [codeAbschnittP, Nat.mod_one]
    · simp [ha, Nat.mod_one]
    · have := hlay.1 e he
      unfold eintragOk at this
      simp only [decide_eq_true_eq] at this
      rw [ha, hv]
      exact ⟨this.2.1, this.2.2.1⟩
  · intro s hs
    unfold wxOk
    rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g, -, -, -, -, -, hw, hx, -⟩ |
      ⟨e, -, -, -, -, -, hw, hx, -⟩
    · simp [codeAbschnittP]
    · simp [hw, hx]
    · simp [hw, hx]
  · apply paarweise_von
    exact (ketteE_pairwise _ _ _ hk).imp fun h => by simpa [fileReich, FGetrennt] using h
  · apply paarweise_von
    refine hpw.imp fun {s t} h => ?_
    simp only [virtReich, baueBildP, effBias, Nat.zero_add]
    unfold VGetrennt at h
    omega
  · intro x hx
    simp only [baueBildP, List.mem_cons, List.mem_nil_iff, or_false] at hx
    unfold eintragEnthalten
    apply List.any_eq_true.mpr
    refine ⟨codeAbschnittP c (encodeAll proP) (encodeAll prog), List.mem_cons_self, ?_⟩
    simp only [inAbschnitt, codeAbschnittP, Bool.and_eq_true, decide_eq_true_eq, baueBildP,
      effBias, Nat.zero_add, and_true]
    rcases hx with rfl | rfl <;> omega
  · intro r hr
    simp [baueBildP] at hr

/-- THE BUILT IMAGE IS COVERED BY THE DECODER (`bildDeckung`): the code
    section is the canonical encoding of the entry sequence and the
    program, every stub section the encoding of its `mov`. -/
theorem baueBildP_deckung :
    bildDeckung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es) = true := by
  unfold bildDeckung
  apply List.all_eq_true.mpr
  intro s hs
  have hs' := hs
  simp only [baueBildP, List.mem_cons, List.mem_append] at hs'
  rcases hs' with (rfl | ht) | ht
  · unfold abschnittDeckung abschnittBytes
    simp only [codeAbschnittP, if_true, baueBildP, List.drop_zero]
    have hx : (encodeAll proP).length + (encodeAll prog).length =
        (encodeAll proP ++ encodeAll prog).length := by simp
    have hd : encodeAll proP ++ encodeAll prog ++ (gs.map stubBytes).flatten ++ datenDatei ps σ es =
        (encodeAll proP ++ encodeAll prog) ++ ((gs.map stubBytes).flatten ++ datenDatei ps σ es) := by
      simp [List.append_assoc]
    rw [hx, hd, List.take_left', ← encodeAll_append]
    · exact validAllFuel_encodeAll _ _ (length_le_encodeAll _)
    · rfl
  · obtain ⟨g, -, -, -, hd, -, -, hx, -⟩ := stub_mem_v c gs _ s ht
    have hl : (encodeAll proP).length + (encodeAll prog).length =
        (encodeAll proP ++ encodeAll prog).length := by simp
    rw [hl] at ht
    obtain ⟨g', -, hb⟩ := stub_bytes c gs (encodeAll proP ++ encodeAll prog)
      (datenDatei ps σ es) s ht
    unfold abschnittDeckung abschnittBytes
    rw [hx, if_pos rfl, hd]
    show validAllFuel (10 + 1) _ = true
    simp only [baueBildP]
    rw [hb]
    have : stubBytes g' = encodeAll [stubBefehl g'] := by simp [stubBytes, encodeAll]
    rw [this]
    exact validAllFuel_encodeAll _ _ (by simp)
  · obtain ⟨e, -, -, -, -, -, -, hx, -⟩ := daten_mem_v es _ s ht
    unfold abschnittDeckung
    rw [hx]
    rfl

/-- The built image passes the existing skeleton validator `valX86`. -/
theorem baueBildP_valX86 (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) :
    valX86 p (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es) = true := by
  unfold valX86
  rw [baueBildP_wohlgeformt p c proP prog gs ps σ es F hnd, baueBildP_deckung]
  rfl

/-- LOADED CODE AND ENTRY SEQUENCE: the loaded built image holds the
    program bytes at `codeBase` and the entry sequence right before them,
    executable and not writable. -/
theorem baueBildP_code (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) :
    codeAtB (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es))
        (natAdresse c.codeBase) (encodeAll prog) = true ∧
      codeAtB (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es))
        (natAdresse (c.codeBase - (encodeAll proP).length)) (encodeAll proP) = true := by
  have hpw := baueBildP_pairwise p c proP prog gs ps σ es F hnd
  have hpro := F.pro_le
  have hh := F.code_halb
  have hhl := halbe_le p
  have hmem : codeAbschnittP c (encodeAll proP) (encodeAll prog) ∈
      (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte :=
    List.mem_cons_self
  constructor
  · have h := codeAtB_von _ rfl hpw _ hmem (by simp [codeAbschnittP]) rfl rfl
      (encodeAll proP).length (encodeAll prog) (by simp [codeAbschnittP])
      (by simp [baueBildP, codeAbschnittP, List.append_assoc])
      (by simp only [codeAbschnittP]; omega)
    simp only [codeAbschnittP] at h
    rwa [Nat.sub_add_cancel hpro] at h
  · have h := codeAtB_von _ rfl hpw _ hmem (by simp [codeAbschnittP]) rfl rfl
      0 (encodeAll proP) (by simp [codeAbschnittP])
      (by simp [baueBildP, codeAbschnittP, List.append_assoc])
      (by simp only [codeAbschnittP]; omega)
    simpa [codeAbschnittP] using h

/-- THE NORMAL STOP: the byte after the code is not executable. -/
theorem baueBildP_stop (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es) :
    (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es)).ausfuehrbar
      (natAdresse (c.codeBase + (encodeAll prog).length)) = false := by
  have hpro := F.pro_le
  have hh := F.code_halb
  have hhl := halbe_le p
  have hst := F.stride
  show ladenAusfuehrbar _ 0 _ = false
  rw [natAdresse_toNat_lt _ (by omega)]
  apply ladenAusfuehrbar_aus
  intro s hs h1 h2
  rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g, hg, hv, hm, -⟩ |
    ⟨e, -, -, -, -, -, -, hx, -⟩
  · simp only [codeAbschnittP] at h1 h2
    omega
  · have := F.stub_code g hg
    rw [hv] at h1
    rw [hv, hm] at h2
    omega
  · exact hx

/-- LOADED STUBS: for every listed reason the loaded image holds its stub
    at its exit, executable and not writable, and the byte after the stub
    is not executable. -/
theorem baueBildP_stubs (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) (g : Nat) (hg : g ∈ gs) :
    codeAtB (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es))
        (natAdresse (exitAdr c g)) (stubBytes g) = true ∧
      (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es)).ausfuehrbar
        (natAdresse (exitAdr c g + 10)) = false := by
  have hpw := baueBildP_pairwise p c proP prog gs ps σ es F hnd
  have hst := F.stride
  have hhl := halbe_le p
  have hgh := F.stub_halb g hg
  obtain ⟨t, ht, hv, hm, hd, hw, hx, hb⟩ := stub_vorhanden c gs
    (encodeAll proP ++ encodeAll prog) (datenDatei ps σ es) g hg
  have hmem : t ∈ (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte := by
    simp only [baueBildP]
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    simpa using ht
  constructor
  · have h := codeAtB_von _ rfl hpw t hmem (by omega) hx hw 0 (stubBytes g)
      (by rw [stubBytes_length]; omega) (by simpa [baueBildP, stubBytes_length] using hb)
      (by rw [stubBytes_length, hv]; omega)
    rwa [hv, Nat.add_zero] at h
  · show ladenAusfuehrbar _ 0 _ = false
    rw [natAdresse_toNat_lt _ (by omega)]
    apply ladenAusfuehrbar_aus
    intro s hs h1 h2
    have hpro := F.pro_le
    rcases baueBildP_sek c proP prog gs ps σ es s hs with rfl | ⟨g', hg', hv', hm', -⟩ |
      ⟨e, -, -, -, -, -, -, hx', -⟩
    · have := F.stub_code g hg
      simp only [codeAbschnittP] at h1 h2
      omega
    · rw [hv'] at h1
      rw [hv', hm'] at h2
      by_cases he : g' = g
      · subst he
        omega
      · rcases Nat.lt_or_gt_of_ne he with hlt | hlt
        · have := exitAdr_abstand c g' g hlt
          omega
        · have := exitAdr_abstand c g g' hlt
          omega
    · exact hx'

/-- LOADED PLACEMENTS AND WORLD: every placement is admitted, readable and
    writable in the loaded image, and reads back the representation word
    of the initial world the image was built from. -/
theorem baueBildP_welt (F : BauFakten p c (encodeAll proP) (encodeAll prog) gs ps es)
    (hnd : gs.Nodup) :
    platzOkB (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es)) ps = true ∧
      weltB (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es)) ps σ = true := by
  have hpw := baueBildP_pairwise p c proP prog gs ps σ es F hnd
  have hhl := halbe_le p
  -- every placed byte lies in the data section of its extent
  have hplatz : ∀ q ∈ ps, ∀ k, k < 8 →
      ∃ t ∈ (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte,
        abteilFinden (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte 0
          (q.a + k) = some t ∧ t.lesbar = true ∧ t.schreibbar = true ∧
        ladenByte (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es) 0 (q.a + k) =
          slotByte ps σ (q.a + k) ∧ q.a + k < 2 ^ 64 := by
    intro q hq k hk
    obtain ⟨e, he, hlo, hhi⟩ := F.platz_in q hq
    have heh := F.daten_halb e he
    obtain ⟨t, ht, hv, hm, hd, hl, hw, hb⟩ := daten_vorhanden ps σ es
      (encodeAll proP ++ encodeAll prog ++ (gs.map stubBytes).flatten) e he
    have hoff : (encodeAll proP ++ encodeAll prog ++ (gs.map stubBytes).flatten).length =
        (encodeAll proP).length + (encodeAll prog).length + 10 * gs.length := by
      rw [List.length_append, List.length_append, stubs_flatten_length]
    rw [hoff] at ht
    have hmem : t ∈ (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).abschnitte := by
      simp only [baueBildP]
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact ht
    have hf := abteilFinden_eindeutig _ hpw t hmem (q.a + k) (by omega) (by omega)
    refine ⟨t, hmem, hf, hl, hw, ?_, by omega⟩
    have hbyte := ladenByte_in _ hpw t hmem (by omega) (q.a + k - e.basis) (by omega)
    rw [show t.vaddr + (q.a + k - e.basis) = q.a + k by omega] at hbyte
    rw [hbyte]
    have hget := getD_von_take_drop _ (datenChunk ps σ e) t.dateiOff e.len (q.a + k - e.basis)
      (BitVec.ofNat 8 0)
      (show ((baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es).datei.drop t.dateiOff).take
        e.len = datenChunk ps σ e from hb) (by omega)
    rw [hget, datenChunk_getD ps σ e _ (by omega), show e.basis + (q.a + k - e.basis) = q.a + k by omega]
  have hadr : ∀ q ∈ ps, ∀ k, k < 8 → (addrOff (natAdresse q.a) k).toNat = q.a + k := by
    intro q hq k hk
    obtain ⟨-, -, -, -, -, -, hlt⟩ := hplatz q hq k hk
    exact addrOff_toNat _ _ hlt
  have hles : ∀ q ∈ ps, lesbar8 (ladung (baueBildP c (encodeAll proP) (encodeAll prog) gs ps σ es))
      (natAdresse q.a) = true := by
    intro q hq
    apply lesbar8_von
    intro k hk
    obtain ⟨t, -, hf, hl, -⟩ := hplatz q hq k hk
    show ladenLesbar _ 0 _ = true
    rw [hadr q hq k hk]
    unfold ladenLesbar
    rw [hf]
    exact hl
  constructor
  · unfold platzOkB
    apply List.all_eq_true.mpr
    intro q hq
    simp only [Bool.and_eq_true]
    refine ⟨⟨F.platz_rep q hq, hles q hq⟩, ?_⟩
    apply schreibbar8_von
    intro k hk
    obtain ⟨t, -, hf, -, hw, -⟩ := hplatz q hq k hk
    show ladenSchreibbar _ 0 _ = true
    rw [hadr q hq k hk]
    unfold ladenSchreibbar
    rw [hf]
    exact hw
  · unfold weltB
    apply List.all_eq_true.mpr
    intro q hq
    apply decide_eq_true
    apply read64_von _ _ _ (hles q hq)
    intro k hk
    obtain ⟨-, -, -, -, -, hbyte, -⟩ := hplatz q hq k hk
    show ladenByte _ 0 _ = _
    rw [hadr q hq k hk, hbyte, slotByte_von ps σ F.platz_getrennt q hq k hk]
end Geladen

end Bau

section BauSchluss
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem gleicherSchluessel_selbst (q : Platz D) : gleicherSchluessel q q = true := by
  unfold gleicherSchluessel
  rw [dif_pos rfl]
  simp

/-- Strictly separated placements pass the decided separation `sepB`. -/
theorem sepB_von (ps : List (Platz D))
    (h : ps.Pairwise fun p q => p.a + 8 ≤ q.a ∨ q.a + 8 ≤ p.a) : sepB ps = true := by
  unfold sepB
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro r hr
  rcases pairwise_drei h hq hr with rfl | h' | h'
  · simp [gleicherSchluessel_selbst]
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr h'
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr (Or.comm.mp h')

/-- **COMPLETENESS OF THE IMAGE BUILDER.** For every block, certificates,
    entry sequence `proP` and lowered program `prog`, the image
    `bildFuerP` built from them passes the image check `imageOk` and the
    initial-world check `weltOk` for the world it was built from, and holds
    the entry sequence in front of the code -- whenever the decided layout
    side conditions `bauOk` hold. Proved in general over the existing
    loader; no computation for a particular program. -/
theorem bildFuerP_ok (p : Profil) (c : PipeCfg) (proP prog : List Befehl) (ps : List (Platz D))
    (σ : World D) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ')
    (h : bauOk p c (encodeAll proP) (encodeAll prog) (ohneDoppel (grundListe (optimise certs src)))
      ps es = true) :
    imageOk p (bildFuerP c (encodeAll proP) certs src (encodeAll prog) ps σ es) c ps es certs src
        (encodeAll prog) = true ∧
      weltOk (bildFuerP c (encodeAll proP) certs src (encodeAll prog) ps σ es) ps σ = true ∧
      codeAtB (ladung (bildFuerP c (encodeAll proP) certs src (encodeAll prog) ps σ es))
        (natAdresse (c.codeBase - (encodeAll proP).length)) (encodeAll proP) = true := by
  have F := bauOk_fakten p c _ _ _ ps es h
  have hnd := ohneDoppel_nodup (grundListe (optimise certs src))
  have hmem : ∀ g, g ∈ grundListe (optimise certs src) →
      g ∈ ohneDoppel (grundListe (optimise certs src)) :=
    fun g hg => (mem_ohneDoppel _ g).mpr hg
  have hcode := baueBildP_code p c proP prog _ ps σ es F hnd
  have hwelt := baueBildP_welt p c proP prog _ ps σ es F hnd
  have hpro := F.pro_le
  have hst := F.stride
  refine ⟨?_, hwelt.2, hcode.2⟩
  unfold imageOk
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨baueBildP_valX86 p c proP prog _ ps σ es F hnd, F.layout⟩, ?_⟩, ?_⟩, hcode.1⟩,
    ?_⟩, ?_⟩, sepB_von ps F.platz_getrennt⟩, hwelt.1⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨e, he, h1, h2⟩ := F.platz_in q hq
    exact List.any_eq_true.mpr ⟨e, he, decide_eq_true ⟨h1, h2⟩⟩
  · apply List.all_eq_true.mpr
    intro e he
    simp only [Bool.and_eq_true]
    refine ⟨?_, List.all_eq_true.mpr fun g hg => ?_⟩
    · have := F.daten_code e he
      unfold regionDisjunkt codeRegion alsRegion
      apply decide_eq_true
      simp only
      omega
    · have := F.stub_daten g (hmem g hg) e he
      unfold regionDisjunkt stubRegion alsRegion
      apply decide_eq_true
      simp only
      omega
  · simp only [Bool.not_eq_true']
    exact baueBildP_stop p c proP prog _ ps σ es F
  · apply List.all_eq_true.mpr
    intro g hg
    have := baueBildP_stubs p c proP prog _ ps σ es F hnd g (hmem g hg)
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact this
  · simp [bildFuerP, baueBildP]

/-- The same for the image without an entry sequence (`bildFuer`). -/
theorem bildFuer_ok (p : Profil) (c : PipeCfg) (prog : List Befehl) (ps : List (Platz D))
    (σ : World D) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ')
    (h : bauOk p c [] (encodeAll prog) (ohneDoppel (grundListe (optimise certs src))) ps es = true) :
    imageOk p (bildFuer c certs src (encodeAll prog) ps σ es) c ps es certs src
        (encodeAll prog) = true ∧
      weltOk (bildFuer c certs src (encodeAll prog) ps σ es) ps σ = true :=
  have h' := bildFuerP_ok p c [] prog ps σ es certs src h
  ⟨h'.1, h'.2.1⟩

/-- A compiled block is the encoding of its lowering. -/
theorem compile_inv (c : PipeCfg) (L : Layout D) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte) (h : compile c L certs src = some bytes) :
    ∃ prog, cfgOk c = true ∧ senkBlock c L 0 (optimise certs src) = some prog ∧
      bytes = encodeAll prog := by
  unfold compile compileProg at h
  by_cases hc : cfgOk c = true
  · rw [if_pos hc] at h
    cases hp : senkBlock c L 0 (optimise certs src) with
    | none => rw [hp] at h; cases h
    | some prog =>
      rw [hp] at h
      cases h
      exact ⟨prog, hc, rfl, rfl⟩
  · rw [if_neg hc] at h; cases h

/-- A written slot address is placed by the layout. -/
theorem stmtAdresse_loc (L : Layout D) {Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ'')
    (A : Nat) (h : stmtAdresse L s = some A) : ∃ t k f, L.loc t k f = some A := by
  unfold stmtAdresse at h
  split at h
  · split at h
    · exact ⟨_, _, _, h⟩
    · cases h
  · cases h

theorem slotAdressen_loc (L : Layout D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (A : Nat) (h : A ∈ slotAdressen L b) :
    ∃ t k f, L.loc t k f = some A := by
  generalize hb0 : b = b0 at h
  cases b0 with
  | nil => simp [slotAdressen] at h
  | cons s rest =>
    simp only [slotAdressen, List.mem_append] at h
    rcases h with h | h
    · cases hs : stmtAdresse L s with
      | none => rw [hs] at h; simp at h
      | some A' =>
        rw [hs] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        subst h
        exact stmtAdresse_loc L s _ hs
    · exact slotAdressen_loc L rest A h
  | pruefung cnd sonst rest =>
    exact slotAdressen_loc L rest A (by simpa [slotAdressen] using h)
  | _ => simp [slotAdressen] at h
termination_by sizeOf b
decreasing_by
  all_goals
    subst hb0
    simp only [Block.cons.sizeOf_spec, Block.pruefung.sizeOf_spec]
    omega

/-- **COMPILE, THEN BUILD THE IMAGE: A TOTAL, CHECKED PATH.** Whatever the
    compiler produces for a block, under the decided layout side
    conditions, is accepted by the code validator, and the image built
    from it passes the image check and the initial-world check. -/
theorem kompiliert_geladen (p : Profil) (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (σ : World D) (hc : compile c (layoutVon ps) certs src = some bytes)
    (hb : bauOk p c [] bytes (ohneDoppel (grundListe (optimise certs src))) ps es = true) :
    validate c (layoutVon ps) certs src bytes = true ∧
      imageOk p (bildFuer c certs src bytes ps σ es) c ps es certs src bytes = true ∧
      weltOk (bildFuer c certs src bytes ps σ es) ps σ = true := by
  obtain ⟨prog, -, -, rfl⟩ := compile_inv c _ certs src bytes hc
  have F := bauOk_fakten p c _ _ _ ps es hb
  refine ⟨validate_compile c _ certs src _ hc ?_, bildFuer_ok p c prog ps σ es certs src hb⟩
  unfold datenGetrennt
  apply List.all_eq_true.mpr
  intro A hA
  obtain ⟨t, k, f, hloc⟩ := slotAdressen_loc _ _ A hA
  obtain ⟨q, hq, -, rfl⟩ := layoutVon_loc ps t k f A hloc
  obtain ⟨e, he, h1, h2⟩ := F.platz_in q hq
  have := F.daten_code e he
  apply decide_eq_true
  simp only [List.length_nil, Nat.sub_zero, Nat.zero_add] at this
  omega

/-- **PIPELINE CORRECTNESS FROM THE COMPILER OUTPUT.** No image premise is
    left: the code is whatever `compile` produced, the image is the one
    `bildFuer` builds from it, and the only remaining premises are the
    decided layout side conditions `bauOk`, the entry registers
    representing the environment, and the source run of the ORIGINAL
    block. The fetched run from the loaded image reaches the code end with
    world and environment represented and stops there. -/
theorem pipeline_correct_compiled (p : Profil) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (hc : compile c (layoutVon ps) certs src = some bytes)
    (hb : bauOk p c [] bytes (ohneDoppel (grundListe (optimise certs src))) ps es = true)
    (σ : World D) (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ)
    (hE : EnvRepr ρ reg (abbOf c)) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (ρ' : Env D Γ) (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    ∃ n s', laufBytes n (startZustand (bildFuer c certs src bytes ps σ es) c reg fl) = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      byteschritt s' = .verweigert := by
  obtain ⟨hval, himg, hwelt⟩ := kompiliert_geladen p c ps es certs src bytes σ hc hb
  obtain ⟨n, s', hrun, hrip, hW, hE', hstop, -⟩ := pipeline_correct_loaded p _ c ps es certs src
    bytes hval himg σ hwelt reg fl ρ hE O passes R σ' ρ' hsrc
  exact ⟨n, s', hrun, hrip, hW, hE', hstop⟩

/-- **PIPELINE REFUSAL FROM THE COMPILER OUTPUT**: a failed check of the
    ORIGINAL block with reason `r` ends, from the loaded built image,
    after the checked stub at `exitAdr c r + 10` with `rax = r` and the
    world represented; the machine stops there. -/
theorem pipeline_refuses_compiled (p : Profil) (c : PipeCfg) (ps : List (Platz D))
    (es : List TabLayout) (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte) (hc : compile c (layoutVon ps) certs src = some bytes)
    (hb : bauOk p c [] bytes (ohneDoppel (grundListe (optimise certs src))) ps es = true)
    (σ : World D) (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ)
    (hE : EnvRepr ρ reg (abbOf c)) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (r : Fin V.gruende) (hsrc : execBlock O passes R src σ ρ = .grund σ' r) :
    ∃ n s', laufBytes n (startZustand (bildFuer c certs src bytes ps σ es) c reg fl) = .weiter s' ∧
      s'.rip = natAdresse (exitAdr c r.val + 10) ∧ s'.register exitReg = intWort r.val ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ byteschritt s' = .verweigert := by
  obtain ⟨hval, himg, hwelt⟩ := kompiliert_geladen p c ps es certs src bytes σ hc hb
  obtain ⟨n, -, s', -, -, -, hrip, hreg, hW, hrun, hstop, -⟩ := pipeline_refuses_loaded p _ c ps
    es certs src bytes hval himg σ hwelt reg fl ρ hE O passes R σ' r hsrc
  exact ⟨n + 1, s', hrun, hrip, hreg, hW, hstop⟩

end BauSchluss
-- END SEC9

/- CUTS (exactly what is NOT proved here):

   Image check. `imageOk` is SOUND, not complete: every theorem takes an
   arbitrary (untrusted) image and demands only the decided check. That
   the constructor `baueBild`/`bildFuer` always passes it is NOT proved in
   general; it is shown by computation for the witnesses only. The
   representation facts (`CodeAt` of code and stubs, the stop bytes,
   permissions and values of placed slots) are decided DIRECTLY over the
   existing loader's memory (`geladen`), byte by byte; `valX86`,
   `layoutOk` and `regionDisjunkt` are checked as admission and are
   load-bearing only for `imageOk_valX86` and `imageOk_daten_getrennt`.

   Layout. Placements are a finite list (`layoutVon`). The table extents
   `es` are a checked `TabLayout` list; they are NOT recomputed from a
   source `UProg` (`TableLayout.layoutFuer`): there is no bridge from a
   `Deklaration` to a `UProg` here. Only integer slots have a
   representation (`slotWort` is `0` elsewhere and `repOk` refuses them).
   The data sections are file-backed (the initial world's bytes), not the
   zero-filled `TableLayout.abschnittVon`.

   Initial world. `weltOk` is a premise decided against the given world
   `σ`; the loaded image does not CHOOSE the world, it is checked to
   represent it. Unplaced slots are neither represented nor claimed.

   Entry. The start state is the existing loader's `bildZustand` at
   `codeBase` with caller-chosen registers and flags; `EnvRepr` of the
   entry registers stays a premise. The entry model of `EntryState`/
   `EntryExecution` (stack, MXCSR, interrupt flag, guard page) is NOT
   connected: this fragment uses no stack.

   Refusal exit ABI. One 10-byte stub `mov rax, r` per REACHABLE reason
   (`grundListe`: the reasons of the block's checks), at the fixed
   `exitBase + r` of `Pipeline.lean`. Since exits are one byte apart, two
   reachable reasons less than eleven apart cannot both have a stub, and
   such a block is REFUSED by `imageOk` (the stub bytes and the stop byte
   cannot all hold); lifting this needs an exit stride in `PipeCfg`
   (`Pipeline.lean`, not owned here). The stop is the absence of a byte
   step (`byteschritt = .verweigert`: no execute permission at the stop
   address); the pilot model has no halt instruction, and returning the
   reason to a caller (`ret`, a call ABI, an operating system) is NOT
   modelled. At the stop only `rax`, the address and the world on placed
   slots are claimed; flags and other registers are not.

   Normal end. The byte after the code is checked non-executable, so the
   machine stops at the code end; the variable registers and the placed
   world are claimed there (from `pipeline_correct`), nothing else.

   Machine. Everything of `Pipeline.lean`'s CUTS still applies: pilot ISA,
   one sequential core (`laufBytes`), the model `Speicher`, no hardware,
   no TSO, no time or budget transfer, no relocations (`reloks = []` in
   the constructor; `valX86` checks any that are present, but no theorem
   here uses them). -/

#print axioms trifft_inv
#print axioms layoutVon_loc
#print axioms layoutVon_some
#print axioms sepB_sound
#print axioms codeAtB_sound
#print axioms slotWort_cast
#print axioms worldRep_von
#print axioms byteRahmen_refl
#print axioms byteRahmen_trans
#print axioms byteRahmen_write64
#print axioms schritt_rahmen
#print axioms byteschritt_rahmen
#print axioms laufBytes_rahmen
#print axioms codeAt_lauf
#print axioms byteschritt_stop
#print axioms grund_mem
#print axioms stubBytes_length
#print axioms imageOk_teile
#print axioms imageOk_codeAt
#print axioms imageOk_layoutSep
#print axioms imageOk_worldRep
#print axioms imageOk_valX86
#print axioms imageOk_daten_getrennt
#print axioms pipeline_correct_loaded
#print axioms pipeline_refuses_loaded
#print axioms pipeline_loaded_ausgang
-- BEGIN AX9
#print axioms mem_ohneDoppel
#print axioms ohneDoppel_nodup
#print axioms halbe_le
#print axioms bauOk_fakten
#print axioms pairwise_drei
#print axioms take_drop_mitte
#print axioms getD_von_take_drop
#print axioms paarweise_von
#print axioms abteilFinden_eindeutig
#print axioms abteilFinden_mem
#print axioms ladenAusfuehrbar_aus
#print axioms natAdresse_toNat_lt
#print axioms addrOff_toNat
#print axioms ladenByte_in
#print axioms codeAtB_von
#print axioms stub_mem_v
#print axioms stub_vorhanden
#print axioms stub_bytes
#print axioms daten_mem_v
#print axioms datenChunk_length
#print axioms daten_vorhanden
#print axioms ketteE_append
#print axioms ketteE_le
#print axioms ketteE_mem
#print axioms ketteE_pairwise
#print axioms ketteE_stubs
#print axioms ketteE_daten
#print axioms stubs_flatten_length
#print axioms decodeFuel_encodeAll
#print axioms validAllFuel_encodeAll
#print axioms stubs_pairwise
#print axioms daten_pairwise
#print axioms datenChunk_getD
#print axioms lesbar8_von
#print axioms schreibbar8_von
#print axioms read64_von
#print axioms slotByte_von
#print axioms baueBildP_sek
#print axioms baueBildP_kette
#print axioms baueBildP_halb
#print axioms baueBildP_pairwise
#print axioms baueBildP_wohlgeformt
#print axioms baueBildP_deckung
#print axioms baueBildP_valX86
#print axioms baueBildP_code
#print axioms baueBildP_stop
#print axioms baueBildP_stubs
#print axioms baueBildP_welt
#print axioms gleicherSchluessel_selbst
#print axioms sepB_von
#print axioms bildFuerP_ok
#print axioms bildFuer_ok
#print axioms compile_inv
#print axioms stmtAdresse_loc
#print axioms slotAdressen_loc
#print axioms kompiliert_geladen
#print axioms pipeline_correct_compiled
#print axioms pipeline_refuses_compiled
-- END AX9

end Gabbro.Grammatik.X86.PipelineImage
