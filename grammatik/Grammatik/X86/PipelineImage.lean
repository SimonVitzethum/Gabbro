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

/-- The code section: readable, executable, never writable. -/
def codeAbschnitt (c : PipeCfg) (bytes : List Byte) : Abschnitt :=
  { dateiOff := 0, dateiLen := bytes.length, vaddr := c.codeBase, memLen := bytes.length,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- One stub section per reason, from file offset `off`. -/
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

/-- The file bytes of the data sections. -/
def datenDatei (ps : List (Platz D)) (σ : World D) (es : List TabLayout) : List Byte :=
  (es.map fun e => (List.range e.len).map fun i => slotByte ps σ (e.basis + i)).flatten

/-- THE IMAGE CONSTRUCTOR from the pipeline output. -/
def baueBild (c : PipeCfg) (bytes : List Byte) (gs : List Nat) (ps : List (Platz D))
    (σ : World D) (es : List TabLayout) : Bild :=
  { datei := bytes ++ (gs.map stubBytes).flatten ++ datenDatei ps σ es
    abschnitte := codeAbschnitt c bytes :: stubAbschnitte c bytes.length gs ++
      datenAbschnitte (bytes.length + 10 * gs.length) es
    reloks := []
    eintraege := [c.codeBase]
    modus := .fest }

/-- The image of a compiled block: stubs for exactly its reachable reasons. -/
def bildFuer {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : PipeCfg)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (ps : List (Platz D)) (σ : World D) (es : List TabLayout) : Bild :=
  baueBild c bytes (grundListe (optimise certs src)) ps σ es

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

end Gabbro.Grammatik.X86.PipelineImage
