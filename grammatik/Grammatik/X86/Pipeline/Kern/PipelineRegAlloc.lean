/-
  File:      Grammatik/X86/PipelineRegAlloc.lean
  Subject:   Pipeline-level register allocation validation (lane 1167).

  A checked register allocator result (untrusted candidate, decided
  validator) for the end-to-end pipeline (`Pipeline.lean`): whole-block
  live ranges from the source block structure (context variables are never
  redefined, so every variable is live throughout), interference-free
  assignment, spill reserves in a private frame region disjoint from every
  source table (`spillSlot` vocabulary of `SpillPrivate.lean`), and
  calling-convention constraints (`rsp`/`rbp` reserved). A validated
  allocation yields a lowering configuration the pipeline validator
  accepts with source meaning preserved (`pipeline_correct`); a
  clobbering allocation is refused (poison probes).

  Reused unchanged: `PipeCfg`/`cfgOk`/`abbOf`, `validate`/`validate_sound`,
  `pipeline_correct`, `Layout`/`LayoutSep`/`WorldRep`/`EnvRepr`, `spillSlot`,
  `Rahmen.schlitzNat`/`schlitzNat_schranke`. No second IR, no second source
  interpreter, no optimiser edit. Spilling a live variable is REFUSED
  (the lowering has no spill code); spill slots are validated as private
  reserves only.
-/
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Opt.Register.SpillPrivate
import Grammatik.X86.Kern.Stapel
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipeRegAlloc

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.PipelineWitnesses

/-- An untrusted register allocator result for one block: one entry per
    source variable (`some r` = register home, `none` = spilled), one
    spill-slot reserve per variable, and the frame holding the slots. -/
structure PipeRegAlloc where
  belegung : List (Option Register)
  spillVon : List Nat
  rahmen : Rahmen
  deriving DecidableEq, Repr

/-- The positional register list: a spilled variable reads as `rsp`
    (which the validator refuses loudly). -/
def pipeAllocRegs (A : PipeRegAlloc) : List Register :=
  A.belegung.map (fun o => o.getD .rsp)

/-- The lowering configuration under the allocation. -/
def pipeAllocCfg (A : PipeRegAlloc) (c : PipeCfg) : PipeCfg :=
  { c with regs := pipeAllocRegs A }

/-! ## 1. The decided validator.

    Whole-block liveness is structural: source context variables are never
    redefined, so every variable index below the assignment length is live
    across the whole block and every two distinct variables interfere.
    The validator decides: no spilled live variable (the lowering has no
    spill code, so a spill is refused, never guessed), pairwise
    collision freedom, the calling convention (`rsp`/`rbp` reserved, the
    System V stack and frame pointers), the working-register freshness the
    pipeline needs (`cfgOk` over the allocated registers, decided here so
    `pipe_alloc_cfgOk` is exact), every spill reserve in-frame, reserves
    aligned with variables, and the frame off the code region. -/

/-- Every pilot register, for bounded decidable quantification. -/
def pipeAlleRegister : List Register :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- Every register is listed (16 cases, each by computation). -/
theorem pipe_reg_mem (r : Register) : r ∈ pipeAlleRegister := by
  cases r <;> decide

/-- Collision freedom, decided over variable indices: two distinct
    variables never share a register. The conclusion is a `Nat` equation,
    so no `Fin` injectivity lemma is needed downstream. -/
def pipeKollisionsFrei (A : PipeRegAlloc) : Bool :=
  decide (∀ i : Fin A.belegung.length, ∀ j : Fin A.belegung.length,
    ∀ r ∈ pipeAlleRegister,
      A.belegung[↑i]? = some (some r) → A.belegung[↑j]? = some (some r) →
        (↑i : Nat) = ↑j)

/-- THE VALIDATOR: an untrusted allocation is accepted only if every
    check below computes to `true`. -/
def pipeRegAllocOk (A : PipeRegAlloc) (c : PipeCfg) (codeLen : Nat) : Bool :=
  A.belegung.all Option.isSome &&
  pipeKollisionsFrei A &&
  decide (.rsp ∉ pipeAllocRegs A ∧ .rbp ∉ pipeAllocRegs A) &&
  decide (c.dst ∉ pipeAllocRegs A ∧ c.tmp ∉ pipeAllocRegs A ∧ c.adr ∉ pipeAllocRegs A ∧
    c.dst ≠ c.tmp ∧ c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧
    c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧ c.adr ≠ .rsp ∧
    c.frei.Nodup ∧ ∀ r ∈ c.frei, r ∉ pipeAllocRegs A ∧ r ≠ c.dst ∧ r ≠ c.tmp ∧
      r ≠ c.adr ∧ r ≠ .rsp) &&
  A.spillVon.all (fun s => decide (s < A.rahmen.schlitzZahl)) &&
  decide (A.belegung.length = A.spillVon.length) &&
  decide (A.rahmen.basis + A.rahmen.tiefe ≤ c.codeBase ∨
    c.codeBase + codeLen ≤ A.rahmen.basis)

/-- A validated allocation yields exactly the checked configuration the
    pipeline lowering needs: every `cfgOk` conjunct is decided by the
    validator over the allocated registers. -/
theorem pipe_alloc_cfgOk (A : PipeRegAlloc) (c : PipeCfg) (codeLen : Nat)
    (h : pipeRegAllocOk A c codeLen = true) : cfgOk (pipeAllocCfg A c) = true := by
  have hcfg : decide (c.dst ∉ pipeAllocRegs A ∧ c.tmp ∉ pipeAllocRegs A ∧
      c.adr ∉ pipeAllocRegs A ∧ c.dst ≠ c.tmp ∧ c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧
      c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧ c.adr ≠ .rsp ∧ c.frei.Nodup ∧
      ∀ r ∈ c.frei, r ∉ pipeAllocRegs A ∧ r ≠ c.dst ∧ r ≠ c.tmp ∧ r ≠ c.adr ∧
        r ≠ .rsp) = true := by
    unfold pipeRegAllocOk at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.2
  show decide (c.dst ∉ pipeAllocRegs A ∧ c.tmp ∉ pipeAllocRegs A ∧
    c.adr ∉ pipeAllocRegs A ∧ c.dst ≠ c.tmp ∧ c.dst ≠ c.adr ∧ c.tmp ≠ c.adr ∧
    c.dst ≠ .rsp ∧ c.tmp ≠ .rsp ∧ c.adr ≠ .rsp ∧ c.frei.Nodup ∧
    ∀ r ∈ c.frei, r ∉ pipeAllocRegs A ∧ r ≠ c.dst ∧ r ≠ c.tmp ∧ r ≠ c.adr ∧
      r ≠ .rsp) = true
  exact hcfg

/-! ## 2. Interference freedom from the decided check.

    Liveness is whole-block and structural: source context variables are
    never redefined, so every variable index below the assignment length
    is live across the whole block and any two distinct variables
    interfere. The validator's decided index check therefore means
    interference freedom. -/

/-- Interference freedom: no two distinct variables share a register. -/
def PipeInterferenzFrei (A : PipeRegAlloc) : Prop :=
  ∀ i j : Nat, ∀ r : Register, i < A.belegung.length → j < A.belegung.length →
    i ≠ j → A.belegung[i]? = some (some r) → A.belegung[j]? = some (some r) →
      False

/-- The decided collision check means interference freedom. -/
theorem pipe_kollisionsFrei_sound (A : PipeRegAlloc)
    (h : pipeKollisionsFrei A = true) : PipeInterferenzFrei A := by
  intro i j r hi hj hne e1 e2
  unfold pipeKollisionsFrei at h
  simp only [decide_eq_true_eq] at h
  have hfin := h ⟨i, hi⟩ ⟨j, hj⟩ r (pipe_reg_mem r) e1 e2
  exact hne hfin

/-- A validated allocation is interference-free. -/
theorem pipe_alloc_interferenzFrei (A : PipeRegAlloc) (c : PipeCfg) (codeLen : Nat)
    (h : pipeRegAllocOk A c codeLen = true) : PipeInterferenzFrei A := by
  unfold pipeRegAllocOk at h
  simp only [Bool.and_eq_true] at h
  exact pipe_kollisionsFrei_sound A h.1.1.1.1.1.2

/-! ## 3. Spill privacy against every source table.

    The frame holds no source table byte (`PipeRahmenGetrennt`, a
    per-program obligation discharged by computation on concrete layouts);
    every validated reserve slot then lies disjoint from every placed slot
    (eight-byte footprints at the canonical `spillSlot` addresses, the
    vocabulary of `SpillPrivate.lean`). -/

variable {D : Deklaration}

/-- The frame region holds no source table byte: every placed slot lies
    fully outside `[basis, basis + tiefe)`. -/
def PipeRahmenGetrennt (r : Rahmen) (L : Layout D) : Prop :=
  ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat),
    L.loc t k f = some a → a + 8 ≤ r.basis ∨ r.basis + r.tiefe ≤ a

/-- Spill privacy: every named reserve slot footprint is disjoint from
    every placed source slot footprint. -/
def PipeSpillPrivat (A : PipeRegAlloc) (L : Layout D) : Prop :=
  ∀ (i s : Nat), A.spillVon[i]? = some s →
    ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat),
      L.loc t k f = some a →
        a + 8 ≤ A.rahmen.schlitzNat s ∨ A.rahmen.schlitzNat s + 8 ≤ a

/-- A validated allocation over a table-free frame is spill-private: the
    validator keeps every reserve slot in-frame, and the frame keeps every
    source table out. -/
theorem pipe_alloc_spillPrivat (A : PipeRegAlloc) (L : Layout D) (c : PipeCfg)
    (codeLen : Nat) (h : pipeRegAllocOk A c codeLen = true)
    (hsep : PipeRahmenGetrennt A.rahmen L) : PipeSpillPrivat A L := by
  intro i s hs t k f a hloc
  have hframe : s < A.rahmen.schlitzZahl := by
    unfold pipeRegAllocOk at h
    simp only [Bool.and_eq_true] at h
    have hall := (List.all_eq_true.mp h.1.1.2) s (List.mem_of_getElem? hs)
    exact of_decide_eq_true hall
  have hslot : A.rahmen.schlitzNat s + 8 ≤ A.rahmen.spitzeNat :=
    schlitzNat_schranke _ _ hframe
  have hge : A.rahmen.basis ≤ A.rahmen.schlitzNat s := by
    unfold Rahmen.schlitzNat
    omega
  unfold Rahmen.spitzeNat at hslot
  rcases hsep t k f a hloc with hlo | hhi
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## 4. Refusal: a clobbering allocation is refused loudly. -/

/-- A clobbering allocation (two distinct variables in one register) is
    refused: the validator answers `false`. -/
theorem pipe_alloc_verweigert_kollision (A : PipeRegAlloc) (c : PipeCfg)
    (codeLen : Nat) (i j : Fin A.belegung.length) (r : Register)
    (hne : (↑i : Nat) ≠ ↑j)
    (hi : A.belegung[↑i]? = some (some r))
    (hj : A.belegung[↑j]? = some (some r)) :
    pipeRegAllocOk A c codeLen = false := by
  have hcon : ¬ ∀ i : Fin A.belegung.length, ∀ j : Fin A.belegung.length,
      ∀ r ∈ pipeAlleRegister,
        A.belegung[↑i]? = some (some r) → A.belegung[↑j]? = some (some r) →
          (↑i : Nat) = ↑j := by
    intro hall
    exact hne (hall i j r (pipe_reg_mem r) hi hj)
  have h2 : pipeKollisionsFrei A = false := by
    unfold pipeKollisionsFrei
    rw [decide_eq_false_iff_not]
    exact hcon
  unfold pipeRegAllocOk
  simp [h2]

/-! ## 5. The closing theorem: a validated allocation preserves the
    source meaning of the lowered block. -/

/-- **ALLOCATION PRESERVATION.** If the pipeline validator accepts
    candidate bytes under the allocated configuration, then every real
    source run of the original block is matched by a fetched byte run
    with world and environment represented — and the allocation is
    interference-free with private spill reserves. Composed from the
    pipeline closing theorem (`pipeline_correct`) plus the allocator legs
    (`pipe_alloc_interferenzFrei`, `pipe_alloc_spillPrivat`); every
    premise is used. -/
theorem pipe_alloc_haelt_bedeutung (c : PipeCfg) (L : Layout D) (A : PipeRegAlloc)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (bytes : List Byte)
    (hval : validate (pipeAllocCfg A c) L certs src bytes = true)
    (hsep : LayoutSep L) (hzul : pipeRegAllocOk A c bytes.length = true)
    (hrahmen : PipeRahmenGetrennt A.rahmen L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse (pipeAllocCfg A c).codeBase) bytes)
    (hrip : s.rip = natAdresse (pipeAllocCfg A c).codeBase)
    (hW : WorldRep L s.speicher σ)
    (hE : EnvRepr ρ s.register (abbOf (pipeAllocCfg A c)))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    (∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse ((pipeAllocCfg A c).codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf (pipeAllocCfg A c))) ∧
    PipeInterferenzFrei A ∧ PipeSpillPrivat A L := by
  refine ⟨?_, pipe_alloc_interferenzFrei A c bytes.length hzul,
    pipe_alloc_spillPrivat A L c bytes.length hzul hrahmen⟩
  exact pipeline_correct (pipeAllocCfg A c) L certs src bytes hval hsep O passes R
    σ ρ s hcode hrip hW hE σ' ρ' hsrc

/-! ## 6. Poison probes and the joint witness.

    One positive probe (the witness allocation validates) and one refused
    probe per validator leg: clobbered registers (also through the refusal
    theorem), the stack pointer, a spilled live variable, an out-of-frame
    reserve, and a frame over the code. -/

/-- The witness allocation: `x` in `r10` (as `pwCfg` has it), one spill
    reserve in a frame at 16384 (off the code at `[4096, 4178)` and off
    the tables at 8192/8200). -/
def pipeA0 : PipeRegAlloc :=
  { belegung := [some .r10], spillVon := [0], rahmen := ⟨16384, 16⟩ }

/-- The witness allocation keeps the witness configuration. -/
theorem pipeA0_cfg : pipeAllocCfg pipeA0 pwCfg = pwCfg := rfl

/-- POSITIVE PROBE: the witness allocation validates, by computation. -/
theorem pipeA0_ok : pipeRegAllocOk pipeA0 pwCfg pwBytes.length = true := by decide

/-- The witness frame holds no source table byte, by computation on the
    two placed addresses. -/
theorem pipeA0_getrennt : PipeRahmenGetrennt pipeA0.rahmen pwL := by
  intro t k f a hloc
  cases t
  cases f
  simp only [pwL] at hloc
  by_cases e1 : k = 0
  · rw [if_pos e1] at hloc
    cases hloc
    exact Or.inl (by decide)
  · rw [if_neg e1] at hloc
    by_cases e2 : k = 1
    · rw [if_pos e2] at hloc
      cases hloc
      exact Or.inl (by decide)
    · rw [if_neg e2] at hloc
      cases hloc

/-- CLOBBER: two variables in `r10` are refused, through the refusal theorem. -/
def pipeBadClash : PipeRegAlloc :=
  { belegung := [some .r10, some .r10], spillVon := [0, 1], rahmen := ⟨16384, 16⟩ }

theorem pipe_probe_clash : pipeRegAllocOk pipeBadClash pwCfg pwBytes.length = false :=
  pipe_alloc_verweigert_kollision pipeBadClash pwCfg pwBytes.length ⟨0, by decide⟩
    ⟨1, by decide⟩ .r10 (by decide) rfl rfl

/-- RSP: allocating the stack pointer is refused (calling convention). -/
def pipeBadRsp : PipeRegAlloc :=
  { belegung := [some .rsp], spillVon := [0], rahmen := ⟨16384, 16⟩ }

theorem pipe_probe_rsp : pipeRegAllocOk pipeBadRsp pwCfg pwBytes.length = false := by
  decide

/-- SPILL: spilling the live variable is refused (no spill code). -/
def pipeBadSpill : PipeRegAlloc :=
  { belegung := [none], spillVon := [0], rahmen := ⟨16384, 16⟩ }

theorem pipe_probe_spill :
    pipeRegAllocOk pipeBadSpill pwCfg pwBytes.length = false := by
  decide

/-- OUT-OF-FRAME: a reserve past the frame is refused. -/
def pipeBadAussen : PipeRegAlloc :=
  { belegung := [some .r10], spillVon := [99], rahmen := ⟨16384, 16⟩ }

theorem pipe_probe_aussen :
    pipeRegAllocOk pipeBadAussen pwCfg pwBytes.length = false := by
  decide

/-- CODE OVERLAP: a frame over the code region is refused. -/
def pipeBadCode : PipeRegAlloc :=
  { belegung := [some .r10], spillVon := [0], rahmen := ⟨4096, 16⟩ }

theorem pipe_probe_code :
    pipeRegAllocOk pipeBadCode pwCfg pwBytes.length = false := by
  decide

/-- JOINT WITNESS for `pipe_alloc_haelt_bedeutung`: every premise holds
    jointly on the pipeline witness program (one variable, two slots
    written, check passed; memory 7 -> 35 and 9 -> 6, so the run is
    non-degenerate and memory-changing); the closing theorem delivers the
    fetched run plus interference freedom and spill privacy. -/
theorem pipe_alloc_haelt_bedeutung_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      pipeRegAllocOk pipeA0 pwCfg pwBytes.length = true ∧
      PipeRahmenGetrennt pipeA0.rahmen pwL ∧
      validate (pipeAllocCfg pipeA0 pwCfg) pwL pwCerts pwSrc pwBytes = true ∧
      LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher
        (natAdresse (pipeAllocCfg pipeA0 pwCfg).codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse (pipeAllocCfg pipeA0 pwCfg).codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf (pipeAllocCfg pipeA0 pwCfg)) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      (∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        s'.rip = natAdresse ((pipeAllocCfg pipeA0 pwCfg).codeBase + pwBytes.length) ∧
        WorldRep pwL s'.speicher σ' ∧
        EnvRepr ρ' s'.register (abbOf (pipeAllocCfg pipeA0 pwCfg))) ∧
      PipeInterferenzFrei pipeA0 ∧ PipeSpillPrivat pipeA0 pwL := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  have hval : validate (pipeAllocCfg pipeA0 pwCfg) pwL pwCerts pwSrc pwBytes = true := by
    rw [pipeA0_cfg]
    exact pw_validate
  have hcode : CodeAt (pwStart 30).speicher
      (natAdresse (pipeAllocCfg pipeA0 pwCfg).codeBase) pwBytes := by
    rw [pipeA0_cfg]
    exact pw_code
  have hrip : (pwStart 30).rip = natAdresse (pipeAllocCfg pipeA0 pwCfg).codeBase := by
    rw [pipeA0_cfg]
    rfl
  have hE : EnvRepr pwEnv30 (pwStart 30).register
      (abbOf (pipeAllocCfg pipeA0 pwCfg)) := by
    rw [pipeA0_cfg]
    exact pw_envRepr30
  obtain ⟨⟨n, s', hrun, hrip', hW, hE'⟩, hfrei, hpriv⟩ :=
    pipe_alloc_haelt_bedeutung pwCfg pwL pipeA0 pwCerts pwSrc pwBytes hval
      pw_layoutSep pipeA0_ok pipeA0_getrennt pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
      hcode hrip pw_worldRep hE σ' ρ' hsrc
  exact ⟨σ', ρ', pipeA0_ok, pipeA0_getrennt, hval, pw_layoutSep, hcode, hrip,
    pw_worldRep, hE, hsrc, rfl, h0, rfl, h1,
    ⟨n, s', hrun, hrip', hW, hE'⟩, hfrei, hpriv⟩

/- CUTS:
    - Proved here: decided validator `pipeRegAllocOk` over an untrusted
      allocation (no spilled live variable, index-decided collision
      freedom, `rsp`/`rbp` calling convention, working-register freshness
      exactly `cfgOk`, in-frame reserves, reserves aligned with variables,
      frame off the code); the validated configuration is the checked one
      (`pipe_alloc_cfgOk`); decided collision check means interference
      freedom (`pipe_kollisionsFrei_sound`, `pipe_alloc_interferenzFrei`);
      validated reserves over a table-free frame are private against every
      placed source slot (`pipe_alloc_spillPrivat`, canonical `spillSlot`
      vocabulary); clobbering allocations are refused
      (`pipe_alloc_verweigert_kollision`); preservation of the lowered
      block meaning plus interference freedom and spill privacy
      (`pipe_alloc_haelt_bedeutung`, via `pipeline_correct`); one positive
      and five refusal probes (clash also through the refusal theorem);
      joint non-degenerate memory-changing witness
      (`pipe_alloc_haelt_bedeutung_zeuge` on `pwSrc`: rows 7 -> 35, 9 -> 6).
    - OPEN / not claimed: spill CODE generation (a spilled live variable
      is refused; the lowering has no spill code, as its own CUTS say);
      liveness finer than whole-block (variables are never redefined, so
      whole-block is sound but incomplete: an unused variable still needs
      a register); callee-saved restore and argument passing (no calls in
      the fragment); TSO freshness of spill slots (`SpillFrisch`,
      covered at the composed level by `ComposeSpillPrivacy.lean`);
      read-trace representation (inherited from the pipeline).
    - The refusal `Bool` is validator admission, never a hardware fault.
    - No second IR and no second evaluator: only the accepted pipeline
      lowering, validator and machine vocabulary are reused.
-/

#print axioms pipeAllocRegs
#print axioms pipeAllocCfg
#print axioms pipeKollisionsFrei
#print axioms pipeRegAllocOk
#print axioms pipe_alloc_cfgOk
#print axioms PipeInterferenzFrei
#print axioms pipe_kollisionsFrei_sound
#print axioms pipe_alloc_interferenzFrei
#print axioms PipeRahmenGetrennt
#print axioms PipeSpillPrivat
#print axioms pipe_alloc_spillPrivat
#print axioms pipe_alloc_verweigert_kollision
#print axioms pipe_alloc_haelt_bedeutung
#print axioms pipeA0
#print axioms pipeA0_cfg
#print axioms pipeA0_ok
#print axioms pipeA0_getrennt
#print axioms pipe_probe_clash
#print axioms pipe_probe_rsp
#print axioms pipe_probe_spill
#print axioms pipe_probe_aussen
#print axioms pipe_probe_code
#print axioms pipe_alloc_haelt_bedeutung_zeuge

end Gabbro.Grammatik.X86.PipeRegAlloc
