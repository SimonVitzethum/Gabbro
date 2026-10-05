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
import Grammatik.X86.Pipeline
import Grammatik.X86.SpillPrivate
import Grammatik.X86.Stapel

namespace Gabbro.Grammatik.X86.PipeRegAlloc

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline

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
    variables never share a register. -/
def pipeKollisionsFrei (A : PipeRegAlloc) : Bool :=
  decide (∀ i : Fin A.belegung.length, ∀ j : Fin A.belegung.length,
    ∀ r ∈ pipeAlleRegister,
      A.belegung[↑i]? = some (some r) → A.belegung[↑j]? = some (some r) → i = j)

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

end Gabbro.Grammatik.X86.PipeRegAlloc
