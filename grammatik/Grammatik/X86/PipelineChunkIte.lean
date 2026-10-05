/-
  File:      Grammatik/X86/PipelineChunkIte.lean
  Subject:   Per-chunk runs and coverage DERIVED for if/else and checks
             (lane 1263, follow-up of lane 1219 `PipelineChunkDerive`).

  Lane 1219 derives per-chunk runs/coverage only for `assignSlot`
  chains; `ite`, checks, loops and calls are refused there. Here the
  chunk run/coverage premises for `ite` and bound checks
  (`Block.pruefung`) are derived from the lowering alone: the accepted
  `senkBlock` of a closed single-ite / single-check chunk IS the
  condition code plus the accepted branch lowerings with the decided
  jump layout (`iteCode`, `sprungOk`) resp. the reason-exit jump with
  its address equation (`senkPruef`), and the fetched-byte run plus
  coverage follow from the admitted layout/representation. Loops
  (`traverse`) and calls (`call`, `bindCall`) stay refused with named
  theorems and firing poison probes. No second IR, no second
  interpreter, no optimiser edit, no existing-file edit. Rust is out
  of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineChunkDerive
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineWorkBranches
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.BudgetExecution

namespace Gabbro.Grammatik.X86.PipeChunkIte

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeChunkDerive
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipeWorkBranches
open Gabbro.Grammatik.X86.PipeBlock

variable {D : Deklaration} {V : Vertrag D}

/-- The validator: recompute the closed-chunk lowering and accept the
    candidate bytes only if they are its encoding. -/
def iteCheckValidate (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  match senkBlock c L 0 b with
  | some prog => decide (bytes = encodeAll prog)
  | none => false

/-! ## 1. Closed ite chunks: lowering inversion.

    A closed ite chunk is one `ite` cons with `nil` rest. An accepted
    lowering IS the deep condition code plus the two accepted branch
    lowerings with the decided jump layout (`iteCode`, both
    `sprungOk`); the rest lowering is `[]` by computation. -/

/-- Witness then-branch: row `0` gets `x + 5` (memory-changing). -/
def witIteT1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.cons
    (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0 pwHw pwHL)
    _root_.Gabbro.Grammatik.Block.nil

/-- Witness else-branch: empty. -/
def witIteE1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.nil

/-- Witness closed ite chunk: `if x < 50 then T[0].f = x + 5`. -/
def witIte1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.cons
    (Stmt.ite (V := pwV) (l := false) pwCheck witIteT1263 witIteE1263)
    _root_.Gabbro.Grammatik.Block.nil

/-- LOWERING INVERSION (closed ite chunk): an accepted lowering is the
    condition code, the two accepted branch lowerings with both jump
    checks, and exactly the `iteCode` layout. Every premise is used:
    `h` drives the accepted inversion and the nil rest equation. -/
theorem iteChunk_inv_abgeleitet (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (t e : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ')
    (pos : Nat) (prog : List Befehl)
    (h : senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.ite cnd t e)
        _root_.Gabbro.Grammatik.Block.nil) = some prog) :
    ∃ code j pt pe, senkBedT c cnd = some (code, j) ∧
      senkBlock c L (pos + (encodeAll code).length + 6) t = some pt ∧
      senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e =
        some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      prog = iteCode code j pt pe := by
  obtain ⟨code, j, pt, pe, q, hb, ht, he, hk1, hk2, hq, hp⟩ :=
    senkBlock_ite_inv c L cnd t e _root_.Gabbro.Grammatik.Block.nil pos prog h
  have hnil : senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length)
      (_root_.Gabbro.Grammatik.Block.nil :
        _root_.Gabbro.Grammatik.Block D V l Γ Λ' Λ') = some [] := rfl
  rw [hnil, Option.some.injEq] at hq
  subst hq
  simp only [List.append_nil] at hp
  exact ⟨code, j, pt, pe, hb, ht, he, hk1, hk2, hp⟩

/-- The witness ite chunk lowers (by computation). -/
theorem witIteLow1263 :
    ∃ prog, senkBlock pwCfg pwL 0 witIte1263 = some prog := by
  have h : (senkBlock pwCfg pwL 0 witIte1263).isSome = true := by decide
  cases hm : senkBlock pwCfg pwL 0 witIte1263 with
  | none => simp [hm] at h
  | some prog => exact ⟨prog, rfl⟩

/-- JOINT WITNESS for `iteChunk_inv_abgeleitet`: every component holds
    jointly on the witness chunk -- the `x < 50` condition code, both
    accepted branch lowerings with both jump checks, exactly the
    `iteCode` layout -- with the shared non-degenerate package
    (`PipePaket`: one table its contract writes, memory-changing
    source and fetched-byte runs). -/
theorem iteChunk_inv_abgeleitet_zeuge :
    ∃ code j pt pe prog,
      senkBlock pwCfg pwL 0 witIte1263 = some prog ∧
      senkBedT pwCfg pwCheck = some (code, j) ∧
      senkBlock pwCfg pwL (0 + (encodeAll code).length + 6) witIteT1263 = some pt ∧
      senkBlock pwCfg pwL
        (0 + (encodeAll code).length + 6 + (encodeAll pt).length + 5) witIteE1263 =
        some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      prog = iteCode code j pt pe ∧
      PipePaket := by
  obtain ⟨prog, hlow⟩ := witIteLow1263
  obtain ⟨code, j, pt, pe, hb, ht, he, hk1, hk2, hp⟩ :=
    iteChunk_inv_abgeleitet pwCfg pwL pwCheck witIteT1263 witIteE1263 0 prog hlow
  exact ⟨code, j, pt, pe, prog, hlow, hb, ht, he, hk1, hk2, hp, pipePaket_hold⟩

/- CUTS:
    - Proved here: closed-ite lowering inversion
      (`iteChunk_inv_abgeleitet`) with joint non-degenerate witness.
    - OPEN: derived runs, coverage, validator soundness, closings,
      refusals; everything listed in the module header.
-/

#print axioms iteCheckValidate
#print axioms iteChunk_inv_abgeleitet
#print axioms iteChunk_inv_abgeleitet_zeuge

end Gabbro.Grammatik.X86.PipeChunkIte
