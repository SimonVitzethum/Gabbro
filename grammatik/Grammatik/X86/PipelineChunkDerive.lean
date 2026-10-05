/-
  File:      Grammatik/X86/PipelineChunkDerive.lean
  Subject:   Per-chunk runs and coverage DERIVED from the lowering alone
              (lane 1219, follow-up of lane 1195 `PipelineBlockInduct`).

  Lane 1195 assumes per-chunk runs (`hrun`), coverage (`hdeck`) and time
  as premises of its two-chunk block theorem. Here the run and the
  coverage of one `assignSlot` chunk are derived from the lowering
  (`senkStmt`) plus the admitted layout/representation (`WorldRep`,
  `LayoutSep`, `cfgOk`), and the induction is extended from two conses
  to n-chunk dependent `assignSlot` chains (`blockAusChunks`). Named
  hardware timing stays a hardware assumption; unsupported shapes are
  refused, never guessed. No second IR, no second interpreter, no
  optimiser edit, no existing-file edit. Rust is out of scope.
-/
import Grammatik.X86.PipelineBlockInduct

namespace Gabbro.Grammatik.X86.PipeChunkDerive

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipeBlock

/-- A lowerable assignment chunk: one placed integer slot at a constant
    index with a deeply lowered value. By construction every element is
    an `assignSlot`, so no case split over the other statement forms
    is ever needed. -/
structure AssignChunk (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) where
  t : D.Tab
  f : D.Feld t
  i : Expr D Γ Λ (.index (D.count t))
  e : Expr D Γ Λ (D.typ t f)
  hw : V.schreibt t = true
  hL : darf D t Λ

open Gabbro.Grammatik.X86.OptimizationRules

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. The lowering inversion: what an accepted chunk is.

    An accepted `senkStmt` over `assignSlot` IS a constant index, a
    placed admitted slot and a deeply lowered value, followed by the
    address materialisation and the slot store. This inversion is what
    lets every later derivation start from the lowering alone. -/

/-- Canonical decoding is the canonical map: `decodiertZu` runs through
    `kanon`, the same map the `lauf` correctness lemmas use. -/
theorem decodiertZu_map_kanon (p : List Befehl) :
    decodiertZu p = p.map kanon := by
  simp [decodiertZu, kanon]

/-- LOWERING INVERSION (single chunk): an accepted assignment chunk is
    a constant index `k`, a placed admitted slot address `A` and a
    deeply lowered value `pv`, with the chunk `pv` plus address plus
    store. Every premise is used: `h` drives all four case splits. -/
theorem senkStmt_assign_inv (c : PipeCfg) (L : Layout D)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (code : List Befehl)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) =
      some code) :
    ∃ (k : Int) (A : Nat) (pv : List Befehl),
      constInt? i = some k ∧ L.loc t k f = some A ∧
      repOk (D.typ t f) A 8 0 = true ∧ senkWertT c e = some pv ∧
      code = pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)] := by
  simp only [senkStmt] at h
  cases hk : constInt? i with
  | none => simp [hk] at h
  | some k =>
    simp only [hk] at h
    cases hA : L.loc t k f with
    | none => simp [hA] at h
    | some A =>
      simp only [hA] at h
      by_cases hr : repOk (D.typ t f) A 8 0 = true
      · rw [if_pos hr] at h
        cases hv : senkWertT c e with
        | none => simp [hv] at h
        | some pv =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨k, A, pv, rfl, hA, hr, rfl, h.symm⟩
      · rw [if_neg hr] at h
        cases h

/-- JOINT WITNESS for `senkStmt_assign_inv`: every component holds
    jointly on the witness chunk -- constant index `0` at `8192`, an
    admitted slot, the deeply lowered value -- with the shared
    non-degenerate package (`PipePaket`: one table the contract
    writes, memory-changing source and fetched-byte runs). -/
theorem senkStmt_assign_inv_zeuge :
    ∃ (k : Int) (A : Nat) (pv code : List Befehl),
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0
          pwHw pwHL) = some code ∧
      constInt? pwIdx0 = some k ∧ pwL.loc () k () = some A ∧
      repOk (pwD.typ () ()) A 8 0 = true ∧
      senkWertT pwCfg pwWert0 = some pv ∧
      code = pv ++ [Befehl.movImm64 pwCfg.adr (natAdresse A),
        Befehl.store64 pwCfg.adr pwCfg.dst (BitVec.ofNat 32 0)] ∧
      PipePaket := by
  refine ⟨0, 8192, _, _, pwChunkWit, rfl, rfl, by decide, pwTief0, rfl,
    pipePaket_hold⟩

/- CUTS:
   - Skeleton green: `AssignChunk` (assignSlot-only chains, no case split).
   - OPEN: everything in the task (derived runs, coverage, n-chunk
     induction, closing theorem, refusals, witnesses).
-/

end Gabbro.Grammatik.X86.PipeChunkDerive
