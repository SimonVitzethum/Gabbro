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

/- CUTS:
   - Skeleton green: `AssignChunk` (assignSlot-only chains, no case split).
   - OPEN: everything in the task (derived runs, coverage, n-chunk
     induction, closing theorem, refusals, witnesses).
-/

end Gabbro.Grammatik.X86.PipeChunkDerive
