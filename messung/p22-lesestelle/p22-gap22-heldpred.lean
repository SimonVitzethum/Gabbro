/-
  P22 probe, LESESTELLE gap #22 `heldpred` (G-HELD).
  Rule: `Held(L)`, with optional `shared`, is not a value but a fact about
  the derivation. It becomes the context index `Res.held L` in the context
  list; the `shared` second kind is the shared lock arm, which desugars.
  Witness: the index membership, checked.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Syntax

open Gabbro.Grammatik

variable (D : Deklaration)

/-- Gap #22: `Held(L)` is the index `Res.held L` held in context. -/
example (L : D.Lock) : Res.held L ∈ [Res.held L] := List.Mem.head _
