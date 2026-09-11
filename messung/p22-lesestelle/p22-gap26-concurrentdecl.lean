/-
  P22 probe, LESESTELLE gap #26 `concurrentdecl` (G-CONC).
  Rule: the declared-concurrent set has no `Syntax.lean` constructor. Member
  paths resolve to dispatch roots, and the set becomes the `Nb :
  Nebeneinander` premise that travels explicitly through the joint model;
  the Extraktion wiring computes footprints, edges, and pairs over it.
  Witness: `miniNb`, one declared pair set, with a checked membership.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Extraktion

open Gabbro.Grammatik

/-- Gap #26: a declared-concurrent pair set holds its declared pair. -/
example : Extraktion.miniNb 0 1 := Or.inl ⟨rfl, rfl⟩
