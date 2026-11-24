module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierInstanzen

@[expose] public section

namespace Scratch

open Gabbro.Core.Ast

example (t : Ty .value) : True := by
  induction t using Ty.rec <;> trivial

example (t : Ty .value) : True := by
  let k : Kind := .value
  change True
  induction (show Ty k from t) <;> trivial

example : ∀ (k : Kind) (t : Ty k), True := by
  intro k t
  cases k
  induction t <;> trivial

end Scratch
