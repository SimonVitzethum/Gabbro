module
public import Bruecke.Kette.Strecke
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik

/-- A reason-only handler satisfies the current canonical handler class even if its
    answer world is arbitrary. Therefore a reason frame cannot be extracted from
    `RespektiertRahmen`. Reason-call sampling needs a different proof boundary. -/
theorem reasonHandler_respektiertRahmen {D : Deklaration} (P : Programm D)
    (reasons : ∀ f : D.Fn, Fin (D.gruende f))
    (answer : D.Fn → World D → World D) :
    RespektiertRahmen P (fun f σ _ => .why (answer f σ) (reasons f)) := by
  constructor
  · intro f σ ρ _ σ' v h
    cases h
  · intro f σ ρ σ' v h
    cases h

end Gabbro.Bruecke
