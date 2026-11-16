module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Fixtures

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten Invarianten.Frag Invarianten.VC

/-- Both arms return x+1; only the success arm receives the narrowed local. -/
def narrowedIncrement : Programm declaration :=
  { increment with rumpf := fun _ =>
      .narrow (.var .here) 0 5
        (.ret (.val (.add (.var .here) (.lit 1))) (List.Perm.refl _))
        (.ret (.val (.widen (by decide) (by decide)
          (.add (.var .here) (.lit 1)))) (List.Perm.refl _)) }

def scopedIncrement : Programm declaration :=
  { increment with rumpf := fun _ =>
      .retScoped (.val (.add (.var .here) (.lit 1)))
        (RueckRessourcen.vonGenau (List.Perm.refl _)) }

theorem narrowedIncrement_zeuge :
    KontrakteGeprueftB narrowedIncrement (SperrInv.leer declaration) [()] = true := by
  decide +kernel

theorem scopedIncrement_zeuge :
    KontrakteGeprueftB scopedIncrement (SperrInv.leer declaration) [()] = true := by
  decide +kernel

/-- The newly admitted conditional shape contains a real memory observation
    and two different integer results; it is not literal truth. -/
def conditionalPost : Expr declaration [] [] .bool :=
  .eq (.eng (.add (.glob false (fun _ member => nomatch member)) (.lit 1))
      0 10 (.glob false (fun _ member => nomatch member))) (.lit 3)

theorem currentOnly_zeuge : (currentOnly conditionalPost).toOption.isSome = true := by
  decide +kernel

/-- A retry mutates a real local on every pass and takes its overflow arm.
    Its totality proof covers all bounds, not the seven sampled passes. -/
def retryBody : Block declaration contract true [.int 0 10] [] [] :=
  .cons (.assignVar .here (.widen (by decide) (by decide) (.lit 3))) .nil

theorem retry_safe_zeuge :
    Basic.StatementResult (retryLauf (V := contract) (l := false)
      (fun next locals => .ok next (locals.set (.here : Var [.int 0 10] (.int 0 10))
        ⟨3, by decide, by decide⟩))
      (fun next _ => (next, false)) (fun next locals => .ok next locals)
      7 world arguments) :=
  Basic.retry_safe _ _ _ (fun _ _ => trivial) (fun _ _ => trivial) 7 world arguments

/-- Two successive 11-way bindings exceed a 100-specialization budget.
    Saturation stops at 101, without constructing either continuation family. -/
theorem specialization_product_zeuge :
    argumentSpecializations 100 [.int 0 10, .int 0 10] = 101 := by decide

end Gabbro.Grammatik.Vertraege.Pruefer.Witness
