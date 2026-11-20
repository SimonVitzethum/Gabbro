module
public import Bruecke.Kette.RahmenBlock
public import Bruecke.Kette.Formen.DispatchStatisch
public import Bruecke.Anweisung.Match.ReasonRahmen
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop} {c : Fin u.fns.length}

theorem reasonArms_statisch (S : Getragen u C) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ fuel count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count)
      tail bs tailZ used,
      Γ = fn.params.map (·.2) → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      (∀ name gf, fnSuch u name = some gf → (∃ args, CallsIn ss name args) →
        Gabbro.Body.Frame ρB name (writesU gf)) →
      tailZ = tail ∧ tail <:+ ss ∧ (∀ arm ∈ bs, Statisch ρB (writesU (fnAt u c)) arm.2) := by
  intro fuel
  exact reasonArms_statisch_with ρB fuel (by
    intro m _ k ss _ fn ft ns _ p tail bs tailZ used hΓ hV hm hG hB hF
    exact statischSeq_G S c hc ρB m k ss fn ft ns p tail bs tailZ used hΓ hV hm hG hB hF)
    fuel (Nat.le_refl fuel)

end Gabbro.Bruecke
