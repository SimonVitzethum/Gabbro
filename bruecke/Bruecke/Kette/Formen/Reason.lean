module
public import Bruecke.Kette.Block
public import Bruecke.Kette.Formen.Dispatch
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}
variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

theorem reasonArms_G {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (hc : C c) (hRR : RespektiertRahmen P R) :
    ∀ fuel count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count)
      tail bs tailZ used,
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧ ReasonRelated u C c O passes R fn ns.active Λ count offset ga bs := by
  intro fuel
  exact reasonArms_G_with fuel
    (fun m _ k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB =>
      laufSeq_G G S c hc O passes R hRR m k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB)
    fuel (Nat.le_refl fuel)

end Gabbro.Bruecke
