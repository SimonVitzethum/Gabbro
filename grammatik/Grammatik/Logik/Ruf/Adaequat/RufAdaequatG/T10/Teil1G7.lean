module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

set_option maxHeartbeats 800000 in
theorem schrittErhalt_g7 {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG7 P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestG A r) :
    ErhaltG O passes A M M' f z ρ r := by
  subst hz
  unfold ErhaltG
  cases hs with
  | dannVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | verbrauchWeiter =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | verbrauchLeer =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | verbrauchFort =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | dannLeaveVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | dannNextVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | rueckScopedWert ρ r2 e R hhead hret
  | rueckScopedWertDirekt ρ r2 e R hhead hret =>
    rcases GRest.scopedWert_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r2 <;>
      widerlege hhead
  | rueckScopedGrund ρ r2 grund R hhead hret
  | rueckScopedGrundDirekt ρ r2 grund R hhead hret =>
    rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r2 <;>
      widerlege hhead
  | rueckFreigabe ρ a L remaining hhead => widerlege hhead
  | rueckFreigabeLetzte ρ a L hhead z hantwort => widerlege hhead

end Gabbro.Grammatik
