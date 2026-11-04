module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2.Teil2

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T1
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_endeGleit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁))
    (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ)
     (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.float op a b lo hi rest)⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) a
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) b
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x) = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.ende rest) ((M.weltVon f).lese Λ (a.orte ++ b.orte)) := by
  subst hz
  exact ⟨_, RufSchrittG.endeGleit M f l Γ Λ l₁ h₁ l₂ h₂ op a b lo hi rest ρ hhead
    _ rfl v hv _ rfl hΛ, zustandG_neu rfl rfl⟩


theorem w_endeGleitLit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q lo hi : Int × Int)
    (rest : Endblock D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ)
     (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.floatLit q lo hi rest)⟩)
    (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.ende rest) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.endeGleitLit M f l Γ Λ q lo hi rest ρ hhead v hv,
    zustandG_neu rfl rfl⟩


theorem w_endeGleitVon {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
    (rest : Endblock D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ)
     (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.floatOf e lo hi rest)⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).n) = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.ende rest) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.endeGleitVon M f l Γ Λ l₁ h₁ e lo hi rest ρ hhead _ rfl v hv
    _ rfl hΛ, zustandG_neu rfl rfl⟩


theorem w_endeGleitNarrowOk {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Endblock D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ)
     (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.floatNarrow e lo hi sonst rest)⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.ende rest) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.endeGleitNarrowOk M f l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead
    _ rfl v hv _ rfl hΛ, zustandG_neu rfl rfl⟩


theorem w_endeGleitNarrowElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Endblock D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ)
     (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.floatNarrow e lo hi sonst rest)⟩)
    (hn : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = none)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ende sonst)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.endeGleitNarrowElse M f l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead
    _ rfl hn _ rfl hΛ, zustandG_neu rfl rfl⟩


end Schritte
end Gabbro.Grammatik
