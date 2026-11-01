module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Ausgaenge
variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_peelDann {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ Λ1)
    (b : Block D (vertragVon D z.kopf.f) true Γ Λ1 Λ2)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ2) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.dann b k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelDannLeave M f true Γ Λ r b k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelDannNext M f true Γ Λ r b k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel a `schrumpf` layer off an abrupt exit: the bound value is dropped. -/
theorem w_peelSchrumpf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true (τ :: Γ) Λ Λ1)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (v : Wert D τ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, τ :: Γ, Λ, .cons v ρ, .dann (.cons (abbS rfl w) r) (.schrumpf k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelSchrumpfLeave M f true Γ Λ τ r k (.cons v ρ) rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelSchrumpfNext M f true Γ Λ τ r k (.cons v ρ) rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel a `frei` layer off an abrupt exit: the lock is released (`gibt`),
    as `execStmt`'s `locks` releases it around the exit outcome. -/
theorem w_peelFrei {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 : List (Res D)} (w : Bool) (L : D.Lock)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.frei L k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) ((M.weltVon f).gibt L) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelFreiLeave M f true Γ Λ L r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelFreiNext M f true Γ Λ L r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel an `abbruch` layer off an abrupt exit: a `leave`/`next` in an
    `else` branch reaches the continuation after the branching form. -/
theorem w_peelAbbruch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 Λk : List (Res D)} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ Λ1)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λk) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.abbruch k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelAbbruchLeave M f Γ Λ Λ1 Λk r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelAbbruchNext M f Γ Λ Λ1 Λk r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

end Ausgaenge
/-- An outcome that is not an abrupt loop exit (`leave`/`next`). -/
def Ausgang.ohneAbbruch {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .leave .. => False
  | .next .. => False
  | _ => True


end Gabbro.Grammatik
