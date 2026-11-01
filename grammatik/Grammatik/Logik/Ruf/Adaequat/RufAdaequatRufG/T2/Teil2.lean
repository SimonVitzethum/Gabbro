module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- `dannBindCallElse`: the caller waits (`wartetSonst`, keeping the else
    block) below the callee. -/
theorem w_bindCallElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {l : Bool}
    (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : 0 < D.gruende g)
    (err : Endblock D (vertragVon D z.kopf.f) l (.why (D.gruende g) :: Γ) (nach D g Λ))
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCallElse g args he hp hr err rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
          ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBindCallElse M f l Γ Λ Λ' Λ' τ g args he hp hr err rest k ρ hhead hΛ
    _ rfl _ rfl _ rfl, zustandG_neu rfl rfl⟩

end Schritte
/-! ### The error channel: popping with a reason -/

/-- Thread `f` of `M'` has popped the frame of `fn` through the error
    channel to `caller` above `rst`, logging `grund fn rho r s0 σ'`; the
    shared memory is `σ'.speicher`. -/
def GepopptGrundG (M' : RufMaschineG D) (f : Faden) (caller : RufRahmenG D)
    (rst : List (RufRahmenG D)) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (log : List (RufEreignisF D)) (r : Fin (D.gruende fn))
    (σ' : World D) : Prop :=
  M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.why fn rho r s0 σ' :: log⟩ ∧
    M'.speicher = σ'.speicher

theorem gepopptGrundG_neu {M : RufMaschineG D} {f : Faden} {sp : Speicher D}
    {z : RufFadenG D} {lauf : Lauf D} {st : World D} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} {fn : D.Fn} {rho : Env D (D.params fn)}
    {s0 : World D} {log : List (RufEreignisF D)} {r : Fin (D.gruende fn)}
    {σ' : World D}
    (hz : z = ⟨rst, caller, σ'.spur, RufEreignisF.why fn rho r s0 σ' :: log⟩)
    (hsp : sp = σ'.speicher) :
    GepopptGrundG ⟨sp, rufUpdateG M.faeden f z, lauf, st⟩ f caller rst fn rho s0 log r σ' :=
  ⟨by rw [← hz]; exact rufUpdateG_self M.faeden f z, hsp⟩

/-- How a caller resumes when the callee `fn` answers a reason: only a
    caller waiting in `let x = g(…) else { err }` (`wartetSonst`) can, and
    it runs `err` with the reason bound, as a block in front of its loop
    continuation (`GRest.abbruch`). `zielG r` is the resumed frame. -/
inductive PopGrund (fn : D.Fn) (caller : RufRahmenG D) :
    (Fin (D.gruende fn) → RufRahmenG D) → Prop where
  | sonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (err : Endblock D (vertragVon D caller.f) l (.why (D.gruende fn) :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst (D.gruende fn) err restb k⟩) :
      PopGrund fn caller (fun r => ⟨caller.f, caller.rho, caller.s0,
        ⟨l, .why (D.gruende fn) :: Γ, Λ, .cons r ρc, .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩)


end Gabbro.Grammatik
