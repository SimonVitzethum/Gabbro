module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2.Teil1Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 3. How a caller resumes, and the call steps over a thread state -/

/-- How the caller frame resumes when the callee `fn` pops: UNCHANGED (a
    plain call; `rueck`, `rueckCons`, `dannRet`), or with the returned value
    bound into its waiting residue (a bind-call; `rueckBind`,
    `rueckConsBind`, `dannRetBind`). `ziel v` is the resumed frame. -/
inductive PopArt (fn : D.Fn) (caller : RufRahmenG D) :
    (ErgVal D (D.erg fn) → RufRahmenG D) → Prop where
  | wie (hnw : caller.wartend = false) : PopArt fn caller (fun _ => caller)
  | bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg fn = some τ) :
      PopArt fn caller (fun v => ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩)
  | bindSonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) (he : D.erg fn = some τ) :
      PopArt fn caller (fun v => ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩)

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_rueckP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie hnw =>
    exact ⟨_, RufSchrittG.rueck M f caller rst hpop Γ Λ e hperm ρ hhead _ rfl
      (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩
  | bind restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckBind M f caller rst hpop _ _ _ _ _ restb k ρc (Or.inl hc) Γ Λ e
      hperm ρ hhead _ rfl (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl he _ rfl,
      gepopptG_neu rfl rfl⟩
  | bindSonst n err restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckBind M f caller rst hpop _ _ _ _ _ restb k ρc
      (Or.inr ⟨n, err, hc⟩) Γ Λ e hperm ρ hhead _ rfl (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl
      _ rfl he _ rfl, gepopptG_neu rfl rfl⟩

theorem w_rueckConsP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) lr Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie hnw =>
    exact ⟨_, RufSchrittG.rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hhead _ rfl
      (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩
  | bind restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckConsBind M f _ Γ Λ e hperm rest ρ hhead caller rst hpop _ _ _ _ _
      restb k ρc (Or.inl hc) hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl he _ rfl,
      gepopptG_neu rfl rfl⟩
  | bindSonst n err restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckConsBind M f _ Γ Λ e hperm rest ρ hhead caller rst hpop _ _ _ _ _
      restb k ρc (Or.inr ⟨n, err, hc⟩) hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl he
      _ rfl, gepopptG_neu rfl rfl⟩

theorem w_dannRetP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie hnw =>
    exact ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ
      _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩
  | bind restb k' ρc hc he =>
    exact ⟨_, RufSchrittG.dannRetBind M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop
      _ _ _ _ _ restb k' ρc (Or.inl hc) hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl he
      _ rfl, gepopptG_neu rfl rfl⟩
  | bindSonst n err restb k' ρc hc he =>
    exact ⟨_, RufSchrittG.dannRetBind M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop
      _ _ _ _ _ restb k' ρc (Or.inr ⟨n, err, hc⟩) hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl
      _ rfl he _ rfl, gepopptG_neu rfl rfl⟩

/-- `rufDann`: the caller advances to `dann rest k` and waits below the
    callee frame, which starts at the read world with the evaluated
    arguments. -/
theorem w_rufDann {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D z.kopf.f) l Γ (nach D g Λ) Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.call g args hp hr) rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rufDann M f l Γ Λ Λ Λ'' g args hp hr rest k ρ hhead hΛ _ rfl _ rfl _ rfl,
    zustandG_neu rfl rfl⟩

/-- `ruf` (repaired): at `ende` position the caller advances to `ende rest`. -/
theorem w_rufEnde {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ (nach D g Λ)) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.ruf M f l Γ Λ g args hp hr rest ρ hhead hΛ _ rfl _ rfl _ rfl,
    zustandG_neu rfl rfl⟩

/-- `dannBindCall`: the caller waits (`wartet rest k`) below the callee. -/
theorem w_bindCall {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCall g args he hp hr rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBindCall M f l Γ Λ Λ' Λ' τ g args he hp hr rest k ρ hhead hΛ
    _ rfl _ rfl _ rfl, zustandG_neu rfl rfl⟩

end Schritte
end Gabbro.Grammatik
