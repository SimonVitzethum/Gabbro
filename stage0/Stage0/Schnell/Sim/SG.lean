/-
  File:      stage0/Stage0/Schnell/Sim/SG.lean
  Subject:   The simulation of the normal form, rules 61 .. 70 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_dannRetBind {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (lk : Bool) (Γk : Ctx) (Λk Λk'' : List (Res D))
      (e : ErgExpr D Γk Λk (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λk.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (restk : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk Λk'')
      (kk : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk'')
      (ρ : Env D Γk)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .dann (.cons (.ret e hperm) restk) kk⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λk e.orte)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs1
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λk e.orte) e (((normal ww M).weltVon f).lese Λk e.orte) ρ = evalErg ((M.weltVon f).lese Λk e.orte) e ((M.weltVon f).lese Λk e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.dannRetBind M f lk Γk Λk Λk'' e hperm restk kk ρ hhead cM rM hM l Γ Λ Λ' τ restb k ρc hcaller ?_ ((M.weltVon f).lese Λk e.orte) (rfl) _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) v (hv.trans hE) he neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueckConsBind {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (lk : Bool) (Γk : Ctx) (Λk : List (Res D))
      (e : ErgExpr D Γk Λk (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λk.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (restk : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk)
      (ρ : Env D Γk)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .ende (.cons (.ret e hperm) restk)⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λk e.orte)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩

  /- The error channel of `let x = g(…) else { err }`: a callee that answers
     a reason (`retGrund r`, from `ende`, an `ende` cons head, or a block)
     pops into its caller waiting in `wartetSonst`, which runs `err` with
     `r` bound 
     nothing (`execEnd`/`execStmt` of `retGrund` read nothing) and logs
     `grund`. -/ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩

  /- The error channel of `let x = g(…) else { err }`: a callee that answers
     a reason (`retGrund r`, from `ende`, an `ende` cons head, or a block)
     pops into its caller waiting in `wartetSonst`, which runs `err` with
     `r` bound 
     nothing (`execEnd`/`execStmt` of `retGrund` read nothing) and logs
     `grund`. -/ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs1
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λk e.orte) e (((normal ww M).weltVon f).lese Λk e.orte) ρ = evalErg ((M.weltVon f).lese Λk e.orte) e ((M.weltVon f).lese Λk e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.rueckConsBind M f lk Γk Λk e hperm restk ρ hhead cM rM hM l Γ Λ Λ' τ restb k ρc hcaller ?_ ((M.weltVon f).lese Λk e.orte) (rfl) _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) v (hv.trans hE) he neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueckGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    {lk : Bool} {Γk : Ctx} {Λk : List (Res D)}
      (r : Fin (vertragVon D ((normal ww M).faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (ρ : Env D Γk)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨lk, Γk, Λk, ρ, .ende (.retWhy r hperm)⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen ((normal ww M).faeden f).spur))
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (rg : Fin (D.gruende g)) (hrg : rg = hfg ▸ r)
      (hn : D.gruende g = n) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  refine ⟨_, RufSchrittG.rueckGrund M f r hperm ρ hhead cM rM hM l Γ Λ Λ' τ n err restb k ρc hcaller ?_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) rg hrg hn, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueckConsGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    {lk : Bool} {Γk : Ctx} {Λk : List (Res D)}
      (r : Fin (vertragVon D ((normal ww M).faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (restk : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk)
      (ρ : Env D Γk)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .ende (.cons (.retWhy r hperm) restk)⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen ((normal ww M).faeden f).spur))
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (rg : Fin (D.gruende g)) (hrg : rg = hfg ▸ r)
      (hn : D.gruende g = n) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  refine ⟨_, RufSchrittG.rueckConsGrund M f r hperm restk ρ hhead cM rM hM l Γ Λ Λ' τ n err restb k ρc hcaller ?_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) rg hrg hn, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRetGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    {lk : Bool} {Γk : Ctx} {Λk Λk'' : List (Res D)}
      (r : Fin (vertragVon D ((normal ww M).faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (restk : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk Λk'')
      (kk : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) lk Γk Λk'')
      (ρ : Env D Γk)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .dann (.cons (.retWhy r hperm) restk) kk⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen ((normal ww M).faeden f).spur))
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (rg : Fin (D.gruende g)) (hrg : rg = hfg ▸ r)
      (hn : D.gruende g = n) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            ((normal ww M).faeden f).spur,
            (RufEreignisF.why g rho rg s0 ((normal ww M).weltVon f)) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  refine ⟨_, RufSchrittG.dannRetGrund M f r hperm restk kk ρ hhead cM rM hM l Γ Λ Λ' τ n err restb k ρc hcaller ?_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) rg hrg hn, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRegLies {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regRead r hk rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen OF.zeiger (D.rtyp r) (OF.regLies r (((normal ww M).weltVon f).fragt (.inr (.inl r)))) = some v)
      (hz : D.rzusage r v = true)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            Ereignis.fremd (.inr (.inl r)) :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.fremd (.inr (.inl r))], (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            Ereignis.fremd (.inr (.inl r)) :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.fremd (.inr (.inl r))], (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannRegLies M f l Γ Λ Λ' r hk rest k ρ hhead v (by rw [← hO.zeiger, ← hO.regLies r (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact hv) hz ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRegLiesElseWahr {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen OF.zeiger (D.rtyp r) (OF.regLies r (((normal ww M).weltVon f).fragt (.inr (.inl r)))) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = (((normal ww M).weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannRegLiesElseWahr M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v (by rw [← hO.zeiger, ← hO.regLies r (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact hv) (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRegLiesElseFalsch {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen OF.zeiger (D.rtyp r) (OF.regLies r (((normal ww M).weltVon f).fragt (.inr (.inl r)))) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = (((normal ww M).weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannRegLiesElseFalsch M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v (by rw [← hO.zeiger, ← hO.regLies r (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact hv) (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannAwaits {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (hat : D.atomar g = true)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.awaits g payload hp hL hat rest) k⟩)
      (hvis : OF.sichtbar g (((normal ww M).weltVon f).fragt (.inr (.inr g))) = true)
      (σ₁ : World D) (hs₁ : σ₁ = (((normal ww M).weltVon f).fragt (.inr (.inr g))).lese Λ [.inr g])
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannAwaits M f l Γ Λ Λ' g payload hp hL hat rest k ρ hhead (by rw [← hO.sichtbar g (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact hvis) (((M.weltVon f).fragt (.inr (.inr g))).lese Λ [.inr g]) (rfl) neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannExchange {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (g : D.Glob) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hL : gdarf D g Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ (.inr g :: neuE.orte))
      (σ₂ : World D)
      (hs₂ : σ₂ = σ₁.schreibGlob g Λ (eval σ₁ neuE σ₁ (.cons (σ₁.globs g) ρ)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  subst hs₂
  have hE : eval (((normal ww M).weltVon f).lese Λ (.inr g :: neuE.orte)) neuE (((normal ww M).weltVon f).lese Λ (.inr g :: neuE.orte)) (.cons ((((normal ww M).weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ) = eval ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) neuE ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ) :=
    Paar.eval (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) neuE _
  rw [hE] at hneu
  refine ⟨_, RufSchrittG.dannExchange M f l Γ Λ Λ' g neuE hw hL rest k ρ hhead ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) (rfl) (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ (eval ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) neuE ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ))) (rfl) neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel
  all_goals try (rw [hE]; sim_ziel)

end Gabbro.Stage0
