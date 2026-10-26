/-
  File:      stage0/Stage0/Schnell/Sim/SE.lean
  Subject:   The simulation of the normal form, rules 41 .. 50 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_dannBindCall {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ)
        (nach D g Λ) Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCall g args he hp hr rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.dannBindCall M f l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead ?_ ((M.weltVon f).lese Λ args.orte) (rfl) rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBindCallInd {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ)
        (nachSig D (D.sigNr n) Λ) Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallInd p args he hp hr rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.dannBindCallInd M f l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead ?_ ((M.weltVon f).lese Λ (p.orte ++ args.orte)) (rfl) g hg ?_ rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBindCallElse {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.signatur g) Λ)
      (hr : 0 < D.gruende g)
      (err : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l
        (.why (D.gruende g) :: Γ) (nach D g Λ))
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ)
        (nach D g Λ) Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallElse g args he hp hr err rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.dannBindCallElse M f l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead ?_ ((M.weltVon f).lese Λ args.orte) (rfl) rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueckBind {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rest)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      {lr : Bool} (Γc : Ctx) (Λc : List (Res D))
      (e : ErgExpr D Γc Λc (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λc.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (ρ : Env D Γc)
      (hkopf_ : ((normal ww M).faeden f).kopf.rest = ⟨lr, Γc, Λc, ρ, .ende (.ret e hperm)⟩)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (hΛ : HeldIn Λc (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λc e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rest,
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
           ⟨rest,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  subst hs1
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rest = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp [normal, fadenNormal, hs] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λc e.orte) e (((normal ww M).weltVon f).lese Λc e.orte) ρ = evalErg ((M.weltVon f).lese Λc e.orte) e ((M.weltVon f).lese Λc e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.rueckBind M f cM rM hM l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hkopf_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) ?_ ((M.weltVon f).lese Λc e.orte) (rfl) v (hv.trans hE) he neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannLeaveTrav {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) rest)
           (.travRest t inv body is k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) ((normal ww M).weltVon f)
          (.cons i ρ)) =
        Ausgang.leave (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (σ₁ : World D) (hs₁ : σ₁ = σ'.lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu₁ : List (Ereignis D))
      (hneu₁ : σ₁.spur = neu₁ ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₁.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f (neu ++ neu₁), (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₁.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f (neu ++ neu₁), (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  subst hs₁
  refine ⟨_, RufSchrittG.dannLeaveTrav M f l Γ Λ t inv body is k rest i ρ hleave hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt (((M.weltVon f)).lese Λ inv.orte) (rfl) ?_ neu₁ ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannNextTrav {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) rest)
           (.travRest t inv body is k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) ((normal ww M).weltVon f)
          (.cons i ρ)) =
        Ausgang.next (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ'.tail, .trav t inv body is k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ'.tail, .trav t inv body is k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  refine ⟨_, RufSchrittG.dannNextTrav M f l Γ Λ t inv body is k rest i ρ hnext hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannLeaveWieder {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) ((normal ww M).weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  refine ⟨_, RufSchrittG.dannLeaveWieder M f l Γ Λ n bis body ueber k rest ρ hleave hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannNextWieder {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) ((normal ww M).weltVon f) ρ) =
        Ausgang.next (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .wieder n bis body ueber k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .wieder n bis body ueber k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  refine ⟨_, RufSchrittG.dannNextWieder M f l Γ Λ n bis body ueber k rest ρ hnext hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannLeaveEwig {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.ewigRest a n inv body k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) ((normal ww M).weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  refine ⟨_, RufSchrittG.dannLeaveEwig M f l Γ Λ a n inv body k rest ρ hleave hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannNextEwig {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.ewigRest a n inv body k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λx Λx) ((normal ww M).weltVon f) ρ) =
        Ausgang.next (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .ewig a n inv body k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .ewig a n inv body k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  simp only [execStmt] at hstep
  cases hstep
  refine ⟨_, RufSchrittG.dannNextEwig M f l Γ Λ a n inv body k rest ρ hnext hhead ((M.weltVon f)) _ neu rfl ?_ hkein_nimmt ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
