/-
  File:      stage0/Stage0/Schnell/Sim/SA.lean
  Subject:   The simulation of the normal form, rules 1 .. 10 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_blatt {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf s ((normal ww M).weltVon f) ρ) =
        Ausgang.ok (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f) σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .ende rest⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .ende rest⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  have hp := blatt_paar (schwanz_normal M f) hO passes keinRuf s hleaf (paar_normal (w := ww) M f) ρ
  rw [hstep] at hp
  generalize hX : execStmt OM passes keinRuf s (M.weltVon f) ρ = X at hp
  cases hp with
  | ok hq =>
    refine ⟨_, RufSchrittG.blatt M f l Γ Λ Λ' s rest ρ hleaf hhead ?_ _ ρ' neu hX ?_ hkein_nimmt,
      sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
    all_goals try sim_ziel

theorem sim_ruf {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ (nach D g Λ))
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩)
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
              ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩ :: ((normal ww M).faeden f).stapel,
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
              ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩ :: ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.ruf M f l Γ Λ g args hp hr rest ρ hhead ?_ ((M.weltVon f).lese Λ args.orte) (rfl) rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueck {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rest) {lr : Bool}
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (ρ : Env D Γ)
      (hkopf_ : ((normal ww M).faeden f).kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur)
      (hnw : caller.wartend = false) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rest, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rest, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  subst hs1
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rest = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp only [normal, fadenNormal, hs, List.map_nil, List.nil_eq, reduceCtorEq] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λ e.orte) e (((normal ww M).weltVon f).lese Λ e.orte) ρ = evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.rueck M f cM rM hM Γ Λ e hperm ρ hkopf_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) ?_ ((M.weltVon f).lese Λ e.orte) (rfl) v (hv.trans hE) neu ?_ hnw, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeEntf {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hent : GEntfaltbar s = true)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons s .nil) (.ende rest)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons s .nil) (.ende rest)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.endeEntf M f l Γ Λ Λ' s rest ρ hent hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeForm {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (e : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hl : l = false)
      (hent : EndEntfaltbar e = true)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende e⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.endeForm M f l Γ Λ e ρ hl hent hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBlatt {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (s : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
      (hstep : (execStmt OF passes keinRuf s ((normal ww M).weltVon f) ρ) =
        Ausgang.ok (D := D) (V := vertragVon D ((normal ww M).faeden f).kopf.f) σ' ρ')
      (hneu : σ'.spur = neu ++ ((normal ww M).faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .dann rest k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ'.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .dann rest k⟩⟩,
            σ'.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  have hp := blatt_paar (schwanz_normal M f) hO passes keinRuf s hleaf (paar_normal (w := ww) M f) ρ
  rw [hstep] at hp
  generalize hX : execStmt OM passes keinRuf s (M.weltVon f) ρ = X at hp
  cases hp with
  | ok hq =>
    refine ⟨_, RufSchrittG.dannBlatt M f l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead ?_ _ ρ' neu hX ?_ hkein_nimmt,
      sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
    all_goals try sim_ziel

theorem sim_dannLeer {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann .nil k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannLeer M f l Γ Λ k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannIteWahr {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (t e : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann t (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann t (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannIteWahr M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead ((M.weltVon f).lese Λ c.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannIteFalsch {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (t e : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannIteFalsch M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead ((M.weltVon f).lese Λ c.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannOnOptionSome {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int)
      (o : Expr D Γ Λ (.opt n))
      (p : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.index n :: Γ) Λ Λ')
      (a : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ o.orte)
      (v : Wert D (.index n)) (hv : eval σ₁ o σ₁ ρ = Option.some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .index n :: Γ, Λ, .cons v ρ,
              .dann p (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .index n :: Γ, Λ, .cons v ρ,
              .dann p (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannOnOptionSome M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead ((M.weltVon f).lese Λ o.orte) (rfl) v ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
