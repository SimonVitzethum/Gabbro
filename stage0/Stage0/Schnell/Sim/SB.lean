/-
  File:      stage0/Stage0/Schnell/Sim/SB.lean
  Subject:   The simulation of the normal form, rules 11 .. 20 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_dannOnOptionNone {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
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
      (hv : eval σ₁ o σ₁ ρ = Option.none)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann a (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann a (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannOnOptionNone M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead ((M.weltVon f).lese Λ o.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannOnTagSome {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (cs : List (Option (Int × Int)))
      (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ' cs)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ v.orte)
      (lo hi : Int)
      (b : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.int lo hi :: Γ) Λ Λ')
      (nutz : Nutzlast (some (lo, hi)))
      (hw : armWahlG arms (eval σ₁ v σ₁ ρ) = ⟨some (lo, hi), b, nutz⟩)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .int lo hi :: Γ, Λ, armEnv nutz ρ,
              .dann b (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .int lo hi :: Γ, Λ, armEnv nutz ρ,
              .dann b (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannOnTagSome M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead ((M.weltVon f).lese Λ v.orte) (rfl) lo hi b nutz ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannOnTagNone {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (cs : List (Option (Int × Int)))
      (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ' cs)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ v.orte)
      (b : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (nutz : Nutzlast none)
      (hw : armWahlG arms (eval σ₁ v σ₁ ρ) = ⟨none, b, nutz⟩)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, armEnv nutz ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, armEnv nutz ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannOnTagNone M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead ((M.weltVon f).lese Λ v.orte) (rfl) b nutz ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannOnGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Nat)
      (r : Expr D Γ Λ (.why n))
      (arms : GrundArms D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ' n)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onWhy r arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ r.orte)
      (b : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (hw : grundWahlG arms (eval σ₁ r σ₁ ρ) = b)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannOnGrund M f l Γ Λ Λ' Λ'' n r arms rest k ρ hhead ((M.weltVon f).lese Λ r.orte) (rfl) b ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeBind {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (e : Expr D Γ Λ τ)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bind e rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ, .ende rest⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ, .ende rest⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.endeBind M f l Γ Λ τ e rest ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeBindAxiom {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiom a args he hw hg hd hgd rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwort OF a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .ende rest⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .ende rest⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiom_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.endeBindAxiom M f l Γ Λ τ a args he hw hg hd hgd rest ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M v hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBind {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (e : Expr D Γ Λ τ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bind e rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannBind M f l Γ Λ Λ' Λ'' τ e rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannNarrowOk {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int)
      (e : Expr D Γ Λ (.int lo hi))
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.int lo' hi' :: Γ)
        Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .int lo' hi' :: Γ, Λ,
              .cons ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .int lo' hi' :: Γ, Λ,
              .cons ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannNarrowOk M f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannNarrowElse {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int)
      (e : Expr D Γ Λ (.int lo hi))
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.int lo' hi' :: Γ)
        Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (h : ¬ (lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'))
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
  refine ⟨_, RufSchrittG.dannNarrowElse M f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannPruefWahr {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann rest k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann rest k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannPruefWahr M f l Γ Λ Λ' Λ'' c sonst rest k ρ hhead ((M.weltVon f).lese Λ c.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
