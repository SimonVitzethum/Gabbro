/-
  File:      stage0/Stage0/Schnell/Sim/SH.lean
  Subject:   The simulation of the normal form, rules 71 .. 80 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_dannGleit {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ l₂ h₂ : Int × Int)
      (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂))
      (lo hi : Int × Int)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.float op a b lo hi rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ (a.orte ++ b.orte))
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi
        (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannGleit M f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead ((M.weltVon f).lese Λ (a.orte ++ b.orte)) (rfl) v ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannGleitLit {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (q lo hi : Int × Int)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatLit q lo hi rest) k⟩)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (bruch q) = some v) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannGleitLit M f l Γ Λ Λ' q lo hi rest k ρ hhead v hv, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannGleitVon {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int)
      (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatOf e lo hi rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannGleitVon M f l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) v ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannGleitNarrowOk {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.dannGleitNarrowOk M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) v ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannGleitNarrowElse {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ e.orte)
      (hn : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = none)
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
  refine ⟨_, RufSchrittG.dannGleitNarrowElse M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead ((M.weltVon f).lese Λ e.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBindAxiom {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiom a args he hw hg hd hgd rest) k⟩)
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
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiom_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.dannBindAxiom M f l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M v hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBindAxiomElseOk {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomElse a args he hr hw hg hd hgd err rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst OF a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiomSonst_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.dannBindAxiomElseOk M f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M v hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBindAxiomElseGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomElse a args he hr hw hg hd hgd err rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst OF a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiomSonst_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.dannBindAxiomElseGrund M f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M r hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeBindAxiomElseOk {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst OF a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
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
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiomSonst_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.endeBindAxiomElseOk M f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M v hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_endeBindAxiomElseGrund {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D ((normal ww M).faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D ((normal ww M).faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst OF a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨σ₂.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := axiomSonst_paar' hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
  refine ⟨_, RufSchrittG.endeBindAxiomElseGrund M f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead ((M.weltVon f).lese Λ args.orte) (rfl) σ₂M r hZ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
