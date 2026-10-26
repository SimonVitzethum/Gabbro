/-
  File:      stage0/Stage0/Schnell/Sim/SC.lean
  Subject:   The simulation of the normal form, rules 21 .. 30 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_dannPruefFalsch {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (sonst : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
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
  refine ⟨_, RufSchrittG.dannPruefFalsch M f l Γ Λ Λ' Λ'' c sonst rest k ρ hhead ((M.weltVon f).lese Λ c.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannBreaking {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (i : D.Inv)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.breaking i body) rest) k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann body (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann body (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannBreaking M f l Γ Λ Λ' Λ'' i body rest k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannLocks {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (L : D.Lock)
      (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ
        (Res.held L :: Λ) (Res.held L :: Λ))
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩)
      (hself : L ∉ offen ((normal ww M).faeden f).spur)
      (hrang : ∀ K ∈ offen ((normal ww M).faeden f).spur, D.rang K < D.rang L)
      (hfrei : RufFreiG (normal ww M) f L) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Res.held L :: Λ, ρ,
              .dann body (.frei L (.dann rest k))⟩⟩,
            Ereignis.nimmt L (offen ((normal ww M).faeden f).spur) :: ((normal ww M).faeden f).spur,
            ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.nimmt L (offen ((normal ww M).faeden f).spur)],
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Res.held L :: Λ, ρ,
              .dann body (.frei L (.dann rest k))⟩⟩,
            Ereignis.nimmt L (offen ((normal ww M).faeden f).spur) :: ((normal ww M).faeden f).spur,
            ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.nimmt L (offen ((normal ww M).faeden f).spur)],
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannLocks M f l Γ Λ Λ'' L hr body rest k ρ hhead ?_ ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_freiGib {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.freiGib M f l Γ Λ L k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_schrumpfVergiss {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (v : Wert D τ) (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, τ :: Γ, Λ, .cons v ρ, .schrumpf k⟩) :
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
  refine ⟨_, RufSchrittG.schrumpfVergiss M f l Γ Λ τ k v ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannTrav {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ,
              .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ,
              .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannTrav M f l Γ Λ Λ'' t inv body rest k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_travNext {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (i : Wert D (.index (D.count t)))
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
              .dann body (.travRest t inv body is k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
              .dann body (.travRest t inv body is k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.travNext M f l Γ Λ t inv body i is k ρ hhead ((M.weltVon f).lese Λ inv.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_travFort {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
         .travRest t inv body is k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .trav t inv body is k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .trav t inv body is k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.travFort M f l Γ Λ t inv body is k i ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_travDone {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .trav t inv body [] k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.travDone M f l Γ Λ t inv body k ρ hhead ((M.weltVon f).lese Λ inv.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRetry {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.retry n bis body ueber) rest) k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannRetry M f l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
