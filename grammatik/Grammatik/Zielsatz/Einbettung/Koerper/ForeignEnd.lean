/- Optional foreign binders preserve full end simulation and signature holdings. -/
module
public import Grammatik.Zielsatz.Einbettung.Koerper.ForeignTransport
@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
namespace Einbettung
variable {D D' : Deklaration} (E : Einbettung D D')
variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop)
  (O' : Orakel D') (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

theorem sim_end_bindAxiomOpt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e) (a) (args) (he) (hp) (hd) (hgd) (rest)
    (ih_sim_end_rest : E.EndSim hZ
      (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest)
      (execEndHA S' O' U' A' passes R' (exEnd hS rest))) :
    E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
      (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R')
      (.bindAxiomOpt e a args he hp hd hgd rest : Endblock D V l Γ Λ))
      (execEndHA S' O' U' A' passes R' (exEnd hS (.bindAxiomOpt e a args he hp hd hgd rest))) := by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hread, hOracle, hInv, hargs⟩ :=
    E.foreign_read hZ pad S T S' T' O' U' A' hB a args hM hρ
  let readWorld : World D' := leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)
  let reply : World D' × Int := O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
    (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))
  let response : World D := E.antwortWelt hZ pad (σ₁.fragt (.inl a)) reply.1
  have fits := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a reply.2 (E.aerg a)
  have he' : D'.aerg (E.ax a) = e.map E.tyE := by rw [E.aerg, he]
  have sourceAnswer (Φ : Phi D D') (hP : Passt Φ M₁) :
      axiomAntwort (E.orakelΦ hZ pad Φ O') a σ₁ (evalArgs σ₁ args σ₁ ρ) =
        (response, einpassenErg (fun _ => Option.none) (D.aerg a) reply.2) := by
    unfold axiomAntwort
    rw [hOracle Φ hP] <;> rfl
  have targetAnswer : axiomAntwort O' (E.ax a) readWorld
      (castE (E.aparams a).symm (evalArgs readWorld (exA E args) readWorld ρ')) =
        (reply.1, einpassenErg O'.zeiger (D'.aerg (E.ax a)) reply.2) := by
    rw [hargs, aparamsUm_falt] <;> rfl
  let continuation := Endblock.umΓ (E.ergCtxE Γ e) (Endblock.umΛ (nachAxE E a Λ) (exEnd hS rest))
  have target : execEndHA S' O' U' A' passes R'
      (exEnd hS (.bindAxiomOpt e a args he hp hd hgd rest : Endblock D V l Γ Λ)) σ' ρ' =
      (match einpassenErg O'.zeiger (D'.aerg (E.ax a)) reply.2 with
      | some v => EndAusgang.weiterOpt (e.map E.tyE)
          (execEndHA S' O' U' A' passes R' continuation reply.1 (ergEnv (e.map E.tyE) (he' ▸ v) ρ'))
      | none => .hardware (.annahme (E.ax a)) : EndAusgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exEnd, execEndHA, Args.orte_umτs, orte_exA, evalArgs_umτs]
    rw [targetAnswer]
    cases einpassenErg O'.zeiger (D'.aerg (E.ax a)) reply.2 <;> rfl
  cases hx : einpassenErg (fun _ => Option.none) (D.aerg a) reply.2 with
  | none =>
    refine ⟨M₁, .hardware (.annahme a), hs, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hread Φ hP]
      rw [sourceAnswer Φ hP, hx]
    · rw [target, fits, hx]
      trivial
  | some v =>
    obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_end_rest M₁ response reply.1
      (ergEnv e (he ▸ v) ρ)
      (castE (E.ergCtxE Γ e).symm
        (ergEnv (e.map E.tyE) (he' ▸ castV (E.aerg a).symm (E.ergE _ v)) ρ'))
      (hInv reply.1) (E.foreign_result_env hZ hρ he he' (E.aerg a) v)
    refine ⟨M₂, EndAusgang.weiterOpt e o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hread Φ (passt_teil hP hs2)]
      rw [sourceAnswer Φ (passt_teil hP hs2), hx]
      exact congrArg (EndAusgang.weiterOpt e) (hΦ2 Φ hP)
    · rw [target, fits, hx]
      simp only [Option.map_some, continuation, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_weiterOpt hZ ((E.endRel_um (E.ergCtxE Γ e) o _).mpr hR2)

theorem sim_end_bindAxiomOptElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e) (a) (args) (he) (hp) (hd) (hgd) (hr) (err) (rest)
    (ih_sim_end_rest : E.EndSim hZ
      (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest)
      (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    (ih_sim_end_err : E.EndSim hZ
      (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err)
      (execEndHA S' O' U' A' passes R' (exEnd hS err))) :
    E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
      (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R')
      (.bindAxiomOptElse e a args he hp hd hgd hr err rest : Endblock D V l Γ Λ))
      (execEndHA S' O' U' A' passes R' (exEnd hS (.bindAxiomOptElse e a args he hp hd hgd hr err rest))) := by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hread, hOracle, hInv, hargs⟩ :=
    E.foreign_read hZ pad S T S' T' O' U' A' hB a args hM hρ
  let readWorld : World D' := leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)
  let reply : World D' × Int := O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
    (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))
  let response : World D := E.antwortWelt hZ pad (σ₁.fragt (.inl a)) reply.1
  have fits := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a reply.2
    (E.aerg a) (E.agruende a)
  have he' : D'.aerg (E.ax a) = e.map E.tyE := by rw [E.aerg, he]
  have hc : (reasonTy (D.agruende a) :: Γ).map E.tyE =
      reasonTy (D'.agruende (E.ax a)) :: Γ.map E.tyE := by rw [E.agruende]; rfl
  have sourceAnswer (Φ : Phi D D') (hP : Passt Φ M₁) :
      axiomAntwortSonst (E.orakelΦ hZ pad Φ O') a σ₁ (evalArgs σ₁ args σ₁ ρ) =
        (response, sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) reply.2) := by
    unfold axiomAntwortSonst
    rw [hOracle Φ hP] <;> rfl
  have targetAnswer : axiomAntwortSonst O' (E.ax a) readWorld
      (castE (E.aparams a).symm (evalArgs readWorld (exA E args) readWorld ρ')) =
        (reply.1, sonstPasst O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2) := by
    rw [hargs, aparamsUm_falt] <;> rfl
  let continuation := Endblock.umΓ (E.ergCtxE Γ e) (Endblock.umΛ (nachAxE E a Λ) (exEnd hS rest))
  let failure := Endblock.umΓ hc (Endblock.umΛ (nachAxE E a Λ) (exEnd hS err))
  have target : execEndHA S' O' U' A' passes R'
      (exEnd hS (.bindAxiomOptElse e a args he hp hd hgd hr err rest : Endblock D V l Γ Λ)) σ' ρ' =
      (match sonstPasst O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2 with
      | some (.inl v) => EndAusgang.weiterOpt (e.map E.tyE)
          (execEndHA S' O' U' A' passes R' continuation reply.1 (ergEnv (e.map E.tyE) (he' ▸ v) ρ'))
      | some (.inr r) => (execEndHA S' O' U' A' passes R' failure reply.1 (.cons r ρ')).schrumpf
      | none => .hardware (.annahme (E.ax a)) : EndAusgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exEnd, execEndHA, Args.orte_umτs, orte_exA, evalArgs_umτs]
    rw [targetAnswer]
    rcases sonstPasst O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2 with _ | (v | r) <;> rfl
  rcases hx : sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) reply.2 with _ | (v | r)
  · refine ⟨M₁, .hardware (.annahme a), hs, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hread Φ hP]
      rw [sourceAnswer Φ hP, hx]
    · rw [target, fits, hx]
      trivial
  · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_end_rest M₁ response reply.1
      (ergEnv e (he ▸ v) ρ)
      (castE (E.ergCtxE Γ e).symm
        (ergEnv (e.map E.tyE) (he' ▸ castV (E.aerg a).symm (E.ergE _ v)) ρ'))
      (hInv reply.1) (E.foreign_result_env hZ hρ he he' (E.aerg a) v)
    refine ⟨M₂, EndAusgang.weiterOpt e o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hread Φ (passt_teil hP hs2)]
      rw [sourceAnswer Φ (passt_teil hP hs2), hx]
      exact congrArg (EndAusgang.weiterOpt e) (hΦ2 Φ hP)
    · rw [target, fits, hx]
      simp only [continuation, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_weiterOpt hZ ((E.endRel_um (E.ergCtxE Γ e) o _).mpr hR2)
  · have channelType : Ty.why (D'.agruende (E.ax a)) = E.tyE (.why (D.agruende a)) := by
      rw [E.agruende] <;> rfl
    obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_end_err M₁ response reply.1
      (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
      (hInv reply.1)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons (τ := .why (D.agruende a))
        (τ' := .why (D'.agruende (E.ax a))) hZ hρ _ _ channelType
        (by
          change (castW (D := D') channelType (Fin.cast (E.agruende a).symm r) : Fin (D.agruende a)) = r
          apply Fin.ext
          exact congrArg Fin.val (castW_why (D' := D') channelType (Fin.cast (E.agruende a).symm r)))))
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hread Φ (passt_teil hP hs2)]
      rw [sourceAnswer Φ (passt_teil hP hs2), hx]
      exact congrArg (EndAusgang.schrumpf) (hΦ2 Φ hP)
    · rw [target, fits, hx]
      simp only [failure, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR2)

end Einbettung
end Gabbro.Grammatik.Einbettung
