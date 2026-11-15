/- A fallible foreign statement discards success and simulates its bound reason arm. -/
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

theorem sim_stmt_axiomCallElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e) (a) (args) (he) (hp) (hd) (hgd) (hr) (err)
    (ih_sim_end_err : E.EndSim hZ
      (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err)
      (execEndHA S' O' U' A' passes R' (exEnd hS err))) :
    E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
      (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R')
      (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _))
      (execStmtHA S' O' U' A' passes R' (exS hS (.axiomCallElse e a args he hp hd hgd hr err))) := by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hread, hOracle, hInv, hargs⟩ :=
    E.foreign_read hZ pad S T S' T' O' U' A' hB a args hM hρ
  let readWorld : World D' := leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)
  let reply : World D' × Int := O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
    (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))
  let response : World D := E.antwortWelt hZ pad (σ₁.fragt (.inl a)) reply.1
  have fits := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a reply.2
    (E.aerg a) (E.agruende a)
  have hc : (reasonTy (D.agruende a) :: Γ).map E.tyE =
      reasonTy (D'.agruende (E.ax a)) :: Γ.map E.tyE := by rw [E.agruende]; rfl
  have sourceAnswer (Φ : Phi D D') (hP : Passt Φ M₁) :
      axiomAntwortSonst (E.orakelΦ hZ pad Φ O') a σ₁ (evalArgs σ₁ args σ₁ ρ) =
        (response, sonstPasst (D := D) (fun _ => Option.none) (D.aerg a) (D.agruende a) reply.2) := by
    unfold axiomAntwortSonst
    rw [hOracle Φ hP] <;> rfl
  have targetAnswer : axiomAntwortSonst O' (E.ax a) readWorld
      (castE (E.aparams a).symm (evalArgs readWorld (exA E args) readWorld ρ')) =
        (reply.1, sonstPasst O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2) := by
    rw [hargs, aparamsUm_falt] <;> rfl
  let failure := Endblock.umΓ hc (Endblock.umΛ (nachAxE E a Λ) (exEnd hS err))
  have target : execStmtHA S' O' U' A' passes R'
      (exS hS (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _)) σ' ρ' =
      (match sonstPasst (D := D') O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2 with
      | some (.inl _) => .ok reply.1 ρ'
      | some (.inr r) => (execEndHA S' O' U' A' passes R' failure reply.1 (.cons r ρ')).schrumpf.zuAusgang
      | none => .hardware (.annahme (E.ax a)) : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exS, exec_nachΛ, execStmtHA, Args.orte_umτs, orte_exA, evalArgs_umτs]
    rw [targetAnswer]
    rcases sonstPasst (D := D') O'.zeiger (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) reply.2 with _ | (v | r) <;> rfl
  rcases hx : sonstPasst (D := D) (fun _ => Option.none) (D.aerg a) (D.agruende a) reply.2 with _ | (v | r)
  · refine ⟨M₁, .hardware (.annahme a), hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hread Φ hP]
      rw [sourceAnswer Φ hP, hx]
    · rw [target, fits, hx]
      trivial
  · refine ⟨M₁, .ok response ρ, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hread Φ hP]
      rw [sourceAnswer Φ hP, hx]
    · rw [target, fits, hx]
      exact ⟨hInv reply.1, hρ⟩
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
    refine ⟨M₂, o.schrumpf.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hread Φ (passt_teil hP hs2)]
      rw [sourceAnswer Φ (passt_teil hP hs2), hx]
      exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ2 Φ hP)
    · rw [target, fits, hx]
      simp only [failure, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR2))

end Einbettung
end Gabbro.Grammatik.Einbettung
