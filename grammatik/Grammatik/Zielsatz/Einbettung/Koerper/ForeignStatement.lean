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
  let readWorld := leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)
  let reply := O'.wirkt (E.ax a) (readWorld.fragt (.inl (E.ax a)))
    (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))
  let response := E.antwortWelt hZ pad (σ₁.fragt (.inl a)) reply.1
  have fits := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a reply.2
    (E.aerg a) (E.agruende a)
  rcases hx : sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) reply.2 with _ | (v | r)
  · refine ⟨M₁, .hardware (.annahme a), hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, axiomAntwortSonst, hread Φ hP, hOracle Φ hP, orakelΦ_zeiger, hx]
    · simp only [exS, exec_nachΛ, execStmtHA, axiomAntwortSonst, Args.orte_umτs, orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, fits, hx]
      trivial
  · refine ⟨M₁, .ok response ρ, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, axiomAntwortSonst, hread Φ hP, hOracle Φ hP, orakelΦ_zeiger, hx]
    · simp only [exS, exec_nachΛ, execStmtHA, axiomAntwortSonst, Args.orte_umτs, orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, fits, hx]
      exact ⟨hInv reply.1, hρ⟩
  · have hc : (reasonTy (D.agruende a) :: Γ).map E.tyE =
        reasonTy (D'.agruende (E.ax a)) :: Γ.map E.tyE := by rw [E.agruende]; rfl
    obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_end_err M₁ response reply.1
      (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
      (hInv reply.1)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [E.agruende])
        (by rw [castW_why]; exact Fin.ext rfl)))
    refine ⟨M₂, o.schrumpf.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, axiomAntwortSonst, hread Φ (passt_teil hP hs2),
        hOracle Φ (passt_teil hP hs2), orakelΦ_zeiger, hx]
      exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ2 Φ hP)
    · simp only [exS, exec_nachΛ, execStmtHA, axiomAntwortSonst, Args.orte_umτs, orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, fits, hx]
      simp only [execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR2))

end Einbettung
end Gabbro.Grammatik.Einbettung
