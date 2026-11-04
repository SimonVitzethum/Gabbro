module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil4
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil4a
public import Grammatik.Zielsatz.Einbettung.Koerper.EndBindings

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')
variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option linter.unusedSectionVars false in
theorem sim_end_regRead {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.regRead r hk rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.regRead r hk rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel (hM.fragt E (.inr (.inl r)) (.inr (.inl (E.reg r))))
  have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) (E.rtyp r)
  have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
    rw [List.map_cons, E.rtyp]
  cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) with
  | none =>
      refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
        rw [hx]
      · simp only [exEnd, execEndHA]
        rw [hw'.1 hx]
        trivial
  | some v =>
      have hz := hS.rzusage r v
      cases hzv : D.rzusage r v
      · refine ⟨_, .hardware (.geraet r), hs1, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
          rw [hx]
          simp only [hzv, Bool.false_eq_true, ↓reduceIte]
        · simp only [exEnd, execEndHA]
          rw [hw'.2 v hx]
          simp only [hz, hzv, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_end_rest)
          _ (σ.fragt (.inr (.inl r))) (σ'.fragt (.inr (.inl (E.reg r)))) (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hk1
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
        refine ⟨M₂, o.schrumpf, teil_trans hs1 hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ (passt_teil hP hs2)]
          rw [hx]
          simp only [hzv, ↓reduceIte]
          exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
        · simp only [exEnd, execEndHA]
          rw [hw'.2 v hx]
          simp only [hz, hzv, ↓reduceIte]
          exact E.endRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_end_regReadElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel (hM.fragt E (.inr (.inl r)) (.inr (.inl (E.reg r))))
  have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) (E.rtyp r)
  have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
    rw [List.map_cons, E.rtyp]
  cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) with
  | none =>
      refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
        rw [hx]
      · simp only [exEnd, execEndHA]
        rw [hw'.1 hx]
        trivial
  | some v =>
      obtain ⟨M₂, σ₁, hs2, hΦ2, hI, hev⟩ := E.lese_eval hZ hk1 T hB.havocA hB.atom Λ (Λ.map E.resE)
        zusage.orte
      have hev0 := E.frei_alle hZ (@hev) hρ
      have hrel := (E.envR_um hZ hc.symm (.cons v ρ)
          (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ' : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE))).mpr
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
      have hz' := E.frei_eq hZ (hev zusage _ _ hrel) rfl
      cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := ih_sim_end_sonst M₂ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₃, o, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
          exact hΦ3 Φ hP
        · simp only [exEnd, execEndHA]
          rw [hw'.2 v hx]
          simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb,
            Bool.false_eq_true, ↓reduceIte]
          exact hR
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_end_rest)
          M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hI
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · simp only [exEnd, execEndHA]
          rw [hw'.2 v hx]
          simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb, ↓reduceIte]
          exact E.endRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_end_awaits {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T (hM.fragt E (.inr (.inr g)) (.inr (.inr (E.glob g)))) hB.havocA hB.atom Λ (Λ.map E.resE)
    [Sum.inr g] [Sum.inr (E.glob g)] rfl
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
  have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
    rw [List.map_cons, E.gtyp]
  have hzf := hZ.frei.atomFrei g hat
  cases hvis : O'.sichtbar (E.glob g) (leseA A' (σ'.fragt (.inr (.inr (E.glob g)))) (Λ.map E.resE) [Sum.inr (E.glob g)])
  · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hzf, hΦ2 Φ hP, hvis,
        Bool.false_eq_true, ↓reduceIte]
    · simp only [exEnd, execEndHA, hvis, Bool.false_eq_true, ↓reduceIte]
      trivial
  · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_end_rest)
      _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' (σ'.fragt (.inr (.inr (E.glob g)))) (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
        (E.glob g)) ρ') hk2 (E.envR_cons hZ hρ _ _ (E.gtyp g) (hk2.treu.2 g))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar, hzf,
        hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, hvis, ↓reduceIte]
      exact E.endRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_end_exchange {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.exchange g neu hw hL rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.exchange g neu hw hL rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (Sum.inr g :: neu.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
    rw [List.map_cons, E.gtyp]
  have hrel := E.envR_cons hZ hρ (σ₁.globs g)
    ((leseA A' σ' (Λ.map E.resE) ((Sum.inr g :: neu.orte).map E.ortE)).globs (E.glob g))
    (E.gtyp g) (hI.treu.2 g)
  obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_end_rest)
    M₁ (σ₁.schreibGlob g Λ (eval σ₁ neu σ₁ (.cons (σ₁.globs g) ρ))) _ (.cons (σ₁.globs g) ρ) _
    (hI.schreibGlob E g Λ (Λ.map E.resE) _ _
      (E.vrel_um hZ (E.gtyp g) (hev neu _ _ ((E.envR_um hZ hc.symm _ _).mpr hrel)))) hrel
  refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
  · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
    exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
  · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, eval_umΓ, eval_umTy]
    exact E.endRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_end_narrow {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_pos hc]
      exact E.endRel_schrumpf hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_neg hc]
      exact hΦ2 Φ hP
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_neg hc]
      exact hR

set_option linter.unusedSectionVars false in
theorem sim_end_narrowRequired {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_pos hc]
      exact E.endRel_schrumpf hR
  · refine ⟨M₁, .logik .kapazitaet, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ hP]
      rw [dif_neg hc]
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_neg hc]
      exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩

set_option linter.unusedSectionVars false in
theorem sim_end_ite {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (ih_sim_end_e : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') e) (execEndHA S' O' U' A' passes R' (exEnd hS e)))
    (ih_sim_end_t : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') t) (execEndHA S' O' U' A' passes R' (exEnd hS t)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.ite c t e : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.ite c t e : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (c.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  cases hb : wahr? (eval σ₁ c σ₁ ρ)
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_e M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
      exact hΦ2 Φ hP
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
      exact hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_t M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
      exact hΦ2 Φ hP
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, ↓reduceIte]
      exact hR
end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
