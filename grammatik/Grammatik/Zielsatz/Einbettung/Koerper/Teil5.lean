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
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluesselF hM (.inr (.inl r)) (.inr (.inl (E.reg r)))
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
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluesselF hM (.inr (.inl r)) (.inr (.inl (E.reg r)))
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
      let value : Wert D' (D'.rtyp (E.reg r)) := castW (D := D') (E.rtyp r).symm (E.valE _ v)
      let condition : Expr D' (D'.rtyp (E.reg r) :: Γ.map E.tyE) (Λ.map E.resE) .bool :=
        Expr.umΓ hc (exE E zusage)
      let read : World D' := leseA A' (σ'.fragt (.inr (.inl (E.reg r)))) (Λ.map E.resE) (zusage.orte.map E.ortE)
      have envRel : E.EnvR hZ (Env.cons (τ := D.rtyp r) v ρ)
          (Env.cons (τ := D'.rtyp (E.reg r)) value ρ') :=
        E.envR_cons (τ := D.rtyp r) (τ' := D'.rtyp (E.reg r)) hZ hρ v value (E.rtyp r)
          (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v))
      have hrel := (E.envR_um hZ hc.symm _ _).mpr envRel
      have reads : Expr.orte (D := D') (τ := .bool) (Expr.umΓ hc (exE E zusage)) =
          zusage.orte.map E.ortE :=
        (Expr.orte_umΓ (D := D') (τ := .bool) hc (exE E zusage)).trans (E.orte_exE zusage)
      have readWorld : leseA A' (σ'.fragt (.inr (.inl (E.reg r)))) (Λ.map E.resE)
          (Expr.orte (D := D') (τ := .bool) (Expr.umΓ hc (exE E zusage))) = read :=
        congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) =>
          leseA A' (σ'.fragt (.inr (.inl (E.reg r)))) (Λ.map E.resE) xs) reads
      have hz' : wahr? (D := D') (eval read condition read (Env.cons value ρ')) =
          wahr? (D := D) (eval σ₁ zusage σ₁ (Env.cons v ρ)) := by
        have same := hev zusage (.cons v ρ) _ hrel
        change (eval read (exE E zusage) read (castE hc.symm (Env.cons value ρ')) : Bool) =
          eval σ₁ zusage σ₁ (Env.cons v ρ) at same
        exact (congrArg (wahr? (D := D')) (eval_umΓ (τ := .bool) hc (exE E zusage) read read
          (Env.cons value ρ'))).trans same
      have target : execEndHA S' O' U' A' passes R'
          (exEnd hS (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) σ' ρ' =
          (if wahr? (D := D) (eval σ₁ zusage σ₁ (Env.cons v ρ)) = true then
            (execEndHA S' O' U' A' passes R' (Endblock.umΓ hc (exEnd hS rest)) read
              (Env.cons value ρ')).schrumpf
          else execEndHA S' O' U' A' passes R' (exEnd hS sonst) read ρ' :
            EndAusgang (E.vertragE V) l (Γ.map E.tyE)) := by
        simp only [exEnd, execEndHA]
        rw [hw'.2 v hx]
        erw [readWorld]
        change (if wahr? (D := D') (eval read condition read (Env.cons value ρ')) = true then
          (execEndHA S' O' U' A' passes R' (Endblock.umΓ hc (exEnd hS rest)) read (Env.cons value ρ')).schrumpf
          else execEndHA S' O' U' A' passes R' (exEnd hS sonst) read ρ' :
            EndAusgang (E.vertragE V) l (Γ.map E.tyE)) = _
        rw [hz']
      cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := ih_sim_end_sonst M₂ σ₁ read ρ ρ' hI hρ
        refine ⟨M₃, o, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
          exact hΦ3 Φ hP
        · rw [target]
          simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact hR
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.endSim_end_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_end_rest)
          M₂ σ₁ read (.cons v ρ) (.cons value ρ') hI envRel
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execEndHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
          exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
        · rw [target]
          simp only [hb, ↓reduceIte]
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
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hMo, hσr, hev⟩ := E.lese_eval'O hZ T (hM.fragt E (.inr (.inr g)) (.inr (.inr (E.glob g)))) hB.havocA hB.atom Λ (Λ.map E.resE)
    [Sum.inr g] [Sum.inr (E.glob g)] rfl
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨hk2, hs2, hΦ2⟩ := E.schluesselO hI (fun p hp => by
    rw [hMo] at hp
    have h1 := hM.oKurz p hp
    rw [hσr, World.rang_fragt]
    omega)
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
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int zi_lo zi_hi) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Zahl zi_lo zi_hi) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Zahl zi_lo zi_hi) = _ at h; exact h
  let branch (w : World D') (z : Zahl zi_lo zi_hi) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execEndHA S' O' U' A' passes R' (exEnd hS rest) w (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ ρ')).schrumpf
    else execEndHA S' O' U' A' passes R' (exEnd hS sonst) w ρ'
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.narrow e lo' hi' sonst rest)) σ' ρ' =
      branch W (eval σ₁ e σ₁ ρ) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
    · rw [target]; dsimp only [branch]; rw [dif_pos hc]
      exact E.endRel_schrumpf hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_neg hc]
      exact hΦ2 Φ hP
    · rw [target]; dsimp only [branch]; rw [dif_neg hc]
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
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int zi_lo zi_hi) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Zahl zi_lo zi_hi) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Zahl zi_lo zi_hi) = _ at h; exact h
  let branch (w : World D') (z : Zahl zi_lo zi_hi) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execEndHA S' O' U' A' passes R' (exEnd hS rest) w (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ ρ')).schrumpf
    else .logik .kapazitaet
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.narrowRequired e lo' hi' rest)) σ' ρ' =
      branch W (eval σ₁ e σ₁ ρ) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
    · rw [target]; dsimp only [branch]; rw [dif_pos hc]
      exact E.endRel_schrumpf hR
  · refine ⟨M₁, .logik .kapazitaet, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ hP]
      rw [dif_neg hc]
    · rw [target]; dsimp only [branch]; rw [dif_neg hc]
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
  let condition : Expr D' (Γ.map E.tyE) (Λ.map E.resE) .bool := E.exE c
  let W : World D' := leseA A' σ' (Λ.map E.resE) (c.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) condition.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE c)
  have value : (eval W condition W ρ' : Bool) = eval σ₁ c σ₁ ρ := by
    have h := hev c ρ ρ' hρ; change (eval W condition W ρ' : Bool) = _ at h; exact h
  let branch (w : World D') (b : Bool) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    if b = true then execEndHA S' O' U' A' passes R' (exEnd hS t) w ρ'
    else execEndHA S' O' U' A' passes R' (exEnd hS e) w ρ'
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.ite c t e)) σ' ρ' =
      branch W (wahr? (D := D) (eval σ₁ c σ₁ ρ)) := by
    change branch (leseA A' σ' (Λ.map E.resE) condition.orte)
      (eval (leseA A' σ' (Λ.map E.resE) condition.orte) condition (leseA A' σ' (Λ.map E.resE) condition.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  cases hb : wahr? (eval σ₁ c σ₁ ρ)
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_e M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
      exact hΦ2 Φ hP
    · rw [target]; simp only [branch, hb, Bool.false_eq_true, ↓reduceIte]
      exact hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_t M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
      exact hΦ2 Φ hP
    · rw [target]; simp only [branch, hb, ↓reduceIte]
      exact hR
end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
