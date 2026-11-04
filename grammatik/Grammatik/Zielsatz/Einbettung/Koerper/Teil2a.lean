module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil1
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')

private theorem scopesInv_eq (hZ : E.Rueck) (S : SperrInv D) (S' : SperrInv D')
    (hSi : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s'))
    {M : Keys D D'} {σ : World D} {σ' : World D'} (h : E.Inv hZ M σ σ') (Ls : List D.Lock) :
    scopesInvH S' (Ls.map E.lock) σ' = scopesInvH S Ls σ := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
      change (S'.inv (E.lock L) σ'.speicher && scopesInvH S' (Ls.map E.lock) σ') =
        (S.inv L σ.speicher && scopesInvH S Ls σ)
      exact congr (congrArg Bool.and ((hSi L σ'.speicher).trans
        (congrArg (S.inv L) (E.speicherZ_treu h.treu)))) ih

variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB
set_option linter.unusedSectionVars false in
theorem sim_stmt_regWrite {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (e)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.regWrite r hk e : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.regWrite r hk e : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  refine ⟨M₁, .ok σ₁ ρ, hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr]
    exact ⟨hI, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_transition {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (m)
    (hm)
    (hl)
    (maske)
    (bits)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.transition r hk m hm hl maske bits : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.transition r hk m hm hl maske bits : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .ok (σ.fragt (.inr (.inl m))) ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, execStmtHA]; exact ⟨hM.fragt E _ _, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_publish {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (e)
    (payload)
    (hp)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.publish g e payload hp hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.publish g e payload hp hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact ⟨hI.schreibGlob E g Λ _ _ _ (E.vrel_um hZ (E.gtyp g) (hev e ρ ρ' hρ)), hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_advances {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (m)
    (a)
    (h)
    (hs)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.advances m a h hs : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.advances m a h hs : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .ok σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_retires {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (m)
    (s)
    (h)
    (a)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retires m s h a : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.retires m s h a : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .ok σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, exec_nachΛ, execStmtHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_ret {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (hΛ)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.ret e hΛ : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.ret e hΛ : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    e.orte (E.exErg e).orte (E.orte_exErg e).symm
  have hev0 := E.frei_alle hZ (@hev) hρ
  have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
  refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · exact ⟨hI, he⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retScoped e R : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.retScoped e R : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    e.orte (E.exErg e).orte (E.orte_exErg e).symm
  have hev0 := E.frei_alle hZ (@hev) hρ
  have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
  let W : World D' := leseA A' σ' (Λ.map E.resE) (E.exErg e).orte
  have checks : scopesInvH S' (R.scopes.map E.lock) W = scopesInvH S R.scopes σ₁ :=
    scopesInv_eq E hZ S S' hB.inv hI R.scopes
  have target : execStmtHA S' O' U' A' passes R' (exS hS (.retScoped e R : Stmt D V l Γ Λ Λ)) σ' ρ' =
      (if scopesInvH S R.scopes σ₁ = true then
        .zurueck ((R.scopes.map E.lock).foldl World.gibt W) (evalErg W (E.exErg e) W ρ')
      else .logik .schleife : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    change (if scopesInvH S' (R.scopes.map E.lock) W = true then
      .zurueck ((R.scopes.map E.lock).foldl World.gibt W) (evalErg W (E.exErg e) W ρ')
      else .logik .schleife : Ausgang (E.vertragE V) l (Γ.map E.tyE)) = _
    rw [checks]
  cases hc : scopesInvH S R.scopes σ₁ with
  | false =>
      refine ⟨M₁, .logik .schleife, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP, hc, Bool.false_eq_true, ↓reduceIte]
      · rw [target]
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨logikRel_schleife, hI.keyOk E⟩
  | true =>
      refine ⟨M₁, .zurueck (R.scopes.foldl World.gibt σ₁) (evalErg σ₁ e σ₁ ρ), hs,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ hP, hc, ↓reduceIte]
      · rw [target]
        simp only [hc, ↓reduceIte]
        exact ⟨hI.gibt_foldl E R.scopes, he⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_retWhy {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hΛ)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retWhy r hΛ : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.retWhy r hΛ : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .why σ r, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, execStmtHA]; exact ⟨hM, rfl⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_retWhyScoped {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (R)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retWhyScoped r R : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.retWhyScoped r R : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have checks : scopesInvH S' (R.scopes.map E.lock) σ' = scopesInvH S R.scopes σ :=
    scopesInv_eq E hZ S S' hB.inv hM R.scopes
  have target : execStmtHA S' O' U' A' passes R' (exS hS (.retWhyScoped r R : Stmt D V l Γ Λ Λ)) σ' ρ' =
      (if scopesInvH S R.scopes σ = true then .why ((R.scopes.map E.lock).foldl World.gibt σ') r
      else .logik .schleife : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    change (if scopesInvH S' (R.scopes.map E.lock) σ' = true then
      .why ((R.scopes.map E.lock).foldl World.gibt σ') r
      else .logik .schleife : Ausgang (E.vertragE V) l (Γ.map E.tyE)) = _
    rw [checks]
  cases hc : scopesInvH S R.scopes σ with
  | false =>
      refine ⟨M, .logik .schleife, teil_refl M, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hc, Bool.false_eq_true, ↓reduceIte]
      · rw [target]
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨logikRel_schleife, hM.keyOk E⟩
  | true =>
      refine ⟨M, .why (R.scopes.foldl World.gibt σ) r, teil_refl M, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hc, ↓reduceIte]
      · rw [target]
        simp only [hc, ↓reduceIte]
        exact ⟨hM.gibt_foldl E R.scopes, rfl⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_leave {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (h)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.leave h : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.leave h : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .leave h σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, execStmtHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_next {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (h)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.next h : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.next h : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .next h σ ρ, teil_refl M, fun Φ hP => by simp only [execStmtHA],
    by simp only [exS, execStmtHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_block_cons {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (ih_sim_stmt_s : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') s) (execStmtHA S' O' U' A' passes R' (exS hS s)))
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := ih_sim_stmt_s M σ σ' ρ ρ' hM hρ
  generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' ρ' = o₁' at hR
  rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
  rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
  simp only [AusRel] at hR <;> (try exact hR.elim)
  · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_block_rest M₁ σ₂ σ₂' ρ₂ ρ₂' hR.1 hR.2
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      exact hΦ2 Φ hP
    · simp only [exB, execBlockHA, ho]
      exact hR2
  all_goals
    refine ⟨M₁, _, hs, fun Φ hP => by simp only [execBlockHA, hΦ Φ hP]; rfl, ?_⟩
    simp only [exB, execBlockHA, ho]
    exact hR

set_option linter.unusedSectionVars false in
theorem sim_block_bind {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
    (.cons (eval (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) (exE E e) (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) ρ') ρ') hI (E.envR_cons hZ hρ _ _ rfl (hev e ρ ρ' hρ))
  refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
  · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
    exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
  · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_bindCall {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (τ)
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCall (τ := τ) f args he hp hr rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindCall (τ := τ) f args he hp hr rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
    ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
  generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execBlock_vorΛ]
      exact E.ausRel_schrumpf hR3
  · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      trivial

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
