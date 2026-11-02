module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil3

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
theorem sim_block_narrow {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_pos hc]
      exact E.ausRel_schrumpf hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_neg hc]
      exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_neg hc]
      exact E.endRel_zuAusgang hR

set_option linter.unusedSectionVars false in
theorem sim_block_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ) (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_pos hc]
      exact E.ausRel_schrumpf hR
  · refine ⟨M₁, .logik .kapazitaet, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ hP]
      rw [dif_neg hc]
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_sum, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int]
      rw [dif_neg hc]
      exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩

set_option linter.unusedSectionVars false in
theorem sim_block_check {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.check c sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.check c sonst rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (c.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  cases hb : wahr? (eval σ₁ c σ₁ ρ)
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
      exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, Bool.false_eq_true, ↓reduceIte]
      exact E.endRel_zuAusgang hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
      exact hΦ2 Φ hP
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, wahr_valE, hb, ↓reduceIte]
      exact hR

set_option linter.unusedSectionVars false in
theorem sim_block_float {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (a.orte ++ b.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  cases hg : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ hP, hg]
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
        exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_floatLit {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatLit q lo hi rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.floatLit q lo hi rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  cases hg : gleitPasst lo hi (bruch q) with
  | none =>
      refine ⟨M, .logik .bereich, teil_refl M, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hg]
      · simp only [exB, execBlockHA, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hM.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M σ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hM
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, hg]
        exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_floatOf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  cases hg : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ hP, hg]
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_int, hg]
        exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_floatNarrow {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  cases hg : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
  | none =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
        exact E.endRel_zuAusgang hR
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_fl, hg]
        exact E.ausRel_schrumpf hR

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
