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
    {zi_lo} {zi_hi} (e) (lo') (hi') (sonst) (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ'))) :=
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
  let branch (w : World D') (z : Zahl zi_lo zi_hi) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockHA S' O' U' A' passes R' (exB hS rest) w (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ ρ')).schrumpf
    else (execEndHA S' O' U' A' passes R' (exEnd hS sonst) w ρ').zuAusgang
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.narrow e lo' hi' sonst rest)) σ' ρ' =
      branch W (eval σ₁ e σ₁ ρ) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ)
      (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
    · rw [target]; dsimp only [branch]; rw [dif_pos hc]
      exact E.ausRel_schrumpf hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_neg hc]
      exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
    · rw [target]; dsimp only [branch]; rw [dif_neg hc]
      exact E.endRel_zuAusgang hR

set_option linter.unusedSectionVars false in
theorem sim_block_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ Λ' : List (Res D)}
    {zi_lo} {zi_hi} (e) (lo') (hi') (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ'))) :=
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
  let branch (w : World D') (z : Zahl zi_lo zi_hi) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockHA S' O' U' A' passes R' (exB hS rest) w (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ ρ')).schrumpf
    else .logik .kapazitaet
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.narrowRequired e lo' hi' rest)) σ' ρ' =
      branch W (eval σ₁ e σ₁ ρ) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  by_cases hc : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ) (Env.cons (τ := .int lo' hi') ⟨(eval σ₁ e σ₁ ρ).n, hc.1, hc.2⟩ ρ') hI
      (E.envR_cons hZ hρ _ _ rfl rfl)
    refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
      rw [dif_pos hc]
      exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
    · rw [target]; dsimp only [branch]; rw [dif_pos hc]
      exact E.ausRel_schrumpf hR
  · refine ⟨M₁, .logik .kapazitaet, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ hP]
      rw [dif_neg hc]
    · rw [target]; dsimp only [branch]; rw [dif_neg hc]
      exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩

set_option linter.unusedSectionVars false in
theorem sim_block_check {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c) (sonst) (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.check c sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.check c sonst rest : Block D V l Γ Λ Λ'))) :=
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
  let branch (w : World D') (b : Bool) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    if b = true then execBlockHA S' O' U' A' passes R' (exB hS rest) w ρ'
    else (execEndHA S' O' U' A' passes R' (exEnd hS sonst) w ρ').zuAusgang
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.check c sonst rest)) σ' ρ' =
      branch W (wahr? (D := D) (eval σ₁ c σ₁ ρ)) := by
    change branch (leseA A' σ' (Λ.map E.resE) condition.orte)
      (eval (leseA A' σ' (Λ.map E.resE) condition.orte) condition (leseA A' σ' (Λ.map E.resE) condition.orte) ρ') = _
    rw [reads]; exact congrArg (branch W) value
  cases hb : wahr? (eval σ₁ c σ₁ ρ)
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, Bool.false_eq_true, ↓reduceIte]
      exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
    · rw [target]; simp only [branch, hb, Bool.false_eq_true, ↓reduceIte]
      exact E.endRel_zuAusgang hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hb, ↓reduceIte]
      exact hΦ2 Φ hP
    · rw [target]; simp only [branch, hb, ↓reduceIte]
      exact hR

set_option linter.unusedSectionVars false in
theorem sim_block_float {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1} {zi_h1} {zi_l2} {zi_h2} (op) (a) (b) (lo) (hi) (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (a.orte ++ b.orte)
  let left : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l1 zi_h1) := E.exE a
  let right : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l2 zi_h2) := E.exE b
  let W : World D' := leseA A' σ' (Λ.map E.resE) ((a.orte ++ b.orte).map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte) = W :=
    congrArg (leseA A' σ' (Λ.map E.resE))
      ((congr (congrArg List.append (E.orte_exE a)) (E.orte_exE b)).trans List.map_append.symm)
  have va : (eval W left W ρ' : Gleit zi_l1 zi_h1) = eval σ₁ a σ₁ ρ := by
    have h := hev a ρ ρ' hρ; change (eval W left W ρ' : Gleit zi_l1 zi_h1) = _ at h; exact h
  have vb : (eval W right W ρ' : Gleit zi_l2 zi_h2) = eval σ₁ b σ₁ ρ := by
    have h := hev b ρ ρ' hρ; change (eval W right W ρ' : Gleit zi_l2 zi_h2) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execBlockHA S' O' U' A' passes R' (exB hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => .logik .bereich
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.float op a b lo hi rest)) σ' ρ' =
      branch W (gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x)) := by
    change branch (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte))
      (gleitPasst lo hi (gleitRechne op
        (eval (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) left (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) ρ').x
        (eval (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) right (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) ρ').x)) = _
    rw [reads, va, vb]
  cases hg : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ hP, hg]
      · rw [target]; simp only [branch, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_floatLit {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q) (lo) (hi) (rest)
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
    {zi_l1} {zi_h1} (e) (lo) (hi) (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int zi_l1 zi_h1) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Zahl zi_l1 zi_h1) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Zahl zi_l1 zi_h1) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execBlockHA S' O' U' A' passes R' (exB hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => .logik .bereich
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.floatOf e lo hi rest)) σ' ρ' =
      branch W (gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n)) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (gleitPasst lo hi (gleitAusInt (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ').n)) = _
    rw [reads, value]
  cases hg : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ hP, hg]
      · rw [target]; simp only [branch, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_floatNarrow {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1} {zi_h1} (e) (lo) (hi) (sonst) (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l1 zi_h1) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Gleit zi_l1 zi_h1) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Gleit zi_l1 zi_h1) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : Ausgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execBlockHA S' O' U' A' passes R' (exB hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => (execEndHA S' O' U' A' passes R' (exEnd hS sonst) w ρ').zuAusgang
  have target : execBlockHA S' O' U' A' passes R' (exB hS (.floatNarrow e lo hi sonst rest)) σ' ρ' =
      branch W (gleitPasst lo hi (eval σ₁ e σ₁ ρ).x) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (gleitPasst lo hi (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ').x) = _
    rw [reads, value]
  cases hg : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
  | none =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o.zuAusgang, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg EndAusgang.zuAusgang (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.endRel_zuAusgang hR
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.ausRel_schrumpf hR

theorem sim_end_float {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1} {zi_h1} {zi_l2} {zi_h2} (op) (a) (b) (lo) (hi) (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (a.orte ++ b.orte)
  let left : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l1 zi_h1) := E.exE a
  let right : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l2 zi_h2) := E.exE b
  let W : World D' := leseA A' σ' (Λ.map E.resE) ((a.orte ++ b.orte).map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte) = W :=
    congrArg (leseA A' σ' (Λ.map E.resE))
      ((congr (congrArg List.append (E.orte_exE a)) (E.orte_exE b)).trans List.map_append.symm)
  have va : (eval W left W ρ' : Gleit zi_l1 zi_h1) = eval σ₁ a σ₁ ρ := by
    have h := hev a ρ ρ' hρ; change (eval W left W ρ' : Gleit zi_l1 zi_h1) = _ at h; exact h
  have vb : (eval W right W ρ' : Gleit zi_l2 zi_h2) = eval σ₁ b σ₁ ρ := by
    have h := hev b ρ ρ' hρ; change (eval W right W ρ' : Gleit zi_l2 zi_h2) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execEndHA S' O' U' A' passes R' (exEnd hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => .logik .bereich
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.float op a b lo hi rest)) σ' ρ' =
      branch W (gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x)) := by
    change branch (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte))
      (gleitPasst lo hi (gleitRechne op
        (eval (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) left (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) ρ').x
        (eval (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) right (leseA A' σ' (Λ.map E.resE) (left.orte ++ right.orte)) ρ').x)) = _
    rw [reads, va, vb]
  cases hg : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ hP, hg]
      · rw [target]; simp only [branch, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.endRel_schrumpf hR

theorem sim_end_floatLit {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q) (lo) (hi) (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatLit q lo hi rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.floatLit q lo hi rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  cases hg : gleitPasst lo hi (bruch q) with
  | none =>
      refine ⟨M, .logik .bereich, teil_refl M, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hg]
      · simp only [exEnd, execEndHA, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hM.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M σ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hM
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hg]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · simp only [exEnd, execEndHA, hg]
        exact E.endRel_schrumpf hR

theorem sim_end_floatOf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1} {zi_h1} (e) (lo) (hi) (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int zi_l1 zi_h1) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Zahl zi_l1 zi_h1) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Zahl zi_l1 zi_h1) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execEndHA S' O' U' A' passes R' (exEnd hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => .logik .bereich
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.floatOf e lo hi rest)) σ' ρ' =
      branch W (gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n)) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (gleitPasst lo hi (gleitAusInt (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ').n)) = _
    rw [reads, value]
  cases hg : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
  | none =>
      refine ⟨M₁, .logik .bereich, hs, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ hP, hg]
      · rw [target]; simp only [branch, hg]
        exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.endRel_schrumpf hR

theorem sim_end_floatNarrow {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1} {zi_h1} (e) (lo) (hi) (sonst) (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.fl zi_l1 zi_h1) := E.exE e
  let W : World D' := leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)
  have reads : leseA A' σ' (Λ.map E.resE) mapped.orte = W :=
    congrArg (leseA A' σ' (Λ.map E.resE)) (E.orte_exE e)
  have value : (eval W mapped W ρ' : Gleit zi_l1 zi_h1) = eval σ₁ e σ₁ ρ := by
    have h := hev e ρ ρ' hρ; change (eval W mapped W ρ' : Gleit zi_l1 zi_h1) = _ at h; exact h
  let branch (w : World D') (answer : Option (Gleit lo hi)) : EndAusgang (E.vertragE V) l (Γ.map E.tyE) :=
    match answer with
    | some v => (execEndHA S' O' U' A' passes R' (exEnd hS rest) w (Env.cons (τ := .fl lo hi) v ρ')).schrumpf
    | none => execEndHA S' O' U' A' passes R' (exEnd hS sonst) w ρ'
  have target : execEndHA S' O' U' A' passes R' (exEnd hS (.floatNarrow e lo hi sonst rest)) σ' ρ' =
      branch W (gleitPasst lo hi (eval σ₁ e σ₁ ρ).x) := by
    change branch (leseA A' σ' (Λ.map E.resE) mapped.orte)
      (gleitPasst lo hi (eval (leseA A' σ' (Λ.map E.resE) mapped.orte) mapped (leseA A' σ' (Λ.map E.resE) mapped.orte) ρ').x) = _
    rw [reads, value]
  cases hg : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
  | none =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_sonst M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hg]
        exact hΦ2 Φ hP
      · rw [target]; simp only [branch, hg]
        exact hR
  | some w =>
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (Env.cons (τ := .fl lo hi) w ρ) (Env.cons (τ := .fl lo hi) w ρ') hI
        (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hg]
        exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
      · rw [target]; simp only [branch, hg]
        exact E.endRel_schrumpf hR

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
