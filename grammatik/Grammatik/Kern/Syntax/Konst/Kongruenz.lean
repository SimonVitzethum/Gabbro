module

public import Grammatik.Kern.Syntax.Konst.Rahmen
public import Grammatik.Kern.Syntax.Konst.Auswertung
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Executable congruence for the admitted fragment.

  `constExecGleich` shows every admitted body computes the same outcome
  under any two oracles, pass counts and handlers that agree pointwise,
  over frame-related worlds and environments: pure evaluation never
  consults the oracle, and conditions/arguments agree by `constEvalGleich`.
  `constRumpfTransport` moves between the transported body of
  `ConstAdmissible` and the raw body `rufAt` runs. `constRufGleich` lifts
  the congruence to calls at a common depth, by induction on the fuel,
  using the existing `rufAt_succ_eq` unfolding. No rank premise: the
  structural congruence holds unconditionally; termination only fixes the
  certified bound in `Zertifikat`. -/

/-- The tag payload environment respects pointwise agreement. -/
theorem armEnvGleich (c : ConstProgram) {Γ : Ctx} {k : Option Ty} (nutz : Nutzlast c.D.Fn c.D.passt k)
    {ρ₁ ρ₂ : Env c.D Γ} (hρ : EnvGleich c ρ₁ ρ₂) :
    EnvGleich c (armEnv nutz ρ₁) (armEnv nutz ρ₂) := by
  cases k with
  | none => simp only [armEnv]; exact hρ
  | some _ => simp only [armEnv]; exact .cons rfl hρ

/-- Shrinking an agreed outcome past a tag arm preserves agreement. -/
theorem schrumpfArmGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {k : Option Ty} {o₁ : Ausgang V l (ArmCtx Γ k)} {o₂ : Ausgang V l (ArmCtx Γ k)}
    (h : AusgangGleich c o₁ o₂) :
    AusgangGleich c (o₁.schrumpfArm k) (o₂.schrumpfArm k) := by
  cases k with
  | none => simp only [Ausgang.schrumpfArm]; exact h
  | some _ =>
    simp only [Ausgang.schrumpfArm]
    cases h with
    | ok _ _ _ _ hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
    | zurueck _ _ _ _ hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
    | why _ _ _ _ hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
    | leave _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
    | next _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
    | logik _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
    | hardware _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he

mutual
theorem constStmtGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Stmt c.D V l Γ [] []} (h : ConstStmt c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execStmt O₁ p₁ R₁ body σ₁ ρ₁) (execStmt O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .assignVar he =>
    have hv := constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    refine AusgangGleich.ok hW.1 hW.2 ?_
    exact envGleichSet c hρ _ _ _ hv
  | .ite hc hyes hno =>
    have hcEq := constEvalGleichExpr c hc σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt, hcEq]
    by_cases hcond : wahr? (eval σ₂ _ σ₂ ρ₂) = true
    · simp only [if_pos hcond]
      exact constBlockGleich c hyes O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
    · simp only [if_neg hcond]
      exact constBlockGleich c hno O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
  | .onOption hv hpresent habsent =>
    have hvEq := constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    cases hval : (eval σ₂ _ σ₂ ρ₂ : Option _) with
    | none =>
      simp only [hval]
      exact constBlockGleich c habsent O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
    | some k =>
      simp only [hval]
      cases constBlockGleich c hpresent O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ) agree with
      | ok _ _ _ _ hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
      | zurueck _ _ _ _ hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
      | why _ _ _ _ hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
      | leave _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
      | next _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
      | logik _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
      | hardware _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
  | .onTag hv harms =>
    have hvEq := constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constArmsGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl _ _ _ _ hW hρ agree
  | .onWhy hv harms =>
    have hvEq := constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constReasonGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl _ _ _ _ hW hρ agree
  | .call _ _ _ hr _ hargs =>
    have harg := constEvalGleichArgs c hargs σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [harg]
    cases (agree _ σ₁ σ₂ (evalArgs σ₂ _ σ₂ ρ₂) hW) with
    | ok _ _ _ _ hS hG _ => dsimp only; exact AusgangGleich.ok hS hG hρ
    | logik _ _ he => dsimp only; exact AusgangGleich.logik he
    | hardware _ _ he => dsimp only; exact AusgangGleich.hardware he
    | why _ _ r₁ _ _ _ _ => exact Fin.elim0 (Fin.cast hr r₁)
  | .ret hres =>
    match hres with
    | .empty => simp only [execStmt]; exact AusgangGleich.zurueck hW.1 hW.2 rfl
    | .val he =>
      have hev := constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ
      simp only [execStmt, evalErg, hev]
      exact AusgangGleich.zurueck hW.1 hW.2 rfl
theorem constBlockGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Block c.D V l Γ [] []} (h : ConstBlock c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execBlock O₁ p₁ R₁ body σ₁ ρ₁) (execBlock O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .nil => simp only [execBlock]; exact AusgangGleich.ok hW.1 hW.2 hρ
  | .cons hs hrest =>
    simp only [execBlock]
    cases constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree with
    | ok _ _ _ _ hS hG hρ' => exact constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ hρ' agree
    | zurueck _ _ _ _ hS hG hv' => dsimp only; exact AusgangGleich.zurueck hS hG hv'
    | why _ _ _ _ hS hG hr' => dsimp only; exact AusgangGleich.why hS hG hr'
    | leave _ _ _ _ _ _ hEq hS hG hρ' => dsimp only; exact AusgangGleich.leave hEq hS hG hρ'
    | next _ _ _ _ _ _ hEq hS hG hρ' => dsimp only; exact AusgangGleich.next hEq hS hG hρ'
    | logik _ _ he => dsimp only; exact AusgangGleich.logik he
    | hardware _ _ he => dsimp only; exact AusgangGleich.hardware he
  | .bind hv hrest =>
    have hvEq := constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execBlock, hvEq]
    cases constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ _ _ hW (.cons rfl hρ) agree with
    | ok _ _ _ _ hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
    | zurueck _ _ _ _ hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
    | why _ _ _ _ hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
    | leave _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
    | next _ _ _ _ _ _ hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
    | logik _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
    | hardware _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
  | .bindCall _ _ _ _ hr _ _ hargs hrest =>
    have harg := constEvalGleichArgs c hargs σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execBlock]
    rw [harg]
    cases (agree _ σ₁ σ₂ (evalArgs σ₂ _ σ₂ ρ₂) hW) with
    | ok _ _ v₁ v₂ hS hG hv =>
      dsimp only
      have herg : ergWert _ v₁ = ergWert _ v₂ := by rw [hv]
      cases constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree with
      | ok _ _ _ _ hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS' hG' (envGleichTail c hρ')
      | zurueck _ _ _ _ hS' hG' hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS' hG' hv'
      | why _ _ _ _ hS' hG' hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS' hG' hr'
      | leave _ _ _ _ _ _ hEq hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS' hG' (envGleichTail c hρ')
      | next _ _ _ _ _ _ hEq hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS' hG' (envGleichTail c hρ')
      | logik _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
      | hardware _ _ he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
    | logik _ _ he => dsimp only; exact AusgangGleich.logik he
    | hardware _ _ he => dsimp only; exact AusgangGleich.hardware he
    | why _ _ r₁ _ _ _ _ => exact Fin.elim0 (Fin.cast hr r₁)
theorem constEndGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Endblock c.D V l Γ []} (h : ConstEnd c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    EndGleich c (execEnd O₁ p₁ R₁ body σ₁ ρ₁) (execEnd O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .ret hres =>
    match hres with
    | .empty => simp only [execEnd]; exact EndGleich.zurueck hW.1 hW.2 rfl
    | .val he =>
      have hev := constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ
      simp only [execEnd, evalErg, hev]
      exact EndGleich.zurueck hW.1 hW.2 rfl
  | .cons hs hrest =>
    simp only [execEnd]
    cases constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree with
    | ok _ _ _ _ hS hG hρ' => exact constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ hρ' agree
    | zurueck _ _ _ _ hS hG hv' => dsimp only; exact EndGleich.zurueck hS hG hv'
    | why _ _ _ _ hS hG hr' => dsimp only; exact EndGleich.why hS hG hr'
    | leave _ _ _ _ _ _ hEq hS hG hρ' => dsimp only; exact EndGleich.leave hEq hS hG hρ'
    | next _ _ _ _ _ _ hEq hS hG hρ' => dsimp only; exact EndGleich.next hEq hS hG hρ'
    | logik _ _ he => dsimp only; exact EndGleich.logik he
    | hardware _ _ he => dsimp only; exact EndGleich.hardware he
  | .bind hv hrest =>
    have hvEq := constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd, hvEq]
    cases constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ _ _ hW (.cons rfl hρ) agree with
    | zurueck _ _ _ _ hS hG hv' => simp only [EndAusgang.schrumpf]; exact EndGleich.zurueck hS hG hv'
    | why _ _ _ _ hS hG hr' => simp only [EndAusgang.schrumpf]; exact EndGleich.why hS hG hr'
    | leave _ _ _ _ _ _ hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.leave hEq hS hG (envGleichTail c hρ')
    | next _ _ _ _ _ _ hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.next hEq hS hG (envGleichTail c hρ')
    | logik _ _ he => simp only [EndAusgang.schrumpf]; exact EndGleich.logik he
    | hardware _ _ he => simp only [EndAusgang.schrumpf]; exact EndGleich.hardware he
  | .bindCall _ _ _ _ hr _ _ hargs hrest =>
    have harg := constEvalGleichArgs c hargs σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    rw [harg]
    cases (agree _ σ₁ σ₂ (evalArgs σ₂ _ σ₂ ρ₂) hW) with
    | ok _ _ v₁ v₂ hS hG hv =>
      dsimp only
      have herg : ergWert _ v₁ = ergWert _ v₂ := by rw [hv]
      cases constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree with
      | zurueck _ _ _ _ hS' hG' hv' => simp only [EndAusgang.schrumpf]; exact EndGleich.zurueck hS' hG' hv'
      | why _ _ _ _ hS' hG' hr' => simp only [EndAusgang.schrumpf]; exact EndGleich.why hS' hG' hr'
      | leave _ _ _ _ _ _ hEq hS' hG' hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.leave hEq hS' hG' (envGleichTail c hρ')
      | next _ _ _ _ _ _ hEq hS' hG' hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.next hEq hS' hG' (envGleichTail c hρ')
      | logik _ _ he => simp only [EndAusgang.schrumpf]; exact EndGleich.logik he
      | hardware _ _ he => simp only [EndAusgang.schrumpf]; exact EndGleich.hardware he
    | logik _ _ he => dsimp only; exact EndGleich.logik he
    | hardware _ _ he => dsimp only; exact EndGleich.hardware he
    | why _ _ r₁ _ _ _ _ => exact Fin.elim0 (Fin.cast hr r₁)
  | .ite hc hyes hno =>
    have hcEq := constEvalGleichExpr c hc σ₁ σ₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd, hcEq]
    by_cases hcond : wahr? (eval σ₂ _ σ₂ ρ₂) = true
    · simp only [if_pos hcond]
      exact constEndGleich c hyes O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
    · simp only [if_neg hcond]
      exact constEndGleich c hno O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
theorem constArmsGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : Arms c.D V l Γ [] [] cs} (h : ConstArms c arms)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v₁ v₂ : Wert c.D (.sum cs)) (hv : v₁ = v₂)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execArms O₁ p₁ R₁ arms v₁ σ₁ ρ₁) (execArms O₂ p₂ R₂ arms v₂ σ₂ ρ₂) :=
  match h with
  | .nil =>
    have _ := hv
    obtain ⟨i, _⟩ := v₁
    exact i.elim0
  | .cons hbody hrest =>
    subst hv
    obtain ⟨⟨tag, htag⟩, nutz⟩ := v₂
    cases tag with
    | zero =>
      simp only [execArms]
      exact schrumpfArmGleich c (constBlockGleich c hbody O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ _ _ hW (armEnvGleich c nutz hρ) agree)
    | succ _ =>
      simp only [execArms]
      exact constArmsGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
theorem constReasonGleich (c : ConstProgram) {V : vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : GrundArms c.D V l Γ [] [] n} (h : ConstReasonArms c arms)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v₁ v₂ : Fin n) (hv : v₁ = v₂)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execGrund O₁ p₁ R₁ arms v₁ σ₁ ρ₁) (execGrund O₂ p₂ R₂ arms v₂ σ₂ ρ₂) :=
  match h with
  | .nil =>
    have _ := hv
    exact Fin.elim0 v₁
  | .cons hbody hrest =>
    subst hv
    cases v₂ with
    | mk tag _ =>
      cases tag with
      | zero =>
        simp only [execGrund]
        exact constBlockGleich c hbody O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
      | succ _ =>
        simp only [execGrund]
        exact constReasonGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
end

/-- The transported body of `ConstAdmissible` runs like the raw body
    `rufAt` uses. -/
theorem constRumpfTransport (c : ConstProgram) (f : c.D.Fn) (O : Orakel c.D) (passes : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D (c.D.params f)) :
    execEnd O passes R (c.emptyEntry f ▸ c.P.rumpf f) σ ρ = execEnd O passes R (c.P.rumpf f) σ ρ := by
  cases c.emptyEntry f

/-- Calls agree across worlds, oracles and pass counts at a common depth:
    induction on the fuel with the handler premise carried by itself. -/
theorem constRufGleich (c : ConstProgram) (hadm : ConstAdmissible c) :
    ∀ (d : Nat) (g : c.D.Fn) (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g))
      (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat),
      WeltRahmen c σ₁ σ₂ →
      RufGleich c (rufAt c.P O₁ p₁ d g σ₁ ρ) (rufAt c.P O₂ p₂ d g σ₂ ρ) := by
  intro d
  induction d with
  | zero =>
    intro g σ₁ σ₂ ρ O₁ O₂ p₁ p₂ hW
    simp only [rufAt]
    exact RufGleich.logik rfl
  | succ d ih =>
    intro g σ₁ σ₂ ρ O₁ O₂ p₁ p₂ hW
    rw [rufAt_succ_eq (c.P) O₁ p₁ d, rufAt_succ_eq (c.P) O₂ p₂ d]
    simp only [rufSchritt]
    have hW0 := constWeltRahmenAlle c σ₁ σ₂
    have hreq : wahr? (eval (σ₁.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.requires g) (σ₁.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) ρ) = wahr? (eval (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.requires g) (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) ρ) :=
      congrArg wahr? (eval_spurfrei (c.P.requires g) _ _ _ _ hW0.1 hW0.2 hW0.1 hW0.2 ρ)
    rw [hreq]
    by_cases hgate : wahr? (eval (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.requires g) (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) ρ) = false
    · simp only [if_pos hgate]
      exact RufGleich.logik rfl
    · simp only [if_neg hgate]
      have hbridge₁ := constRumpfTransport c g O₁ p₁ (rufAt c.P O₁ p₁ d) _ _
      have hbridge₂ := constRumpfTransport c g O₂ p₂ (rufAt c.P O₂ p₂ d) _ _
      have hbody := constEndGleich c (hadm g) O₁ O₂ p₁ p₂ (rufAt c.P O₁ p₁ d) (rufAt c.P O₂ p₂ d) _ _ _ _ ⟨hW0.1, hW0.2⟩ (envGleichRefl c _) (fun h s₁ s₂ r w => ih h s₁ s₂ r O₁ O₂ p₁ p₂ w)
      rw [hbridge₁, hbridge₂] at hbody
      cases hbody with
      | zurueck s1 s2 w1 w2 hS hG hv =>
        have hρe : ergEnv (c.D.erg g) w1 ρ = ergEnv (c.D.erg g) w2 ρ := by rw [hv]
        have hens : wahr? (eval (σ₁.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.ensures g) (s1.lese (vertragVon c.D g).ende (c.P.ensures g).orte) (ergEnv (c.D.erg g) w1 ρ)) = wahr? (eval (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.ensures g) (s2.lese (vertragVon c.D g).ende (c.P.ensures g).orte) (ergEnv (c.D.erg g) w2 ρ)) := by
          rw [hρe]
          exact congrArg wahr? (eval_spurfrei (c.P.ensures g) _ _ _ _ hW0.1 hW0.2 hS hG _)
        simp only [hens]
        by_cases hensgate : wahr? (eval (σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte) (c.P.ensures g) (s2.lese (vertragVon c.D g).ende (c.P.ensures g).orte) (ergEnv (c.D.erg g) w2 ρ)) = false
        · simp only [if_pos hensgate]
          exact RufGleich.logik rfl
        · simp only [if_neg hensgate]
          have hempty : c.D.invs = [] := by cases h : c.D.invs with | nil => rfl | cons i _ => exact (c.noInvariants i).elim
          rw [hempty]
          dsimp only
          exact RufGleich.ok hS hG hv
      | logik _ _ he => dsimp only; exact RufGleich.logik he
      | hardware _ _ he => dsimp only; exact RufGleich.hardware he
      | why _ _ _ _ hS hG hr' => dsimp only; exact RufGleich.why hS hG hr'
      | leave h1 _ _ _ _ _ _ _ _ _ => cases h1
      | next h1 _ _ _ _ _ _ _ _ _ => cases h1

end Gabbro.Grammatik
