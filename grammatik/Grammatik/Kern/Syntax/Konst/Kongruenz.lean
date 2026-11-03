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
theorem schrumpfArmGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {k : Option Ty} {o₁ : Ausgang V l (ArmCtx Γ k)} {o₂ : Ausgang V l (ArmCtx Γ k)}
    (h : AusgangGleich c o₁ o₂) :
    AusgangGleich c (o₁.schrumpfArm k) (o₂.schrumpfArm k) := by
  cases k with
  | none => simp only [Ausgang.schrumpfArm]; exact h
  | some _ =>
    simp only [Ausgang.schrumpfArm]
    cases h with
    | ok hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
    | zurueck hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
    | why hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
    | leave hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
    | next hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
    | logik he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
    | hardware he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he

/-- Resource-index transport does not change execution. Generalize both
    endpoints before eliminating the equality of resource lists. -/
private theorem constExecStmtCast (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ X Y : List (Res c.D)} (h : X = Y) (body : Stmt c.D V l Γ Λ X)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ) :
    execStmt O p R (h ▸ body) σ ρ = execStmt O p R body σ ρ := by
  cases h
  rfl

private theorem constExecBlockCast (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {X Y Λ : List (Res c.D)} (h : X = Y) (body : Block c.D V l Γ X Λ)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ) :
    execBlock O p R (h ▸ body) σ ρ = execBlock O p R body σ ρ := by
  cases h
  rfl

private theorem constExecEndCast (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {X Y : List (Res c.D)} (h : X = Y) (body : Endblock c.D V l Γ X)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ) :
    execEnd O p R (h ▸ body) σ ρ = execEnd O p R body σ ρ := by
  cases h
  rfl

private theorem constEvalGleichResult (c : ConstProgram) {Γ : Ctx} {τ : Option Ty}
    {e : ErgExpr c.D Γ [] τ} (hp : ConstResult c e)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂) :
    evalErg σ₁ e σ₁ ρ₁ = evalErg σ₂ e σ₂ ρ₂ :=
  match hp with
  | .empty => rfl
  | .val he => constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ

mutual
theorem constStmtGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Stmt c.D V l Γ [] []} (h : ConstStmt c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execStmt O₁ p₁ R₁ body σ₁ ρ₁) (execStmt O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .assignVar (e := e) he => by
    have hv := constEvalGleichExpr c he (σ₁.lese [] e.orte) (σ₂.lese [] e.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    refine AusgangGleich.ok hW.1 hW.2 ?_
    exact envGleichSet c hρ _ _ _ hv
  | .ite (condition := condition) hc hyes hno => by
    let s₁ := σ₁.lese [] condition.orte
    let s₂ := σ₂.lese [] condition.orte
    have hcEq := constEvalGleichExpr c hc (σ₁.lese [] condition.orte) (σ₂.lese [] condition.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hcEq]
    by_cases hcond : wahr? (eval (σ₂.lese [] condition.orte) condition (σ₂.lese [] condition.orte) ρ₂) = true
    · simp only [if_pos hcond]
      exact constBlockGleich c hyes O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
    · simp only [if_neg hcond]
      exact constBlockGleich c hno O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .onOption (value := value) hv hpresent habsent => by
    let s₁ := σ₁.lese [] value.orte
    let s₂ := σ₂.lese [] value.orte
    have hvEq := constEvalGleichExpr c hv (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    cases hval : (eval s₂ value s₂ ρ₂ : Option _) with
    | none =>
      simp only [hval]
      exact constBlockGleich c habsent O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
    | some k =>
      simp only [hval]
      have hh := constBlockGleich c hpresent O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ) agree
      generalize execBlock O₁ p₁ R₁ _ _ _ = o₁ at hh ⊢
      generalize execBlock O₂ p₂ R₂ _ _ _ = o₂ at hh ⊢
      cases hh with
      | ok hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
      | zurueck hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
      | why hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
      | leave hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
      | next hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
      | logik he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
      | hardware he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
  | .onTag (value := value) hv harms => by
    let s₁ := σ₁.lese [] value.orte
    let s₂ := σ₂.lese [] value.orte
    have hvEq := constEvalGleichExpr c hv (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constArmsGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .onWhy (reason := reason) hv harms => by
    let s₁ := σ₁.lese [] reason.orte
    let s₂ := σ₂.lese [] reason.orte
    have hvEq := constEvalGleichExpr c hv (σ₁.lese [] reason.orte) (σ₂.lese [] reason.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constReasonGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .call f args hp hr resourceEq hargs => by
    let s₁ := σ₁.lese [] args.orte
    let s₂ := σ₂.lese [] args.orte
    have harg := constEvalGleichArgs c hargs (σ₁.lese [] args.orte) (σ₂.lese [] args.orte) ρ₁ ρ₂ hW hρ
    rw [constExecStmtCast c, constExecStmtCast c]
    simp only [execStmt]
    rw [harg]
    have hh := agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW
    generalize R₁ f s₁ _ = r₁ at hh ⊢
    generalize R₂ f s₂ _ = r₂ at hh ⊢
    cases hh with
    | ok hS hG _ => dsimp only; exact AusgangGleich.ok hS hG hρ
    | logik he => dsimp only; exact AusgangGleich.logik he
    | hardware he => dsimp only; exact AusgangGleich.hardware he
    | why hS hG hreason =>
      exact Fin.elim0 (Fin.cast hr (by assumption))
  | .ret (value := value) hres => by
    have hev := constEvalGleichResult c hres (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    exact AusgangGleich.zurueck hW.1 hW.2 hev
theorem constBlockGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Block c.D V l Γ [] []} (h : ConstBlock c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execBlock O₁ p₁ R₁ body σ₁ ρ₁) (execBlock O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .nil => by simp only [execBlock]; exact AusgangGleich.ok hW.1 hW.2 hρ
  | .cons hs hrest => by
    simp only [execBlock]
    have hh := constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
    generalize execStmt O₁ p₁ R₁ _ _ _ = o₁ at hh ⊢
    generalize execStmt O₂ p₂ R₂ _ _ _ = o₂ at hh ⊢
    cases hh with
    | ok hS hG hρ' => exact constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ hρ' agree
    | zurueck hS hG hv' => dsimp only; exact AusgangGleich.zurueck hS hG hv'
    | why hS hG hr' => dsimp only; exact AusgangGleich.why hS hG hr'
    | leave hEq hS hG hρ' => dsimp only; exact AusgangGleich.leave hEq hS hG hρ'
    | next hEq hS hG hρ' => dsimp only; exact AusgangGleich.next hEq hS hG hρ'
    | logik he => dsimp only; exact AusgangGleich.logik he
    | hardware he => dsimp only; exact AusgangGleich.hardware he
  | .bind (value := value) hv hrest => by
    let s₁ := σ₁.lese [] value.orte
    let s₂ := σ₂.lese [] value.orte
    have hvEq := constEvalGleichExpr c hv (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execBlock]
    have hh := constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) (.cons (eval (σ₁.lese [] value.orte) value (σ₁.lese [] value.orte) ρ₁) ρ₁) (.cons (eval (σ₂.lese [] value.orte) value (σ₂.lese [] value.orte) ρ₂) ρ₂) hW (.cons hvEq hρ) agree
    generalize execBlock O₁ p₁ R₁ _ _ _ = o₁ at hh ⊢
    generalize execBlock O₂ p₂ R₂ _ _ _ = o₂ at hh ⊢
    cases hh with
    | ok hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS hG (envGleichTail c hρ')
    | zurueck hS hG hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS hG hv'
    | why hS hG hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS hG hr'
    | leave hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS hG (envGleichTail c hρ')
    | next hEq hS hG hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS hG (envGleichTail c hρ')
    | logik he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
    | hardware he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
  | .bindCall f args he hp hr resourceEq rest hargs hrest => by
    let s₁ := σ₁.lese [] args.orte
    let s₂ := σ₂.lese [] args.orte
    have harg := constEvalGleichArgs c hargs (σ₁.lese [] args.orte) (σ₂.lese [] args.orte) ρ₁ ρ₂ hW hρ
    simp only [execBlock]
    rw [harg]
    have hh := agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW
    generalize R₁ f s₁ _ = r₁ at hh ⊢
    generalize R₂ f s₂ _ = r₂ at hh ⊢
    cases hh with
    | ok hS hG hv =>
      dsimp only
      have herg := congrArg (ergWert he) hv
      have hrec := constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree
      simp only [constExecBlockCast c] at hrec
      generalize execBlock O₁ p₁ R₁ _ _ _ = o₁ at hrec ⊢
      generalize execBlock O₂ p₂ R₂ _ _ _ = o₂ at hrec ⊢
      cases hrec with
      | ok hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.ok hS' hG' (envGleichTail c hρ')
      | zurueck hS' hG' hv' => simp only [Ausgang.schrumpf]; exact AusgangGleich.zurueck hS' hG' hv'
      | why hS' hG' hr' => simp only [Ausgang.schrumpf]; exact AusgangGleich.why hS' hG' hr'
      | leave hEq hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.leave hEq hS' hG' (envGleichTail c hρ')
      | next hEq hS' hG' hρ' => simp only [Ausgang.schrumpf]; exact AusgangGleich.next hEq hS' hG' (envGleichTail c hρ')
      | logik he => simp only [Ausgang.schrumpf]; exact AusgangGleich.logik he
      | hardware he => simp only [Ausgang.schrumpf]; exact AusgangGleich.hardware he
    | logik he => dsimp only; exact AusgangGleich.logik he
    | hardware he => dsimp only; exact AusgangGleich.hardware he
    | why hS hG hreason =>
      exact Fin.elim0 (Fin.cast hr (by assumption))
theorem constEndGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Endblock c.D V l Γ []} (h : ConstEnd c body)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    EndGleich c (execEnd O₁ p₁ R₁ body σ₁ ρ₁) (execEnd O₂ p₂ R₂ body σ₂ ρ₂) :=
  match h with
  | .ret (value := value) hres => by
    have hev := constEvalGleichResult c hres (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    exact EndGleich.zurueck hW.1 hW.2 hev
  | .cons hs hrest => by
    simp only [execEnd]
    have hh := constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
    generalize execStmt O₁ p₁ R₁ _ _ _ = o₁ at hh ⊢
    generalize execStmt O₂ p₂ R₂ _ _ _ = o₂ at hh ⊢
    cases hh with
    | ok hS hG hρ' => exact constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ hρ' agree
    | zurueck hS hG hv' => dsimp only; exact EndGleich.zurueck hS hG hv'
    | why hS hG hr' => dsimp only; exact EndGleich.why hS hG hr'
    | leave hEq hS hG hρ' => dsimp only; exact EndGleich.leave hEq hS hG hρ'
    | next hEq hS hG hρ' => dsimp only; exact EndGleich.next hEq hS hG hρ'
    | logik he => dsimp only; exact EndGleich.logik he
    | hardware he => dsimp only; exact EndGleich.hardware he
  | .bind (value := value) hv hrest => by
    let s₁ := σ₁.lese [] value.orte
    let s₂ := σ₂.lese [] value.orte
    have hvEq := constEvalGleichExpr c hv (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    have hh := constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ (σ₁.lese [] value.orte) (σ₂.lese [] value.orte) (.cons (eval (σ₁.lese [] value.orte) value (σ₁.lese [] value.orte) ρ₁) ρ₁) (.cons (eval (σ₂.lese [] value.orte) value (σ₂.lese [] value.orte) ρ₂) ρ₂) hW (.cons hvEq hρ) agree
    generalize execEnd O₁ p₁ R₁ _ _ _ = o₁ at hh ⊢
    generalize execEnd O₂ p₂ R₂ _ _ _ = o₂ at hh ⊢
    cases hh with
    | zurueck hS hG hv' => simp only [EndAusgang.schrumpf]; exact EndGleich.zurueck hS hG hv'
    | why hS hG hr' => simp only [EndAusgang.schrumpf]; exact EndGleich.why hS hG hr'
    | leave hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.leave hEq hS hG (envGleichTail c hρ')
    | next hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.next hEq hS hG (envGleichTail c hρ')
    | logik he => simp only [EndAusgang.schrumpf]; exact EndGleich.logik he
    | hardware he => simp only [EndAusgang.schrumpf]; exact EndGleich.hardware he
  | .bindCall f args he hp hr resourceEq rest hargs hrest => by
    let s₁ := σ₁.lese [] args.orte
    let s₂ := σ₂.lese [] args.orte
    have harg := constEvalGleichArgs c hargs (σ₁.lese [] args.orte) (σ₂.lese [] args.orte) ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    rw [harg]
    have hh := agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW
    generalize R₁ f s₁ _ = r₁ at hh ⊢
    generalize R₂ f s₂ _ = r₂ at hh ⊢
    cases hh with
    | ok hS hG hv =>
      dsimp only
      have herg := congrArg (ergWert he) hv
      have hrec := constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree
      simp only [constExecEndCast c] at hrec
      generalize execEnd O₁ p₁ R₁ _ _ _ = o₁ at hrec ⊢
      generalize execEnd O₂ p₂ R₂ _ _ _ = o₂ at hrec ⊢
      cases hrec with
      | zurueck hS' hG' hv' => simp only [EndAusgang.schrumpf]; exact EndGleich.zurueck hS' hG' hv'
      | why hS' hG' hr' => simp only [EndAusgang.schrumpf]; exact EndGleich.why hS' hG' hr'
      | leave hEq hS' hG' hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.leave hEq hS' hG' (envGleichTail c hρ')
      | next hEq hS' hG' hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.next hEq hS' hG' (envGleichTail c hρ')
      | logik he => simp only [EndAusgang.schrumpf]; exact EndGleich.logik he
      | hardware he => simp only [EndAusgang.schrumpf]; exact EndGleich.hardware he
    | logik he => dsimp only; exact EndGleich.logik he
    | hardware he => dsimp only; exact EndGleich.hardware he
    | why hS hG hreason =>
      exact Fin.elim0 (Fin.cast hr (by assumption))
  | .ite (condition := condition) hc hyes hno => by
    let s₁ := σ₁.lese [] condition.orte
    let s₂ := σ₂.lese [] condition.orte
    have hcEq := constEvalGleichExpr c hc (σ₁.lese [] condition.orte) (σ₂.lese [] condition.orte) ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    rw [hcEq]
    by_cases hcond : wahr? (eval (σ₂.lese [] condition.orte) condition (σ₂.lese [] condition.orte) ρ₂) = true
    · simp only [if_pos hcond]
      exact constEndGleich c hyes O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
    · simp only [if_neg hcond]
      exact constEndGleich c hno O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
theorem constArmsGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : Arms c.D V l Γ [] [] cs} (h : ConstArms c arms)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v₁ v₂ : Wert c.D (.sum cs)) (hv : v₁ = v₂)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execArms O₁ p₁ R₁ arms v₁ σ₁ ρ₁) (execArms O₂ p₂ R₂ arms v₂ σ₂ ρ₂) :=
  match cs, arms, h, v₁, v₂, hv with
  | _, _, .nil, v₁, v₂, hv => by
    have _ := hv
    obtain ⟨i, _⟩ := v₁
    exact i.elim0
  | _, _, .cons hbody hrest, v₁, v₂, hv => by
    subst hv
    obtain ⟨⟨tag, htag⟩, nutz⟩ := v₁
    cases tag with
    | zero =>
      simp only [execArms]
      exact schrumpfArmGleich c (constBlockGleich c hbody O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ _ _ hW (armEnvGleich c nutz hρ) agree)
    | succ _ =>
      simp only [execArms]
      exact constArmsGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl σ₁ σ₂ ρ₁ ρ₂ hW hρ agree
theorem constReasonGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : GrundArms c.D V l Γ [] [] n} (h : ConstReasonArms c arms)
    (O₁ O₂ : Orakel c.D) (p₁ p₂ : Nat)
    (R₁ R₂ : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v₁ v₂ : Fin n) (hv : v₁ = v₂)
    (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ)
    (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂)
    (agree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ → RufGleich c (R₁ g σ₁ ρ) (R₂ g σ₂ ρ)) :
    AusgangGleich c (execGrund O₁ p₁ R₁ arms v₁ σ₁ ρ₁) (execGrund O₂ p₂ R₂ arms v₂ σ₂ ρ₂) :=
  match n, arms, h, v₁, v₂, hv with
  | _, _, .nil, v₁, v₂, hv => by
    have _ := hv
    exact Fin.elim0 v₁
  | _, _, .cons hbody hrest, v₁, v₂, hv => by
    subst hv
    cases v₁ with
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
  exact constExecEndCast c (c.emptyEntry f) (c.P.rumpf f) O passes R σ ρ

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
    generalize hs₁def : σ₁.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte = s₁
    generalize hs₂def : σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte = s₂
    have hW0 := constWeltRahmenAlle c s₁ s₂
    have hreq : wahr? (eval s₁ (c.P.requires g) s₁ ρ) =
        wahr? (eval s₂ (c.P.requires g) s₂ ρ) :=
      congrArg wahr? (eval_spurfrei (c.P.requires g) s₁ s₂ s₁ s₂ hW0.1 hW0.2 hW0.1 hW0.2 ρ)
    rw [hreq]
    by_cases hgate : wahr? (eval s₂ (c.P.requires g) s₂ ρ) = false
    · simp only [if_pos hgate]
      exact RufGleich.logik rfl
    · simp only [if_neg hgate]
      have hbridge₁ := constRumpfTransport c g O₁ p₁ (rufAt c.P O₁ p₁ d) s₁ ρ
      have hbridge₂ := constRumpfTransport c g O₂ p₂ (rufAt c.P O₂ p₂ d) s₂ ρ
      have hbody := constEndGleich c (hadm g) O₁ O₂ p₁ p₂
        (rufAt c.P O₁ p₁ d) (rufAt c.P O₂ p₂ d) s₁ s₂ ρ ρ hW0
        (envGleichRefl c ρ) (fun h s₁ s₂ r w => ih h s₁ s₂ r O₁ O₂ p₁ p₂ w)
      rw [hbridge₁, hbridge₂] at hbody
      generalize execEnd O₁ p₁ _ _ _ _ = o₁ at hbody ⊢
      generalize execEnd O₂ p₂ _ _ _ _ = o₂ at hbody ⊢
      cases hbody with
      | @zurueck w1 w2 s1 s2 hS hG hv =>
        have hρe : ergEnv (c.D.erg g) w1 ρ = ergEnv (c.D.erg g) w2 ρ := by rw [hv]
        have hempty : c.D.invs = [] := by
          cases h : c.D.invs with
          | nil => rfl
          | cons i _ => exact (c.noInvariants i).elim
        have hens : wahr? (eval s₁ (c.P.ensures g)
              (s1.lese (Vertrag.ende c.D (vertragVon c.D g)) (c.P.ensures g).orte)
              (ergEnv (c.D.erg g) w1 ρ)) =
            wahr? (eval s₂ (c.P.ensures g)
              (s2.lese (Vertrag.ende c.D (vertragVon c.D g)) (c.P.ensures g).orte)
              (ergEnv (c.D.erg g) w2 ρ)) := by
          rw [hρe]
          exact congrArg wahr? (eval_spurfrei (c.P.ensures g) s₁ s₂ _ _ hW0.1 hW0.2
            (constWeltRahmenAlle c _ _).1 (constWeltRahmenAlle c _ _).2 _)
        dsimp only
        rw [hens]
        by_cases hensgate : wahr? (eval s₂ (c.P.ensures g)
            (s2.lese (Vertrag.ende c.D (vertragVon c.D g)) (c.P.ensures g).orte)
            (ergEnv (c.D.erg g) w2 ρ)) = false
        · rw [if_pos hensgate, if_pos hensgate]
          exact RufGleich.logik rfl
        · rw [if_neg hensgate, if_neg hensgate, hempty]
          simp only [List.filter_nil, List.foldl_nil, List.find?_nil]
          exact RufGleich.ok (constWeltRahmenAlle c _ _).1 (constWeltRahmenAlle c _ _).2 hv
      | logik he => dsimp only; exact RufGleich.logik he
      | hardware he => dsimp only; exact RufGleich.hardware he
      | why hS hG hr' => dsimp only; exact RufGleich.why hS hG hr'
      | leave hEq hS hG hρ' =>
        have hfalse : false = true := by assumption
        cases hfalse
      | next hEq hS hG hρ' =>
        have hfalse : false = true := by assumption
        cases hfalse

end Gabbro.Grammatik
