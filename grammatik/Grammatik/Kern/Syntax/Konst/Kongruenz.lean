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
    have hcEq := constEvalGleichExpr c hc s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt, hcEq]
    by_cases hcond : wahr? (eval s₂ condition s₂ ρ₂) = true
    · simp only [if_pos hcond]
      exact constBlockGleich c hyes O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
    · simp only [if_neg hcond]
      exact constBlockGleich c hno O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .onOption (value := value) hv hpresent habsent => by
    let s₁ := σ₁.lese [] value.orte
    let s₂ := σ₂.lese [] value.orte
    have hvEq := constEvalGleichExpr c hv s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    cases hval : (eval s₂ value s₂ ρ₂ : Option _) with
    | none =>
      simp only [hval]
      exact constBlockGleich c habsent O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ ρ₁ ρ₂ hW hρ agree
    | some k =>
      simp only [hval]
      cases constBlockGleich c hpresent O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ) agree with
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
    have hvEq := constEvalGleichExpr c hv s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constArmsGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .onWhy (reason := reason) hv harms => by
    let s₁ := σ₁.lese [] reason.orte
    let s₂ := σ₂.lese [] reason.orte
    have hvEq := constEvalGleichExpr c hv s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execStmt]
    rw [hvEq]
    exact constReasonGleich c harms O₁ O₂ p₁ p₂ R₁ R₂ _ _ rfl s₁ s₂ ρ₁ ρ₂ hW hρ agree
  | .call f args hp hr resourceEq hargs => by
    let s₁ := σ₁.lese [] args.orte
    let s₂ := σ₂.lese [] args.orte
    have harg := constEvalGleichArgs c hargs s₁ s₂ ρ₁ ρ₂ hW hρ
    rw [constExecStmtCast c, constExecStmtCast c]
    simp only [execStmt]
    rw [harg]
    cases (agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW) with
    | ok hS hG _ => dsimp only; exact AusgangGleich.ok hS hG hρ
    | logik he => dsimp only; exact AusgangGleich.logik he
    | hardware he => dsimp only; exact AusgangGleich.hardware he
    | why hS hG hreason =>
      rename_i s₁' s₂' r₁ r₂
      exact Fin.elim0 (Fin.cast hr r₁)
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
    cases constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree with
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
    have hvEq := constEvalGleichExpr c hv s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execBlock, hvEq]
    cases constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ _ _ hW (.cons rfl hρ) agree with
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
    have harg := constEvalGleichArgs c hargs s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execBlock]
    rw [harg]
    cases (agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW) with
    | ok hS hG hv =>
      dsimp only
      have herg := congrArg (ergWert he) hv
      have hrec := constBlockGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree
      simp only [constExecBlockCast c] at hrec
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
      rename_i s₁' s₂' r₁ r₂
      exact Fin.elim0 (Fin.cast hr r₁)
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
    cases constStmtGleich c hs O₁ O₂ p₁ p₂ R₁ R₂ σ₁ σ₂ ρ₁ ρ₂ hW hρ agree with
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
    have hvEq := constEvalGleichExpr c hv s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd, hvEq]
    cases constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ _ _ hW (.cons rfl hρ) agree with
    | zurueck hS hG hv' => simp only [EndAusgang.schrumpf]; exact EndGleich.zurueck hS hG hv'
    | why hS hG hr' => simp only [EndAusgang.schrumpf]; exact EndGleich.why hS hG hr'
    | leave hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.leave hEq hS hG (envGleichTail c hρ')
    | next hEq hS hG hρ' => simp only [EndAusgang.schrumpf]; exact EndGleich.next hEq hS hG (envGleichTail c hρ')
    | logik he => simp only [EndAusgang.schrumpf]; exact EndGleich.logik he
    | hardware he => simp only [EndAusgang.schrumpf]; exact EndGleich.hardware he
  | .bindCall f args he hp hr resourceEq rest hargs hrest => by
    let s₁ := σ₁.lese [] args.orte
    let s₂ := σ₂.lese [] args.orte
    have harg := constEvalGleichArgs c hargs s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd]
    rw [harg]
    cases (agree f s₁ s₂ (evalArgs s₂ args s₂ ρ₂) hW) with
    | ok hS hG hv =>
      dsimp only
      have herg := congrArg (ergWert he) hv
      have hrec := constEndGleich c hrest O₁ O₂ p₁ p₂ R₁ R₂ _ _ _ _ ⟨hS, hG⟩ (.cons herg hρ) agree
      simp only [constExecEndCast c] at hrec
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
      rename_i s₁' s₂' r₁ r₂
      exact Fin.elim0 (Fin.cast hr r₁)
  | .ite (condition := condition) hc hyes hno => by
    let s₁ := σ₁.lese [] condition.orte
    let s₂ := σ₂.lese [] condition.orte
    have hcEq := constEvalGleichExpr c hc s₁ s₂ ρ₁ ρ₂ hW hρ
    simp only [execEnd, hcEq]
    by_cases hcond : wahr? (eval s₂ condition s₂ ρ₂) = true
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
  match h with
  | .nil => by
    have _ := hv
    obtain ⟨i, _⟩ := v₁
    exact i.elim0
  | .cons hbody hrest => by
    subst hv
    obtain ⟨⟨tag, htag⟩, nutz⟩ := v₂
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
  match h with
  | .nil => by
    have _ := hv
    exact Fin.elim0 v₁
  | .cons hbody hrest => by
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
    let s₁ := σ₁.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte
    let s₂ := σ₂.lese (Signatur.anfang c.D (c.D.signatur g)) (c.P.requires g).orte
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
      cases hbody with
      | zurueck hS hG hv =>
        rename_i s1 s2 w1 w2
        have hρe : ergEnv (c.D.erg g) w1 ρ = ergEnv (c.D.erg g) w2 ρ := by rw [hv]
        let t₁ := s1.lese (vertragVon c.D g).ende (c.P.ensures g).orte
        let t₂ := s2.lese (vertragVon c.D g).ende (c.P.ensures g).orte
        have hens : wahr? (eval s₁ (c.P.ensures g) t₁ (ergEnv (c.D.erg g) w1 ρ)) =
            wahr? (eval s₂ (c.P.ensures g) t₂ (ergEnv (c.D.erg g) w2 ρ)) := by
          rw [hρe]
          exact congrArg wahr? (eval_spurfrei (c.P.ensures g) s₁ s₂ t₁ t₂ hW0.1 hW0.2 hS hG _)
        simp only [hens]
        by_cases hensgate : wahr? (eval s₂ (c.P.ensures g) t₂ (ergEnv (c.D.erg g) w2 ρ)) = false
        · simp only [if_pos hensgate]
          exact RufGleich.logik rfl
        · simp only [if_neg hensgate]
          have hempty : c.D.invs = [] := by cases h : c.D.invs with | nil => rfl | cons i _ => exact (c.noInvariants i).elim
          rw [hempty]
          dsimp only
          exact RufGleich.ok hS hG hv
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
