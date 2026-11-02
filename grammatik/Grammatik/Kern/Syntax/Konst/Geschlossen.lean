module

public import Grammatik.Kern.Syntax.Konst.Programm
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Closed integer arguments.

   A const call is evaluated at compile time, so its arguments must be
   closed: no variables, no binders, no places. `GeschlossenExpr` is
   that variable-free integer fragment (literals, widening and the
   integer operations); `GeschlossenArgs` lifts it to call arguments.
   Closed arguments evaluate independently of the environment and read
   no places, so evaluating them appends no trace event. Anything
   outside this fragment keeps the program refused. -/

/-- Variable-free integer expressions: closed under literals,
    widening and the integer operations. -/
inductive GeschlossenExpr (c : ConstProgram) : {Γ : Ctx} → {τ : Ty} → Expr c.D Γ [] τ → Prop where
  | lit (n : Int) : GeschlossenExpr c (.lit n)
  | widen : GeschlossenExpr c e → GeschlossenExpr c (.widen h1 h2 e)
  | neg : GeschlossenExpr c a → GeschlossenExpr c (.neg a)
  | add : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.add a b)
  | sub : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.sub a b)
  | mul : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.mul a b)
  | div : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.div h0 h1p a b)
  | rem : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.rem h0 h1p a b)
  | sdiv : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.sdiv hb a b)
  | srem : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.srem hb a b)
  | band : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.band h0 h0p a b)
  | bor : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.bor w h0 h0p hw1 hw2 a b)
  | bxor : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.bxor w h0 h0p hw1 hw2 a b)
  | shl : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.shl w hw1 hw2 h0 h0p a b)
  | shr : GeschlossenExpr c a → GeschlossenExpr c b → GeschlossenExpr c (.shr w hw1 hw2 h0 h0p a b)

/-- Closed call arguments: every argument expression is closed. -/
inductive GeschlossenArgs (c : ConstProgram) : {Γ : Ctx} → {ts : List Ty} → Args c.D Γ [] ts → Prop where
  | nil : GeschlossenArgs c .nil
  | cons : GeschlossenExpr c e → GeschlossenArgs c rest → GeschlossenArgs c (.cons e rest)

/-- Closed expressions evaluate independently of the environment. -/
theorem geschlossen_eval (c : ConstProgram) {Γ : Ctx} {τ : Ty} {e : Expr c.D Γ [] τ}
    (h : GeschlossenExpr c e) (σ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) :
    eval σ e σ ρ₁ = eval σ e σ ρ₂ :=
  match h with
  | .lit _ => by simp only [eval]
  | .widen ha => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂]
  | .neg ha => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂]
  | .add ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .sub ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .mul ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .div ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .rem ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .sdiv ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .srem ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .band ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .bor ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .bxor ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .shl ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]
  | .shr ha hb => by simp only [eval, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_eval c hb σ ρ₁ ρ₂]

/-- Closed expressions read no places. -/
theorem geschlossen_orte (c : ConstProgram) {Γ : Ctx} {τ : Ty} {e : Expr c.D Γ [] τ}
    (h : GeschlossenExpr c e) : e.orte = [] :=
  match h with
  | .lit _ => by simp only [Expr.orte]
  | .widen ha => by simp only [Expr.orte, geschlossen_orte c ha]
  | .neg ha => by simp only [Expr.orte, geschlossen_orte c ha]
  | .add ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .sub ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .mul ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .div ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .rem ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .sdiv ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .srem ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .band ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .bor ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .bxor ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .shl ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]
  | .shr ha hb => by simp only [Expr.orte, geschlossen_orte c ha, geschlossen_orte c hb]

/-- Closed arguments evaluate independently of the environment. -/
theorem geschlossen_args_eval (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {args : Args c.D Γ [] τs}
    (h : GeschlossenArgs c args) (σ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) :
    evalArgs σ args σ ρ₁ = evalArgs σ args σ ρ₂ :=
  match h with
  | .nil => by simp only [evalArgs]
  | .cons ha hr => by
    simp only [evalArgs, geschlossen_eval c ha σ ρ₁ ρ₂, geschlossen_args_eval c hr σ ρ₁ ρ₂]

/-- Closed arguments read no places. -/
theorem geschlossen_args_orte (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {args : Args c.D Γ [] τs}
    (h : GeschlossenArgs c args) : args.orte = [] :=
  match h with
  | .nil => by simp only [Args.orte]
  | .cons ha hr => by
    simp only [Args.orte, geschlossen_orte c ha, geschlossen_args_orte c hr]

end Gabbro.Grammatik
