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
  -- Use definitional reduction, without generating the mutual evaluator's equation lemmas.
  | .lit _ => rfl
  | .widen (h1 := h1) (h2 := h2) ha =>
      congrArg (Zahl.weiter h1 h2) (geschlossen_eval c ha σ ρ₁ ρ₂)
  | .neg ha => congrArg Zahl.neg (geschlossen_eval c ha σ ρ₁ ρ₂)
  | .add (a := a) (b := b) ha hb =>
      show Zahl.add (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.add (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg Zahl.add (geschlossen_eval c ha σ ρ₁ ρ₂)) (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .sub (a := a) (b := b) ha hb =>
      show Zahl.sub (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.sub (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg Zahl.sub (geschlossen_eval c ha σ ρ₁ ρ₂)) (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .mul (a := a) (b := b) ha hb =>
      show Zahl.mul (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.mul (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg Zahl.mul (geschlossen_eval c ha σ ρ₁ ρ₂)) (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .div (a := a) (b := b) (h0 := h0) (h1p := h1p) ha hb =>
      show Zahl.div h0 h1p (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.div h0 h1p (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.div h0 h1p) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .rem (a := a) (b := b) (h0 := h0) (h1p := h1p) ha hb =>
      show Zahl.rem h0 h1p (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.rem h0 h1p (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.rem h0 h1p) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .sdiv (a := a) (b := b) (hb := hnonzero) ha hb =>
      show Zahl.sdiv hnonzero (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.sdiv hnonzero (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.sdiv hnonzero) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .srem (a := a) (b := b) (hb := hnonzero) ha hb =>
      show Zahl.srem hnonzero (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.srem hnonzero (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.srem hnonzero) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .band (a := a) (b := b) (h0 := h0) (h0p := h0p) ha hb =>
      show Zahl.band h0 h0p (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.band h0 h0p (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.band h0 h0p) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .bor (a := a) (b := b) (w := w) (h0 := h0) (h0p := h0p) (hw1 := hw1) (hw2 := hw2) ha hb =>
      show Zahl.bor w h0 h0p hw1 hw2 (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.bor w h0 h0p hw1 hw2 (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.bor w h0 h0p hw1 hw2) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .bxor (a := a) (b := b) (w := w) (h0 := h0) (h0p := h0p) (hw1 := hw1) (hw2 := hw2) ha hb =>
      show Zahl.bxor w h0 h0p hw1 hw2 (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.bxor w h0 h0p hw1 hw2 (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.bxor w h0 h0p hw1 hw2) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .shl (a := a) (b := b) (w := w) (hw1 := hw1) (hw2 := hw2) (h0 := h0) (h0p := h0p) ha hb =>
      show Zahl.shl w hw1 hw2 h0 h0p (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.shl w hw1 hw2 h0 h0p (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.shl w hw1 hw2 h0 h0p) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)
  | .shr (a := a) (b := b) (w := w) (hw1 := hw1) (hw2 := hw2) (h0 := h0) (h0p := h0p) ha hb =>
      show Zahl.shr w hw1 hw2 h0 h0p (eval σ a σ ρ₁) (eval σ b σ ρ₁) =
        Zahl.shr w hw1 hw2 h0 h0p (eval σ a σ ρ₂) (eval σ b σ ρ₂) from
      congr (congrArg (Zahl.shr w hw1 hw2 h0 h0p) (geschlossen_eval c ha σ ρ₁ ρ₂))
        (geschlossen_eval c hb σ ρ₁ ρ₂)

/-- Closed expressions read no places. -/
theorem geschlossen_orte (c : ConstProgram) {Γ : Ctx} {τ : Ty} {e : Expr c.D Γ [] τ}
    (h : GeschlossenExpr c e) : e.orte = [] :=
  match h with
  | .lit _ => rfl
  | .widen (e := a) ha => show a.orte = [] from geschlossen_orte c ha
  | .neg (a := a) ha => show a.orte = [] from geschlossen_orte c ha
  | .add ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .sub ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .mul ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .div ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .rem ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .sdiv ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .srem ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .band ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .bor ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .bxor ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .shl ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl
  | .shr ha hb =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_orte c hb)).trans rfl

/-- Closed arguments evaluate independently of the environment. -/
theorem geschlossen_args_eval (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {args : Args c.D Γ [] τs}
    (h : GeschlossenArgs c args) (σ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) :
    evalArgs σ args σ ρ₁ = evalArgs σ args σ ρ₂ :=
  match h with
  | .nil => rfl
  | .cons (e := e) (rest := rest) ha hr =>
      show Env.cons (eval σ e σ ρ₁) (evalArgs σ rest σ ρ₁) =
        Env.cons (eval σ e σ ρ₂) (evalArgs σ rest σ ρ₂) from
      congr (congrArg Env.cons (geschlossen_eval c ha σ ρ₁ ρ₂)) (geschlossen_args_eval c hr σ ρ₁ ρ₂)

/-- Closed arguments read no places. -/
theorem geschlossen_args_orte (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {args : Args c.D Γ [] τs}
    (h : GeschlossenArgs c args) : args.orte = [] :=
  match h with
  | .nil => rfl
  | .cons ha hr =>
      (congr (congrArg List.append (geschlossen_orte c ha)) (geschlossen_args_orte c hr)).trans rfl

end Gabbro.Grammatik
