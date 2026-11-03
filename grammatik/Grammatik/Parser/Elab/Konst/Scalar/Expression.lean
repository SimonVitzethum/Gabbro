module
public import Grammatik.Parser.Elab.Konst.Scalar.Model
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Uebersetze

/-- Source names resolve to their declared typed positions, including the ensures result. -/
abbrev Locals (Γ : Ctx) := List (String × Sigma (Var Γ))

def locals : (params : List (String × Ty)) → Locals (params.map Prod.snd)
  | [] => []
  | (name, τ) :: rest =>
    (name, ⟨τ, .here⟩) :: (locals rest).map (fun (n, ⟨t, x⟩) => (n, ⟨t, .there x⟩))

def integer {D : Deklaration} {Γ : Ctx} : SomeCode D Γ → Except String (Sigma fun lo => Sigma fun hi => Code D Γ (.int lo hi))
  | ⟨.int lo hi, code⟩ => .ok ⟨lo, hi, code⟩
  | _ => .error "const type failure: expected an integer expression"

def boolean {D : Deklaration} {Γ : Ctx} : SomeCode D Γ → Except String (Code D Γ .bool)
  | ⟨.bool, code⟩ => .ok code
  | _ => .error "const type failure: expected a Boolean predicate"

/-- The typed G operators are the only arithmetic implementation in this pass. -/
def binary {D : Deklaration} {Γ : Ctx} (op : String)
    (left right : SomeCode D Γ) : Except String (SomeCode D Γ) := do
  if op == "&&" then return ⟨.bool, Code.boolAnd (← boolean left) (← boolean right)⟩
  if op == "||" then return ⟨.bool, Code.boolOr (← boolean left) (← boolean right)⟩
  let ⟨l, h, a⟩ ← integer left
  let ⟨l', h', b⟩ ← integer right
  match op with
  | "+" => return ⟨_, Code.add a b⟩
  | "-" => return ⟨_, Code.sub a b⟩
  | "*" => return ⟨_, Code.mul a b⟩
  | "<" => return ⟨_, Code.less a b⟩
  | "<=" => return ⟨_, Code.lessEqual a b⟩
  | ">" => return ⟨_, Code.less b a⟩
  | ">=" => return ⟨_, Code.lessEqual b a⟩
  | "==" => return ⟨_, Code.equal a b⟩
  | "!=" => return ⟨_, Code.boolNot (Code.equal a b)⟩
  | "/" | "%" =>
    if h0 : 0 ≤ l then
      if h1 : 1 ≤ l' then
        if op == "/" then
          return ⟨_, ⟨.div h0 h1 a.expr b.expr,
            fun env => Zahl.div h0 h1 (a.denote env) (b.denote env), by
              intros; simp only [eval, a.equation, b.equation]⟩⟩
        else
          return ⟨_, ⟨.rem h0 h1 a.expr b.expr,
            fun env => Zahl.rem h0 h1 (a.denote env) (b.denote env), by
              intros; simp only [eval, a.equation, b.equation]⟩⟩
      else throw "const divisor range includes zero"
    else throw "const unsigned division requires a nonnegative numerator"
  | "&" =>
    if h0 : 0 ≤ l then
      if h1 : 0 ≤ l' then
        return ⟨_, ⟨.band h0 h1 a.expr b.expr,
          fun env => Zahl.band h0 h1 (a.denote env) (b.denote env), by
            intros; simp only [eval, a.equation, b.equation]⟩⟩
      else throw "const bit operand has a negative range"
    else throw "const bit operand has a negative range"
  | "|" | "^" =>
    if h0 : 0 ≤ l then
      if h1 : 0 ≤ l' then
        let width := max h.toNat.log2 h'.toNat.log2 + 1
        if hw : h < 2 ^ width ∧ h' < 2 ^ width then
          if op == "|" then
            return ⟨_, ⟨.bor width h0 h1 hw.1 hw.2 a.expr b.expr,
              fun env => Zahl.bor width h0 h1 hw.1 hw.2 (a.denote env) (b.denote env), by
                intros; simp only [eval, a.equation, b.equation]⟩⟩
          else
            return ⟨_, ⟨.bxor width h0 h1 hw.1 hw.2 a.expr b.expr,
              fun env => Zahl.bxor width h0 h1 hw.1 hw.2 (a.denote env) (b.denote env), by
                intros; simp only [eval, a.equation, b.equation]⟩⟩
        else throw "const bit width could not be certified"
      else throw "const bit operand has a negative range"
    else throw "const bit operand has a negative range"
  | _ => throw ("const expression without typed G operator: " ++ op)

/-- Elaborate the existing single-expression const fragment directly to typed G.
    Unsupported forms fail explicitly; no environment or call defaults to zero. -/
def expression {D : Deklaration} {Γ : Ctx} (names : Locals Γ) :
    SExpr → Except String (SomeCode D Γ)
  | .lit n => .ok ⟨_, Code.literal n⟩
  | .tru => .ok ⟨_, Code.truth true⟩
  | .fls => .ok ⟨_, Code.truth false⟩
  | .variable name =>
    match names.find? (fun entry => strEq entry.1 name) with
    | some (_, ⟨τ, x⟩) => .ok ⟨τ, Code.variable x⟩
    | none => .error ("const unresolved name: " ++ name)
  | .res =>
    match names.find? (fun entry => strEq entry.1 "result") with
    | some (_, ⟨τ, x⟩) => .ok ⟨τ, Code.variable x⟩
    | none => .error "const result outside ensures"
  | .un op source => do
    let code ← expression names source
    if op == "!" then return ⟨_, Code.boolNot (← boolean code)⟩
    else if op == "-" then
      let ⟨_, _, value⟩ ← integer code
      return ⟨_, Code.negate value⟩
    else throw ("const unary operator without G form: " ++ op)
  | .bin op left right => do
    binary op (← expression names left) (← expression names right)
  | .field (.variable ty) member =>
    match uTypName [] ty with
    | .ok (lo, hi) =>
      if member == "max" then .ok ⟨_, Code.literal hi⟩
      else if member == "min" then .ok ⟨_, Code.literal lo⟩
      else .error "const field without G form"
    | .error error => .error error
  | _ => .error "const expression without a source-to-G derivation"

/-- Bind the canonical evaluator's integers at exactly the original parameter types. -/
def arguments (D : Deklaration) : (params : List (String × Ty)) →
    List Int → Except String (Env D (params.map Prod.snd))
  | [], [] => .ok .nil
  | (_, .int lo hi) :: rest, value :: values => do
    if h : lo ≤ value ∧ value ≤ hi then
      return .cons ⟨value, h.1, h.2⟩ (← arguments D rest values)
    else throw "const argument outside its declared parameter range"
  | _, _ => .error "const argument type or arity mismatch"

/-- Contract predicates are conjoined in declaration order; other clauses cannot vanish. -/
def clauses {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (post : Bool) : List SKlausel → Except String (Code D Γ .bool)
  | [] => .ok (Code.truth true)
  | clause :: rest => do
    let tail ← clauses names post rest
    match clause with
    | .needs source =>
      if post then return tail
      else return Code.boolAnd (← boolean (← expression names source)) tail
    | .gives source =>
      if post then return Code.boolAnd (← boolean (← expression names source)) tail
      else return tail
    | .effs effects =>
      if effects.all (fun | .pure => true | _ => false) then return tail
      else throw "const effect clause is not pure"
    | _ => throw "const clause without a compile-time certificate"

/-- Accepted expressions retain their generic G denotation at every environment. -/
theorem expression_denotes {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (source : SExpr) (code : SomeCode D Γ)
    (_ : expression names source = .ok code) (before after : World D) (env : Env D Γ) :
    eval before code.2.expr after env = code.2.denote env := code.2.equation _ _ _

end Gabbro.Grammatik.Parser.Konst.Scalar
