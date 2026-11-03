module
public import Grammatik.Parser.Elab.Konst.Scalar.Names
public import Grammatik.Parser.Elab.Uebersetze.Folds.ConstantBytes

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values
open Uebersetze Scalar UebersetzeAllg

/-- The declared result type controls every literal and payload. Integer widening
    requires interval inclusion; no cast changes a Boolean, table bound or tag. -/
def adapt {D : Deklaration} {Γ : Ctx} (target : Ty) (source : SomeCode D Γ) :
    Except String (Code D Γ target) :=
  match target, source with
  | .int lo hi, ⟨.int lower upper, code⟩ =>
    if h : lo ≤ lower ∧ upper ≤ hi then
      .ok ⟨.widen h.1 h.2 code.expr, fun args => Zahl.weiter h.1 h.2 (code.denote args), by
        intros; simp only [eval, code.equation]⟩
    else .error "const value interval is outside its declared type"
  | target, ⟨actual, code⟩ =>
    if h : actual = target then .ok (h ▸ code)
    else .error "const value has a different declared type"

/-- Typed payload code keeps dependent case selection out of the source reader. -/
structure PayloadCode (D : Deklaration) (Γ : Ctx) (c : Option Ty) where
  expr : NutzlastExpr D Γ [] c
  denote : Env D Γ → Nutzlast D.Fn D.passt c
  equation : ∀ before after args, evalNutz before expr after args = denote args

mutual
/-- One checked value constructor, using the canonical G value semantics. The
    fuel bounds elaboration of nested payloads, not execution or source recursion. -/
def expression {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) :
    Nat → (target : Ty) → SExpr → Except String (Code D Γ target)
  | 0, _, _ => .error "const value elaboration exhausted its structural limit"
  | fuel + 1, target, source =>
    match target, source with
    | .opt n, .call "None" [] =>
      .ok ⟨.none n, fun _ => none, by intros; rfl⟩
    | .opt n, .call "Some" [value] => do
      let payload ← expression names globals schemas fuel (.index n) value
      return ⟨.some payload.expr, fun args => some (payload.denote args), by
        intros; simp only [eval, payload.equation]⟩
    | .str n, .ext .text [text] [] =>
      if n > 1 then .error "const string result exceeds the A28 one-byte maximum"
      else match bytesZahl (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) with
      | none => .error "const string literal contains a non-byte value"
      | some bytes =>
        if h : bytes.length ≤ n then
          .ok ⟨.strLit bytes h, fun _ => ⟨bytes, h⟩, by intros; rfl⟩
        else .error "const string literal exceeds its declared maximum"
    | .why n, .why owner name => do
      let some schema := schemas.find? (fun schema => strEq schema.name owner)
        | throw ("const reason owner is unknown: " ++ owner)
      if schema.cases.length != n || !schema.cases.all (fun entry => entry.2.isNone) then
        throw "const reason owner differs from its declared type"
      let some index := schema.cases.findIdx? (fun entry => strEq entry.1 name)
        | throw ("const reason case is unknown: " ++ name)
      if hi : index < n then
        return ⟨.why n ⟨index, hi⟩, fun _ => ⟨index, hi⟩, by intros; rfl⟩
      else throw "const reason case lies outside its declared type"
    | .sum cases, source => do
      let schema ← match schemas.find? (fun schema => schema.spec = cases) with
        | some schema => pure schema
        | none => throw "const tagged result has no resolved schema"
      let (name, payload) ← match source with
        | .variable name => pure (name, none)
        | .call name [value] => pure (name, some value)
        | _ => throw "const tagged result needs a named constructor"
      let some index := schema.cases.findIdx? (fun entry => strEq entry.1 name)
        | throw ("const tagged constructor is unknown: " ++ name)
      if hi : index < cases.length then
        let i : Fin cases.length := ⟨index, hi⟩
        let value ← payloadExpression names globals schemas fuel (cases.get i) payload
        return ⟨.case cases i value.expr,
          fun args => ⟨i, Fall.ofNutzlast D.Fn D.passt cases i (value.denote args)⟩,
          by intros; simp only [eval, value.equation]⟩
      else throw "const tagged constructor lies outside its declared schema"
    | _, _ => do
      let normalized ← Scalar.normalize names globals source
      adapt target normalized.code

/-- Payload presence and its declared type are checked together. -/
def payloadExpression {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) :
    Nat → (target : Option Ty) → Option SExpr → Except String (PayloadCode D Γ target)
  | 0, _, _ => .error "const payload elaboration exhausted its structural limit"
  | _ + 1, none, none => .ok ⟨.empty, fun _ => (), by intros; rfl⟩
  | fuel + 1, some τ, some source => do
    let code ← expression names globals schemas fuel τ source
    return ⟨.val code.expr, code.denote, by intros; simp only [evalNutz, code.equation]⟩
  | _ + 1, _, _ => .error "const tagged constructor payload does not match its declared type"
end

/-- Only portable A28 results enter this additional value path. Other types keep
    a named refusal; integer calls retain the existing bounded/KExpr certificate. -/
def resultType : Ty → Bool
  | .bool | .opt _ | .sum _ | .why _ => true
  | .str n => n ≤ 1
  | _ => false

end Gabbro.Grammatik.Parser.Konst.Values
