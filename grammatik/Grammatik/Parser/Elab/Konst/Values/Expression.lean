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
        match ht : cases.get i, payload with
        | none, none =>
          let term : Expr D Γ [] (.sum cases) := .case cases i (ht ▸ .empty)
          return ⟨term, fun _ => ⟨i, Fall.ofNutzlast D.Fn D.passt cases i (ht ▸ ())⟩,
            by intros; simp only [term, eval, evalNutz]; cases ht; rfl⟩
        | some τ, some value =>
          let value ← expression names globals schemas fuel τ value
          let term : Expr D Γ [] (.sum cases) := .case cases i (ht ▸ .val value.expr)
          return ⟨term, fun args => ⟨i, Fall.ofNutzlast D.Fn D.passt cases i (ht ▸ value.denote args)⟩,
            by intros; simp only [term, eval, evalNutz]; cases ht; simp only [value.equation]⟩
        | _, _ => throw "const tagged constructor payload does not match its declared type"
      else throw "const tagged constructor lies outside its declared schema"
    | _, _ => do
      let normalized ← Scalar.normalize names globals source
      adapt target normalized.code

/-- Only portable A28 results enter this additional value path. Other types keep
    a named refusal; integer calls retain the existing bounded/KExpr certificate. -/
def resultType : Ty → Bool
  | .bool | .opt _ | .sum _ => true
  | .str n => n ≤ 1
  | _ => false

end Gabbro.Grammatik.Parser.Konst.Values
