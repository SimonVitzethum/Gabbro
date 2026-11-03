module
public import Grammatik.Parser.Elab.Konst.Values.Expression

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values
open Uebersetze Scalar UebersetzeAllg

/-- Literal source meaning is typed and retains tag names through their resolved
    schema. This is a source judgment, not a second evaluator. -/
mutual
inductive LiteralMeaning (D : Deklaration) (schemas : List USum) :
    (τ : Ty) → SExpr → Wert D τ → Prop where
  | integer (value : Zahl lo hi) :
      LiteralMeaning D schemas (.int lo hi) (literalVonInt value.n) value
  | truth (value : Bool) :
      LiteralMeaning D schemas .bool (if value then .tru else .fls) value
  | none (n : Int) : LiteralMeaning D schemas (.opt n) (.call "None" []) none
  | some (value : Zahl 0 (n - 1)) :
      LiteralMeaning D schemas (.opt n) (.call "Some" [literalVonInt value.n]) (some value)
  | text (text : String) (bytes : List (Zahl 0 255))
      (decoded : bytesZahl (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) = some bytes)
      (bound : bytes.length ≤ n) :
      LiteralMeaning D schemas (.str n) (.ext .text [text] []) ⟨bytes, bound⟩
  | reason (schema : USum) (member : schema ∈ schemas) (value : Fin n) (name : String)
      (shape : schema.cases.length = n)
      (named : (schema.cases[value.val]?).map Prod.fst = some name) :
      LiteralMeaning D schemas (.why n) (.why schema.name name) value
  | tag (schema : USum) (member : schema ∈ schemas) (shape : schema.spec = cases)
      (i : Fin cases.length) (name : String)
      (named : (schema.cases[i.val]?).map Prod.fst = some name)
      («syntax» : Option SExpr) (value : Nutzlast D.Fn D.passt (cases.get i))
      (payload : PayloadMeaning D schemas (cases.get i) «syntax» value) :
      LiteralMeaning D schemas (.sum cases)
        (match «syntax» with | none => .variable name | some source => .call name [source])
        ⟨i, Fall.ofNutzlast D.Fn D.passt cases i value⟩
inductive PayloadMeaning (D : Deklaration) (schemas : List USum) :
    (c : Option Ty) → Option SExpr → Nutzlast D.Fn D.passt c → Prop where
  | empty : PayloadMeaning D schemas none none ()
  | val (source : SExpr) (value : Wert D τ) (meaning : LiteralMeaning D schemas τ source value) :
      PayloadMeaning D schemas (some τ) (some source) value
end

/-- Exact source literal and its G expression for a complete portable value. -/
structure Reified (D : Deklaration) (Γ : Ctx) (schemas : List USum) (τ : Ty) (value : Wert D τ) where
  «syntax» : SExpr
  expr : Expr D Γ [] τ
  source : LiteralMeaning D schemas τ «syntax» value
  equation : ∀ before after args, eval before expr after args = value

structure ReifiedPayload (D : Deklaration) (Γ : Ctx) (schemas : List USum)
    (c : Option Ty) (value : Nutzlast D.Fn D.passt c) where
  «syntax» : Option SExpr
  expr : NutzlastExpr D Γ [] c
  source : PayloadMeaning D schemas c «syntax» value
  equation : ∀ before after args, evalNutz before expr after args = value

private def numberEq (a b : Zahl lo hi) : Decidable (a = b) :=
  if h : a.n = b.n then .isTrue (by cases a; cases b; cases h; rfl)
  else .isFalse (fun equal => h (congrArg Zahl.n equal))

/-- UTF-8 spelling is retained from source; bytes are compared exactly. A missing
    spelling is a refusal, never lossy Unicode conversion or replacement by zero. -/
structure TextFor (bytes : List (Zahl 0 255)) where
  text : String
  decoded : bytesZahl (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) = some bytes

def findText (bytes : List (Zahl 0 255)) : List String → Except String (TextFor bytes)
  | [] => .error "const string result has no exact UTF-8 source spelling"
  | text :: rest =>
    match hd : bytesZahl (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) with
    | none => findText bytes rest
    | some decoded =>
      letI : DecidableEq (Zahl 0 255) := numberEq
      if h : decoded = bytes then .ok ⟨text, by simpa only [h] using hd⟩
      else findText bytes rest

/-- Generic typed quotation of canonical G values. It checks every constructor
    and carries its complete payload; there is no integer encoding of other types. -/
mutual
def reify {D : Deklaration} {Γ : Ctx} (schemas : List USum) (texts : List String) :
    Nat → (τ : Ty) → (value : Wert D τ) → Except String (Reified D Γ schemas τ value)
  | 0, _, _ => .error "const value quotation exhausted its structural limit"
  | _ + 1, .int lo hi, value =>
    .ok ⟨literalVonInt value.n, .widen value.lo_le value.le_hi (.lit value.n), .integer value,
      by intros; cases value; rfl⟩
  | _ + 1, .bool, value =>
    if h : value = true then
      .ok ⟨.tru, .tru, by simpa only [h] using LiteralMeaning.truth (D := D) (schemas := schemas) true,
        by intros; simpa only [h] using (rfl : eval _ (.tru : Expr D Γ [] .bool) _ _ = true)⟩
    else
      have hf : value = false := by cases value <;> simp_all
      .ok ⟨.fls, .fls, by simpa only [hf] using LiteralMeaning.truth (D := D) (schemas := schemas) false,
        by intros; simpa only [hf] using (rfl : eval _ (.fls : Expr D Γ [] .bool) _ _ = false)⟩
  | _ + 1, .opt n, none => .ok ⟨.call "None" [], .none n, .none n, by intros; rfl⟩
  | _ + 1, .opt n, some value =>
    .ok ⟨.call "Some" [literalVonInt value.n],
      .some (.widen value.lo_le value.le_hi (.lit value.n)), .some value,
      by intros; cases value; rfl⟩
  | _ + 1, .str n, value => do
    if n > 1 then throw "const string result exceeds the A28 one-byte maximum"
    let spelling ← findText value.val texts
    return ⟨.ext .text [spelling.text] [], .strLit value.val value.property,
      .text spelling.text value.val spelling.decoded value.property, by intros; rfl⟩
  | _ + 1, .why n, value => do
    match hf : schemas.find? (fun schema =>
        schema.cases.length == n && schema.cases.all (fun entry => entry.2.isNone)) with
    | none => throw "const reason quotation has no resolved owner"
    | some schema =>
      if hs : schema.cases.length = n then
        match hn : (schema.cases[value.val]?).map Prod.fst with
        | none => throw "const reason quotation has no declared case"
        | some name =>
          return ⟨.why schema.name name, .why n value,
            .reason schema (List.mem_of_find?_eq_some hf) value name hs hn, by intros; rfl⟩
      else throw "const reason quotation owner differs from its declared type"
  | fuel + 1, .sum cases, ⟨i, value⟩ => do
    match hf : schemas.find? (fun schema => schema.spec = cases) with
    | none => throw "const tagged quotation has no resolved schema"
    | some schema =>
      if hs : schema.spec = cases then
        match hn : (schema.cases[i.val]?).map Prod.fst with
        | none => throw "const tagged quotation has no constructor name"
        | some actualName =>
          let payload ← reifyPayload schemas texts fuel (cases.get i)
            (Fall.toNutzlast D.Fn D.passt cases i value)
          let source := match payload.syntax with
            | none => SExpr.variable actualName
            | some literal => .call actualName [literal]
          return ⟨source, .case cases i payload.expr,
            by simpa only [Fall.of_to] using
              (LiteralMeaning.tag schema (List.mem_of_find?_eq_some hf) hs i actualName hn
                payload.syntax _ payload.source),
            by intros; simp only [eval, payload.equation, Fall.of_to]⟩
      else throw "const tagged quotation schema mismatch"
  | _ + 1, _, _ => .error "const result type is outside the portable A28 fragment"

def reifyPayload {D : Deklaration} {Γ : Ctx} (schemas : List USum) (texts : List String) :
    Nat → (c : Option Ty) → (value : Nutzlast D.Fn D.passt c) →
      Except String (ReifiedPayload D Γ schemas c value)
  | 0, _, _ => .error "const payload quotation exhausted its structural limit"
  | _ + 1, none, () => .ok ⟨none, .empty, .empty, by intros; rfl⟩
  | fuel + 1, some τ, value => do
    let quoted ← reify schemas texts fuel τ value
    return ⟨some quoted.syntax, .val quoted.expr, .val quoted.syntax value quoted.source,
      by intros; simp only [evalNutz, quoted.equation]⟩
end

/-- Quotation preserves every component of the canonical value at every world. -/
theorem reify_denotes (literal : Reified D Γ schemas τ value)
    (before after : World D) (args : Env D Γ) :
    eval before literal.expr after args = value := literal.equation before after args

end Gabbro.Grammatik.Parser.Konst.Values
