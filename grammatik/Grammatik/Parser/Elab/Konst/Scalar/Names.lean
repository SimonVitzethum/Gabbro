module
public import Grammatik.Parser.Elab.Konst.Scalar.Expression

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst
open Uebersetze

/-- Signed source literals retain their exact value. -/
def literalVonInt (value : Int) : SExpr :=
  if 0 ≤ value then .lit value.toNat else .un "-" (.lit (-value).toNat)

namespace Scalar

/-- Resolve value names only. Type-limit fields occupy the type namespace; locals
    shadow globals, and qualified names are looked up as complete source identities. -/
def normalizeNames {Γ : Ctx} (names : Locals Γ) (globals : List (String × Int)) : SExpr → SExpr
  | .variable name =>
    if (names.find? (fun entry => strEq entry.1 name)).isSome then .variable name
    else match globals.find? (fun entry => strEq entry.1 name) with
      | some (_, value) => literalVonInt value
      | none => .variable name
  | .un op value => .un op (normalizeNames names globals value)
  | .bin op left right => .bin op (normalizeNames names globals left) (normalizeNames names globals right)
  | source => source

/-- Source-to-G derivations before normalization. The global rule records the
    actual resolved value; operator rules use precisely the existing typed G reader.
    There is no arbitrary mathematical denotation or accepting wildcard. -/
inductive SourceMeaning {D : Deklaration} {Γ : Ctx}
    (names : Locals Γ) (globals : List (String × Int)) : SExpr → SomeCode D Γ → Prop where
  | literal (n : Nat) : SourceMeaning names globals (.lit n) ⟨_, Code.literal n⟩
  | truth (b : Bool) : SourceMeaning names globals (if b then .tru else .fls) ⟨_, Code.truth b⟩
  | local (name : String) (τ : Ty) (x : Var Γ τ)
      (found : names.find? (fun entry => strEq entry.1 name) = some (name, ⟨τ, x⟩)) :
      SourceMeaning names globals (.variable name) ⟨τ, Code.variable x⟩
  | global (name key : String) (value : Int) (code : SomeCode D Γ)
      (notLocal : names.find? (fun entry => strEq entry.1 name) = none)
      (found : globals.find? (fun entry => strEq entry.1 name) = some (key, value))
      (typed : expression names (literalVonInt value) = .ok code) :
      SourceMeaning names globals (.variable name) code
  | result (code : SomeCode D Γ) (typed : expression names .res = .ok code) :
      SourceMeaning names globals .res code
  | limit (ty member : String) (code : SomeCode D Γ)
      (typed : expression names (.field (.variable ty) member) = .ok code) :
      SourceMeaning names globals (.field (.variable ty) member) code
  | unary (op : String) (source : SExpr) (input output : SomeCode D Γ)
      (child : SourceMeaning names globals source input)
      (typed : Scalar.unary op input = .ok output) :
      SourceMeaning names globals (.un op source) output
  | binary (op : String) (left right : SExpr) (a b output : SomeCode D Γ)
      (leftMeaning : SourceMeaning names globals left a)
      (rightMeaning : SourceMeaning names globals right b)
      (typed : Scalar.binary op a b = .ok output) :
      SourceMeaning names globals (.bin op left right) output

/-- Structural normalization preserves the source-derived typed G expression,
    including its type. This induction is generic over source expressions. -/
theorem SourceMeaning.normalized {D : Deklaration} {Γ : Ctx}
    {names : Locals Γ} {globals : List (String × Int)} {source : SExpr}
    {code : SomeCode D Γ} (meaning : SourceMeaning names globals source code) :
    expression names (normalizeNames names globals source) = .ok code := by
  induction meaning with
  | literal n => rfl
  | truth b => cases b <;> rfl
  | local name τ x found => simp [normalizeNames, found, expression]
  | global name key value code notLocal found typed =>
    simpa only [normalizeNames, notLocal, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, found] using typed
  | result code typed => exact typed
  | limit ty member code typed => exact typed
  | unary op source input output child typed ih =>
    simpa only [normalizeNames, expression, ih] using typed
  | binary op left right a b output lm rm typed ihl ihr =>
    simpa only [normalizeNames, expression, ihl, ihr] using typed

/-- A successful normalization returns its original source derivation, rather
    than making denotation an unchecked premise of the replacement theorem. -/
structure Normalized {D : Deklaration} {Γ : Ctx}
    (names : Locals Γ) (globals : List (String × Int)) (source : SExpr) where
  code : SomeCode D Γ
  meaning : SourceMeaning names globals source code

/-- Construct the derivation alongside the normalized expression. -/
def normalize {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (source : SExpr) :
    Except String (Normalized (D := D) names globals source) :=
  match source with
  | .lit n => .ok ⟨⟨_, Code.literal n⟩, .literal n⟩
  | .tru => .ok ⟨⟨_, Code.truth true⟩, .truth true⟩
  | .fls => .ok ⟨⟨_, Code.truth false⟩, .truth false⟩
  | .variable name =>
    match hl : names.find? (fun entry => strEq entry.1 name) with
    | some (key, ⟨τ, x⟩) =>
      -- The reader retains the lookup key as well as the typed position.
      match ht : expression (D := D) names (.variable name) with
      | .error error => .error error
      | .ok code =>
        if hk : key = name then
          .ok ⟨⟨τ, Code.variable x⟩, .local name τ x (by simpa [hk] using hl)⟩
        else .error "const local identity mismatch"
    | none =>
      match hg : globals.find? (fun entry => strEq entry.1 name) with
      | none => .error ("const unresolved name: " ++ name)
      | some (key, value) =>
        match ht : expression (D := D) names (literalVonInt value) with
        | .error error => .error error
        | .ok code => .ok ⟨code, .global name key value code hl hg ht⟩
  | .res =>
    match ht : expression (D := D) names .res with
    | .error error => .error error
    | .ok code => .ok ⟨code, .result code ht⟩
  | .field (.variable ty) member =>
    match ht : expression (D := D) names (.field (.variable ty) member) with
    | .error error => .error error
    | .ok code => .ok ⟨code, .limit ty member code ht⟩
  | .un op value => do
    let child ← normalize names globals value
    match ht : unary op child.code with
    | .error error => throw error
    | .ok code => return ⟨code, .unary op value child.code code child.meaning ht⟩
  | .bin op left right => do
    let a ← normalize names globals left
    let b ← normalize names globals right
    match ht : binary op a.code b.code with
    | .error error => throw error
    | .ok code => return ⟨code, .binary op left right a.code b.code code a.meaning b.meaning ht⟩
  | _ => .error "const expression without a source-to-G derivation"

/-- Contracts normalize in their own entry/result context and preserve clause order. -/
def normalizeClauses {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (post : Bool) : List SKlausel → Except String (Code D Γ .bool)
  | [] => .ok (Code.truth true)
  | clause :: rest => do
    let tail ← normalizeClauses names globals post rest
    match clause with
    | .needs source =>
      if post then return tail
      else return Code.boolAnd (← boolean (← normalize names globals source).code) tail
    | .gives source =>
      if post then return Code.boolAnd (← boolean (← normalize names globals source).code) tail
      else return tail
    | .effs effects =>
      if effects.all (fun | .pure => true | _ => false) then return tail
      else throw "const effect clause is not pure"
    | _ => throw "const clause without a compile-time certificate"


end Scalar
end Gabbro.Grammatik.Parser.Konst
