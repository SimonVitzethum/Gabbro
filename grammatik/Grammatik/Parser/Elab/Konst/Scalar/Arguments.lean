module
public import Grammatik.Parser.Elab.Konst.Scalar.Names

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Uebersetze

/-- An argument retains its original source, structural name derivation, bounded
    canonical evaluation and equality with that original source-derived G value. -/
structure IntegerArgument (fns : List UKonstFn) (globals : List (String × Int))
    (lo hi : Int) (source : SExpr) (value : Int) where
  normalization : Normalized (D := declaration [] (.int lo hi)) (Γ := []) [] globals source
  lower : Int
  upper : Int
  code : Code (declaration [] (.int lo hi)) [] (.int lower upper)
  typed : normalization.code = ⟨_, code⟩
  candidate : uKonstWert lo hi fns [] 64
    (normalizeNames ([] : Locals []) globals source) = some value
  denotes : (code.denote .nil).n = value

inductive ArgumentMeaning (fns : List UKonstFn) (globals : List (String × Int)) :
    List (String × Ty) → List SExpr → List Int → Prop where
  | nil : ArgumentMeaning fns globals [] [] []
  | cons (name : String) (lo hi : Int) (source : SExpr) (value : Int)
      (argument : IntegerArgument fns globals lo hi source value)
      (tail : ArgumentMeaning fns globals params sources values) :
      ArgumentMeaning fns globals ((name, .int lo hi) :: params) (source :: sources) (value :: values)

structure CheckedArguments (fns : List UKonstFn) (globals : List (String × Int))
    (params : List (String × Ty)) (sources : List SExpr) where
  values : List Int
  meaning : ArgumentMeaning fns globals params sources values

/-- Candidate argument values are checked, never assumed to agree with G. -/
def checkArguments (fns : List UKonstFn) (globals : List (String × Int)) :
    (params : List (String × Ty)) → (sources : List SExpr) →
      Except String (CheckedArguments fns globals params sources)
  | [], [] => .ok ⟨[], .nil⟩
  | (name, .int lo hi) :: rest, source :: sources => do
    let normalized ← normalize (D := declaration [] (.int lo hi)) (Γ := []) [] globals source
    match ht : normalized.code with
    | ⟨.int lower upper, code⟩ =>
      match hc : uKonstWert lo hi fns [] 64 (normalizeNames ([] : Locals []) globals source) with
      | none => throw "const argument is not a compile-time value in its declared range"
      | some value =>
        if hd : (code.denote .nil).n = value then
          let tail ← checkArguments fns globals rest sources
          let argument : IntegerArgument fns globals lo hi source value :=
            ⟨normalized, lower, upper, code, ht, hc, hd⟩
          return ⟨value :: tail.values, .cons name lo hi source value argument tail.meaning⟩
        else throw "const argument evaluator differs from its original source G value"
    | _ => throw "const type failure: expected an integer expression"
  | _, _ => .error "const argument type or arity mismatch"

/-- The scalar list projection preserves the historical candidate interface. -/
def argumentValues (fns : List UKonstFn) (globals : List (String × Int))
    (params : List (String × Ty)) (sources : List SExpr) : Except String (List Int) :=
  (checkArguments fns globals params sources).map CheckedArguments.values

/-- Normalization and bounded canonical evaluation denote the original source
    argument at every world; the structural derivation is part of the certificate. -/
theorem IntegerArgument.normalized_denotation
    (argument : IntegerArgument fns globals lo hi source value)
    (before after : World (declaration [] (.int lo hi))) :
    uKonstWert lo hi fns [] 64 (normalizeNames ([] : Locals []) globals source) =
      some (eval before argument.code.expr after .nil).n := by
  rw [argument.code.equation, argument.denotes]
  exact argument.candidate

end Gabbro.Grammatik.Parser.Konst.Scalar
