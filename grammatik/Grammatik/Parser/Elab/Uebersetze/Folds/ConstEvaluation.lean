module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- One exact integer evaluator. Optional bounds permit contract operands outside
    the result interval; bounded value evaluation checks every intermediate result.
    Fuel bounds evaluation only, and is never identified with a source decreases measure. -/
def uKonstEval (bounds : Option (Int × Int)) (fns : List UKonstFn)
    (env : List (String × Int)) : Nat → SExpr → Option Int
  | 0, _ => none
  | fuel + 1, expression =>
    let checked : Int → Option Int := fun value =>
      match bounds with
      | none => some value
      | some (lo, hi) => if lo ≤ value ∧ value ≤ hi then some value else none
    match expression with
    | .lit n => checked n
    | .tru => if bounds.isNone then checked 1 else none
    | .fls => if bounds.isNone then checked 0 else none
    | .res => (env.find? (fun p => strEq p.1 "result")).bind (fun p => checked p.2)
    | .variable name => (env.find? (fun p => strEq p.1 name)).bind (fun p => checked p.2)
    | .un "-" (.lit n) => checked (-(Int.ofNat n))
    | .un op source => do
      let value ← uKonstEval bounds fns env fuel source
      if op == "-" then checked (-value)
      else if op == "!" then if bounds.isNone then checked (if value == 0 then 1 else 0) else none
      else none
    | .field (.variable ty) member =>
      match uTypName [] ty with
      | .ok (lo, hi) =>
        if strEq member "max" then checked hi
        else if strEq member "min" then checked lo else none
      | .error _ => none
    | .bin op left right => do
      let a ← uKonstEval bounds fns env fuel left
      let b ← uKonstEval bounds fns env fuel right
      if op == "+" then checked (a + b)
      else if op == "-" then checked (a - b)
      else if op == "*" then checked (a * b)
      else if op == "/" then if 0 < b then checked (a / b) else none
      else if op == "%" then if 0 < b then checked (a % b) else none
      else if op == "&" then
        if 0 ≤ a ∧ 0 ≤ b then checked (Int.ofNat (a.toNat &&& b.toNat)) else none
      else if op == "|" then
        if 0 ≤ a ∧ 0 ≤ b then checked (Int.ofNat (a.toNat ||| b.toNat)) else none
      else if op == "^" then
        if 0 ≤ a ∧ 0 ≤ b then checked (Int.ofNat (a.toNat ^^^ b.toNat)) else none
      else if op == "<<" then
        if 0 ≤ a ∧ 0 ≤ b ∧ b < 64 then checked (a * 2 ^ b.toNat) else none
      else if op == ">>" then
        if 0 ≤ a ∧ 0 ≤ b ∧ b < 64 then checked (a / 2 ^ b.toNat) else none
      else if bounds.isSome then none
      else if op == "==" then checked (if a == b then 1 else 0)
      else if op == "!=" then checked (if a != b then 1 else 0)
      else if op == "<" then checked (if a < b then 1 else 0)
      else if op == "<=" then checked (if a ≤ b then 1 else 0)
      else if op == ">" then checked (if b < a then 1 else 0)
      else if op == ">=" then checked (if b ≤ a then 1 else 0)
      else if op == "&&" then checked (if a == 0 || b == 0 then 0 else 1)
      else if op == "||" then checked (if a == 0 && b == 0 then 0 else 1)
      else none
    | .call name args => do
      let fn ← fns.find? (fun k => strEq k.name name)
      if args.length != fn.params.length then none else do
      let values ← (args.zip fn.params).mapM fun (source, (_, ty)) =>
        match ty with
        | .int lo hi => uKonstEval (some (lo, hi)) fns env fuel source
        | _ => none
      let bindings ← uKonstBinde fn.params values
      let permits := fun (post : Bool) (scope : List (String × Int)) =>
        fn.signature.klauseln.all fun
          | .needs predicate => post || uKonstEval none fns scope fuel predicate == some 1
          | .gives predicate => !post || uKonstEval none fns scope fuel predicate == some 1
          | .effs effects => effects.all (fun | .pure => true | _ => false)
          -- This evaluator proposes values, not source cost certificates.
          -- CheckedCall retains and checks every original bound at its typed
          -- entry arguments before checkReplacement can return a source literal.
          | .cost _ => true
          | _ => false
      if !permits false bindings then none else do
      match fn.erg, fn.rumpf with
      | .int lo hi, .block [] (some (.ret (some body))) => do
        let value ← uKonstEval (some (lo, hi)) fns bindings fuel body
        if permits true (("result", value) :: bindings) then checked value else none
      | _, _ => none
    | _ => none

/-- The canonical bounded entry point retains its existing interface and exact arithmetic. -/
def uKonstWert (lo hi : Int) (fns : List UKonstFn) (env : List (String × Int))
    (fuel : Nat) (source : SExpr) : Option Int :=
  uKonstEval (some (lo, hi)) fns env fuel source

/-- Negative surface literals are checked at their signed declared range. -/
theorem uKonstWert_negative_zeuge :
    uKonstWert (-10) (-1) [] [] 64 (.un "-" (.lit 5)) = some (-5) := rfl

/-- Every intermediate integer stays checked; overflow followed by cancellation fails. -/
theorem uKonstWert_overflow_zeuge :
    uKonstWert 0 255 [] [] 64
      (.bin "-" (.bin "+" (.lit 255) (.lit 1)) (.lit 1)) = none := rfl

end Gabbro.Grammatik.Parser.Uebersetze
