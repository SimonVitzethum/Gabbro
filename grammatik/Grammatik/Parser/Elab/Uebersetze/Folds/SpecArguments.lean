module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
public import Grammatik.Parser.Elab.Uebersetze.Folds.ConstantBytes

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Typed value paths consist of a name and ordinary record projections.
    Their types come from the lexical declaration and its record schema. -/
def uSpecValuePath : SExpr → Bool
  | .variable _ => true
  | .field base _ => uSpecValuePath base
  | _ => false

/-- Before substitution, read the exact type of each supported value.
    Strings use decoded byte lengths, declared path bounds and the
    ordinary G rule for concatenation. -/
def uSpecValueType (ctx : UCtx) : SExpr → USide → Option Ty
  | .ext .text [_] [], .text bytes => (bytesZahl bytes).map fun decoded => Ty.str decoded.length
  | .bin "+" lhs rhs, .add a b => do
    let some (.str left) := uSpecValueType ctx lhs a | none
    let some (.str right) := uSpecValueType ctx rhs b | none
    pure (.str (left + right))
  | argument, side => if uSpecValuePath argument then uValueType ctx side else none

/-- Compare the full value type, including nominal record identity, array
    shape and string bound, before substituting into the predicate. -/
def uSpecValueArgument (ctx : UCtx) (expected : Ty) (argument : SExpr) : Except String Unit := do
  let side ← uWertBody ctx argument
  if uSpecValueType ctx argument side = some expected then pure ()
  else throw "spec value argument does not have the declared type"

theorem uSpecValueArgument_exact {ctx : UCtx} {expected : Ty} {argument : SExpr}
    (accepted : uSpecValueArgument ctx expected argument = .ok ()) :
    ∃ side, uWertBody ctx argument = .ok side ∧
      uSpecValueType ctx argument side = some expected := by
  cases read : uWertBody ctx argument with
  | error err => simp [uSpecValueArgument, read, bind, Except.bind] at accepted
  | ok side =>
    by_cases typeMatches : uSpecValueType ctx argument side = some expected
    · exact ⟨side, rfl, typeMatches⟩
    · simp [uSpecValueArgument, read, typeMatches, bind, Except.bind] at accepted

theorem specValueArgument_erfuellbar (ctx : UCtx) (name : String) (expected : Ty)
    (read : uWertBody ctx (.variable name) = .ok (.param name))
    (typeMatches : uValueType ctx (.param name) = some expected) :
    uSpecValueArgument ctx expected (.variable name) = .ok () := by
  simp [uSpecValueArgument, uSpecValueType, uSpecValuePath, read, typeMatches,
    bind, Except.bind, pure, Except.pure]

/-- The literal lane accepts exactly the type of the checked byte list. -/
theorem specTextArgument_erfuellbar (ctx : UCtx) (text : String) :
    uSpecValueArgument ctx (.str text.toUTF8.toList.length) (.ext .text [text] []) = .ok () := by
  obtain ⟨decoded, valid⟩ := bytesZahl_uint8 text.toUTF8.toList
  have length := bytesZahl_laenge _ decoded valid
  rw [List.length_map] at length
  have parsed : uWertBody ctx (.ext .text [text] []) =
      .ok (.text (text.toUTF8.toList.map fun b => Int.ofNat b.toNat)) := by
    simp only [uWertBody, uRechne]
  simp only [uSpecValueArgument, parsed, bind, Except.bind, uSpecValueType, valid,
    Option.map_some, length, ite_true] <;> rfl

/-- The ordinary source reader keeps a concatenation of accepted
    arguments as the same pair of operands through the precheck. -/
theorem specStringConcatArgument_erfuellbar (ctx : UCtx) (lhs rhs : SExpr) (left right : Nat)
    (leftAccepted : uSpecValueArgument ctx (.str left) lhs = .ok ())
    (rightAccepted : uSpecValueArgument ctx (.str right) rhs = .ok ()) :
    ∃ a b, uWertBody ctx (.bin "+" lhs rhs) = .ok (.add a b) ∧
      uSpecValueArgument ctx (.str (left + right)) (.bin "+" lhs rhs) = .ok () := by
  obtain ⟨a, readLeft, typedLeft⟩ := uSpecValueArgument_exact leftAccepted
  obtain ⟨b, readRight, typedRight⟩ := uSpecValueArgument_exact rightAccepted
  have read : uWertBody ctx (.bin "+" lhs rhs) = .ok (.add a b) := by
    change uRechne ctx (uWertBlatt ctx) (.bin "+" lhs rhs) = _
    rw [uRechne]
    have plus : strEq "+" "+" = true := rfl
    simp only [plus, Bool.true_or, ite_true, ← uWertBody, readLeft, readRight]
  exact ⟨a, b, read, by
    simp only [uSpecValueArgument, bind, Except.bind, read, uSpecValueType, typedLeft, typedRight,
      pure, Option.pure_def, Except.pure, ite_true]⟩

/-- Reuse annotated local elaboration and the existing integer interval calculation.
    Structured and floating values must match the declared type exactly. -/
def uSpecArgument (ctx : UCtx) (g : String) (i : Nat) (ty : STyp) (arg : SExpr) :
    Except String Unit :=
  let checked : Except String Unit := do
    let expected ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty
    match expected with
    | .bool =>
      let _ ← uBool ctx arg
      pure ()
    | .int .. =>
      let (statement, _) ← uBindWertAllg ctx false "#spec-argument" (some ty) arg
      let .bind _ (some (lo, hi)) value := statement
        | throw "spec argument is not an annotated integer binding"
      let some range := foldRangeWithIndexCheck ctx true value
        | throw "spec argument interval is unresolved"
      if lo ≤ range.1 ∧ range.2 ≤ hi then pure ()
      else throw "spec argument is outside its annotated range"
    | .prod .. | .arr .. | .str .. | .fl .. =>
      uSpecValueArgument ctx expected arg
    | _ => throw "spec parameter type is unsupported"
  match checked with
  | .ok () => .ok ()
  | .error _ => .error ("spec " ++ g ++ ": argument " ++ toString i ++
      " does not fit its parameter type")

/-- Check every original call before inlining, including calls brought by a helper's body.
    Argument expressions use the caller's scope; quantifiers extend it with their real domain.
    Exhausted expansion refuses instead of allowing an unchecked recursive helper. -/
def uSpecArgs : Nat → UCtx → SExpr → Except String Unit
  | 0, _, _ => .error "spec argument checking exceeded its expansion depth"
  | n + 1, ctx, e => do
    match e with
    | .call g args =>
      for arg in args do uSpecArgs n ctx arg
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, _, body) =>
        for (arg, i) in args.zipIdx do
          if specArgumentCaptures body (uSpecEin ctx.specs n arg) then
            throw ("spec " ++ g ++ ": argument " ++ toString (i + 1) ++
              " names a binder of the predicate")
      | none => pure ()
      match ctx.specTypen.find? (fun p => strEq p.1 g) with
      | some (_, types) =>
        if args.length != types.length then
          throw ("spec " ++ g ++ ": argument " ++ toString (min args.length types.length + 1) ++
            " does not fit its parameter type")
        for ((ty, arg), i) in (types.zip args).zipIdx do
          uSpecArgument ctx g (i + 1) ty (uSpecEin ctx.specs n arg)
      | none => pure ()
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, names, body) =>
        if names.length == args.length then
          uSpecArgs n ctx (sErsetze (names.zip args) 1000 body)
        else throw ("spec " ++ g ++ ": argument count does not fit its parameter type")
      | none => pure ()
    | .field a _ | .arrow a _ | .un _ a | .old a => uSpecArgs n ctx a
    | .index a b | .bin _ a b =>
      uSpecArgs n ctx a
      uSpecArgs n ctx b
    | .ext k [binder, domain] [subject, body] =>
      if k == .all || k == .any || k == .count then
        uSpecArgs n ctx subject
        -- Read the predicate domain directly: array quantifiers need no traversal carrier.
        let inner ← if domain == "elems" then do
            let (_, _, count) ← uArrayDomain ctx subject
            pure (uMitLokal ctx binder .int (Ty.index count) ctx.muts)
          else do
            let (_, inner, _) ← uLoopExport ctx binder none domain subject "unvisited" "" none
            pure inner
        uSpecArgs n inner body
      else
        uSpecArgs n ctx subject
        uSpecArgs n ctx body
    | .built _ args | .ext _ _ args =>
      for arg in args do uSpecArgs n ctx arg
    | _ => pure ()

end Gabbro.Grammatik.Parser.Uebersetze
