/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben30.lean
  Subject:   Track P: contracts beyond `Held(..)`. A `requires p` (every predicate form of an `ensures` without
             `old` and `result`) is `UFn.needs` and lowers to `Programm.requires` (the conjunction; `.tru`
             without one). `forall x in slots of T : p` and `exists x in slots of T : p` are `Expr.forallSlots` /
             `existsSlots` (the binder an index into `T`, the table under its guards). Beside a result (an
             `ensures` of a function with a value) a quantifier is refused by name: the binder would stand
             before the result variable, which the side reader does not shift.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben30

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The `requires` predicates of the elaborated functions. -/
def needs (s : String) : Option (List (List UEns)) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.fns.map (·.needs))

/-- Is a lowered `requires` the empty conjunction? -/
def istTru {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} : Expr D Γ Λ .bool → Bool
  | .tru => true
  | _ => false

/-- For every function of the lowered program: is its `requires` `.tru`? -/
def reqTru (s : String) : Option (List Bool) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u =>
        match lowerAllg u with
        | .error _ => none
        | .ok (P, _) => some ((List.finRange u.fns.length).map fun f => istTru (P.requires f))

/-- A comparison over a parameter. -/
def req_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 9) requires a > 2 { } impl fn g() { } }"
theorem req_ok_stufe : stufe req_ok = "OK" := by decide +kernel
theorem req_ok_needs : needs req_ok = some [[.cmp ">" (.param "a") (.lit 2)], []] := by decide +kernel
theorem req_ok_tru : reqTru req_ok = some [false, true] := by decide +kernel

/-- A universal quantifier over the slots of an unguarded table. -/
def forall_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn f() requires forall k in slots of T : T.slots[k].v > 0 { } }"
theorem forall_ok_stufe : stufe forall_ok = "OK" := by decide +kernel
theorem forall_ok_tru : reqTru forall_ok = some [false] := by decide +kernel

/-- An existential one in an `ensures` without a result. -/
def exists_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn f() ensures exists k in slots of T : T.slots[k].v == 0 { } }"
theorem exists_ok_stufe : stufe exists_ok = "OK" := by decide +kernel

/-- Planted defect: the quantified table is guarded and the guard is not held. -/
def forall_guard_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn f() requires forall k in slots of T : T.slots[k].v > 0 { } }"
theorem forall_guard_refused_stufe : stufe forall_guard_refused = "elab: access without held guard" := by
  decide +kernel

/-- A quantifier beside a result is refused by name. -/
def forall_erg_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn f() -> u32 in 0 .. 9 ensures forall k in slots of T : T.slots[k].v > 0 { return 0; } }"
theorem forall_erg_refused_stufe :
    stufe forall_erg_refused = "lower: quantifier beside a result without G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben30
