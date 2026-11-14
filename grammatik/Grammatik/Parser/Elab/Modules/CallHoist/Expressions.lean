/-
  Calls inside expressions, as sugar.

  Machine G calls a function in a statement of its own (`let x = f(a);`, `f(a);`, `return f(a);`).
  A call written inside an expression -- an operand, a condition, an assigned value, an argument of
  another call -- is rewritten here into such statements: the call is bound to a fresh name in front
  of the statement that contains it, and the name stands where the call stood.

  The rewrite keeps the order of evaluation, left to right:
  * the calls of one statement are bound in the order they are written, arguments before their call;
  * a call is moved only when nothing in front of it in the statement reads mutable state (a static,
    a table slot): such a read would otherwise happen after the call. The target of a compound
    assignment (`S += f();`) is such a read. Such a call stays where it is and
    the elaborator refuses it as before, so the writer binds it by hand;
  * the right operand of `&&` and `||` is evaluated conditionally: its calls are bound inside an `if`
    over the left operand, and a fresh mutable `bool` carries the result;
  * an `else if` whose condition holds a call becomes an `if` inside an `else`, so its calls run only
    when the conditions in front of it failed.

  The fresh names (`#r0`, `#r1`, ...) cannot be written in source text. The result contains only forms
  the elaborator already reads; no form of the language is added.
-/
module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

/-- A set of names: a list for the kernel, a hash map for compiled code (`Tafel`). -/
abbrev Namen := Tafel String (fun name => name)

/-- What the rewrite knows of the unit: the functions a `let` can bind a call of, and the statics. -/
structure Kontext where
  fns : Namen
  /-- The names in scope: a local may hold a function pointer, so a call of it is bound too. -/
  lokal : List String := []
  /-- The cases of the unit's tagged types: a constructed value inside an expression is bound like a
      call (`let x = Case(v);` is the form the elaborator reads). -/
  faelle : Namen := Tafel.von _ []
  /-- Aggregate and tagged table fields (table, field, declared type): untyped reads receive
      their declared type; tagged reads use the existing match expansion. -/
  felder : List (String × String × STyp) := []
  statics : Namen
  /-- The statics whose declared type an untyped `let` of them gets written (option and tagged). -/
  statikTyp : List (String × STyp) := []
  /-- The tagged statics with the cases of their type (name, whether it carries a payload): a `let` of
      such a static is read case by case, the one form in which machine G reads a tagged static. -/
  statikFaelle : List (String × List (String × Bool)) := []
  /-- Tagged type names and their cases, for reads of declared table fields. -/
  typFaelle : List (String × List (String × Bool)) := []
  /-- Whether the statement is the function body itself: a call returned at its end stands as it is. -/
  oben : Bool := false

/-- Whether `&&` or `||`: the right operand is evaluated conditionally. -/
def bedingt (op : String) : Bool := strEq op "&&" || strEq op "||"

/-- Only value projections rooted in a known local: no dereference, indexing, call or static.
    Local mutability is not recorded by `binders`. Even a mutable local is private to this call
    frame: a callee cannot assign it, so delaying its value projection past a lifted call is safe.
    A name also listed among statics is conservatively excluded, even when shadowed. -/
def lokalerWert (k : Kontext) : SExpr → Bool
  | .variable x => k.lokal.contains x && !(k.statics.finde x).isSome
  | .field e _ => lokalerWert k e
  | _ => false

/-- The index forms the existing place reader accepts without a source binding. -/
def atomarerIndex : SExpr → Bool
  | .lit _ | .variable _ => true
  | _ => false

/-- Whether an expression reads no mutable state and holds no call: literals, locals, constants and
    operators over them. -/
def ruhig (k : Kontext) : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .lit _ | _ + 1, .float _ | _ + 1, .tru | _ + 1, .fls | _ + 1, .res | _ + 1, .why _ _
  | _ + 1, .fnref _ => true
  | _ + 1, .ext .text [_] [] => true
  | _ + 1, .variable v => !(k.statics.finde v).isSome
  | _ + 1, e@(.field _ _) => lokalerWert k e
  | n + 1, .un _ e => ruhig k n e
  | n + 1, .bin _ a b => ruhig k n a && ruhig k n b
  | n + 1, .built _ args => args.all (ruhig k n)
  | _ + 1, _ => false
termination_by structural fuel => fuel

/-- The result of rewriting an expression: the bindings to put in front, the expression, the next
    fresh number, and whether everything evaluated so far reads no mutable state. -/
abbrev Schritt := List SAnw × SExpr × Nat × Bool

/-- The declared type of an aggregate table field read by the table's name (`T.slots[i].f`). -/
def feldTyp (k : Kontext) : SExpr → Option STyp
  | .field (.index (.field (.variable table) "slots") _) field =>
    (k.felder.find? fun entry => strEq entry.1 table && strEq entry.2.1 field).map (·.2.2)
  | _ => none

/-- A case without a payload written as an argument of a function call (`f(End)`): bound like a
    constructed value. `ruf` says that the surrounding call is one of a function. -/
def bindeFall (k : Kontext) (ruf : Bool) (nr : Nat) (sauber : Bool) : SExpr → Option Schritt
  | .variable v =>
    if ruf && sauber && (k.faelle.finde v).isSome && !k.lokal.contains v && !(k.statics.finde v).isSome then
      some ([.bind false ("#r" ++ toString nr) none (.variable v)], .variable ("#r" ++ toString nr), nr + 1, true)
    else none
  | _ => none

/-- Rewrite one expression. `sauber` says that nothing in front of it read mutable state. -/
def hebeE (k : Kontext) : Nat → Nat → Bool → SExpr → Schritt
  | 0, nr, _, e => ([], e, nr, false)
  | n + 1, nr, sauber, .call f args =>
    let step := args.foldl (fun (acc : List SAnw × List SExpr × Nat × Bool) a =>
      let r := (bindeFall k ((k.fns.finde f).isSome || k.lokal.contains f) acc.2.2.1 acc.2.2.2 a).getD
        (hebeE k n acc.2.2.1 acc.2.2.2 a)
      (acc.1 ++ r.1, acc.2.1 ++ [r.2.1], r.2.2.1, r.2.2.2)) ([], [], nr, sauber)
    if (k.fns.finde f).isSome || k.lokal.contains f || (k.faelle.finde f).isSome then
      if step.2.2.2 then
        let name := "#r" ++ toString step.2.2.1
        (step.1 ++ [.bind false name none (.call f step.2.1)], .variable name, step.2.2.1 + 1, true)
      else (step.1, .call f step.2.1, step.2.2.1, false)
    else (step.1, .call f step.2.1, step.2.2.1, step.2.2.2)
  | n + 1, nr, sauber, .built f args =>
    let step := args.foldl (fun (acc : List SAnw × List SExpr × Nat × Bool) a =>
      let r := hebeE k n acc.2.2.1 acc.2.2.2 a
      (acc.1 ++ r.1, acc.2.1 ++ [r.2.1], r.2.2.1, r.2.2.2)) ([], [], nr, sauber)
    (step.1, .built f step.2.1, step.2.2.1, step.2.2.2)
  | n + 1, nr, sauber, .un op e =>
    let r := hebeE k n nr sauber e
    (r.1, .un op r.2.1, r.2.2.1, r.2.2.2)
  | n + 1, nr, sauber, .bin op a b =>
    let ra := hebeE k n nr sauber a
    if bedingt op then
      -- `a && f()`: `let mut t : bool = false; if a { t = f(); }` (`||`: `true` and `!a`).
      let name := "#r" ++ toString ra.2.2.1
      let rb := hebeE k n (ra.2.2.1 + 1) ra.2.2.2 b
      if rb.1.isEmpty then (ra.1, .bin op ra.2.1 b, ra.2.2.1, ra.2.2.2 && ruhig k n b)
      else
        let und := strEq op "&&"
        (ra.1 ++ [.bind true name (some (.atom "bool")) (if und then .fls else .tru),
            .cond (if und then ra.2.1 else .un "!" ra.2.1)
              (.block (rb.1 ++ [.set (.variable name) "=" rb.2.1]) none) [] none],
          .variable name, rb.2.2.1, rb.2.2.2)
    else
      let rb := hebeE k n ra.2.2.1 ra.2.2.2 b
      (ra.1 ++ rb.1, .bin op ra.2.1 rb.2.1, rb.2.2.1, rb.2.2.2)
  | n + 1, nr, sauber, .index base@(.field (.variable table) "slots") index =>
    if k.lokal.contains table || (k.statics.finde table).isSome then
      let ra := hebeE k n nr sauber base
      let rb := hebeE k n ra.2.2.1 ra.2.2.2 index
      (ra.1 ++ rb.1, .index ra.2.1 rb.2.1, rb.2.2.1, false)
    else
      -- A named table is not evaluated. Bind its computed index at this read, after its own
      -- lifted calls, only if no earlier residual operand read state. The slot read itself
      -- remains unclean: no later call may cross it. Branch recursion keeps this binding
      -- inside the guard, where the ordinary elaborator infers its narrowed range.
      let r := hebeE k n nr sauber index
      if sauber && !atomarerIndex r.2.1 then
        let name := "#r" ++ toString r.2.2.1
        (r.1 ++ [.bind false name none r.2.1], .index base (.variable name), r.2.2.1 + 1, false)
      else (r.1, .index base r.2.1, r.2.2.1, false)
  | n + 1, nr, sauber, .index a b =>
    let ra := hebeE k n nr sauber a
    let rb := hebeE k n ra.2.2.1 ra.2.2.2 b
    (ra.1 ++ rb.1, .index ra.2.1 rb.2.1, rb.2.2.1, false)
  | n + 1, nr, sauber, .field e name =>
    let r := hebeE k n nr sauber e
    (r.1, .field r.2.1 name, r.2.2.1, r.2.2.2 && lokalerWert k (.field e name))
  | n + 1, nr, sauber, .arrow e name =>
    let r := hebeE k n nr sauber e
    (r.1, .arrow r.2.1 name, r.2.2.1, false)
  | _ + 1, nr, sauber, .variable v => ([], .variable v, nr, sauber && !(k.statics.finde v).isSome)
  | n + 1, nr, sauber, e => ([], e, nr, sauber && ruhig k n e)

/-- Rewrite an expression in a position where a call may stand as it is (`let x = f(a);`,
    `return f(a);`): only the arguments of such a call are rewritten. -/
def hebeOben (k : Kontext) (n nr : Nat) : SExpr → List SAnw × SExpr × Nat
  | .call f args =>
    if (k.fns.finde f).isSome || k.lokal.contains f || (k.faelle.finde f).isSome then
      let step := args.foldl (fun (acc : List SAnw × List SExpr × Nat × Bool) a =>
        let r := (bindeFall k ((k.fns.finde f).isSome || k.lokal.contains f) acc.2.2.1 acc.2.2.2 a).getD
          (hebeE k n acc.2.2.1 acc.2.2.2 a)
        (acc.1 ++ r.1, acc.2.1 ++ [r.2.1], r.2.2.1, r.2.2.2)) ([], [], nr, true)
      (step.1, .call f step.2.1, step.2.2.1)
    else
      let r := hebeE k n nr true (.call f args)
      (r.1, r.2.1, r.2.2.1)
  | e =>
    let r := hebeE k n nr true e
    (r.1, r.2.1, r.2.2.1)

/-- Rewrite a returned expression. At the end of the function body a call stands as it is; inside a
    branch, an arm or a loop body the call of a function is bound first (`let r = f(a); return r;`). -/
def hebeRet (k : Kontext) (n nr : Nat) : SExpr → List SAnw × SExpr × Nat
  | .call f args =>
    if !k.oben && ((k.fns.finde f).isSome || k.lokal.contains f) then
      let y := hebeE k n nr true (.call f args)
      (y.1, y.2.1, y.2.2.1)
    else hebeOben k n nr (.call f args)
  | e => hebeOben k n nr e

/-- Rewrite the arguments of a call statement. -/
def hebeArgs (k : Kontext) (n nr : Nat) (args : List SExpr) : List SAnw × List SExpr × Nat :=
  let step := args.foldl (fun (acc : List SAnw × List SExpr × Nat × Bool) a =>
    let r := (bindeFall k true acc.2.2.1 acc.2.2.2 a).getD (hebeE k n acc.2.2.1 acc.2.2.2 a)
    (acc.1 ++ r.1, acc.2.1 ++ [r.2.1], r.2.2.1, r.2.2.2)) ([], [], nr, true)
  (step.1, step.2.1, step.2.2.1)

end Gabbro.Grammatik.Parser.CallHoist
