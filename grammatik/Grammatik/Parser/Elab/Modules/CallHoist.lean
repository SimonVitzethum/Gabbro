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
  /-- The aggregate fields of the unit's tables (table, field, declared type): an untyped `let` of
      such a field read gets the declared type written, the form the elaborator reads. -/
  felder : List (String × String × STyp) := []
  statics : Namen
  /-- The statics whose declared type an untyped `let` of them gets written (option and tagged). -/
  statikTyp : List (String × STyp) := []
  /-- The tagged statics with the cases of their type (name, whether it carries a payload): a `let` of
      such a static is read case by case, the one form in which machine G reads a tagged static. -/
  statikFaelle : List (String × List (String × Bool)) := []

/-- Whether `&&` or `||`: the right operand is evaluated conditionally. -/
def bedingt (op : String) : Bool := strEq op "&&" || strEq op "||"

/-- Whether an expression reads no mutable state and holds no call: literals, locals, constants and
    operators over them. -/
def ruhig (k : Kontext) : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .lit _ | _ + 1, .float _ | _ + 1, .tru | _ + 1, .fls | _ + 1, .res | _ + 1, .why _ _
  | _ + 1, .fnref _ => true
  | _ + 1, .variable v => !(k.statics.finde v).isSome
  | n + 1, .un _ e => ruhig k n e
  | n + 1, .bin _ a b => ruhig k n a && ruhig k n b
  | n + 1, .built _ args => args.all (ruhig k n)
  | _ + 1, _ => false

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
  | n + 1, nr, sauber, .index a b =>
    let ra := hebeE k n nr sauber a
    let rb := hebeE k n ra.2.2.1 ra.2.2.2 b
    (ra.1 ++ rb.1, .index ra.2.1 rb.2.1, rb.2.2.1, false)
  | n + 1, nr, sauber, .field e name =>
    let r := hebeE k n nr sauber e
    (r.1, .field r.2.1 name, r.2.2.1, false)
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

/-- Rewrite the arguments of a call statement. -/
def hebeArgs (k : Kontext) (n nr : Nat) (args : List SExpr) : List SAnw × List SExpr × Nat :=
  let step := args.foldl (fun (acc : List SAnw × List SExpr × Nat × Bool) a =>
    let r := (bindeFall k true acc.2.2.1 acc.2.2.2 a).getD (hebeE k n acc.2.2.1 acc.2.2.2 a)
    (acc.1 ++ r.1, acc.2.1 ++ [r.2.1], r.2.2.1, r.2.2.2)) ([], [], nr, true)
  (step.1, step.2.1, step.2.2.1)

/-- The first `else if` whose condition satisfies `p`: the arms in front, the condition, its body, the
    arms behind. -/
def elsifSpalte (p : SExpr → Bool) : List SAnw → Option (List SAnw × SExpr × SAnw × List SAnw)
  | [] => none
  | .elsif c b :: rest =>
    if p c then some ([], c, b, rest)
    else (elsifSpalte p rest).map fun (vor, c2, b2, nach) => (.elsif c b :: vor, c2, b2, nach)
  | arm :: rest => (elsifSpalte p rest).map fun (vor, c2, b2, nach) => (arm :: vor, c2, b2, nach)

/-- The declared type of an option or tagged static read by its name, outside any local of that name. -/
def statikTypVon (k : Kontext) : SExpr → Option STyp
  | .variable v =>
    if k.lokal.contains v then none else (k.statikTyp.find? fun entry => strEq entry.1 v).map (·.2)
  | _ => none

/-- `let x = S;` for a tagged static `S` whose type has a case without a payload: a fresh mutable
    local starts at that case and a `match S` assigns it the case `S` holds; `x` is then bound to it.
    `none` when `e` is no such static. -/
def leseStatik (k : Kontext) (nr : Nat) (mu : Bool) (x : String) (ty : Option STyp) : SExpr → Option (List SAnw × Nat)
  | .variable v =>
    if k.lokal.contains v then none else
    match k.statikFaelle.find? (fun entry => strEq entry.1 v), k.statikTyp.find? (fun entry => strEq entry.1 v) with
    | some (_, faelle), some (_, typ) =>
      match faelle.find? (fun fall => !fall.2) with
      | none => none
      | some (start, _) =>
        let r := "#r" ++ toString nr
        let p := "#r" ++ toString (nr + 1)
        some ([.bind true r (some typ) (.variable start),
          .cases (.variable v) (faelle.map fun (fall, nutzlast) =>
            if nutzlast then .arm fall (some p) (.block [.set (.variable r) "=" (.call fall [.variable p])] none)
            else .arm fall none (.block [.set (.variable r) "=" (.variable fall)] none)),
          .bind mu x (ty.orElse fun _ => some typ) (.variable r)], nr + 2)
    | _, _ => none
  | _ => none

/-- Rewrite one statement into the statements that replace it, with the next fresh number. -/
def hebeS (k : Kontext) : Nat → Nat → SAnw → List SAnw × Nat
  | 0, nr, s => ([s], nr)
  | n + 1, nr, s =>
    -- A body: every statement in order, each seeing the names bound before it, then the calls of a
    -- closing `return`. `zus` are names the body itself opens (a loop binder, a payload, a reason).
    let koerper : List String → Nat → SAnw → SAnw × Nat := fun zus nr b =>
      match b with
      | .block ss ende =>
        let r := ss.foldl (fun (acc : List SAnw × Nat × List String) t =>
          let x := hebeS { k with lokal := acc.2.2 } n acc.2.1 t
          (acc.1 ++ x.1, x.2, ExportMetadata.binders t ++ acc.2.2)) ([], nr, zus ++ k.lokal)
        match ende with
        | some (.ret (some e)) =>
          let x := hebeOben { k with lokal := r.2.2 } n r.2.1 e
          (.block (r.1 ++ x.1) (some (.ret (some x.2.1))), x.2.2)
        | _ => (.block r.1 ende, r.2.1)
      | t =>
        let x := hebeS { k with lokal := zus ++ k.lokal } n nr t
        match x.1 with
        | [one] => (one, x.2)
        | many => (.block many none, x.2)
    let koerperL : Nat → List SAnw → List SAnw × Nat := fun nr bs =>
      bs.foldl (fun (acc : List SAnw × Nat) b =>
        let x := koerper [] acc.2 b
        (acc.1 ++ [x.1], x.2)) ([], nr)
    match s with
    | .bind mu x ty e =>
      match leseStatik k nr mu x ty e with
      | some gelesen => gelesen
      | none =>
        let r := if mu then (let y := hebeE k n nr true e; (y.1, y.2.1, y.2.2.1)) else hebeOben k n nr e
        (r.1 ++ [.bind mu x (ty.orElse fun _ => (feldTyp k r.2.1).orElse fun _ => statikTypVon k r.2.1) r.2.1], r.2.2)
    | .bindElse x ty e g b =>
      let r := hebeOben k n nr e
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.bindElse x ty r.2.1 g y.1], y.2)
    | .set target op value =>
      match target with
      | .variable x =>
        -- `x = Case(v);` is read as it stands for a local; for a static the value is bound first, as
        -- is any other call in the value. A compound assignment `x op= v` is `x = x op v`: the target
        -- is read first, so a call in `v` moves only when that read is no read of mutable state.
        let plain := strEq op "="
        let lokal := k.lokal.contains x || !(k.statics.finde x).isSome
        let r := match value with
          | .call c _ =>
            if plain && (k.faelle.finde c).isSome && lokal then hebeOben k n nr value
            else (let y := hebeE k n nr (plain || lokal) value; (y.1, y.2.1, y.2.2.1))
          | _ =>
            -- `S = End;` for a static `S`: the case without a payload is bound first as well.
            match (if !plain || lokal then none else bindeFall k true nr true value) with
            | some y => (y.1, y.2.1, y.2.2.1)
            | none => let y := hebeE k n nr (plain || lokal) value; (y.1, y.2.1, y.2.2.1)
        (r.1 ++ [.set target op r.2.1], r.2.2)
      | .field (.index base i) name =>
        -- A compound assignment reads the slot before the value: nothing in the value moves then.
        let ri := hebeE k n nr true i
        let rv := hebeE k n ri.2.2.1 (ri.2.2.2 && strEq op "=") value
        (ri.1 ++ rv.1 ++ [.set (.field (.index base ri.2.1) name) op rv.2.1], rv.2.2.1)
      | _ => ([s], nr)
    | .call f args =>
      let r := hebeArgs k n nr args
      (r.1 ++ [.call f r.2.1], r.2.2)
    | .callElse f args g b =>
      let r := hebeArgs k n nr args
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.callElse f r.2.1 g y.1], y.2)
    | .callIndElse p args g b =>
      let r := hebeArgs k n nr args
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.callIndElse p r.2.1 g y.1], y.2)
    | .ret (some e) =>
      let r := hebeOben k n nr e
      (r.1 ++ [.ret (some r.2.1)], r.2.2)
    | .cond c t eis sonst =>
      match elsifSpalte (fun bed => !(hebeE k n 0 true bed).1.isEmpty) eis with
      | some (vor, c2, b2, nach) =>
        hebeS k n nr (.cond c t vor (some (.block [.cond c2 b2 nach sonst] none)))
      | none =>
        let r := hebeE k n nr true c
        let yt := koerper [] r.2.2.1 t
        let ye := koerperL yt.2 eis
        match sonst with
        | some b =>
          let ys := koerper [] ye.2 b
          (r.1 ++ [.cond r.2.1 yt.1 ye.1 (some ys.1)], ys.2)
        | none => (r.1 ++ [.cond r.2.1 yt.1 ye.1 none], ye.2)
    | .elsif c b =>
      let y := koerper [] nr b
      ([.elsif c y.1], y.2)
    | .cases scrutinee arms =>
      let r := hebeE k n nr true scrutinee
      let y := koerperL r.2.2.1 arms
      (r.1 ++ [.cases r.2.1 y.1], y.2)
    | .arm v binder b =>
      let y := koerper binder.toList nr b
      ([.arm v binder y.1], y.2)
    | .emit z w p =>
      let r := hebeE k n nr true w
      (r.1 ++ [.emit z r.2.1 p], r.2.2.1)
    | .each a b c d m raw inv body =>
      let y := koerper [a] nr body
      ([.each a b c d m raw inv y.1], y.2)
    | .retry h b => let y := koerper [] nr b; ([.retry h y.1], y.2)
    | .loop h b => let y := koerper [] nr b; ([.loop h y.1], y.2)
    | .waive ns b => let y := koerper [] nr b; ([.waive ns y.1], y.2)
    | .trim o t b => let y := koerper [] nr b; ([.trim o t y.1], y.2)
    | .locks g o b => let y := koerper [] nr b; ([.locks g o y.1], y.2)
    | .watch d b => let y := koerper [] nr b; ([.watch d y.1], y.2)
    | .block _ _ => let y := koerper [] nr s; ([y.1], y.2)
    | _ => ([s], nr)

/-- Rewrite the body of a function. -/
def hebeKoerper (k : Kontext) (b : SAnw) : SAnw :=
  match (hebeS k 100000 0 b).1 with
  | [one] => one
  | many => .block many none

/-- Rewrite the ordinary functions of an item; a `const fn` is evaluated at compile time and stays. -/
def hebeItem (k : Kontext) : SItemTief → SItemTief
  | .fnT s b => if strEq s.art "const" then .fnT s b
    else .fnT s (hebeKoerper { k with lokal := s.params.map (·.1) } b)
  | .gateT item => .gateT (hebeItem k item)
  | item => item

/-- The names a `let` can bind a call of: functions, foreign prototypes and gates. -/
def fnNamen (items : List SItemTief) : List String :=
  items.filterMap fun
    | .fnT s _ => if strEq s.art "const" then none else some s.name
    | .protoT s => some s.name
    | .callT s => some s.name
    | .gateT (.fnT s _) => some s.name
    | _ => none

/-- The statics of a unit. -/
def statikNamen (items : List SItemTief) : List String :=
  items.filterMap fun
    | .globT _ n _ _ _ _ _ => some n
    | .atomT n _ _ _ _ => some n
    | _ => none

/-- The case names of the unit's tagged types. -/
def fallNamen (items : List SItemTief) : List String :=
  match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
  | .ok schemas => schemas.flatMap fun schema => schema.cases.map (·.1)
  | .error _ => []

/-- The fields of the unit's tables whose declared type is a string, an array or a record. -/
def feldNamen (items : List SItemTief) : List (String × String × STyp) :=
  let records : List String := items.filterMap fun
    | .typeT _ name _ _ (some (.raw _)) => some name
    | _ => none
  items.flatMap fun
    | .tableT name _ _ _ _ _ parts _ => parts.flatMap fun
      | .tSlot fields => fields.filterMap fun field =>
          match field.ftyp with
          | .array .. | .str _ => some (name, field.fname, field.ftyp)
          | .atom a => if records.contains a then some (name, field.fname, field.ftyp) else none
          | _ => none
      | _ => []
    | _ => []

/-- The statics of option or tagged type, with their declared type. -/
def statikTypen (items : List SItemTief) : List (String × STyp) :=
  let tagged : List String := match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
    | .ok schemas => schemas.map fun schema => schema.name
    | .error _ => []
  items.filterMap fun
    | .globT _ n t _ _ _ _ =>
      match t with
      | .index true _ => some (n, t)
      | .atom a => if tagged.contains a then some (n, t) else none
      | _ => none
    | _ => none

/-- The tagged statics with the cases of their type. -/
def statikFaelleVon (items : List SItemTief) : List (String × List (String × Bool)) :=
  match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
  | .error _ => []
  | .ok schemas =>
    items.filterMap fun
      | .globT _ n (.atom a) _ _ _ _ =>
        (schemas.find? fun schema => strEq schema.name a).map fun schema =>
          (n, schema.cases.map fun fall => (fall.1, fall.2.isSome))
      | _ => none

/-- **Calls inside expressions become bindings**, in every ordinary function of the unit. -/
def hebe (items : List SItemTief) : List SItemTief :=
  let k : Kontext :=
    { fns := Tafel.von _ (fnNamen items), statics := Tafel.von _ (statikNamen items),
      faelle := Tafel.von _ (fallNamen items), felder := feldNamen items, statikTyp := statikTypen items,
      statikFaelle := statikFaelleVon items }
  items.map (hebeItem k)

end Gabbro.Grammatik.Parser.CallHoist
