/-
  File:      Grammatik/Gen/Reflect.lean
  Subject:   Generator, the generic part: a random term generator read off the INDUCTIVE TYPES. It works on
             the type's constructor list in the environment (`getConstInfoInduct`) and the constructors'
             binder types; it names no constructor of the grammar. A new constructor of `SAnw`/`SExpr`/`STyp`
             is generated the moment it exists.

             Plausible's deriving handler (checked: it derives `Arbitrary` for the surface AST, see
             `Gen/Leaves.lean`) cannot give a leaf its ROLE: a `String` that is an operator at `SExpr.bin` is a
             name at `SExpr.variable`, and an uninformed pool makes the parse alone refuse 99 % of the
             candidates (measured, 0 of 600 accepted). So the leaf roles are a small table keyed by
             constructor and field (`rollen`), and the weights another (`gewichte`): data about the leaves,
             not syntax. Everything not in a table falls back to the default pool.

  The result is a closed `Lean.Expr` (a constructor application); `Gen/Bau.lean` evaluates batches of them.
-/
import Lean

namespace Gabbro.Grammatik.Gen

open Lean Meta

/-- Default leaf pools. -/
def namenPool : List String := ["x", "y", "z", "i", "j", "k", "A", "B", "F", "T", "U", "L", "v", "w", "b", "n"]
def zahlenPool : List Nat := [0, 0, 1, 1, 2, 3, 4, 5, 7, 8, 9, 10, 15, 16, 100, 127, 128, 255, 256, 1000]

/-- Leaf roles: key `Type.ctor.fieldIndex` (the last two name components of the constructor) to the
    pool of strings that make sense there. -/
def rollen : List (String × List String) :=
  [ ("SExpr.bin.0", ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<", "<=", "==", "!=", ">", ">=", "&&", "||"])
  , ("SExpr.un.0", ["!", "-", "~"])
  , ("SAnw.set.1", ["=", "=", "=", "+=", "-="])
  , ("SExpr.variable.0", ["x", "y", "z", "i", "j", "A", "B", "F", "L", "T"])
  , ("SExpr.field.1", ["v", "w", "b", "n", "slots"])
  , ("SExpr.call.0", ["h"])
  , ("SExpr.built.0", ["sizeof", "lenof"])
  , ("SAnw.call.0", ["h"])
  , ("SAnw.bind.1", ["x", "y", "z", "a", "c", "p", "q", "r", "s", "t", "u", "w"])
  , ("SAnw.each.0", ["i", "j", "k"])
  , ("SAnw.arm.0", ["0", "1", "2", "3"])
  , ("SAnw.each.2", ["slots"])
  , ("SAnw.each.4", ["unvisited"])
  , ("SAnw.each.5", [""])
  , ("SAnw.leave.0", ["i", "j", "k"])
  , ("SAnw.next.0", ["i", "j", "k"])
  , ("SEnde.leave.0", ["i", "j", "k"])
  , ("SEnde.next.0", ["i", "j", "k"])
  , ("STyp.atom.0", ["u8", "u16", "u32", "bool", "u64", "i8"]) ]

/-- Constructor weights (default 1). A weight of 0 would opt a constructor out; none is. -/
def gewichte : List (String × Nat) :=
  [("SAnw.bind", 4), ("SAnw.set", 4), ("SAnw.cond", 3), ("SAnw.locks", 2), ("SAnw.each", 2),
   ("SExpr.lit", 3), ("SExpr.variable", 3), ("SExpr.bin", 3)]

/-- Shapes the reader builds at one place: a field that holds a block, an `else if`, a match arm. The
    printer prints any tree, the parser reads back only these; without this table 60 % of the candidates
    die in the parser (measured). Key `Type.ctor.fieldIndex`, value the constructor the field must be. -/
def erzwinge : List (String × String) :=
  [ ("SAnw.cond.1", "SAnw.block"), ("SAnw.cond.2", "SAnw.elsif"), ("SAnw.cond.3", "SAnw.block")
  , ("SAnw.elsif.1", "SAnw.block"), ("SAnw.cases.1", "SAnw.arm"), ("SAnw.arm.2", "SAnw.block")
  , ("SAnw.each.7", "SAnw.block"), ("SAnw.retry.1", "SAnw.block"), ("SAnw.loop.1", "SAnw.block")
  , ("SAnw.waive.1", "SAnw.block"), ("SAnw.trim.2", "SAnw.block"), ("SAnw.locks.2", "SAnw.block")
  , ("SAnw.watch.1", "SAnw.block"), ("SAnw.grow.2", "SAnw.block"), ("SAnw.child.0", "SAnw.block")
  , ("SAnw.bindElse.4", "SAnw.block"), ("SAnw.alloc.5", "SAnw.block") ]

/-- Fields that introduce a name: the pool loses the names already in scope (a second `let` of the same
    name is refused by the checker, rule `N001`, though the model's de Bruijn terms allow it). -/
def binderRollen : List String := ["SAnw.bind.1"]

/-- Probability (percent) that a field listed in `saatRollen` takes a seed of its role. -/
def saatProzent : Nat := 75

/-- Seed roles of expression fields: key `Type.ctor.fieldIndex` to the role (0 integer value, 1 truth
    value, 2 assignable place, 3 lock name, 4 table name). The seeds themselves are computed from the frame. -/
def saatRollen : List (String × Nat) :=
  [("SAnw.bind.3", 0), ("SAnw.set.2", 0), ("SAnw.set.0", 2), ("SAnw.cond.0", 1), ("SAnw.elsif.0", 1),
   ("SAnw.locks.1", 3), ("SAnw.ret.0", 0), ("SEnde.ret.0", 0), ("SAnw.call.1", 0), ("SAnw.cases.0", 0),
   ("SAnw.each.6", 1), ("SAnw.each.3", 4), ("SExpr.bin.1", 0), ("SExpr.bin.2", 0), ("SExpr.un.1", 0), ("SExpr.index.1", 0)]

/-- The last two components of a name: `Gabbro.Grammatik.Parser.SAnw.bind` to `SAnw.bind`. -/
def kurzName (n : Name) : String :=
  match n with
  | .str p s => (match p with | .str _ t => t ++ "." ++ s | _ => s)
  | _ => n.toString

def wuerfle (lo hi : Nat) : IO Nat := IO.rand lo hi

def waehle {α : Type} [Inhabited α] (xs : List α) : IO α := do
  if xs.isEmpty then return default
  let i ← wuerfle 0 (xs.length - 1)
  return xs[i]!

/-- The head constants a field type mentions, through `List`/`Option`/`Prod`. -/
partial def koepfe (t : Expr) : List Name :=
  match t.getAppFn with
  | .const n _ =>
    if n == ``List || n == ``Option || n == ``Prod then t.getAppArgs.toList.flatMap koepfe else [n]
  | _ => []

structure Kontext where
  /-- the inductive types reachable from the root through constructor fields. -/
  huelle : List Name
  /-- those with a constructor that needs no value of a type of the closure outside `grund` (the base). -/
  grund : List Name
  /-- seeds: the type they are values of, the function `Nat → T` that makes one from a code, and per role
      the first code and the count. -/
  saatTyp : Name := .anonymous
  saatFn : Name := .anonymous
  /-- a function `String → T` that makes a seed of `saatTyp` from a name, and the names in scope. -/
  saatLokal : Name := .anonymous
  lokale : List String := []
  saat : Nat → Option (Nat × Nat) := fun _ => none

/-- A field type that needs a value of a non-base type of the closure (no `Option`/`List` escape). -/
partial def zwingend (k : Kontext) (t : Expr) : Bool :=
  match t.getAppFn with
  | .const n _ =>
    if n == ``List || n == ``Option then false
    else if n == ``Prod then t.getAppArgs.any (zwingend k)
    else k.huelle.contains n && !k.grund.contains n
  | _ => false

/-- The closure of a root type and its base types (least fixed point). -/
partial def baueKontext (root : Name) : MetaM Kontext := do
  let mut huelle : List Name := []
  let mut todo := [root]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if huelle.contains n then continue
    if !(n.toString.startsWith "Gabbro") then continue
    let some (.inductInfo info) := (← getEnv).find? n | continue
    huelle := n :: huelle
    for c in info.ctors do
      let ci ← getConstInfoCtor c
      let tys ← forallTelescope ci.type fun xs _ => xs.mapM inferType
      for t in tys do todo := todo ++ koepfe t
  let mut grund : List Name := []
  let mut aenderung := true
  while aenderung do
    aenderung := false
    for n in huelle do
      if grund.contains n then continue
      let info ← getConstInfoInduct n
      let k : Kontext := { huelle, grund }
      let mut hat := false
      for c in info.ctors do
        let ci ← getConstInfoCtor c
        let tys ← forallTelescope ci.type fun xs _ => xs.mapM inferType
        if !(tys.any (zwingend k)) then hat := true
      if hat then grund := n :: grund; aenderung := true
  return { huelle, grund }

/-- Generate a closed term of type `ty` with recursion budget `fuel`; `schl` is the field key for roles. -/
partial def erzeuge (k : Kontext) (ty : Expr) (fuel : Nat) (schl : String) : MetaM Expr := do
  let ty ← whnfR ty
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  match fn with
  | .const n us =>
    if n == ``String then
      let pool := (rollen.lookup schl).getD namenPool
      let pool := if binderRollen.contains schl then pool.filter (!k.lokale.contains ·) else pool
      return mkStrLit (← waehle pool)
    else if n == ``Nat then
      return mkNatLit (← waehle zahlenPool)
    else if n == ``Bool then
      return mkConst (if (← wuerfle 0 1) == 0 then ``Bool.false else ``Bool.true)
    else if n == ``List then
      let len ← if fuel == 0 then pure 0 else (do let l ← wuerfle 0 7; pure (if l == 0 then 0 else 1 + l % 3))
      let mut es := #[]
      for _ in [0:len] do
        es := es.push (← erzeuge k args[0]! (fuel - 1) schl)
      mkListLit args[0]! es.toList
    else if n == ``Option then
      if fuel == 0 || (← wuerfle 0 2) == 0 then mkNone args[0]!
      else mkSome args[0]! (← erzeuge k args[0]! (fuel - 1) schl)
    else if n == ``Prod then
      let a ← erzeuge k args[0]! fuel schl
      let b ← erzeuge k args[1]! fuel schl
      return mkAppN (mkConst ``Prod.mk us) #[args[0]!, args[1]!, a, b]
    else
      -- seeds: a declared place or call stands in for a generated value of this type
      match (if n == k.saatTyp then (saatRollen.lookup schl).bind k.saat else none) with
      | some (base, cnt) =>
        if (saatRollen.lookup schl) == some 0 && !k.lokale.isEmpty && (← wuerfle 1 100) ≤ 40 then
          return mkApp (mkConst k.saatLokal) (mkStrLit (← waehle k.lokale))
        else if cnt > 0 && (← wuerfle 1 100) ≤ saatProzent then
          return mkApp (mkConst k.saatFn) (mkNatLit (base + (← wuerfle 0 (cnt - 1))))
        else erzeugeInd k n fuel schl
      | none => erzeugeInd k n fuel schl
  | _ => throwError "erzeuge: unsupported type {ty}"
where
  erzeugeInd (k : Kontext) (n : Name) (fuel : Nat) (schl : String) : MetaM Expr := do
    let info ← getConstInfoInduct n
    -- the constructors with their field types
    let mut cands : Array (Name × Array Expr × Nat) := #[]
    for c in info.ctors do
      let ci ← getConstInfoCtor c
      let tys ← forallTelescope ci.type fun xs _ => xs.mapM inferType
      let ok := fuel > 0 || !(tys.any (zwingend k))
      let erzwungen := (erzwinge.lookup schl).map (kurzName c == ·)
      if ok && erzwungen.getD true then
        cands := cands.push (c, tys, (gewichte.lookup (kurzName c)).getD 1)
    if cands.isEmpty then throwError "erzeuge: no constructor of {n} fits the budget"
    let total := cands.foldl (· + ·.2.2) 0
    let mut r ← wuerfle 1 total
    let mut pick := cands[0]!
    for c in cands do
      if r ≤ c.2.2 then pick := c; break
      r := r - c.2.2
    let (c, tys, _) := pick
    let mut as := #[]
    let mut i := 0
    for t in tys do
      as := as.push (← erzeuge k t (fuel - 1) (kurzName c ++ "." ++ toString i))
      i := i + 1
    return mkAppN (mkConst c) as

end Gabbro.Grammatik.Gen
