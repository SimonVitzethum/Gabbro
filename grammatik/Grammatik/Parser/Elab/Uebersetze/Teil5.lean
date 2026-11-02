module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

mutual
/-- One `ensures` predicate (the `tr_ensures` of `lean_g.rs`). -/
def uSichert (ctx : UCtx) : SExpr → Except String UEns
  | .ext k [x, dk] [subject, body] =>
    if !(k == XKind.all || k == XKind.any) then .error "ensures clause without G form"
    else if dk == "elems" then do
      let (array, _, count) ← uArrayDomain ctx subject
      let predicate ← uSichert {ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits} body
      pure (.arrayElements (k == XKind.all) array x predicate)
    else if dk == "descendants" || dk == "ancestors" then do
      let (table, number, seed, field) ← uTreeDomain ctx subject
      let count := (ctx.tabs[number]?).map (·.count) |>.getD 0
      let predicate ← uSichert {ctx with names := x :: ctx.names, kinds := .index number :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits} body
      pure (.filtered (k == XKind.all) table x field (dk == "ancestors") seed predicate)
    else if !strEq dk "slots" then .error "source export: quantifier domain lacks a canonical G expansion"
    else
      match subject with
      | .variable tn =>
        match uTabNr ctx.tabs tn with
        | .error e => .error e
        | .ok (num, c) =>
          match uSichert { ctx with names := x :: ctx.names, kinds := .index num :: ctx.kinds,
                                    types := Ty.index c :: ctx.types, bits := 0 :: ctx.bits } body with
          | .error e => .error e
          | .ok b => .ok (if k == XKind.all then .alle tn x b else .einige tn x b)
      | _ => .error "source export: slots domain requires an explicit table"
  | .ext .reach [field] [a, b] => uReachExport ctx field a b
  | .ext .mem ["slots"] [value, .variable table] => do
      let (number, _) ← uTabNr ctx.tabs table
      pure (.member table (← uMemberIndex ctx table number value))
  | .ext .mem ["elems"] [value, subject] => do
      let (array, element, _) ← uArrayDomain ctx subject
      let compared ← uSeite ctx value
      pure (.arrayElements false array "#array-member" (.cmp "==" compared (.param "#array-member")))
  | .ext .mem [kind] [value, seed] => do
      if kind != "descendants" && kind != "ancestors" then
        throw "source export: membership domain lacks a canonical G expansion"
      let (table, number, start, field) ← uTreeDomain ctx seed
      let stop ← uExportIndex ctx table number value
      pure (if kind == "ancestors" then .reach table field stop start else .reach table field start stop)
  | .ext .imp [] [p, q] =>
    match uSichert ctx p with
    | .error e => .error e
    | .ok a =>
      match uSichert ctx q with
      | .error e => .error e
      | .ok b => .ok (.imp a b)
  | .call "Held" [.variable name] =>
    if ctx.locks.any (fun lock => strEq lock.name name) then .ok (.held name)
    else .error ("lock unknown: " ++ name)
  | .bin op l r =>
    if uIstVgl op then
      -- the sides of `uSeite` first; a side that holds a count (C13) is read by `uZSeite` (the count-free forms read
      -- exactly as before)
      match uSeite ctx l, uSeite ctx r with
      | .ok a, .ok b => .ok (.cmp op a b)
      | _, _ =>
        match uZSeite ctx l with
        | .error e => .error e
        | .ok a =>
          match uZSeite ctx r with
          | .error e => .error e
          | .ok b => .ok (.cmp op a b)
    else if strEq op "&&" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.and a b)
    else if strEq op "||" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.or a b)
    else .error "operator without G form"
  | .un "!" q =>
    match uSichert ctx q with
    | .error e => .error e
    | .ok a => .ok (.not a)
  | .ext .all [_, "threads"] [_] | .ext .any [_, "threads"] [_] =>
      .error "source export: threads domain has no explicit scheduler-table binding"
  | .ext .mem ("chain" :: _) _ =>
      .error "source export: chain field-pair semantics lack a canonical G expansion"
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .res => if ctx.resBool then .ok .ergB else .error "ensures clause without G form"
  | .variable g =>
    match (match uParamNr ctx g with
        | .ok j =>
          match uArtBei ctx.kinds j with
          | .ok .bool => some true
          | _ => some false
        | .error _ => none : Option Bool) with
    | some true => .ok (.var g)
    | some false => .error "number as a truth value"
    | none =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .some gl =>
      match gl.ty with
      | .bool => .ok (.globB g)
      | _ => .error "number static as a truth value"
    | .none => .error "ensures clause without G form"
  | .ext .call [] [.field o "is_some"] =>
    match uOptEin ctx o with
    | .error x => .error x
    | .ok (v, m) => .ok (.istSome v m)
  -- C13: the numeric `aligned(x, N)` is `x mod N = 0` for a positive constant `N` (`Expr.rem`, signed remainder for
  -- a signed `x`); a capability (a pointer) is no number here and stays refused by the side reader
  | .built "aligned" [x, n] =>
    match uKonstWert 1 9223372036854775807 [] ctx.lits 64 n with
    | none => .error "source export: alignment must be a positive constant"
    | some m =>
      match uZSeite ctx x with
      | .error e => .error e
      | .ok s => .ok (.cmp "==" (.rem s (.lit m)) (.lit 0))
  | e =>
    match uZugriff ctx e with
    | .error x => .error (if uPraemisse x then x else "ensures clause without G form")
    | .ok (.thru b, tb, f, ix) => do
      uReadThrough ctx b
      if uBoolFeld ctx tb f then .ok (.slotB b f ix) else .error "ensures clause without G form"
    | .ok (.tabelle b, tb, f, ix) =>
      if uBoolFeld ctx tb f then .ok (.tabB b f ix) else .error "ensures clause without G form"

/-- C13: one side of a comparison with `count x in D : p` as a NUMBER at any depth of `+ - *` (`Expr.count`): the
    domains are `slots of T`, `descendants of s`, `ancestors of s` (the checked `reaches` filter) and `elems of a`
    (the index domain of a fixed array); every other form is the side of `uSeite`. The body is read under the binder
    `x` exactly as the bodies of `forall`/`exists` over the same domain. A count in a BODY value (not in a
    predicate) has no G form here. -/
def uZSeite (ctx : UCtx) : SExpr → Except String USide
  | .ext .count [x, dk] [subject, body] =>
    if dk == "elems" then do
      let (array, _, count) ← uArrayDomain ctx subject
      let inner : UCtx := { ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits }
      let predicate ← uSichert inner body
      pure (.zaehleFeld array x predicate)
    else if dk == "descendants" || dk == "ancestors" then do
      let (table, number, seed, field) ← uTreeDomain ctx subject
      let count := (ctx.tabs[number]?).map (·.count) |>.getD 0
      let inner : UCtx := { ctx with names := x :: ctx.names, kinds := .index number :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits }
      let predicate ← uSichert inner body
      pure (.zaehleBaum table x field (dk == "ancestors") seed predicate)
    else if !strEq dk "slots" then .error "source export: count domain lacks a canonical G expansion"
    else
      match subject with
      | .variable tn =>
        match uTabNr ctx.tabs tn with
        | .error e => .error e
        | .ok (num, c) =>
          match uSichert { ctx with names := x :: ctx.names, kinds := .index num :: ctx.kinds,
                                    types := Ty.index c :: ctx.types, bits := 0 :: ctx.bits } body with
          | .error e => .error e
          | .ok b => .ok (.zaehle tn x b)
      | _ => .error "source export: slots domain requires an explicit table"
  | .bin op a b =>
    if strEq op "+" || strEq op "-" || strEq op "*" then
      match uZSeite ctx a with
      | .error e => .error e
      | .ok x =>
        match uZSeite ctx b with
        | .error e => .error e
        | .ok y => .ok (if strEq op "+" then .add x y else if strEq op "-" then .sub x y else .mul x y)
    else uSeite ctx (.bin op a b)
  | e => uSeite ctx e
end

mutual
/-- `old(..)` or `result` inside a side (a count's body included). -/
def seiteAltErg : USide → Bool
  | .old .. | .erg => true
  | .add a b | .sub a b | .mul a b | .band a b | .bor a b | .bxor a b | .div a b | .rem a b | .shl a b | .shr a b =>
    seiteAltErg a || seiteAltErg b
  | .conv _ _ a | .neg a => seiteAltErg a
  | .ib1 _ _ a => seiteAltErg a
  | .ib2 _ _ a b => seiteAltErg a || seiteAltErg b
  | .zaehle _ _ b => ensAltErg b
  | .zaehleBaum _ _ _ _ _ b => ensAltErg b
  | .zaehleFeld a _ b => seiteAltErg a || ensAltErg b
  | .taggedValue _ _ a | .typed _ a | .len a | .present _ a => seiteAltErg a
  | .arrCons a b | .idx a b => seiteAltErg a || seiteAltErg b
  | .product _ _ fields => fields.any (fun (_, side) => seiteAltErg side)
  | .field a _ => seiteAltErg a
  | .replace a _ b => seiteAltErg a || seiteAltErg b
  | .upd a i v => seiteAltErg a || seiteAltErg i || seiteAltErg v
  | .predicate p => ensAltErg p
  | _ => false

/-- `old(..)` or `result` inside a predicate. -/
def ensAltErg : UEns → Bool
  | .cmp _ a b => seiteAltErg a || seiteAltErg b
  | .and a b | .or a b | .imp a b => ensAltErg a || ensAltErg b
  | .not a => ensAltErg a
  | .alle _ _ b | .einige _ _ b | .filtered _ _ _ _ _ _ b => ensAltErg b
  | .arrayElements _ source _ b => seiteAltErg source || ensAltErg b
  | .ergB => true
  | _ => false
end
