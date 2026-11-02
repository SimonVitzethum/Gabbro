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
      match uSeite ctx l with
      | .error e => .error e
      | .ok a =>
        match uSeite ctx r with
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
  | e =>
    match uZugriff ctx e with
    | .error x => .error (if uPraemisse x then x else "ensures clause without G form")
    | .ok (.thru b, tb, f, ix) =>
      if uBoolFeld ctx tb f then .ok (.slotB b f ix) else .error "ensures clause without G form"
    | .ok (.tabelle b, tb, f, ix) =>
      if uBoolFeld ctx tb f then .ok (.tabB b f ix) else .error "ensures clause without G form"

/-- `old(..)` or `result` inside a side. -/
def seiteAltErg : USide → Bool
  | .old .. | .erg => true
  | .add a b | .sub a b | .mul a b | .band a b | .bor a b | .bxor a b | .div a b | .rem a b | .shl a b | .shr a b =>
    seiteAltErg a || seiteAltErg b
  | .conv _ _ a | .neg a => seiteAltErg a
  | _ => false

/-- `old(..)` or `result` inside a predicate. -/
def ensAltErg : UEns → Bool
  | .cmp _ a b => seiteAltErg a || seiteAltErg b
  | .and a b | .or a b | .imp a b => ensAltErg a || ensAltErg b
  | .not a => ensAltErg a
  | .alle _ _ b | .einige _ _ b | .filtered _ _ _ _ _ _ b | .arrayElements _ _ _ b => ensAltErg b
  | .ergB => true
  | _ => false

/-- A truth value in a BODY (a returned or stored `bool`): the predicate forms of an `ensures`,
    without `old` and `result`. -/
def uBool (ctx : UCtx) (e : SExpr) : Except String UEns :=
  match uSichert { ctx with res := none, resBool := false } e with
  | .error x => .error x
  | .ok v => if ensAltErg v then .error "old or result in a body" else .ok v

/-- A leaf of a body value: a literal, a numeric parameter, a named constant, a limit word or a
    slot read. -/
def uWertBlatt (ctx : UCtx) : SExpr → Except String USide
  | .lit v => .ok (.lit (Int.ofNat v))
  | .variable p =>
    match uParamNr ctx p with
    | .error _ =>
      match ctx.lits.find? (fun k => strEq k.1 p) with
      | .some k => .ok (.lit k.2)
      | .none =>
        match ctx.arrKonst.find? (fun k => strEq k.1 p) with
        | .some k => .ok k.2
        | .none => uGlobLies ctx p
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr _ _) => .error "pointer as value without G form"
      | .ok .bool => .error "truth value as a number"
      | .ok (.ref _) => .error "reference as a number"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | .arrow (.variable r) f =>
    match uRefLokal ctx r with
    | .some _ => .ok (.refSlot r f)
    | .none => .error "value without G form"
  | e =>
    match uGrenzwort ctx e with
    | .some v => .ok (.lit v)
    | .none =>
      match uZugriff ctx e with
      | .error x => .error (if uPraemisse x then x else "value without G form")
      | .ok (.thru b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.slot b f ix)
      | .ok (.tabelle b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.tab b f ix)

/-- A value in a body (the `tr_value` of `lean_g.rs` at `in_ensures := false`: `result` and
    `old` have no G form here), with the arithmetic layer of `uRechne`. -/
def uWertBody (ctx : UCtx) : SExpr → Except String USide :=
  uRechne ctx (uWertBlatt ctx)

/-- Sequence: the first error wins (like the exporter's
    straight-line `?`). -/
def uSeq : List (Except String α) → Except String (List α)
  | [] => .ok []
  | .error e :: _ => .error e
  | .ok x :: rest =>
    match uSeq rest with
    | .error e => .error e
    | .ok xs => .ok (x :: xs)

/-- One function head: name, parameters (names, kinds, types),
    the optional result range and the held lock names (pass one
    of `collect` in `lean_g.rs`). -/
structure UFnKopf where
  name : String
  names : List String
  kinds : List UParamArt
  types : List Ty
  res : Option (Int × Int)
  resBool : Bool := false
  resOpt : Option (Nat × Int) := none
  /-- The reason channel: the position of `R` among the unit's reasons and its number of cases. -/
  kanal : Option (Nat × Nat) := none
  /-- The result is a tagged type: its position and its specification. -/
  resSum : Option (Nat × List (Option (Int × Int))) := none
  /-- The result is a reason (`-> R`): the position of `R` among the unit's reasons and its number of cases. -/
  resWhy : Option (Nat × Nat) := none
  bits : List Nat := []
  held : List String
  /-- The statics it writes. -/
  gputs : List String := []
  /-- A foreign body (`extern fn`): called as `D.Ax`, never as a function of the unit. -/
  ext : Bool := false
  /-- The answer of a foreign body is `never` (the call does not return). -/
  resNever : Bool := false
  /-- The device handles among the declared parameters: the position in the WRITTEN parameter list, the
      name and the device. They are erased from `names`/`kinds`/`types`; a call drops their arguments. -/
  griffe : List (Nat × String × String) := []
  /-- The answer of a foreign body is a reference into the open table number `n` (`-> index into T`). -/
  resRef : Option Nat := none
  /-- The result is an aggregate value: its type. -/
  resTy : Option Ty := none
  /-- The tables a foreign body writes (`ext`). -/
  puts : List String := []
  /-- The linear marks the function consumes (`effects { consumes m }`, C16). -/
  nimmt : List String := []
  /-- The linear marks the function produces (`effects { allocs m }`, C16). -/
  gibt : List String := []

/-- The kind and the type of the value a call of a function of the unit binds: a truth value, a number, a
    reason. -/
def uWertArt (k : UFnKopf) : Option (UParamArt × Ty) :=
  if let some τ := k.resTy then some (UParamArt.wert, τ) else
  if k.resBool then some (UParamArt.bool, Ty.bool)
  else match k.res with
    | some r => some (UParamArt.int, Ty.int r.1 r.2)
    | none => k.resWhy.map (fun (k, n) => (UParamArt.why k, Ty.why n))

/-- The answer type of a foreign body. -/
def UFnKopf.axErg (k : UFnKopf) : Option Ty :=
  if let some n := k.resRef then some (Ty.ref n)
  else if k.resNever then some Ty.never
  else if k.resBool then some Ty.bool
  else k.res.map fun r => Ty.int r.1 r.2

/-- The storage width of a declared parameter type: a bare unsigned word, with or without a range
    (`u8 in 0 .. 15` is stored in 8 bits); `0` for everything else. -/
def uParamBreite : STyp → Nat
  | .atom a | .range (.atom a) _ _ _ =>
    if strEq a "u8" then 8 else if strEq a "u16" then 16
    else if strEq a "u32" then 32 else if strEq a "u64" then 64 else 0
  | _ => 0

/-- A parameter with its kind (the `param_ty` of `lean_g.rs`). -/
def uParam (alias : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum := [])
    (whys : List UWhy := []) (zeiger : List String := []) (zb : Nat := 0) :
    String × STyp → Except String (String × Ty × UParamArt)
  | (n, .raw r) =>
    match zeiger.findIdx? (strEq · r) with
    | .some j => .ok (n, Ty.fnptr (zb + j), .fnptr (zb + j))
    | .none =>
      match uTyp alias tabs (.raw r) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, .int)
  | (n, .ptr raum rechte (.atom t)) =>
    if !strEq raum "normal" then .error "space without G form"
    else if strEq rechte "rw" || strEq rechte "own" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num true, .ptr num true)
    else if strEq rechte "r" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num false, .ptr num false)
    else .error "pointer right without G form"
  | (n, .index false t) =>
    match uTabNr tabs t with
    | .error e => .error e
    | .ok (num, c) => .ok (n, .index c, .index num)
  | (n, .atom "bool") => .ok (n, .bool, .bool)
  | (n, .index true t) =>
    match uTabNr tabs t with
    | .error e => .error e
    | .ok (num, c) => .ok (n, .opt c, .opt num)
  | (n, .atom a) =>
    match sums.findIdx? (fun s => strEq s.name a) with
    | .some k =>
      match sums[k]? with
      | .some s => .ok (n, Ty.sum s.spec, UParamArt.sum k)
      | .none => .error ("type unknown: " ++ a)
    | .none =>
      match whys.findIdx? (fun w => strEq w.name a) with
      | .some k =>
        match whys[k]? with
        | .some w => .ok (n, Ty.why w.cases.length, UParamArt.why k)
        | .none => .error ("reason unknown: " ++ a)
      | .none =>
      match uTyp alias tabs (.atom a) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, .int)
  | (n, t) =>
    match uTyp alias tabs t with
    | .error e => .error e
    | .ok ty => .ok (n, ty, uArtVon ty)

/-- A result range (the `int_range` of `lean_g.rs` on the
    result type). -/
def uErgBereich (alias : List (String × (Int × Int))) : STyp →
    Except String (Int × Int)
  | .atom a => uTypName alias a
  | .range _ lo hi o =>
    match uSchranke alias lo, uSchranke alias hi with
    | some a, some b => .ok (a, if o then b - 1 else b)
    | _, _ => .error "result without G form"
  | t => .error ("result without G form: " ++ sTypText t)

/-- `requires Held(L)`: exactly the signature-held locks (the
    requires loop of `check_fn`; every other requires-clause is
    an explicit error). -/
def uGehaltenAux : List ULock → List SExpr → Except String (List String)
  | _, [] => .ok []
  | locks, .variable l :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("lock unknown: " ++ l)
    | .some _ =>
      match uGehaltenAux locks rest with
      | .error e => .error e
      | .ok ls => .ok (l :: ls)
  | _, _ :: _ => .error "requires clause without G form"

def uGehalten (locks : List ULock) : List SKlausel →
    Except String (List String)
  | [] => .ok []
  | .needs (.call "Held" args) :: rest =>
    match uGehaltenAux locks args with
    | .error e => .error e
    | .ok ls =>
      match uGehalten locks rest with
      | .error e => .error e
      | .ok ms => .ok (ls ++ ms)
  | .needs _ :: rest => uGehalten locks rest
  | _ :: rest => uGehalten locks rest

/-- A name position in a list (for `writes` through a
    parameter). -/
def uStelle : List String → String → Except String Nat
  | [], p => .error ("name unknown: " ++ p)
  | q :: rest, p =>
    if strEq q p then .ok 0
    else
      match uStelle rest p with
      | .error e => .error e
      | .ok k => .ok (k + 1)

/-- The table a `writes` place names (the `write_table` of
    `lean_g.rs`): `writes k.slots` through a pointer parameter,
    or `writes T.slots` at a table. -/
def uSchreibtOrt (kopf : UFnKopf) (tabs : List UTab) : SExpr →
    Except String String
  | .field (.variable b) s =>
    if !strEq s "slots" then .error "writes clause without G form"
    else
      match uStelle kopf.names b with
      | .ok j =>
        match uArtBei kopf.kinds j with
        | .ok (.ptr num _) =>
          match tabs[num]? with
          | .some tb => .ok tb.name
          | .none => .error "pointer table unknown"
        | _ => .error "writes clause without G form"
      | .error _ =>
        match tabs.find? (fun x => strEq x.name b) with
        | .some tb => .ok tb.name
        | .none => .error ("name unknown: " ++ b)
  | _ => .error "writes clause without G form"

/-- The effect arms: `locks L` names held locks, `writes`
    names written tables, `reads`/`pure`/`diverges` are no form
    (ignored, like `lean_g.rs`); every other arm is an explicit
    error. -/
structure UEffekte where
  locks : List String
  puts : List String
  gputs : List String := []
  /-- The linear marks the function consumes (`effects { consumes m }`, C16). -/
  nimmt : List String := []
  /-- The linear marks the function produces (`effects { allocs m }`, C16). -/
  gibt : List String := []

/-- A written name is a static when it is no parameter and no table. -/
def uIstGlobName (kopf : UFnKopf) (tabs : List UTab) (globs : List UGlob) (g : String) : Bool :=
  !(kopf.names.any (strEq · g)) && !(tabs.any (fun x => strEq x.name g)) && globs.any (fun x => strEq x.name g)

/-- A place through a device handle (`d`, `d.R`, `d.R.F`): a register is outside the world, so `writes d`
    names no carrier (the class decides the access, `Stmt.regWrite`). -/
def uIstGriffOrt (kopf : UFnKopf) : SExpr → Bool
  | .variable h => kopf.griffe.any (fun g => strEq g.2.1 h)
  | .field o _ => uIstGriffOrt kopf o
  | _ => false

def uEffekteAux (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) (globs : List UGlob) :
    List SEffekt → Except String UEffekte
  | [] => .ok { locks := [], puts := [] }
  | .locks false (.variable l) :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("lock unknown: " ++ l)
    | .some _ =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with locks := l :: r.locks }
  | .writes o :: rest =>
    if uIstGriffOrt kopf o then uEffekteAux kopf tabs locks globs rest else
    match (match o with
        | .variable a => if tabs.any (fun x => x.arena && strEq x.name a) then some a else none
        | _ => none : Option String) with
    | some a =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with puts := a :: r.puts, gputs := (a ++ "#used") :: r.gputs }
    | none =>
    match (match o with
        | .variable g => if uIstGlobName kopf tabs globs g then some g else none
        | _ => none : Option String) with
    | some g =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with gputs := g :: r.gputs }
    | none =>
    match uSchreibtOrt kopf tabs o with
    | .error e => .error e
    | .ok t =>
      match uEffekteAux kopf tabs locks globs rest with
      | .error e => .error e
      | .ok r => .ok { r with puts := t :: r.puts }
  | .reads _ :: rest => uEffekteAux kopf tabs locks globs rest
  | .pure :: rest => uEffekteAux kopf tabs locks globs rest
  | .loops :: rest => uEffekteAux kopf tabs locks globs rest
  | .allocs m :: rest =>
    match uEffekteAux kopf tabs locks globs rest with
    | .error e => .error e
    | .ok r => .ok { r with gibt := m :: r.gibt }
  | .takes (.variable m) :: rest =>
    match uEffekteAux kopf tabs locks globs rest with
    | .error e => .error e
    | .ok r => .ok { r with nimmt := m :: r.nimmt }
  | _ :: _ => .error "effect without G form"

end Gabbro.Grammatik.Parser.Uebersetze
