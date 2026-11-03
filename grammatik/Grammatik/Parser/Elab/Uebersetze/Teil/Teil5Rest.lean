module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

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
      | .ok (.ptr _) => .error "pointer as value without G form"
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
  resSum : Option (Nat × List (Option Ty)) := none
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
  nimmt : List String := []
  gibt : List String := []
  /-- Call-scoped owner loans (`borrows m`, C12). -/
  leiht : List String := []
  /-- The named `assume` witnessing a hardware origin (the generated core
      query's `assume` clause; `none` for software items and while unresolved). -/
  annahme : Option String := none

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
    (whys : List UWhy := []) (zeiger : List String := []) (zb : Nat := 0) (spaces : List String := []) (named : List (String × Ty) := []) (eigner : List String := []) :
    String × STyp → Except String (String × Ty × UParamArt)
  | (n, .raw r) =>
    match zeiger.findIdx? (strEq · r) with
    | .some j => .ok (n, Ty.fnptr (zb + j), .fnptr (zb + j))
    | .none =>
      match uTypIn alias tabs named spaces eigner (.raw r) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, uArtVon ty)
  | (n, .ptr raum rechte (.atom t)) =>
    if !strEq raum "normal" then .error "space without G form"
    else if strEq t "u8" then .error "live byte capability requires C01 value flow, C08 grant generations and C09 loans"
    else do
      let access ← uTableRight eigner rechte
      let (num, _) ← uTabNr tabs t
      pure (n, .ptr (.table num access), .ptr (.table num access))
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
      match uTypIn alias tabs named spaces eigner (.atom a) with
      | .error e => .error e
      | .ok ty => .ok (n, ty, uArtVon ty)
  | (n, t) =>
    match uTypIn alias tabs named spaces eigner t with
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
        | .ok (.ptr ⟨_, _, .table num⟩) =>
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
  nimmt : List String := []
  gibt : List String := []
  /-- Call-scoped owner loans (`borrows m`, C12). -/
  leiht : List String := []

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
  | .borrows m :: rest =>
    match uEffekteAux kopf tabs locks globs rest with
    | .error e => .error e
    | .ok r => .ok { r with leiht := m :: r.leiht }
  | _ :: _ => .error "effect without G form"

end Gabbro.Grammatik.Parser.Uebersetze
