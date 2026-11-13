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
  match uSichert
      { ctx with
        res := none
        resBool := false } e with
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
  | value@(.ext .count _ _) => do
    let side ← uZSeite ctx value
    if seiteAltErg side then .error "old or result in a body" else .ok side
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

/-- Executable reader with the identical list specification and cached projections. -/
def uWertBlattFast (ctx : UCtx) : SExpr → Except String USide
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
      match uKindAt ctx j with
      | .ok (.ptr _) => .error "pointer as value without G form"
      | .ok .bool => .error "truth value as a number"
      | .ok (.ref _) => .error "reference as a number"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | value@(.ext .count _ _) => do
    let side ← uZSeite ctx value
    if seiteAltErg side then .error "old or result in a body" else .ok side
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

@[csimp] theorem uWertBlatt_eq_fast : @uWertBlatt = @uWertBlattFast := by
  funext ctx value
  rfl

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

/-- A named alias supplies a word width only when it denotes that complete unsigned word.
    Explicitly ranged builtin storage keeps its written width (needed by nonzero scans). -/
def uWordBindingBreite (alias : List (String × (Int × Int))) (ty : STyp)
    (widths : List (String × (Int × Int)) := []) : Nat :=
  match ty with
  | .atom name =>
    let width := uSpeicherBreite widths ty
    if 0 < uAtomBreite name then width else
      match uTypName alias name with
      | .ok (lo, hi) => if lo = 0 ∧ hi = (2 : Int) ^ width - 1 then width else 0
      | .error _ => 0
  | _ => uSpeicherBreite widths ty

/-- Compiler-only declaration widths. Canonical printed heads retain their existing metadata. -/
def uBindingBreite (ctx : UCtx) (ty : STyp) : Nat :=
  if ctx.narrow then uWordBindingBreite ctx.alias ty ctx.widths else uParamBreite ty

/-- Read parameter storage from the written signature, after erasing device handles. -/
def uParameterBreiten (alias : List (String × (Int × Int))) (params : List (String × STyp))
    (widths : List (String × (Int × Int)) := []) : List Nat :=
  params.map (fun parameter => uWordBindingBreite alias parameter.2 widths)

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
  | (n, source@(.ptr _ _ (.atom _))) =>
    match uTypIn alias tabs named spaces eigner source with
    | .error error => .error error
    | .ok (.ptr cap) => .ok (n, .ptr cap, .ptr cap)
    | .ok _ => .error "pointer parameter without G form"
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

private theorem uArtVon_ne_ptr (ty : Ty) (cap : DataCapTy) : uArtVon ty ≠ .ptr cap := by
  cases ty <;> simp [uArtVon]

/-- Every successful pointer parameter producer writes the same complete capability into
    its type and kind. Spaces, rights and owners are never reconstructed from flag pairs. -/
theorem uParam_pointer_coherent
    (alias : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum)
    (whys : List UWhy) (zeiger : List String) (zb : Nat) (spaces : List String)
    (named : List (String × Ty)) (eigner : List String)
    {source : String × STyp} {result : String × Ty × UParamArt}
    (accepted : uParam alias tabs sums whys zeiger zb spaces named eigner source = .ok result)
    (cap : DataCapTy) (kind : result.2.2 = .ptr cap) : result.2.1 = .ptr cap := by
  unfold uParam at accepted
  repeat' split at accepted
  all_goals cases accepted
  all_goals first
    | exact False.elim (uArtVon_ne_ptr _ _ kind)
    | (cases kind <;> rfl)

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
  /-- Linear owner handoffs (`moves m`, C09). -/
  bewegt : List String := []
  /-- Checked owner mints (`mints m`, C09). -/
  praegt : List String := []

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
  | [] => .ok
      { locks := []
        puts := [] }
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
      | .ok r => .ok
          { r with
            puts := a :: r.puts
            gputs := (a ++ "#used") :: r.gputs }
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
  | .moves m :: rest =>
    match uEffekteAux kopf tabs locks globs rest with
    | .error e => .error e
    | .ok r => .ok { r with bewegt := m :: r.bewegt }
  | .mints m :: rest =>
    match uEffekteAux kopf tabs locks globs rest with
    | .error e => .error e
    | .ok r => .ok { r with praegt := m :: r.praegt }
  | _ :: _ => .error "effect without G form"

end Gabbro.Grammatik.Parser.Uebersetze
