module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Elab.Uebersetze.Teil4Index

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def uZugriff (ctx : UCtx) : SExpr →
    Except String (UBasis × String × String × UIdx)
  | .index (.variable b) idx =>
    match ctx.tabs.find? (fun x => strEq x.name b) with
    | .some tb =>
      if !tb.arena then .error "place without G form"
      else
        match uHaeltWaechter ctx tb.name with
        | .error e => .error e
        | .ok _ =>
          match uTabNrAux ctx.tabs 0 tb.name with
          | .error e => .error e
          | .ok (num, _) =>
            match uIndex ctx tb.name num idx with
            | .error e => .error e
            | .ok ix => .ok (.tabelle b, tb.name, "wert", ix)
    | .none => .error "place without G form"
  | .field (.index (.field (.variable b) s) idx) f =>
    if !strEq s "slots" then .error "place without G form"
    else
      match uParamNr ctx b with
      | .ok j =>
        match uArtBei ctx.kinds j with
        | .ok (.ptr ⟨_, _, .table num⟩) =>
          match ctx.tabs[num]? with
          | .none => .error "pointer table unknown"
          | .some tb =>
            if tb.arena then .error "place without G form"
            else if !(tb.cols.any (fun (g, _) => strEq g f)) then
              .error "field unknown"
            else match uHaeltWaechter ctx tb.name with
              | .error e => .error e
              | .ok _ =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.thru b, tb.name, f, ix)
        | _ => .error "place without G form"
      | .error _ =>
        match ctx.tabs.find? (fun x => strEq x.name b) with
        | .none => .error ("name unknown: " ++ b)
        | .some tb =>
          if tb.arena then .error "place without G form"
          else if !(tb.cols.any (fun (g, _) => strEq g f)) then
            .error "field unknown"
          else match uHaeltWaechter ctx tb.name with
            | .error e => .error e
            | .ok _ =>
              match uTabNrAux ctx.tabs 0 tb.name with
              | .error e => .error e
              | .ok (num, _) =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.tabelle b, tb.name, f, ix)
  | _ => .error "place without G form"

/-- The field `f` of the table `tb` is a `bool` field. -/
def uBoolFeld (ctx : UCtx) (tb f : String) : Bool :=
  match ctx.tabs.find? (fun x => strEq x.name tb) with
  | .some x => x.bools.any (fun g => strEq g f)
  | .none => false

/-- The option field `f` of the table `tb`: the number of the table its values index. -/
def uOptFeld (ctx : UCtx) (tb f : String) : Option Nat :=
  match ctx.tabs.find? (fun x => strEq x.name tb) with
  | .some x => (x.opts.find? (fun p => strEq p.1 f)).map (·.2)
  | .none => none

/-- A limit word `T::max` / `T::min` of a type word (an alias or a built-in width), as its number
    (the `grenzwort` of `tr_typed`: it travels as a literal). -/
def uGrenzwort (ctx : UCtx) : SExpr → Option Int
  | .field (.variable t) f =>
    match uTypName ctx.alias t with
    | .ok (lo, hi) =>
      if strEq f "max" then some hi
      else if strEq f "min" then some lo
      else none
    | .error _ => none
  | _ => none

/-- An error of the place reader that names a premise of the model (the read is outside the table, or the guard
    is not held), not a missing form: it must reach the verdict, not be masked by the leaf's own message. -/
def uPraemisse (e : String) : Bool :=
  strEq e "index outside count" || strEq e "access without held guard" ||
    strEq e "read through pointer without read right"

/-- Reading a place through a parameter needs read permission, including in contracts and old views.
    An owned capability with read permission elaborates (C12): the owner mark travels only through
    the checked owner flow and guards (never via the read/write flags alone); the lowering
    admits the read only where the table's owner guard is held (`darf` over `braucht`). -/
def uReadThrough (ctx : UCtx) (name : String) : Except String Unit := do
  let j ← uParamNr ctx name
  let kind ← uArtBei ctx.kinds j
  match kind with
  | .ptr ⟨_, ⟨true, _, _⟩, _⟩ => .ok ()
  | .ptr _ => .error "read through pointer without read right"
  | _ => .error "place without G form"

/-- `a[i]` reads a CARRIER (a table's or an arena's slot, `T.slots[i]`, `p.slots[i]`, `A[i]`), not an aggregate value. -/
def uTraegerIndex (ctx : UCtx) : SExpr → Bool
  | .field _ f => strEq f "slots"
  | .variable n => ctx.tabs.any (fun t => strEq t.name n)
  | _ => false

/-- The arithmetic layer shared by body values and `ensures` sides: `+ - *`, `& | ^` and the
    integer conversion `T(e)`; every other form is a LEAF, handled by `blatt`. C13 adds the closed integer builtins
    (`+% -% *% <<% +|`, `clz ctz log2_floor popcount bswap rotl rotr`) at the declared storage width. -/
def uRechne (ctx : UCtx) (blatt : SExpr → Except String USide) : SExpr → Except String USide
  | .bin op a b =>
    if strEq op "+" || strEq op "-" || strEq op "*" || strEq op "&" || strEq op "|" || strEq op "^"
        || strEq op "/" || strEq op "%" || strEq op "<<" || strEq op ">>" then
      match uRechne ctx blatt a with
      | .error e => .error e
      | .ok x =>
        match uRechne ctx blatt b with
        | .error e => .error e
        | .ok y =>
          if strEq op "+" then .ok (.add x y)
          else if strEq op "-" then .ok (.sub x y)
          else if strEq op "*" then .ok (.mul x y)
          else if strEq op "&" then .ok (.band x y)
          else if strEq op "|" then .ok (.bor x y)
          else if strEq op "^" then .ok (.bxor x y)
          else if strEq op "/" then .ok (.div x y)
          else if strEq op "%" then .ok (.rem x y)
          else if strEq op "<<" then .ok (.shl x y)
          else .ok (.shr x y)
    else
      match uBinEin op with
      | some bi =>
        match uRechne ctx blatt a with
        | .error e => .error e
        | .ok x =>
          match uRechne ctx blatt b with
          | .error e => .error e
          | .ok y =>
            if bi == .addS then .ok (.ib2 bi 0 x y)
            else
              match uBreite ctx (.bin op a b) with
              | some w => .ok (.ib2 bi w x y)
              | none => .error "builtin of unknown width"
      | none => blatt (.bin op a b)
  | .un "-" (.lit v) => .ok (.lit (-(Int.ofNat v)))
  | .un "-" a =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.neg x)
  | .un "-()" a =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.neg x)
  | .un "~" (.variable p) =>
    -- `~p` is `p ^ (2^w - 1)` over the parameter's declared STORAGE width `w` (what the checker reads);
    -- for any other operand the width is not known here, so the form is refused.
    match uParamNr ctx p with
    | .error _ => blatt (.un "~" (.variable p))
    | .ok j =>
      match ctx.bits[j]?, uArtBei ctx.kinds j with
      | .some w, .ok .int =>
        if 0 < w then .ok (.bxor (.param p) (.lit ((2 : Int) ^ w - 1)))
        else .error "complement of unknown width"
      | _, _ => .error "complement of unknown width"
  | .call f [a] =>
    match ctx.records.find? (fun schema => strEq schema.name f) with
    | some schema => do
      let values ← uRecordSides ctx [a] (fun source smaller => uRechne ctx blatt source)
      uRecordValues schema values
    | none =>
      match uTypName ctx.alias f with
      | .ok (lo, hi) =>
        match uRechne ctx blatt a with
        | .error e => .error e
        | .ok x => .ok (.conv lo hi x)
      | .error _ =>
        match uBitEin f with
        | some bi =>
          match uRechne ctx blatt a with
          | .error e => .error e
          | .ok x =>
            match uBreite ctx a with
            | some w => .ok (.ib1 bi w x)
            | none => .error "builtin of unknown width"
        | none => blatt (.call f [a])
  | .call f [a, b] =>
    match ctx.records.find? (fun schema => strEq schema.name f) with
    | some schema => do
      let values ← uRecordSides ctx [a, b] (fun source smaller => uRechne ctx blatt source)
      uRecordValues schema values
    | none =>
      match uRotEin f with
      | some bi =>
        match uRechne ctx blatt a with
        | .error e => .error e
        | .ok x =>
          match uRechne ctx blatt b with
          | .error e => .error e
          | .ok y =>
            match uBreite ctx a with
            | some w => .ok (.ib2 bi w x y)
            | none => .error "builtin of unknown width"
      | none => blatt (.call f [a, b])
  -- C13: `sizeof(e)` is the declared storage size of `e`, a literal only once it is resolved (`uGroesse`)
  | .built "sizeof" [a] =>
    match uGroesse ctx a with
    | some n => .ok (.lit (Int.ofNat n))
    | none => .error "sizeof without a resolved declared size"
  | .built "lenof" [a] =>
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x => .ok (.len x)
  | .ext .text [t] [] => .ok (.text (t.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
  | .index a i =>
    if uTraegerIndex ctx a then blatt (.index a i) else
    match uRechne ctx blatt a with
    | .error e => .error e
    | .ok x =>
      match uRechne ctx blatt i with
      | .error e => .error e
      | .ok y => .ok (.idx x y)
  /- A field projection from a by-value product (`p.f`): the base elaborates first, then the
      nominal position is resolved from the schema. -/
  | .field base field =>
    match blatt (.field base field) with
    | .ok value => .ok value
    | .error original =>
      match uRechne ctx blatt base with
      | .error _ => .error original
      | .ok value => .ok (.field value field)
  /- An `old` view that is not a carrier read may project a record field of the old value. -/
  | .old base =>
    match blatt (.old base) with
    | .ok value => .ok value
    | .error _ =>
      match uRechne ctx blatt base with
      | .error e => .error e
      | .ok value => uOldRecord value
  /- Labelled record constructors share the canonical component elaborator and schema order. -/
  | .call name args =>
    match ctx.records.find? (fun schema => strEq schema.name name) with
    | some schema => do
      let values ← uRecordSides ctx args (fun source smaller => uRechne ctx blatt source)
      uRecordValues schema values
    | none => blatt (.call name args)
  | e => blatt e
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals try simp_all
  all_goals omega

/-- A name that is no parameter and no constant: a number static (`Expr.glob`), or an unknown name. -/
def uGlobLies (ctx : UCtx) (p : String) : Except String USide :=
  match ctx.globs.find? (fun g => strEq g.name p) with
  | .some g =>
    match g.ty with
    | .bool => .error "bool static as a number"
    | _ => .ok (.glob p)
  | .none => .error ("name unknown: " ++ p)

/-- One side of an `ensures` comparison (the `tr_side` of
    `lean_g.rs`): literals, numeric parameters, named constants, limit words, slot reads,
    `old` and `result` travel, with the arithmetic layer of `uRechne`; a pointer parameter in a
    comparison and everything else are explicit errors. -/
def uSeiteBlatt (ctx : UCtx) : SExpr → Except String USide
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
      | .ok (.ptr _) => .error "pointer in a compare without G form"
      | .ok .bool => .error "truth value as a number"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | .res =>
    match ctx.res with
    | .some _ => .ok .erg
    | .none => .error "result without result"
  | .old o =>
    match uZugriff ctx o with
    | .error e => .error e
    | .ok (.thru b, _, f, ix) => do
      uReadThrough ctx b
      pure (.old b f ix)
    | .ok (.tabelle b, _, f, ix) => .ok (.old b f ix)
  | e =>
    match uGrenzwort ctx e with
    | .some v => .ok (.lit v)
    | .none =>
      match uZugriff ctx e with
      | .error x => .error (if uPraemisse x then x else "compare side without G form")
      | .ok (.thru b, tb, f, ix) => do
        uReadThrough ctx b
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.slot b f ix)
      | .ok (.tabelle b, tb, f, ix) =>
        if uBoolFeld ctx tb f then .error "bool field as a number"
        else if (uOptFeld ctx tb f).isSome then .error "option field as a number" else .ok (.tab b f ix)

def uSeite (ctx : UCtx) : SExpr → Except String USide :=
  uRechne ctx (uSeiteBlatt ctx)

/-- A comparison operator with G form (`==`, `!=`, `<`, `<=`,
    `>`, `>=`; G folds all but `lt`/`le`/`eq`). -/
def uIstVgl : String → Bool
  | "==" => true
  | "!=" => true
  | "<" => true
  | "<=" => true
  | ">" => true
  | ">=" => true
  | _ => false

/-- An option value read off an expression, with the number of its table: an option variable or the read of
    an option field. -/
def uOptEin (ctx : UCtx) : SExpr → Except String (UOpt × Nat)
  | .variable p =>
    match uParamNr ctx p with
    | .error e =>
      match ctx.globs.find? (fun g => strEq g.name p) with
      | .some gl =>
        match gl.optNum with
        | .some m => .ok (.glob p, m)
        | .none => .error e
      | .none => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.opt m) => .ok (.var p, m)
      | _ => .error "match without G form"
  | e =>
    match uZugriff ctx e with
    | .error x => .error x
    | .ok (b, tb, f, ix) =>
      match uOptFeld ctx tb f with
      | .none => .error "match without G form"
      | .some m =>
        match b with
        | .thru p => do
          uReadThrough ctx p
          pure (.slot p f ix, m)
        | .tabelle t => .ok (.tab t f ix, m)

end Gabbro.Grammatik.Parser.Uebersetze
