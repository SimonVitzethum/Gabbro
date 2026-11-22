module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Kontext.LocalLookup
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Elab.Uebersetze.Teil4Index
public import Grammatik.Korpus.Programme.Export104

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

/-- The length operand of a full slice names the same lexical value.
    Restricting it to a resolved local avoids duplicating a memory read. -/
def uFullLocalSlice (ctx : UCtx) (first : Int) : USide → SExpr → Bool
  | .param name, .built "lenof" [.variable last] =>
    first == 0 && strEq name last &&
      match uValueType ctx (.param name) with
      | some (.arr ..) | some (.str ..) => true
      | _ => false
  | _, _ => false

/-- Expand a fixed number of array elements using the ordinary typed
    expression reader. The start and array operands are lexical locals. -/
def uLocalArraySpan (array start : USide) (element : Ty) : Nat → Nat → USide
  | _, 0 => .typed (.arr element 0) .arrNil
  | offset, count + 1 =>
    .arrCons (.idx array (.add start (.lit offset))) (uLocalArraySpan array start element (offset + 1) count)

def uSliceConstants (ctx : UCtx) : List (String × (Int × Int)) :=
  (ctx.lits.filter fun entry => !ctx.names.any (strEq · entry.1)).map
    (fun (name, value) => (name, (value, value)))

/-- Bounds must come from a resolved binding, never from an untyped
    local's placeholder range awaiting dependent lowering. -/
def uSliceLocalType (ctx : UCtx) (name : String) : Option Ty :=
  if ctx.unknownRanges.contains name then none else uValueType ctx (.param name)

/-- The dynamic endpoint form `array[start .. start + N]` fixes the
    number of selected elements statically. The same lexical start
    must be used at both endpoints, and its complete interval must fit. -/
def uFixedLocalArraySlice (ctx : UCtx) (blatt : SExpr → Except String USide) :
    USide → SExpr → SExpr → Option USide
  | .param array, .variable start, .bin "+" (.variable lastStart) amount => do
    if !strEq start lastStart then none else
      let some (.arr element length) := uSliceLocalType ctx array | none
      let some (.int lo hi) := uSliceLocalType ctx start | none
      let some count := uSchranke (uSliceConstants ctx) amount | none
      if 0 ≤ count ∧ 0 ≤ lo ∧ hi + count ≤ length then
        if blatt (.variable start) = .ok (.param start) then
          some (uLocalArraySpan (.param array) (.param start) element 0 count.toNat)
        else none
      else none
  | _, _, _ => none

/-- Observe a local array slice using its endpoints and, for an element
    observation, the translated index in the original array. -/
def uLocalArraySliceObservation (ctx : UCtx) (blatt : SExpr → Except String USide)
    (index : Option SExpr) : SExpr → Option USide
  | .built "#slice" [.variable array, .variable first, .variable last] => do
    let some (.arr _ capacity) := uSliceLocalType ctx array | none
    let some (.int firstLo firstHi) := uSliceLocalType ctx first | none
    let some (.int lastLo lastHi) := uSliceLocalType ctx last | none
    if 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity then
      if blatt (.variable array) = .ok (.param array) ∧
          blatt (.variable first) = .ok (.param first) ∧ blatt (.variable last) = .ok (.param last) then
        match index with
        | none => some (.sub (.param last) (.param first))
        | some (.variable name) => do
          let some (.int lo hi) := uSliceLocalType ctx name | none
          if 0 ≤ lo ∧ hi < lastLo - firstHi ∧ blatt (.variable name) = .ok (.param name) then
            some (.idx (.param array) (.add (.param first) (.param name)))
          else none
        | some _ => none
      else none
    else none
  | _ => none

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
    match uRecordConstructor ctx f with
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
    match uRecordConstructor ctx f with
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
  | .built "#slice" [base, first, last] => do
    let operand ← uRechne ctx blatt base
    if let some span := uFixedLocalArraySlice ctx blatt operand first last then return span
    let some first := uSchranke (uSliceConstants ctx) first | throw "slice: first endpoint must be static"
    if uFullLocalSlice ctx first operand last then return operand
    let some last := uSchranke (uSliceConstants ctx) last | throw "slice: last endpoint must be static"
    if first < 0 || last < first then throw "slice: invalid endpoint order"
    return .slice operand first.toNat last.toNat
  -- C13: `sizeof(e)` is the declared storage size of `e`, a literal only once it is resolved (`uGroesse`)
  | .built "sizeof" [a] =>
    match uGroesse ctx a with
    | some n => .ok (.lit (Int.ofNat n))
    | none => .error "sizeof without a resolved declared size"
  | .built "lenof" [a] =>
    if let some length := uLocalArraySliceObservation ctx blatt none a then .ok length
    else
      match uRechne ctx blatt a with
      | .error e => .error e
      | .ok x => .ok (.len x)
  | .ext .array [] values =>
    uArraySides ctx values (fun source smaller => uRechne ctx blatt source)
  | .ext .text [t] [] => .ok (.text (t.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
  | .index a i =>
    if let some element := uLocalArraySliceObservation ctx blatt (some i) a then .ok element
    else if uTraegerIndex ctx a then blatt (.index a i) else
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
    match uRecordConstructor ctx name with
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

/-- A full slice is admitted for a lexical string or array whenever the
    first endpoint proves zero. Its source export is that same value. -/
theorem fullLocalSlice_erfuellbar (ctx : UCtx) (blatt : SExpr → Except String USide)
    (name : String) (first : SExpr)
    (zero : uSchranke (uSliceConstants ctx) first = some 0)
    (localValue : uRechne ctx blatt (.variable name) = .ok (.param name))
    (aggregate : (∃ τ n, uValueType ctx (.param name) = some (.arr τ n)) ∨
      (∃ n, uValueType ctx (.param name) = some (.str n))) :
    uRechne ctx blatt (.built "#slice" [.variable name, first, .built "lenof" [.variable name]]) =
      .ok (.param name) := by
  rw [uRechne]
  have sameName : strEq name name = true := by simp [strEq]
  rcases aggregate with ⟨_, _, exactType⟩ | ⟨_, exactType⟩ <;>
    simp only [zero, localValue, bind, Except.bind, uFullLocalSlice, exactType,
      sameName, beq_self_eq_true, Bool.true_and, ite_true, pure, Except.pure, uFixedLocalArraySlice]

theorem fixedLocalArraySlice_erfuellbar (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array start : String) (element : Ty) (length : Nat) (lo hi count : Int) (amount : SExpr)
    (arrayRead : uRechne ctx blatt (.variable array) = .ok (.param array))
    (indexRead : blatt (.variable start) = .ok (.param start))
    (arrayType : uSliceLocalType ctx array = some (.arr element length))
    (indexType : uSliceLocalType ctx start = some (.int lo hi))
    (width : uSchranke (uSliceConstants ctx) amount = some count)
    (bounds : 0 ≤ count ∧ 0 ≤ lo ∧ hi + count ≤ length) :
    uRechne ctx blatt (.built "#slice"
      [.variable array, .variable start, .bin "+" (.variable start) amount]) =
      .ok (uLocalArraySpan (.param array) (.param start) element 0 count.toNat) := by
  rw [uRechne]
  have sameName : strEq start start = true := by simp [strEq]
  simp only [arrayRead, bind, Except.bind, uFixedLocalArraySlice, sameName, Bool.not_true,
    Bool.false_eq_true, ite_false, arrayType, indexType, width, bounds, ite_true, indexRead,
    and_self, pure, Except.pure]

/-- The accepted source shape exposes the actual length through subtraction. -/
theorem localArraySliceLength_erfuellbar (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array first last : String) (τ : Ty) (capacity : Nat) (firstLo firstHi lastLo lastHi : Int)
    (arrayType : uSliceLocalType ctx array = some (.arr τ capacity))
    (firstType : uSliceLocalType ctx first = some (.int firstLo firstHi))
    (lastType : uSliceLocalType ctx last = some (.int lastLo lastHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (locals : blatt (.variable array) = .ok (.param array) ∧
      blatt (.variable first) = .ok (.param first) ∧ blatt (.variable last) = .ok (.param last)) :
    uRechne ctx blatt (.built "lenof" [.built "#slice" [.variable array, .variable first, .variable last]]) =
      .ok (.sub (.param last) (.param first)) := by
  rw [uRechne]
  simp only [uLocalArraySliceObservation, arrayType, firstType, lastType, bounds, locals, and_self, ite_true]

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
