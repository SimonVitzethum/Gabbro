module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- An aggregate static (a number static goes to the integer lowering). -/
def lowGlobWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Option (Except String (LowWert u Γ Λ)) :=
  match globIdx u.globs p with
  | .error _ => none
  | .ok g =>
    match (globAt u g).ty with
    | .int .. | .bool => none
    | _ =>
      some (if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        .ok ⟨(declOf u).gtyp g, Expr.glob (D := declOf u) g hd⟩
      else .error "access without held guard")

/-- An aggregate field read through a pointer parameter (`p.slots[i].f`); `none` for any other field. -/
def lowDurchWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (b fname : String)
    (ix : UIdx) : Option (Except String (LowWert u Γ Λ)) :=
  match paramPos fn.params b with
  | .error _ => none
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
        (fieldHitW u ⟨num, h⟩ fname).map fun fi =>
          match lowVar Γ (sh + j) (.ptr num w), lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
          | .ok v, .ok i =>
            if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) then
              .ok ⟨_, Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) fi i hL⟩
            else .error "access without held guard"
          | .error e, _ | _, .error e => .error e
      else none
    | _ => none

/-- An aggregate field read at a table (`T.slots[i].f`); `none` for any other field. -/
def lowTabWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (b fname : String)
    (ix : UIdx) : Option (Except String (LowWert u Γ Λ)) :=
  match tabIdx u.tabs b with
  | .error _ => none
  | .ok t =>
    (fieldHitW u t fname).map fun fi =>
      match lowIdx u Γ Λ fn sh t ix with
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) then
          .ok ⟨_, Expr.slot (D := declOf u) t fi i hL⟩
        else .error "access without held guard"
      | .error e => .error e

/-- A constant literal at its type (`USide.typed`): numbers inside the range, array literals element by element,
    string literals under the maximum. -/
def lowLit {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : (τ : Ty) → USide → Except String (Expr (declOf u) Γ Λ τ)
  | .int lo hi, .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n)) else .error "constant outside its range"
    else .error "constant outside its range"
  | .arr _ 0, .arrNil => .ok Expr.arrNil
  | .arr τ (k + 1), .arrCons a r =>
    match lowLit τ a, lowLit (.arr τ k) r with
    | .ok a', .ok r' => .ok (Expr.arrCons a' r')
    | .error e, _ | _, .error e => .error e
  | .str m, .text bs =>
    match bytesZahl bs with
    | some zs => if h : zs.length ≤ m then .ok (Expr.strLit zs h) else .error "string literal longer than the maximum"
    | none => .error "string literal outside bytes"
  | _, _ => .error "constant without G form"

/-- The integer side of a value. -/
def zahlVon {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    Except String (LowWert u Γ Λ) → Except String (LowSide u Γ Λ)
  | .ok w => w.zahl
  | .error e => .error e

/-- A value of any type (`LowWert`), in an `ensures` (`er` the result type) or a body (`er = none`): literals,
    parameters, statics, slot reads, `old` and `result`, the integer arithmetic, and the aggregate forms (arrays and
    strings by their type). One structural recursion, so that the lowering stays reducible. -/
def lowWertE (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) : USide → Except String (LowWert u Γ Λ)
  | .lit n => .ok (LowSide.wert { range := (n, n), term := Expr.lit n })
  | .param p =>
    match lowParamWert u Γ Λ fn (if er.isSome then 1 else 0) p with
    | some r => r
    | none => (lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p).map LowSide.wert
  | .glob p =>
    match lowGlobWert u Γ Λ p with
    | some r => r
    | none => (lowGlobSide u Γ Λ p).map LowSide.wert
  | .slot b f ix =>
    match lowDurchWert u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | some r => r
    | none => (lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .refSlot r f =>
    (lowRefRead u Γ Λ fn (if er.isSome then 1 else 0) r f).map LowSide.wert
  | .tab b f ix =>
    match lowTabWert u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | some r => r
    | none => (lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .old b f ix =>
    (lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .add a b =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er b with
    | .ok ⟨.int a1 a2, x⟩, .ok ⟨.int b1 b2, y⟩ =>
      .ok (LowSide.plus { range := (a1, a2), term := x } { range := (b1, b2), term := y }).wert
    | .ok wa, .ok wb => catW wa wb
    | .error e, _ | _, .error e => .error e
  | .sub a b =>
    match zahlVon (lowWertE u Γ Λ fn er a), zahlVon (lowWertE u Γ Λ fn er b) with
    | .ok x, .ok y => .ok (LowSide.minus x y).wert
    | .error e, _ | _, .error e => .error e
  | .mul a b =>
    match zahlVon (lowWertE u Γ Λ fn er a), zahlVon (lowWertE u Γ Λ fn er b) with
    | .ok x, .ok y => .ok (LowSide.times x y).wert
    | .error e, _ | _, .error e => .error e
  | .conv lo hi a =>
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok x => (LowSide.conv lo hi x).map LowSide.wert
  | .band a b => (lowZwei LowSide.and (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .bor a b => (lowZwei LowSide.or (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .bxor a b => (lowZwei LowSide.xoder (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .div a b => (lowZwei LowSide.durch (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .rem a b => (lowZwei LowSide.rest (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .shl a b => (lowZwei LowSide.links (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .shr a b => (lowZwei LowSide.rechts (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .neg a =>
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok x => .ok (LowSide.minusEins x).wert
  | .erg =>
    match er with
    | some (.int a b) =>
      match lowVar Γ 0 (.int a b) with
      | .error e => .error e
      | .ok v => .ok ⟨.int a b, Expr.var v⟩
    | none =>
      match paramPos fn.params "#erg", fn.params.find? (·.1 == "#erg") with
      | .ok j, some (_, .int a b) =>
        match lowVar Γ j (.int a b) with
        | .error e => .error e
        | .ok v => .ok ⟨.int a b, Expr.var v⟩
      | _, _ => .error "result without result"
    | _ => .error "result without result"
  | .text bs => lowText bs
  | .arrNil => .error "an empty array literal needs its type"
  | .arrCons a r =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er r with
    | .ok wa, .ok wr => consW wa wr
    | .error e, _ | _, .error e => .error e
  | .idx a i =>
    match lowWertE u Γ Λ fn er a, zahlVon (lowWertE u Γ Λ fn er i) with
    | .ok wa, .ok wi => idxW wa wi
    | .error e, _ | _, .error e => .error e
  | .len a =>
    match lowWertE u Γ Λ fn er a with
    | .ok wa => lenW wa
    | .error e => .error e
  | .upd a i v =>
    match lowWertE u Γ Λ fn er a, zahlVon (lowWertE u Γ Λ fn er i), lowWertE u Γ Λ fn er v with
    | .ok wa, .ok wi, .ok wv => updW wa wi wv
    | .error e, _, _ | _, .error e, _ | _, _, .error e => .error e
  | .typed τ s => (lowLit τ s).map (⟨τ, ·⟩)
  | .eng s lo' hi' =>
    match lowWertE u Γ Λ fn er s with
    | .ok ⟨.int _ _, t⟩ =>
      if h : lo' ≤ hi' then .ok ⟨.int lo' hi', Expr.eng t lo' hi' (Expr.widen (Int.le_refl lo') h (Expr.lit lo'))⟩
      else .error "narrowing to an empty range"
    | .ok _ => .error "narrowing of a non-number"
    | .error e => .error e

/-- A comparison side in `ensures`: literals, numeric parameters,
    slot reads, `old` and `result` travel (the integer values of `lowWertE`). -/
def lowSideEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (s : USide) : Except String (LowSide u Γ Λ) :=
  zahlVon (lowWertE u Γ Λ fn er s)

/-- A value at the type `τ` (checking mode): an array literal element by element, everything else by `fitW`. -/
def lowWertAtE (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    (τ : Ty) → USide → Except String (Expr (declOf u) Γ Λ τ)
  | .arr _ 0, .arrNil => .ok Expr.arrNil
  | .arr τ (k + 1), .arrCons a r =>
    match lowWertAtE u Γ Λ fn er τ a, lowWertAtE u Γ Λ fn er (.arr τ k) r with
    | .ok a', .ok r' => .ok (Expr.arrCons a' r')
    | .error e, _ | _, .error e => .error e
  | τ, s =>
    match lowWertE u Γ Λ fn er s with
    | .ok w => fitW τ w
    | .error e => .error e

/-- A value side in a body: the sides of an `ensures` without `old` and `result` (a body reads neither). -/
def lowSideVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (s : USide) : Except String (LowSide u Γ Λ) :=
  if seiteAltErg s then .error "side in body without G form"
  else lowSideEns u Γ Λ fn none s

/-- One comparison in `ensures` (G folds all but `lt`/`le`/`eq`). -/
def lowCmp (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    String → USide → USide → Except String (Expr (declOf u) Γ Λ .bool)
  | op, a, b =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er b with
    | .ok ⟨.str _, x⟩, .ok ⟨.str _, y⟩ => do
      u.exportGate
      match op with
      | "==" => .ok (Expr.strEq x y)
      | "!=" => .ok (Expr.not (Expr.strEq x y))
      | "<" => .ok (Expr.strLt x y)
      | "<=" => .ok (Expr.or (Expr.strLt x y) (Expr.strEq x y))
      | ">" => .ok (Expr.strLt y x)
      | ">=" => .ok (Expr.or (Expr.strLt y x) (Expr.strEq x y))
      | _ => .error "operator without G form"
    | .ok ⟨.ref region, x⟩, .ok ⟨.ref other, y⟩ => do
      u.exportGate
      if same : other = region then
        match op with
        | "==" => .ok (Expr.refEq x (same ▸ y))
        | "!=" => .ok (Expr.not (Expr.refEq x (same ▸ y)))
        | _ => .error "source export: reference ordering has no canonical G form"
      else .error "source export: reference equality requires the same region"
    | _, _ =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok s1 =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

/-! ### Option values (`Ty.opt n`, `option index into T`)

An option value is `None` (`Expr.none`), `Some(i)` (`Expr.some` of an index expression of the table), an option
variable (a parameter or a `let`) or the read of an option field through a pointer (`Expr.thru`) or at a table
(`Expr.slot`). The field's type is `typAt u t f = .opt n` with `n` the count of the table the option indexes
(`OptHit`); the term is cast along that fact, as the integer reads are (`durchTerm`, `slotTerm`). -/

/-- An option field read through a pointer parameter, at its type `opt n`. -/
def durchTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (num : Nat) (h : num < u.tabs.length)
    (oh : OptHit u ⟨num, h⟩) {w : Bool} (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) oh.idx i hL

/-- An option field read at a table, at its type `opt n`. -/
def slotTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (t : Fin u.tabs.length) (oh : OptHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.slot (D := declOf u) t oh.idx i hL

/-- An option value over the table `num` (positions of parameters shift by `sh`, see `lowIdx`). -/
def lowOpt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (num : Nat) (hnum : num < u.tabs.length) :
    UOpt → Except String (Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hnum⟩)))
  | .nichts => .ok (Expr.none (D := declOf u) _)
  | .etwas ix =>
    match lowIdx u Γ Λ fn sh ⟨num, hnum⟩ ix with
    | .error e => .error e
    | .ok i => .ok (Expr.some (D := declOf u) i)
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.opt m) =>
        if m == num then
          match lowVar Γ (sh + j) (.opt ((declOf u).count ⟨num, hnum⟩)) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "option of a foreign table"
      | _ => .error "option without G form"
  | .slot b f ix =>
    match paramPos fn.params b with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.ptr pnum w) =>
        if h : pnum < u.tabs.length then
          match fieldHitO u ⟨pnum, h⟩ f with
          | .error e => .error e
          | .ok oh =>
            if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
              match lowVar Γ (sh + j) (.ptr pnum w) with
              | .error e => .error e
              | .ok pv =>
                match lowIdx u Γ Λ fn sh ⟨pnum, h⟩ ix with
                | .error e => .error e
                | .ok i =>
                  if hL : (∀ wdd ∈ (declOf u).braucht ⟨pnum, h⟩, Res.von (declOf u) wdd ∈ Λ) then
                    .ok (by rw [← hn]; exact durchTermO u Γ Λ pnum h oh pv i hL)
                  else .error "access without held guard"
            else .error "option of a foreign table"
        else .error "pointer table unknown"
      | _ => .error "place without G form"
  | .tab b f ix =>
    match tabIdx u.tabs b with
    | .error e => .error e
    | .ok t =>
      match fieldHitO u t f with
      | .error e => .error e
      | .ok oh =>
        if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
          match lowIdx u Γ Λ fn sh t ix with
          | .error e => .error e
          | .ok i =>
            if hL : (∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) then
              .ok (by rw [← hn]; exact slotTermO u Γ Λ t oh i hL)
            else .error "access without held guard"
        else .error "option of a foreign table"
  | .glob p =>
    match globIdx u.globs p with
    | .error e => .error e
    | .ok g =>
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        if h : (declOf u).gtyp g = .opt ((declOf u).count ⟨num, hnum⟩) then
          .ok (h ▸ Expr.glob (D := declOf u) g hd)
        else .error "option of a foreign table"
      else .error "access without held guard"

/-- Reify an ordinary held-lock fact only after checking the current resource list. -/
def lowHeld (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (name : String) :
    Except String (Expr (declOf u) Γ Λ .bool) := do
  u.exportGate
  match lockIdx u.locks name with
  | .error e => .error e
  | .ok lock =>
    if Res.held lock ∈ Λ then .ok Expr.tru
    else .error "Held predicate without possession"

/-- A self edge retains its declaration, field identity and exact optional index type. -/
structure SelfEdge (u : UProg) (table : Fin u.tabs.length) (name : String) where
  field : (declOf u).Feld table
  self : (declOf u).typ table field = .opt ((declOf u).count table)
  original : OptHit u table
  lookup : fieldHitO u table name = .ok original
  found : field = original.idx
  identity : original.tnum = table.val

/-- Equal slot counts never substitute for the identity of the edge's target table. -/
def selfEdge (u : UProg) (table : Fin u.tabs.length) (name : String) : Except String (SelfEdge u table name) :=
  match lookup : fieldHitO u table name with
  | .error error => .error error
  | .ok edge =>
    if same : edge.tnum = table.val then
      have tableSame : (⟨edge.tnum, edge.hlt⟩ : Fin u.tabs.length) = table := Fin.ext same
      have countSame : edge.n = (declOf u).count table := by
        rw [← edge.hcnt, tableSame]
      .ok ⟨edge.idx, edge.hopt.trans (congrArg Ty.opt countSame), edge, lookup, rfl, same⟩
    else .error "source export: reach edge points to another table"

/-- Source relations are built with the canonical typed index and guard checks. -/
def lowReach (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name field : String) (a b : UIdx) : Except String (Expr (declOf u) Γ Λ .bool) := do
  u.exportGate
  let table ← tabIdx u.tabs name
  let edge ← selfEdge u table field
  let start ← lowIdx u Γ Λ fn sh table a
  let stop ← lowIdx u Γ Λ fn sh table b
  if guard : (∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) then
    pure (.reaches table edge.field edge.self start stop guard)
  else .error "access without held guard"

/-- A membership operand is an integer value, not a proof that it is already in range.
    The second origin check also protects generic UProg callers from foreign nominal indices. -/
def lowMemberValue (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (shift : Nat)
    (table : Fin u.tabs.length) : UIdx → Except String (LowSide u Γ Λ)
  | .lit value => .ok {range := (value, value), term := .lit value}
  | .param name => do
    let position ← paramPos fn.params name
    match fn.kinds[position]? with
    | some .int => lowParamSide u Γ Λ fn shift name
    | some (.index origin) =>
        if origin == table.val then lowParamSide u Γ Λ fn shift name
        else .error "source export: index belongs to another table"
    | _ => .error "source export: membership value is not an integer index"

/-- Membership enumerates exactly G's finite slot domain, retaining its guard even for
    a statically out-of-range operand. No narrowing or integer-to-reference cast occurs. -/
def lowMember (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name : String) (index : UIdx) : Except String (Expr (declOf u) Γ Λ .bool) := do
  u.exportGate
  let table ← tabIdx u.tabs name
  let value ← lowMemberValue u Γ Λ fn sh table index
  if guard : (∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) then
    pure (Expr.existsSlots table (Expr.eq (.var .here) value.term.weaken) guard)
  else .error "access without held guard"

/-- The checked fixed array domain retains its real element type and length. Only lexical
    arrays are admitted: a stateful domain must first be captured by an explicit binding. -/
structure ArrayValue (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  element : Ty
  count : Nat
  value : Expr (declOf u) Γ Λ (.arr element count)
  lexical : value.orte.isEmpty = true

def lowArrayValue (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty)
    (source : USide) : Except String (ArrayValue u Γ Λ) := do
  match ← lowWertE u Γ Λ fn er source with
  | ⟨.arr element count, term⟩ =>
      if lexical : term.orte.isEmpty = true then .ok ⟨element, count, term, lexical⟩
      else .error "source export: array domain requires an immutable value binding"
  | _ => .error "source export: elems domain is not an array"

structure ArrayCarrier (u : UProg) (count : Nat) where
  table : Fin u.tabs.length
  same : (declOf u).count table = (count : Int)

def arrayCarrier (u : UProg) (count : Nat) : Except String (ArrayCarrier u count) := do
  let table ← tabIdx u.tabs (uArrayCarrierName count)
  if same : (declOf u).count table = (count : Int) then .ok ⟨table, same⟩
  else .error "source export: array iterator count disagrees with its value"


end Gabbro.Grammatik.Parser.UebersetzeAllg
