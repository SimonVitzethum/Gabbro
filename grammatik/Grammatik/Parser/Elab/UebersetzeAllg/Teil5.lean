module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil4
public import Grammatik.Parser.Elab.Generic.C09Sig

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

mutual

/-- A value of any type (`LowWert`), in an `ensures` (`er` the result type) or a body (`er = none`): literals,
    parameters, statics, slot reads, `old` and `result`, the integer arithmetic, and the aggregate forms (arrays and
    strings by their type). One structural recursion, so that the lowering stays reducible. -/
def lowWertE (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) : USide → Except String (LowWert u Γ Λ)
  | .lit n => .ok (LowSide.wert { range := (n, n), term := Expr.lit n })
  | .truth b => .ok ⟨.bool, if b then Expr.tru else Expr.fls⟩
  | .predicate p => (lowEns u Γ Λ fn er p).map (⟨.bool, ·⟩)
  | .absent n => .ok ⟨.opt n, Expr.none (D := declOf u) n⟩
  | .present n value =>
    (lowWertAtE u Γ Λ fn er (Ty.index n) value).map (fun term => ⟨.opt n, Expr.some (D := declOf u) term⟩)
  | .option num value =>
    if h : num < u.tabs.length then
      (lowOpt u Γ Λ fn (if er.isSome then 1 else 0) num h value).map
        (⟨.opt ((declOf u).count ⟨num, h⟩), ·⟩)
    else .error "option table unknown"
  | .reason count tag =>
    if h : tag < count then .ok ⟨.why count, Expr.why (D := declOf u) count ⟨tag, h⟩⟩
    else .error "reason case outside the type"
  | .function signature name => (lowFnRef u Γ Λ signature name).map (⟨.fnptr signature, ·⟩)
  | .taggedEmpty cs i =>
    if hi : i < cs.length then
      match hc : cs.get ⟨i, hi⟩ with
      | none => .ok ⟨.sum cs, Expr.case cs ⟨i, hi⟩ (hc.symm ▸ NutzlastExpr.empty)⟩
      | some _ => .error "missing tagged payload"
    else .error "case outside the tagged type"
  | .taggedValue cs i value =>
    if hi : i < cs.length then
      match hc : cs.get ⟨i, hi⟩ with
      | none => .error "extra tagged payload"
      | some τ =>
        match lowWertAtE u Γ Λ fn er τ value with
        | .ok term => .ok ⟨.sum cs, Expr.case cs ⟨i, hi⟩ (hc.symm ▸ NutzlastExpr.val term)⟩
        | .error e => .error e
    else .error "case outside the tagged type"
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

  | .ib1 bi w a =>
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok x => (lowIb1 bi w x).map LowSide.wert
  | .ib2 bi w a b =>
    (lowZwei (lowIb2 bi w) (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .zaehle .. | .zaehleBaum .. | .zaehleFeld .. => .error "count is read only in a comparison of a predicate"
  /- A nominal product value: every field elaborated at its carried type, then checked against
      a declared nominal schema -- no structural guess, no default field. -/
  | .product identity _ sides => do
    u.exportGate
    let args ← lowProductArgs u Γ Λ fn er sides
    match uRecordOf u.records (.prod identity (sides.map (·.1))) with
    | .error e => .error e
    | .ok _ => .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩
  /- A field projection from a by-value product: the position comes from the nominal schema. -/
  | .field base name => do
    u.exportGate
    let ⟨τ, e⟩ ← lowWertE u Γ Λ fn er base
    let ⟨sch, hsch⟩ ← uRecordOf u.records τ
    let ⟨fieldTy, pos⟩ ← uRecordPosition sch.fields name
    let baseE : Expr (declOf u) Γ Λ sch.ty := cast (congrArg (Expr (declOf u) Γ Λ) hsch.symm) e
    pure ⟨fieldTy, Expr.prodGet baseE pos⟩
  /- A field replacement on a by-value product: read/modify/write of the whole local value. -/
  | .replace base name value => do
    u.exportGate
    let ⟨τ, e⟩ ← lowWertE u Γ Λ fn er base
    let ⟨sch, hsch⟩ ← uRecordOf u.records τ
    let ⟨fieldTy, pos⟩ ← uRecordPosition sch.fields name
    let baseE : Expr (declOf u) Γ Λ sch.ty := cast (congrArg (Expr (declOf u) Γ Λ) hsch.symm) e
    let v ← lowWertAtE u Γ Λ fn er fieldTy value
    pure ⟨sch.ty, Expr.prodSet baseE pos v⟩
termination_by value => 3 * sizeOf value
decreasing_by all_goals (simp_wf <;> omega)

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

termination_by _ value => 3 * sizeOf value + 1
decreasing_by all_goals (simp_wf <;> omega)

/-- Elaborate the existing ordered typed field list, keeping recursive calls visible to the
    shared termination proof. Every component uses the same canonical checking-mode lowerer. -/
def lowProductArgs (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    (sides : List (Ty × USide)) → Except String (Args (declOf u) Γ Λ (sides.map (·.1)))
  | [] => .ok .nil
  | (ty, side) :: rest => do
    let head ← lowWertAtE u Γ Λ fn er ty side
    let tail ← lowProductArgs u Γ Λ fn er rest
    pure (.cons head tail)
termination_by sides => 3 * sizeOf sides + 2
decreasing_by all_goals (simp_wf <;> omega)

/-- One comparison in `ensures` (G folds all but `lt`/`le`/`eq`). -/
def lowCmp (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    String → USide → USide → Except String (Expr (declOf u) Γ Λ .bool)
  | op, a, b =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er b with
    | .ok ⟨.fl _ _, x⟩, .ok ⟨.fl _ _, y⟩ =>
      match op with
      | "<" => .ok (Expr.fllt x y)
      | "<=" => .ok (Expr.flle x y)
      | ">" => .ok (Expr.fllt y x)
      | ">=" => .ok (Expr.flle y x)
      | _ => .error "float: comparison without canonical G form"
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
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok s1 =>
      match zahlVon (lowWertE u Γ Λ fn er b) with
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

termination_by _ a b => 3 * (sizeOf a + sizeOf b) + 1
decreasing_by all_goals (simp_wf <;> omega)

/-- One `ensures` predicate. -/
def lowEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | .arrayElements universal source binder body => do
      u.exportGate
      let array ← lowArrayValue u Γ Λ fn er source
      let carrier ← arrayCarrier u array.count
      let fnR ← ergAlsParam u fn er
      if guard : (∀ resource ∈ (declOf u).braucht carrier.table, Res.von (declOf u) resource ∈ Λ) then
        let predicate ← lowEns u (Ty.index ((declOf u).count carrier.table) :: Γ) Λ
          (fnR.mitTy binder (.index ((declOf u).count carrier.table))) none body
        pure (if universal then Expr.forallSlots carrier.table predicate guard else Expr.existsSlots carrier.table predicate guard)
      else .error "access without held guard"
  | .reach table field a b => lowReach u Γ Λ fn (if er.isSome then 1 else 0) table field a b
  | .member table index => lowMember u Γ Λ fn (if er.isSome then 1 else 0) table index
  | .filtered all name binder field reverse source body => do
      u.exportGate
      let table ← tabIdx u.tabs name
      let edge ← selfEdge u table field
      let seed ← lowIdx u Γ Λ fn (if er.isSome then 1 else 0) table source
      let fnR ← ergAlsParam u fn er
      if guard : (∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) then
        let predicate ← lowEns u (.index ((declOf u).count table) :: Γ) Λ
          (fnR.mitIndex binder table.val ((declOf u).count table)) none body
        let filter : Expr (declOf u) (Ty.index ((declOf u).count table) :: Γ) Λ .bool :=
          if reverse then Expr.reaches table edge.field edge.self (.var .here) seed.weaken guard
          else Expr.reaches table edge.field edge.self seed.weaken (.var .here) guard
        pure (if all then Expr.forallSlots table (Expr.impl filter predicate) guard
          else Expr.existsSlots table (Expr.and filter predicate) guard)
      else .error "access without held guard"
  | .held name => lowHeld u Γ Λ name
  | .imp a b => do
      u.exportGate
      pure (Expr.or (Expr.not (← lowEns u Γ Λ fn er a)) (← lowEns u Γ Λ fn er b))
  | .cmp op a b =>
    if usideHatZaehle a || usideHatZaehle b then
      match lowSeiteZ u Γ Λ fn er a, lowSeiteZ u Γ Λ fn er b with
      | .ok s1, .ok s2 => lowVglSeiten op s1 s2
      | .error e, _ | _, .error e => .error e
    else lowCmp u Γ Λ fn er op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .globB p => lowGlobBool u Γ Λ p
  | .ergB =>
    match er with
    | some .bool =>
      match lowVar Γ 0 .bool with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)
    | none =>
      match paramPos fn.params "#erg", fn.params.find? (·.1 == "#erg") with
      | .ok j, some (_, .bool) =>
        match lowVar Γ j .bool with
        | .error e => .error e
        | .ok v => .ok (Expr.var v)
      | _, _ => .error "result without result"
    | _ => .error "result without result"
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match lowVar Γ ((if er.isSome then 1 else 0) + j) .bool with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)
  | .istSome o num =>
    if h : num < u.tabs.length then
      match lowOpt u Γ Λ fn (if er.isSome then 1 else 0) num h o with
      | .error e => .error e
      | .ok x => .ok (Expr.istSome x)
    else .error "option table unknown"
  | .slotB b f ix => lowBoolDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .tabB b f ix => lowBoolTab u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .alle tn x body =>
    match tabIdx u.tabs tn, ergAlsParam u fn er with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok t, .ok fnR =>
      if hL : (∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) then
        match lowEns u (.index ((declOf u).count t) :: Γ) Λ (fnR.mitIndex x t.val ((declOf u).count t)) none body with
        | .error e => .error e
        | .ok b => .ok (Expr.forallSlots (D := declOf u) t b hL)
      else .error "access without held guard"
  | .einige tn x body =>
    match tabIdx u.tabs tn, ergAlsParam u fn er with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok t, .ok fnR =>
      if hL : (∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) then
        match lowEns u (.index ((declOf u).count t) :: Γ) Λ (fnR.mitIndex x t.val ((declOf u).count t)) none body with
        | .error e => .error e
        | .ok b => .ok (Expr.existsSlots (D := declOf u) t b hL)
      else .error "access without held guard"

termination_by predicate => 3 * sizeOf predicate
decreasing_by all_goals (simp_wf <;> omega)

def lowArrayValue (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty)
    (source : USide) : Except String (ArrayValue u Γ Λ) := do
  match ← lowWertE u Γ Λ fn er source with
  | ⟨.arr element count, term⟩ =>
      if lexical : term.orte.isEmpty = true then .ok ⟨element, count, term, lexical⟩
      else .error "source export: array domain requires an immutable value binding"
  | _ => .error "source export: elems domain is not an array"

termination_by 3 * sizeOf source + 1
decreasing_by all_goals (simp_wf <;> omega)

/-- C13: one side of a comparison that holds `count x in D : p` as a number (`Expr.count`), at the arithmetic layer
    `+ - *`; every other side is the side of `lowSideEns`. The binder `x` is an index into the exact domain:
    * `slots of T`: the `count T` cells; an OPEN table has no static cardinality and is refused;
    * `descendants of s` / `ancestors of s`: the same cells filtered through the checked `reaches` relation
      (`lowEns .filtered`), so the membership is exact; the guards of `T` are required;
    * `elems of a`: the index domain `0 ..< n` of the lexical fixed array `a`, on its private carrier, whose count
      is the array's length by `ArrayCarrier.same`.
    The count reads the cells its body reads, under the guards the body's own reads carry; the enumeration of the
    indices reads none (`Expr.orte` of `count` is the body's). -/
def lowSeiteZ (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) : USide → Except String (LowSide u Γ Λ)
  | .zaehle tn x body =>
    match tabIdx u.tabs tn, ergAlsParam u fn er with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok t, .ok fnR =>
      if (declOf u).offen t then .error "count over an open table has no static cardinality"
      else if hc : 0 ≤ (declOf u).count t then
        match lowEns u (.index ((declOf u).count t) :: Γ) Λ (fnR.mitIndex x t.val ((declOf u).count t)) none body with
        | .error e => .error e
        | .ok b => .ok (LowSide.zaehleVon u Γ Λ ((declOf u).count t).toNat (umIdx (Int.toNat_of_nonneg hc).symm b))
      else .error "table count is negative"
  | .zaehleBaum name x field reverse source body => do
    u.exportGate
    let table ← tabIdx u.tabs name
    let edge ← selfEdge u table field
    let seed ← lowIdx u Γ Λ fn (if er.isSome then 1 else 0) table source
    let fnR ← ergAlsParam u fn er
    if (declOf u).offen table then .error "count over an open table has no static cardinality"
    else if hc : 0 ≤ (declOf u).count table then
      if guard : (∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) then
        let predicate ← lowEns u (.index ((declOf u).count table) :: Γ) Λ
          (fnR.mitIndex x table.val ((declOf u).count table)) none body
        let filter : Expr (declOf u) (Ty.index ((declOf u).count table) :: Γ) Λ .bool :=
          if reverse then Expr.reaches table edge.field edge.self (.var .here) seed.weaken guard
          else Expr.reaches table edge.field edge.self seed.weaken (.var .here) guard
        pure (LowSide.zaehleVon u Γ Λ ((declOf u).count table).toNat
          (umIdx (Int.toNat_of_nonneg hc).symm (Expr.and filter predicate)))
      else .error "access without held guard"
    else .error "table count is negative"
  | .zaehleFeld source binder body => do
    u.exportGate
    let array ← lowArrayValue u Γ Λ fn er source
    let carrier ← arrayCarrier u array.count
    let fnR ← ergAlsParam u fn er
    let predicate ← lowEns u (Ty.index ((declOf u).count carrier.table) :: Γ) Λ
      (fnR.mitTy binder (.index ((declOf u).count carrier.table))) none body
    pure (LowSide.zaehleVon u Γ Λ array.count (umIdx carrier.same predicate))
  | .add a b => lowZwei (fun x y => .ok (LowSide.plus x y)) (lowSeiteZ u Γ Λ fn er a) (lowSeiteZ u Γ Λ fn er b)
  | .sub a b => lowZwei (fun x y => .ok (LowSide.minus x y)) (lowSeiteZ u Γ Λ fn er a) (lowSeiteZ u Γ Λ fn er b)
  | .mul a b => lowZwei (fun x y => .ok (LowSide.times x y)) (lowSeiteZ u Γ Λ fn er a) (lowSeiteZ u Γ Λ fn er b)
  | s => zahlVon (lowWertE u Γ Λ fn er s)
termination_by source => 3 * sizeOf source + 1
decreasing_by all_goals (simp_wf <;> omega)
end

/-- A comparison side in `ensures`: literals, numeric parameters,
    slot reads, `old` and `result` travel (the integer values of `lowWertE`). -/
def lowSideEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (s : USide) : Except String (LowSide u Γ Λ) :=
  zahlVon (lowWertE u Γ Λ fn er s)

/-- A value side in a body: the sides of an `ensures` without `old` and `result` (a body reads neither). -/
def lowSideVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (s : USide) : Except String (LowSide u Γ Λ) :=
  if seiteAltErg s then .error "side in body without G form"
  else lowSideEns u Γ Λ fn none s

/-- The `ensures` conjunction (empty is `.tru`). -/
def lowEnsList (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowEns u Γ Λ fn er e with
    | .error err => .error err
    | .ok x =>
      match lowEnsList u Γ Λ fn er rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

end Gabbro.Grammatik.Parser.UebersetzeAllg

/-
  CUTS: what is not proved here.

  1. This file builds the generic declaration `declOf` (Fin carriers)
     and lowers sides and `ensures` (`lowIdx` through `lowEnsList`).
     NOT yet built: statement lowering (`assign`/`call`), `RufPasst`
     assembly, bodies, `lowerAllg`, the 104/108 fragment and footprint
     pins, the data agreement, the real-text lexer pin and the chaining
     theorem. Those remain open work.
  2. `beq`-style soundness is proved for nothing here; there are no
     `beq` lemmas in this file.
  3. Elaboration lessons (for the lane that continues): pin `D`
     explicitly on every constructor over the Fin carriers
     (`Expr.slot (D := declOf u)` etc.), since `D` never unifies out
     of a stuck `(declOf u).Tab` projection; keep struct literals on
     one line (a trailing comma at end of line misparses); a term
     continuation line must not start with `(` (it parses as a tactic).
-/

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.notEmpty_ne_nil
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.sigAt_get
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.params_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.erg_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.haelt_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.ende_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.rangeO_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.typAt_of
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.tabNr_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldPos_lt
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldAtPos_get
