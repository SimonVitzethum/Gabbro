module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

mutual
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
  | s => lowSideEns u Γ Λ fn er s
end

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
