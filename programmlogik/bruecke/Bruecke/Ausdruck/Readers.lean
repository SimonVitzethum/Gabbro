module
public import Grammatik.Parser.Elab.Uebersetze
public import Gabbro.Body
public import Bruecke.Ausdruck.RecordData
public import Grammatik.Parser.Elab.Generic.SignatureData
@[expose] public section


/-! # Shared typed readers for scalar, record and Boolean expressions. -/

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik (Ty)

namespace Gabbro.Bruecke

open Gabbro.Body
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-! ## 0. Lookups -/

/-- How the body readers resolve a callee by name. Every statement of the bridge is about the one
    standard instance, the first function of the name in `u.fns` (`instFnSuche`). A generated duty
    module computes its readings with a logarithmic table that answers the same for every name
    (`Kette/Suche.lean`), and rewrites back to the standard instance by `funktionsTabelle_suche`. -/
class FnSuche (u : UProg) where
  such : String → Option UFn

/-- The standard callee lookup: the first function of the name. -/
instance (priority := low) instFnSuche (u : UProg) : FnSuche u :=
  ⟨fun n => u.fns.find? (fun f => f.name == n)⟩

/-- The callee of the name, through the reader's lookup (by default the first function of the name). -/
def fnSuch (u : UProg) [i : FnSuche u] (n : String) : Option UFn := i.such n

/-- The pointer parameter of `f` that points at the table `tab` -- only when there is exactly one
    (a call that passes "a pointer to `tab`" names no variable in `UArg.freshPtr`). -/
def ptrParam (u : UProg) (f : UFn) (tab : String) : Option String :=
  match f.params.filter (fun q => match q.2 with
      | .ptr ⟨_, _, .table t⟩ => (u.tabs[t]?).map (·.name) == some tab
      | _ => false) with
  | [q] => some q.1
  | _ => none

/-! ## 1. Expressions -/

/-- One side of a comparison. `old` (the entry value) is handled by the caller (`altSides`), and
    reads here as the `old#i` binder it is numbered to. -/
def oldName : Nat → String
  | 0 => "old#1" | 1 => "old#2" | 2 => "old#3" | 3 => "old#4" | 4 => "old#5" | 5 => "old#6"
  | 6 => "old#7" | 7 => "old#8" | _ => "old#9"

/-- The place a slot read names. -/
def slotPlace (u : UProg) (f : UFn) : USide → Option Expr
  | .slot p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | .tab t fld i => some (.place t (idxExpr i) fld)
  | .old p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | _ => none

/-- Two operands under one Body operator (both must have a Body form). -/
def binE (op : BinOp) : Option Expr → Option Expr → Option Expr
  | some x, some y => some (.bin op x y)
  | _, _ => none

/-- Scalar parameters are distinguished from the capability parameters of `argExpr`. -/
def numericParam (f : UFn) (p : String) : Bool :=
  match f.params.find? (fun q => q.1 == p) with
  | some (_, .int ..) => true
  | _ => false

/-- Assignment supports value parameters; capability parameters remain protected. -/
def assignableParam (f : UFn) (p : String) : Bool :=
  numericParam f p || (valueParamTy f p).isSome

/-- Only integer and bool, non-atomic module statics belong to this bridge fragment. -/
def ScalarStatics (u : UProg) : Prop :=
  ∀ g : Fin u.globs.length,
    ((∃ lo hi : Int, (globAt u g).ty = .int lo hi) ∨ (globAt u g).ty = .bool) ∧
      (globAt u g).atomic = false

mutual
/-- Numeric operands share recursive record reading. Only integer fields are projected;\n    Boolean fields retain their own typed comparison path. -/
def numericSideExprG (u : UProg) (f : UFn) : USide → Option Expr
  | .lit n => some (.lit (.int n))
  | .param p => if numericParam f p then some (.name p) else none
  | .slot p fld i => slotPlace u f (.slot p fld i)
  | .tab t fld i => slotPlace u f (.tab t fld i)
  | .glob g =>
      match globIdx u.globs g with
      | .error _ => none
      | .ok i =>
          match (globAt u i).ty with
          | .int .. => some (.global g)
          | .bool | .wert _ => none
  | .old .. => none
  | .erg => none
  | .add a b => binE .add (numericSideExprG u f a) (numericSideExprG u f b)
  | .sub a b => binE .sub (numericSideExprG u f a) (numericSideExprG u f b)
  | .mul a b => binE .mul (numericSideExprG u f a) (numericSideExprG u f b)
  | .conv _ _ a => numericSideExprG u f a
  | .band a b => binE .band (numericSideExprG u f a) (numericSideExprG u f b)
  | .bor a b => binE .bor (numericSideExprG u f a) (numericSideExprG u f b)
  | .bxor a b => binE .bxor (numericSideExprG u f a) (numericSideExprG u f b)
  | .div a b => binE .div (numericSideExprG u f a) (numericSideExprG u f b)
  | .rem a b => binE .rem (numericSideExprG u f a) (numericSideExprG u f b)
  | .shl a b => binE .shl (numericSideExprG u f a) (numericSideExprG u f b)
  | .shr a b => binE .shr (numericSideExprG u f a) (numericSideExprG u f b)
  | .neg a => (numericSideExprG u f a).map (.un .neg ·)
  | .field base name => do
      let (some (.int _ _), e) ← recordProject u (recordRead u f base) name | none
      pure e
  | _ => none
termination_by sd => 3 * sizeOf sd
decreasing_by all_goals (simp_wf <;> omega)


/-- A Body value together with optional exact type information. Scalar leaves retain the
    existing reader; record operations resolve nominal schemas and typed positions using
    the very same lookups as `lowWertE`. The lowerer separately checks every field value. -/
def recordRead (u : UProg) (f : UFn) :
    USide → Option (Option Ty × Expr)
  | .param p =>
      match valueParamTy f p with
      | some ty => some (some ty, .name p)
      | none => (numericSideExprG u f (.param p)).map (none, ·)
  | .option num v => do
      let t ← u.tabs[num]?
      let e ← optionExpr u f v
      pure (some (.opt t.count), e)
  | .present n value => do
      let (_, e) ← recordRead u f value
      pure (some (.opt n), .someOf e)
  | .absent n => some (some (.opt n), .lit .absent)
  | .truth b => some (some .bool, .lit (.bool b))
  | .product identity _ fields => do
      let _ ← (uRecordOf u.records (.prod identity (fields.map (·.1)))).toOption
      let es ← recordReads u f fields
      pure (some (.prod identity (fields.map (·.1))), .recOf es)
  | .field base name => recordProject u (recordRead u f base) name
  | .replace base name value => do
      let (some ty, e) ← recordRead u f base | none
      let sch ← (uRecordOf u.records ty).toOption
      let pos ← (uRecordPosition sch.val.fields name).toOption
      let (_, v) ← recordRead u f value
      pure (some sch.val.ty, .recSet e (recordIndex pos.2) v)
  | sd => (numericSideExprG u f sd).map (none, ·)
termination_by sd => 3 * sizeOf sd + 1
decreasing_by all_goals (simp_wf <;> omega)

def recordReads (u : UProg) (f : UFn) :
    List (Ty × USide) → Option (List Expr)
  | [] => some []
  | (_, sd) :: rest => do
      let (_, e) ← recordRead u f sd
      let es ← recordReads u f rest
      pure (e :: es)
termination_by ss => 3 * sizeOf ss + 2
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Values and arithmetic share one recursive reader, including record field operands. -/
def sideExprG (u : UProg) (f : UFn) (sd : USide) : Option Expr :=
  (recordRead u f sd).map (·.2)

/-- An `ensures` side, numbering the `old(..)` reads met so far: the term, the reads in order,
    whether `result` occurs. -/
structure Acc where
  olds : List Expr := []
  result : Bool := false

def ensSide (u : UProg) (f : UFn) (a : Acc) : USide → Option (Expr × Acc)
  | .old p fld i =>
      (slotPlace u f (.old p fld i)).map (fun pl => (.name (oldName a.olds.length), { a with olds := a.olds ++ [pl] }))
  | .erg => some (.name "result", { a with result := true })
  -- Pure arithmetic reuses the scalar reader without changing the accumulator. Nested
  -- `old`/`result` still have no scalar form and are refused by `sideExprG`.
  | s => (numericSideExprG u f s).map (fun e => (e, a))

def opOf : String → Option BinOp
  | "==" => some .eq | "<" => some .lt | "<=" => some .le
  | ">" => some .gt | ">=" => some .ge | "!=" => some .ne | _ => none

/-- Truth comparisons retain their Boolean values instead of using integer projection. -/
def boolOpOf : String → Option BinOp
  | "==" => some .eq | "!=" => some .ne | _ => none

def boolCmpExpr (u : UProg) (f : UFn) (op : String) (l r : USide) : Option Expr :=
  match boolOpOf op, recordRead u f l, recordRead u f r with
  | some o, some (some .bool, le), some (some .bool, re) => some (.bin o le re)
  | _, _, _ => none

def ensExpr (u : UProg) (f : UFn) (a : Acc) : UEns → Option (Expr × Acc)
  | .tru => some (.lit (.bool true), a)
  | .fls => some (.lit (.bool false), a)
  | .var p => some (.name p, a)
  | .cmp op l r =>
      match boolCmpExpr u f op l r with
      | some e => some (e, a)
      | none =>
          match opOf op, ensSide u f a l with
          | some o, some (le, a1) =>
              match ensSide u f a1 r with
              | some (re, a2) => some (.bin o le re, a2)
              | none => none
          | _, _ => none
  | .and x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .and xe ye, a2)
          | none => none
      | none => none
  | .or x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .or xe ye, a2)
          | none => none
      | none => none
  | .not x =>
      match ensExpr u f a x with
      | some (xe, a1) => some (.un .not xe, a1)
      | none => none
  | .istSome v _ => (optionExpr u f v).map (fun e => (.bin .ne e (.lit .absent), a))
  -- A `bool` static reads its Body global; other statics are refused (as by `lowGlobBool`).
  | .globB g =>
      match globIdx u.globs g with
      | .error _ => none
      | .ok i =>
          match (globAt u i).ty with
          | .bool => some (.global g, a)
          | .int .. | .wert _ => none
  -- Bool fields have no slot encoding in this bridge and remain refused by name.
  | .slotB .. | .tabB .. => none
  | _ => none

def rawCond (u : UProg) (fn : UFn) (c : UEns) : Option Gabbro.Body.Expr :=
  match ensExpr u fn {} c with
  | some (x, a) => if a.olds.length = 0 ∧ a.result = false then some x else none
  | none => none

end Gabbro.Bruecke
