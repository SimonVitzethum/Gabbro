module
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Gabbro.Body
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Body

/-- Erase a checked, typed field position to its runtime list index. -/
def recordIndex : {fs : List Ty} → {ty : Ty} → FieldAt fs ty → Nat
  | _, _, .head => 0
  | _, _, .tail i => recordIndex i + 1

/-- Bools and nominal products supply exact value type information. Integer ranges are
    deliberately absent: the statement reader can use placeholder ranges for locals. -/
def valueParamTy (f : UFn) (name : String) : Option Ty :=
  match f.params.find? (fun q => q.1 == name) with
  | some (_, ty@(.prod ..)) => some ty
  | some (_, .bool) => some .bool
  | some (_, ty@(.why _)) => some ty
  | some (_, ty@(.sum _)) => some ty
  | _ => none

mutual
/-- A Body value together with optional exact type information. Scalar leaves retain the
    existing reader; record operations resolve nominal schemas and typed positions using
    the very same lookups as `lowWertE`. The lowerer separately checks every field value. -/
def recordRead (u : UProg) (f : UFn) (scalar : USide → Option Expr) :
    USide → Option (Option Ty × Expr)
  | .param p =>
      match valueParamTy f p with
      | some ty => some (some ty, .name p)
      | none => (scalar (.param p)).map (none, ·)
  | .truth b => some (some .bool, .lit (.bool b))
  | .product identity _ fields => do
      let _ ← (uRecordOf u.records (.prod identity (fields.map (·.1)))).toOption
      let es ← recordReads u f scalar fields
      pure (some (.prod identity (fields.map (·.1))), .recOf es)
  | .field base name => do
      let (some ty, e) ← recordRead u f scalar base | none
      let sch ← (uRecordOf u.records ty).toOption
      let pos ← (uRecordPosition sch.val.fields name).toOption
      pure (some pos.1, .recGet e (recordIndex pos.2))
  | .replace base name value => do
      let (some ty, e) ← recordRead u f scalar base | none
      let sch ← (uRecordOf u.records ty).toOption
      let pos ← (uRecordPosition sch.val.fields name).toOption
      let (_, v) ← recordRead u f scalar value
      pure (some sch.val.ty, .recSet e (recordIndex pos.2) v)
  | sd => (scalar sd).map (none, ·)
termination_by sd => 3 * sizeOf sd
decreasing_by all_goals (simp_wf <;> omega)

def recordReads (u : UProg) (f : UFn) (scalar : USide → Option Expr) :
    List (Ty × USide) → Option (List Expr)
  | [] => some []
  | (_, sd) :: rest => do
      let (_, e) ← recordRead u f scalar sd
      let es ← recordReads u f scalar rest
      pure (e :: es)
termination_by ss => 3 * sizeOf ss + 1
decreasing_by all_goals (simp_wf <;> omega)
end

mutual
/-- Shapes erase nominal identity, while the source reader checks it with `uRecordOf`.
    Unsupported field types refuse the entire shape instead of dropping components. -/
def shapeOfTy : Ty → Option Shape
  | .int lo hi => some (.intIn lo hi)
  | .bool => some .bool
  | .prod _ fs => (shapesOfTys fs).map Shape.record
  | _ => none
termination_by structural ty => ty

def shapesOfTys : List Ty → Option (List Shape)
  | [] => some []
  | ty :: rest => do
      let sh ← shapeOfTy ty
      let ss ← shapesOfTys rest
      pure (sh :: ss)
termination_by structural ts => ts
end

/-- Internal ordinal labels have no source-name dependency. -/
def caseLabel (n : Nat) : String := String.ofList (List.replicate n '#')

theorem caseLabel_injective {a b : Nat} (h : caseLabel a = caseLabel b) : a = b := by
  have hl := congrArg (fun s : String => s.toList.length) h
  simpa only [caseLabel, String.toList_ofList, List.length_replicate] using hl

/-- Entry shapes include option subjects without extending the result-binding gate. -/
def entryShapeOfTy : Ty → Option Shape
  | .opt _ => some .opt
  | .sum cs => some (.sum ((List.range cs.length).map (fun i => (caseLabel i, none))))
  | ty => shapeOfTy ty

/-- A finite reason entry check uses ordinary Body equality and boolean disjunction. -/
def reasonCheck (x : String) : List String → Expr
  | [] => .lit (.bool false)
  | label :: labels => .bin .or (.bin .eq (.name x) (.lit (.reason label))) (reasonCheck x labels)

def entryCheck (x : String) : Ty → Option Expr
  | .why n => some (reasonCheck x ((List.range n).map caseLabel))
  | ty => (entryShapeOfTy ty).map (Expr.hasShape x)

end Gabbro.Bruecke
