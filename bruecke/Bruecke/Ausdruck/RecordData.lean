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
  | some (_, ty@(.opt _)) => some ty
  | some (_, ty@(.why _)) => some ty
  | some (_, ty@(.sum _)) => some ty
  | _ => none

/-- The name of the table a pointer parameter points at. -/
def ptrTab (u : UProg) (f : UFn) (p : String) : Option String :=
  match f.params.find? (fun q => q.1 == p) with
  | some (_, .ptr ⟨_, _, .table t⟩) => (u.tabs[t]?).map (·.name)
  | _ => none

def idxExpr : UIdx → Expr
  | .lit n => .lit (.int n)
  | .param p => .name p

/-- Read optional table indices with the same places as ordinary slot reads. The
    canonical lowerer checks the table identity and index bounds. -/
def optionExpr (u : UProg) (f : UFn) : UOpt → Option Expr
  | .nichts => some (.lit .absent)
  | .etwas ix => some (.someOf (idxExpr ix))
  | .var x => some (.name x)
  | .slot p fld ix => (ptrTab u f p).map (fun t => .place t (idxExpr ix) fld)
  | .tab t fld ix => some (.place t (idxExpr ix) fld)
  | .glob _ => none

/-- Project a named field using the canonical nominal schema and typed position. -/
def recordProject (u : UProg) (base : Option (Option Ty × Expr)) (name : String) :
    Option (Option Ty × Expr) := do
  let (some ty, e) ← base | none
  let sch ← (uRecordOf u.records ty).toOption
  let pos ← (uRecordPosition sch.val.fields name).toOption
  pure (some pos.1, .recGet e (recordIndex pos.2))

mutual
/-- Shapes erase nominal identity, while the source reader checks it with `uRecordOf`.
    Unsupported field types refuse the entire shape instead of dropping components. -/
def shapeOfTy : Ty → Option Shape
  | .int lo hi => some (.intIn lo hi)
  | .bool => some .bool
  | .opt _ => some .opt
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
