module

public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze

variable {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}

private theorem uSliceIntegerConstant_low (ctx : UCtx) (fn : UFn) (er : Option Ty)
    (source : SExpr) {lo hi : Int} {side : USide}
    (recognized : uSliceIntegerConstant ctx source = some (lo, hi, side)) :
    ∃ term : Expr (declOf u) Γ Λ (.int lo hi),
      lowWertE u Γ Λ fn er side = .ok ⟨.int lo hi, term⟩ ∧ term.orte = [] := by
  unfold uSliceIntegerConstant at recognized
  cases folded : uSchranke (uSliceConstants ctx) source with
  | none => rw [folded] at recognized; cases recognized
  | some value =>
    rw [folded] at recognized
    cases recognized
    exact ⟨.lit value, by simp only [lowWertE, LowSide.wert], rfl⟩

/-- Every recognized endpoint or index has precisely the interval used
    by its surface bound check. The typed term reads lexical values only. -/
theorem uSliceInteger_low (ctx : UCtx) (blatt : SExpr → Except String USide) (fn : UFn) (er : Option Ty)
    (locals : ∀ name lo hi, uSliceLocalType ctx name = some (.int lo hi) →
      ∃ term : Expr (declOf u) Γ Λ (.int lo hi),
        lowWertE u Γ Λ fn er (.param name) = .ok ⟨.int lo hi, term⟩ ∧ term.orte = [])
    (source : SExpr) {lo hi : Int} {side : USide}
    (recognized : uSliceInteger ctx blatt source = some (lo, hi, side)) :
    ∃ term : Expr (declOf u) Γ Λ (.int lo hi),
      lowWertE u Γ Λ fn er side = .ok ⟨.int lo hi, term⟩ ∧ term.orte = [] := by
  cases source
  case «variable» name =>
    simp only [uSliceInteger] at recognized
    split at recognized
    · next localLo localHi declared =>
      split at recognized
      · cases recognized
        exact locals name localLo localHi declared
      · cases recognized
    · split at recognized
      · cases recognized
      · exact uSliceIntegerConstant_low ctx fn er _ recognized
  case bin op left right =>
    simp only [uSliceInteger] at recognized
    split at recognized
    · exact uSliceIntegerConstant_low ctx fn er _ recognized
    · cases readLeft : uSliceInteger ctx blatt left with
      | none => simp only [readLeft] at recognized; cases recognized
      | some leftInfo =>
        cases readRight : uSliceInteger ctx blatt right with
        | none => simp only [readLeft, readRight] at recognized; cases recognized
        | some rightInfo =>
          obtain ⟨leftLo, leftHi, leftSide⟩ := leftInfo
          obtain ⟨rightLo, rightHi, rightSide⟩ := rightInfo
          simp only [readLeft, readRight] at recognized
          obtain ⟨a, ha, aLocal⟩ := uSliceInteger_low ctx blatt fn er locals left readLeft
          obtain ⟨b, hb, bLocal⟩ := uSliceInteger_low ctx blatt fn er locals right readRight
          split at recognized
          · cases recognized
            refine ⟨.add a b, ?_, by simp only [Expr.orte, aLocal, bLocal, List.nil_append]⟩
            simp only [lowWertE, ha, hb, zahlVon, LowSide.plus, LowSide.wert, LowWert.zahl]
          · split at recognized
            · cases recognized
              refine ⟨.sub a b, ?_, by simp only [Expr.orte, aLocal, bLocal, List.nil_append]⟩
              exact lowWertE_arraySliceLength hb ha
            · cases recognized
  all_goals
    simp only [uSliceInteger] at recognized
    exact uSliceIntegerConstant_low ctx fn er _ recognized
termination_by sizeOf source
decreasing_by all_goals simp_wf <;> omega

/-- Independent runtime bounds can be arithmetic expressions. The
    source length is their difference and a projected element stays a
    single read of the original array. -/
theorem arithmeticSliceObservations_erfuellbar (element : Ty) (capacity : Nat)
    (enough : 5 ≤ capacity) :
    ∃ scope : UCtx,
      let first := SExpr.bin "+" (.variable "i") (.lit 1)
      let last := SExpr.bin "-" (.variable "j") (.lit 1)
      let slice := SExpr.built "#slice" [.variable "a", first, last]
      uWertBody scope (.built "lenof" [slice]) =
        .ok (.sub (.sub (.param "j") (.lit 1)) (.add (.param "i") (.lit 1))) ∧
      uWertBody scope (.index slice (.lit 0)) =
        .ok (.idx (.param "a") (.add (.add (.param "i") (.lit 1)) (.lit 0))) := by
  let scope : UCtx := {
    names := ["a", "i", "j"], kinds := [.wert, .int, .int]
    types := [.arr element capacity, .int 0 1, .int 5 6]
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have arrayType : uSliceLocalType scope "a" = some (.arr element capacity) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have firstType : uSliceLocalType scope "i" = some (.int 0 1) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have lastType : uSliceLocalType scope "j" = some (.int 5 6) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have arrayRead : uWertBlatt scope (.variable "a") = .ok (.param "a") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have firstRead : uWertBlatt scope (.variable "i") = .ok (.param "i") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have lastRead : uWertBlatt scope (.variable "j") = .ok (.param "j") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  let first := SExpr.bin "+" (.variable "i") (.lit 1)
  let last := SExpr.bin "-" (.variable "j") (.lit 1)
  let slice := SExpr.built "#slice" [.variable "a", first, last]
  have noFirstConstant : uSchranke (uSliceConstants scope) first = none := rfl
  have noLastConstant : uSchranke (uSliceConstants scope) last = none := rfl
  have begin : uSliceInteger scope (uWertBlatt scope) first = some (1, 2, .add (.param "i") (.lit 1)) := by
    simp only [first, uSliceInteger, uSliceIntegerConstant,
      show uSchranke (uSliceConstants scope) (.bin "+" (.variable "i") (.lit 1)) =
      none from noFirstConstant, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false,
      firstType, firstRead, ite_true, uSchranke, Option.map_some, show strEq "+" "+" = true from rfl] <;> rfl
  have finish : uSliceInteger scope (uWertBlatt scope) last = some (4, 5, .sub (.param "j") (.lit 1)) := by
    simp only [last, uSliceInteger, uSliceIntegerConstant,
      show uSchranke (uSliceConstants scope) (.bin "-" (.variable "j") (.lit 1)) =
      none from noLastConstant, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false,
      lastType, lastRead, ite_true, uSchranke, Option.map_some, show strEq "-" "+" = false from rfl,
      show strEq "-" "-" = true from rfl] <;> rfl
  have fits : (0 : Int) ≤ 1 ∧ (2 : Int) ≤ 4 ∧ (5 : Int) ≤ capacity := by omega
  have index : (0 : Int) ≤ Int.ofNat 0 ∧ Int.ofNat 0 < 4 - 2 := by decide
  refine ⟨scope, ?_, ?_⟩
  · change uWertBody scope (.built "lenof" [slice]) = _
    simp only [slice, uWertBody, uRechne, uLocalArraySliceObservation, uFixedLocalArrayExtent,
      arrayType, arrayRead, ite_true, begin, finish, fits, and_self, bind, Option.bind] <;> rfl
  · change uWertBody scope (.index slice (.lit 0)) = _
    simp only [slice, uWertBody, uRechne, uLocalArraySliceObservation, uFixedLocalArrayExtent,
      arrayType, arrayRead, ite_true, begin, finish, fits, index, and_self, bind, Option.bind,
      uSliceInteger, uSliceIntegerConstant, uSchranke, Option.map_some] <;> rfl

end Gabbro.Grammatik.Parser.UebersetzeAllg
