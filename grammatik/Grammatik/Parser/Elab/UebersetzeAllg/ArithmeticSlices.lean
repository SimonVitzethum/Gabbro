module

public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze
open LowLevel.Construct

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
    exact ⟨.lit lo, by simp only [lowWertE, LowSide.wert], rfl⟩

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
  cases classified : source
  case «variable» name =>
    simp only [classified, uSliceInteger] at recognized
    split at recognized
    · next localLo localHi declared =>
      split at recognized
      · cases recognized
        exact locals name _ _ declared
      · cases recognized
    · split at recognized
      · cases recognized
      · exact uSliceIntegerConstant_low ctx fn er _ recognized
  case bin op left right =>
    simp only [classified, uSliceInteger] at recognized
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
    simp only [classified, uSliceInteger] at recognized
    exact uSliceIntegerConstant_low ctx fn er _ recognized
termination_by sizeOf source
decreasing_by
  all_goals rw [classified]
  all_goals simp_wf <;> omega

/-- A shared start makes the variable extent available even when the
    independently checked endpoint intervals overlap. -/
theorem relativeSliceWithLength_exact (ctx : UCtx) (blatt : SExpr → Except String USide)
    (name : String) (amount : SExpr) (capacity firstLo firstHi countLo countHi : Int)
    (offset extent : USide)
    (first : uSliceInteger ctx blatt (.variable name) = some (firstLo, firstHi, offset))
    (count : uSliceInteger ctx blatt amount = some (countLo, countHi, extent))
    (bounds : 0 ≤ firstLo ∧ 0 ≤ countLo ∧ firstHi + countHi ≤ capacity) :
    uRelativeSliceWithLength ctx blatt capacity (.variable name) (.bin "+" (.variable name) amount) =
      some (offset, extent, countLo) := by
  have same : strEq name name = true := by simp [strEq]
  simp only [uRelativeSliceWithLength, show strEq "+" "+" = true from rfl, same, Bool.and_self,
    ite_true, bind, Option.bind, first, count, ite_eq_left bounds]

/-- The production observer admits an overlapping endpoint interval
    and a genuinely variable count at every capacity that contains both. -/
theorem relativeSliceWithLength_erfuellbar (element : Ty) (capacity : Nat) (fits : 7 ≤ capacity) :
    ∃ ctx : UCtx,
      let slice := SExpr.built "#slice"
        [.variable "a", .variable "i", .bin "+" (.variable "i") (.variable "n")]
      uWertBody ctx (.built "lenof" [slice]) = .ok (.param "n") ∧
        uWertBody ctx (.index slice (.lit 1)) =
          .ok (.idx (.param "a") (.add (.param "i") (.lit 1))) := by
  let ctx : UCtx := {
    names := ["a", "i", "n"], kinds := [.wert, .int, .int]
    types := [.arr element capacity, .int 0 4, .int 2 3]
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have declared : uSliceLocalType ctx "a" = some (.arr element capacity) := rfl
  have readArray : uWertBlatt ctx (.variable "a") = .ok (.param "a") := rfl
  have readFirst : uSliceInteger ctx (uWertBlatt ctx) (.variable "i") = some (0, 4, .param "i") := by
    rw [uSliceInteger]
    rfl
  have readCount : uSliceInteger ctx (uWertBlatt ctx) (.variable "n") = some (2, 3, .param "n") := by
    rw [uSliceInteger]
    rfl
  have readIndex : uSliceInteger ctx (uWertBlatt ctx) (.lit 1) = some (1, 1, .lit 1) := by
    rw [uSliceInteger]
    rfl
  have readLast : uSliceInteger ctx (uWertBlatt ctx) (.bin "+" (.variable "i") (.variable "n")) =
      some (2, 7, .add (.param "i") (.param "n")) := by
    rw [uSliceInteger, readFirst, readCount]
    rfl
  have ordinary : uRelativeSlice ctx (uWertBlatt ctx) capacity (.variable "i")
      (.bin "+" (.variable "i") (.variable "n")) = none := by
    simp only [uRelativeSlice, readFirst, readLast, bind, Option.bind]
    rfl
  have noConstant : uFixedLocalArrayExtent ctx (uWertBlatt ctx) (.param "a") (.variable "i")
      (.bin "+" (.variable "i") (.variable "n")) = none := rfl
  have checked := relativeSliceWithLength_exact ctx (uWertBlatt ctx) "i" (.variable "n") capacity
    0 4 2 3 (.param "i") (.param "n") readFirst readCount (by omega)
  refine ⟨ctx, ?_, ?_⟩ <;>
    simp only [uWertBody, uRechne, uSliceObservation, uSliceView, readArray, declared, ite_true,
      bind, Option.bind, noConstant, uSliceExtent, ordinary, Option.orElse_none, checked, readIndex] <;> rfl

/-- The correlated lowering retains precisely the model's dynamic
    length and shifts every observation once into the original array. -/
theorem relativeSliceWithLength_refines {α : Type} {capacity : Nat} (array : Fin capacity → α)
    {firstLo firstHi countLo countHi : Int}
    (offset : Zahl firstLo firstHi) (extent : Zahl countLo countHi)
    (bounds : 0 ≤ firstLo ∧ 0 ≤ countLo ∧ firstHi + countHi ≤ (capacity : Int)) :
    ∃ ok : SliceOk capacity offset.n.toNat (offset.n + extent.n).toNat,
      let view := BoundedSlice.ofArray array offset.n.toNat (offset.n + extent.n).toNat ok
      view.length = extent.n.toNat ∧
        ∀ i : Fin view.length, view.get i = array ⟨offset.n.toNat + i.val, by
          have inside := i.isLt
          have upper := ok.2
          change i.val < (offset.n + extent.n).toNat - offset.n.toNat at inside
          omega⟩ := by
  have firstLower := offset.lo_le
  have firstUpper := offset.le_hi
  have countLower := extent.lo_le
  have countUpper := extent.le_hi
  obtain ⟨first, count, upper⟩ := bounds
  have ok : SliceOk capacity offset.n.toNat (offset.n + extent.n).toNat := ⟨by omega, by omega⟩
  exact ⟨ok, by change (offset.n + extent.n).toNat - offset.n.toNat = extent.n.toNat; omega,
    fun _ => rfl⟩

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
    simp only [slice, uWertBody, uRechne, uSliceObservation, uSliceView, uSliceExtent, Option.orElse_some, uRelativeSlice, uFixedLocalArrayExtent,
      arrayType, arrayRead, ite_true, begin, finish, fits, and_self, bind, Option.bind] <;> rfl
  · change uWertBody scope (.index slice (.lit 0)) = _
    simp only [slice, uWertBody, uRechne, uSliceObservation, uSliceView, uSliceExtent, Option.orElse_some, uRelativeSlice, uFixedLocalArrayExtent,
      arrayType, arrayRead, ite_true, begin, finish, fits, index, and_self, bind, Option.bind,
      uSliceInteger, uSliceIntegerConstant, uSchranke, Option.map_some] <;> rfl

/-- The productive observer composes two checked relative ranges into
    one original-array index. Both relative lower bounds are retained. -/
theorem nestedLocalArraySlice_observations (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array : String) (τ : Ty) (capacity : Nat) (first last innerFirst innerLast index : SExpr)
    (begin length innerBegin innerLength offset : USide) (minimum innerMinimum lo hi : Int)
    (arrayType : uSliceLocalType ctx array = some (.arr τ capacity))
    (arrayRead : blatt (.variable array) = .ok (.param array))
    (independent : uFixedLocalArrayExtent ctx blatt (.param array) first last = none)
    (outerBounds : uRelativeSlice ctx blatt capacity first last = some (begin, length, minimum))
    (innerBounds : uRelativeSlice ctx blatt minimum innerFirst innerLast =
      some (innerBegin, innerLength, innerMinimum))
    (position : uSliceInteger ctx blatt index = some (lo, hi, offset))
    (indexBounds : 0 ≤ lo ∧ hi < innerMinimum) :
    let slice := SExpr.built "#slice" [.variable array, first, last]
    let nested := SExpr.built "#slice" [slice, innerFirst, innerLast]
    uRechne ctx blatt (.built "lenof" [nested]) = .ok innerLength ∧
      uRechne ctx blatt (.index nested index) =
        .ok (.idx (.param array) (.add (.add begin innerBegin) offset)) := by
  dsimp only
  constructor <;> rw [uRechne] <;>
    simp only [uSliceObservation, uSliceView, arrayType, arrayRead, independent,
      uSliceExtent, Option.orElse_some, outerBounds, innerBounds, position, indexBounds, and_self, bind, Option.bind, ite_true]

/-- Both observations are accepted for a dynamically sized outer slice
    and a proper inner slice. The premise admits every array capacity above the endpoints. -/
theorem nestedLocalArraySlice_erfuellbar (element : Ty) (capacity : Nat) (fits : 5 ≤ capacity) :
    ∃ scope : UCtx,
      let outer := SExpr.built "#slice" [.variable "a", .variable "i", .variable "j"]
      let inner := SExpr.built "#slice" [outer, .lit 1, .lit 2]
      uWertBody scope (.built "lenof" [inner]) = .ok (.sub (.lit 2) (.lit 1)) ∧
        uWertBody scope (.index inner (.lit 0)) =
          .ok (.idx (.param "a") (.add (.add (.param "i") (.lit 1)) (.lit 0))) := by
  let scope : UCtx := {
    names := ["a", "i", "j"], kinds := [.wert, .int, .int]
    types := [.arr element capacity, .int 0 1, .int 4 5]
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have array : uSliceLocalType scope "a" = some (.arr element capacity) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have begin : uSliceLocalType scope "i" = some (.int 0 1) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have finish : uSliceLocalType scope "j" = some (.int 4 5) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have readArray : uWertBlatt scope (.variable "a") = .ok (.param "a") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have readFirst : uWertBlatt scope (.variable "i") = .ok (.param "i") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have readLast : uWertBlatt scope (.variable "j") = .ok (.param "j") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have range : (0 : Int) ≤ 0 ∧ (1 : Int) ≤ 4 ∧ (5 : Int) ≤ capacity := by omega
  have outer : uRelativeSlice scope (uWertBlatt scope) capacity (.variable "i") (.variable "j") =
      some (.param "i", .sub (.param "j") (.param "i"), 3) := by
    simp only [uRelativeSlice, uSliceInteger, begin, finish, readFirst, readLast, range, bind, Option.bind,
      and_self, ite_true] <;> rfl
  refine ⟨scope, nestedLocalArraySlice_observations scope (uWertBlatt scope) "a" element capacity
    (.variable "i") (.variable "j") (.lit 1) (.lit 2) (.lit 0)
    (.param "i") (.sub (.param "j") (.param "i")) (.lit 1) (.sub (.lit 2) (.lit 1)) (.lit 0)
    3 1 0 0 array readArray rfl outer ?_ ?_ (by decide)⟩ <;>
    simp only [uRelativeSlice, uSliceInteger, uSliceIntegerConstant, uSchranke, Option.map_some,
      bind, Option.bind] <;> rfl

/-- The actual typed elaborator emits one array read with the translated
    index. The outer start, inner start and selected index are evaluated once. -/
theorem lowWertE_nestedLocalArraySliceIndex {fn : UFn} {er : Option Ty}
    {array : String} {first cut index : USide} {τ : Ty} {capacity : Nat} {a b c d i j : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ capacity)}
    {begin : Expr (declOf u) Γ Λ (.int a b)} {innerBegin : Expr (declOf u) Γ Λ (.int c d)}
    {position : Expr (declOf u) Γ Λ (.int i j)}
    (readArray : lowWertE u Γ Λ fn er (.param array) = .ok ⟨.arr τ capacity, base⟩)
    (readFirst : lowWertE u Γ Λ fn er first = .ok ⟨.int a b, begin⟩)
    (readCut : lowWertE u Γ Λ fn er cut = .ok ⟨.int c d, innerBegin⟩)
    (readIndex : lowWertE u Γ Λ fn er index = .ok ⟨.int i j, position⟩)
    (lower : 0 ≤ a + c + i) (upper : b + d + j ≤ (capacity : Int) - 1) :
    lowWertE u Γ Λ fn er (.idx (.param array) (.add (.add first cut) index)) =
      .ok ⟨τ, .arrGet base (.widen lower upper (.add (.add begin innerBegin) position))⟩ := by
  have readStart : lowWertE u Γ Λ fn er (.add first cut) =
      .ok ⟨.int (a + c) (b + d), .add begin innerBegin⟩ := by
    simp only [lowWertE, readFirst, readCut, zahlVon, LowSide.plus, LowSide.wert, LowWert.zahl]
  exact lowWertE_localArraySliceIndex readArray readStart readIndex lower upper

/-- Reading the composed index in G returns the exact element of the
    nested value slice. The typed term has one array operand. -/
theorem eval_nestedLocalArraySliceIndex {D : Deklaration} {τ : Ty} {capacity : Nat} {Γ : Ctx}
    {Λ : List (Res D)} {a b c d e f g h i j : Int}
    (array : Expr D Γ Λ (.arr τ capacity)) (begin : Expr D Γ Λ (.int a b)) (finish : Expr D Γ Λ (.int c d))
    (innerBegin : Expr D Γ Λ (.int e f)) (innerFinish : Expr D Γ Λ (.int g h))
    (index : Expr D Γ Λ (.int i j))
    (outer : 0 ≤ a ∧ b ≤ c ∧ d ≤ capacity)
    (inner : 0 ≤ e ∧ f ≤ g ∧ h ≤ c - b)
    (position : 0 ≤ i ∧ j < g - f)
    (entry world : World D) (env : Env D Γ) :
    let first := eval entry begin world env
    let last := eval entry finish world env
    let cutFirst := eval entry innerBegin world env
    let cutLast := eval entry innerFinish world env
    let atIndex := eval entry index world env
    ∃ outerFit : SliceOk capacity first.n.toNat last.n.toNat,
      ∃ innerFit : SliceOk (last.n.toNat - first.n.toNat) cutFirst.n.toNat cutLast.n.toNat,
        ∃ indexFit : atIndex.n.toNat < cutLast.n.toNat - cutFirst.n.toNat,
          eval entry (.arrGet array (.widen (by omega)
            (by have := last.lo_le; have := last.le_hi
                have := cutLast.lo_le; have := cutLast.le_hi
                omega) (.add (.add begin innerBegin) index))) world env =
            ((BoundedSlice.ofArray (eval entry array world env) first.n.toNat last.n.toNat outerFit).subslice
              cutFirst.n.toNat cutLast.n.toNat innerFit).get ⟨atIndex.n.toNat, indexFit⟩ := by
  dsimp only
  have aLow := (eval entry begin world env).lo_le
  have aHigh := (eval entry begin world env).le_hi
  have bLow := (eval entry finish world env).lo_le
  have bHigh := (eval entry finish world env).le_hi
  have cLow := (eval entry innerBegin world env).lo_le
  have cHigh := (eval entry innerBegin world env).le_hi
  have dLow := (eval entry innerFinish world env).lo_le
  have dHigh := (eval entry innerFinish world env).le_hi
  have indexLow := (eval entry index world env).lo_le
  have indexHigh := (eval entry index world env).le_hi
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
  simp only [eval, BoundedSlice.ofArray, BoundedSlice.subslice, arrSliceValue]
  apply congrArg (eval entry array world env)
  apply Fin.ext
  simp only [Zahl.fin, Zahl.weiter, Zahl.add]
  omega

end Gabbro.Grammatik.Parser.UebersetzeAllg
