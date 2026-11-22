module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Niedrig.Konstrukte.Schnitt
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze
open LowLevel.Construct

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Build a fixed-length subarray at a runtime index using ordinary
    checked array reads. The whole start interval and every offset fit. -/
def arraySpanFrom {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) : (offset count : Nat) →
    hi + offset + count ≤ length → Expr D Γ Λ (.arr τ count)
  | _, 0, _ => .arrNil
  | offset, count + 1, inside =>
    .arrCons (.arrGet base (.widen (by omega) (by omega) (.add start (.lit offset))))
      (arraySpanFrom base start nonnegative (offset + 1) count (by omega))
termination_by structural _ count _ => count

/-- Expanding local reads neither introduces nor repeats a carrier
    observation. The production source form requires both operands local. -/
theorem arraySpanFrom_reads {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) (baseLocal : base.orte = []) (startLocal : start.orte = [])
    (offset count : Nat) (bounds : hi + offset + count ≤ length) :
    (arraySpanFrom base start nonnegative offset count bounds).orte = [] := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    simp only [arraySpanFrom, Expr.orte, baseLocal, startLocal, List.nil_append,
      ih (offset + 1) (by omega)]

/-- The ordinary core term reads exactly the translated array position
    for every index of the materialized slice and every environment. -/
theorem eval_arraySpanFrom {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) (initial world : World D) (env : Env D Γ) :
    ∀ (offset count : Nat) (bounds : hi + offset + count ≤ length) (index : Fin count),
      eval initial (arraySpanFrom base start nonnegative offset count bounds) world env index =
        eval initial base world env ⟨((eval initial start world env).n + offset + index.val).toNat,
          by
            have lower := (eval initial start world env).lo_le
            have upper := (eval initial start world env).le_hi
            have valid := index.isLt
            omega⟩
  | _, 0, _, index => index.elim0
  | offset, count + 1, bounds, index => by
    simp only [arraySpanFrom, eval, arrConsW]
    split
    · next first =>
      apply congrArg (eval initial base world env)
      apply Fin.ext
      simp [Zahl.fin, Zahl.weiter, Zahl.add, first]
    · next later =>
      rw [eval_arraySpanFrom base start nonnegative initial world env (offset + 1) count
        (by omega) ⟨index.val - 1, by omega⟩]
      apply congrArg (eval initial base world env)
      apply Fin.ext
      simp only
      omega

/-- A known-length span at a varying start can be indexed without
    materialising the span. The start and end may have overlapping
    intervals because the end is defined from that same start. -/
theorem eval_localArraySpanIndex {τ : Ty} {capacity count : Nat}
    {lo hi indexLo indexHi : Int}
    (array : Expr D Γ Λ (.arr τ capacity)) (start : Expr D Γ Λ (.int lo hi))
    (index : Expr D Γ Λ (.int indexLo indexHi))
    (lower : 0 ≤ lo) (within : hi + count ≤ capacity)
    (position : 0 ≤ indexLo ∧ indexHi < count)
    (initial world : World D) (env : Env D Γ) :
    let k := eval initial index world env
    eval initial (.arrGet array (.widen (by omega) (by omega) (.add start index))) world env =
      eval initial (arraySpanFrom array start lower 0 count (by omega)) world env
        ⟨k.n.toNat, by have low := k.lo_le; have high := k.le_hi; omega⟩ := by
  dsimp only
  rw [eval_arraySpanFrom array start lower initial world env 0 count (by omega)]
  simp only [eval]
  apply congrArg (eval initial array world env)
  apply Fin.ext
  simp only [Zahl.fin, Zahl.weiter, Zahl.add]
  have nonnegative := (eval initial index world env).lo_le
  omega

/-- The actual source expansion lowers to the same typed core term.
    Each indexed read is performed by the ordinary dependent reader. -/
theorem lowWertE_localArraySpan {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {array index : String} {τ : Ty} {length : Nat} {lo hi : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ length)} {start : Expr (declOf u) Γ Λ (.int lo hi)}
    (readArray : lowWertE u Γ Λ fn er (.param array) = .ok ⟨.arr τ length, base⟩)
    (readIndex : lowWertE u Γ Λ fn er (.param index) = .ok ⟨.int lo hi, start⟩)
    (nonnegative : 0 ≤ lo) (offset count : Nat) (bounds : hi + offset + count ≤ length) :
    lowWertE u Γ Λ fn er (uLocalArraySpan (.param array) (.param index) τ offset count) =
      .ok ⟨.arr τ count, arraySpanFrom base start nonnegative offset count bounds⟩ := by
  induction count generalizing offset with
  | zero => simp only [uLocalArraySpan, lowWertE, lowLit, Except.map, arraySpanFrom]
  | succ count ih =>
    have low : 0 ≤ lo + offset := by omega
    have high : hi + offset ≤ (length : Int) - 1 := by omega
    have head :
        lowWertE u Γ Λ fn er (.idx (.param array) (.add (.param index) (.lit offset))) =
          .ok ⟨τ, .arrGet base (.widen low high (.add start (.lit offset)))⟩ := by
      simp only [lowWertE, readArray, readIndex, LowSide.plus, LowSide.wert, zahlVon, LowWert.zahl,
        idxW, dite_eq_left low, dite_eq_left high]
    simp only [uLocalArraySpan, lowWertE, head, ih (offset + 1) (by omega), consW, fitW,
      dite_true, arraySpanFrom]

/-- The actual core lowering of a runtime slice length is integer
    subtraction in the direction of the half-open range. -/
theorem lowWertE_arraySliceLength {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {first last : USide} {firstLo firstHi lastLo lastHi : Int}
    {begin : Expr (declOf u) Γ Λ (.int firstLo firstHi)}
    {finish : Expr (declOf u) Γ Λ (.int lastLo lastHi)}
    (readFirst : lowWertE u Γ Λ fn er first = .ok ⟨.int firstLo firstHi, begin⟩)
    (readLast : lowWertE u Γ Λ fn er last = .ok ⟨.int lastLo lastHi, finish⟩) :
    lowWertE u Γ Λ fn er (.sub last first) =
      .ok ⟨.int (lastLo - firstHi) (lastHi - firstLo), .sub finish begin⟩ := by
  simp only [lowWertE, readFirst, readLast, zahlVon, LowWert.zahl, LowSide.minus, LowSide.wert]

/-- Interval checking suffices for all runtime endpoints. The generated
    subtraction returns the exact length of the model slice. -/
theorem eval_localArraySliceLength {τ : Ty} {capacity : Nat} {firstLo firstHi lastLo lastHi : Int}
    (array : Wert D (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi))
    (ranges : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (initial world : World D) (env : Env D Γ) :
    ∃ bounds : SliceOk capacity (eval initial begin world env).n.toNat (eval initial finish world env).n.toNat,
      (eval initial (.sub finish begin) world env).n =
        ((BoundedSlice.ofArray array (eval initial begin world env).n.toNat
          (eval initial finish world env).n.toNat bounds).length : Int) := by
  obtain ⟨nonnegative, ordered, within⟩ := ranges
  have lo := (eval initial begin world env).lo_le
  have hi := (eval initial begin world env).le_hi
  have lo' := (eval initial finish world env).lo_le
  have hi' := (eval initial finish world env).le_hi
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  change (eval initial finish world env).n - (eval initial begin world env).n =
    (((eval initial finish world env).n.toNat - (eval initial begin world env).n.toNat : Nat) : Int)
  omega

/-- The projected source index lowers to one read of the original array. -/
theorem localArraySliceIndex_erfuellbar (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array first last index : String) (τ : Ty) (capacity : Nat)
    (firstLo firstHi lastLo lastHi indexLo indexHi : Int)
    (arrayType : uSliceLocalType ctx array = some (.arr τ capacity))
    (firstType : uSliceLocalType ctx first = some (.int firstLo firstHi))
    (lastType : uSliceLocalType ctx last = some (.int lastLo lastHi))
    (indexType : uSliceLocalType ctx index = some (.int indexLo indexHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (locals : blatt (.variable array) = .ok (.param array) ∧
      blatt (.variable first) = .ok (.param first) ∧ blatt (.variable last) = .ok (.param last))
    (indexBounds : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi ∧
      blatt (.variable index) = .ok (.param index)) :
    uRechne ctx blatt (.index (.built "#slice" [.variable array, .variable first, .variable last])
      (.variable index)) = .ok (.idx (.param array) (.add (.param first) (.param index))) := by
  rw [uRechne]
  simp only [uLocalArraySliceObservation, uFixedLocalArrayExtent, uSliceInteger, arrayType, firstType, lastType, indexType, bounds,
    locals.1, locals.2.1, locals.2.2, indexBounds.2.2, indexBounds.1, indexBounds.2.1,
    and_self, bind, Option.bind, ite_true]

theorem lowWertE_localArraySliceIndex {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {array : String} {first index : USide} {τ : Ty} {capacity : Nat}
    {firstLo firstHi indexLo indexHi : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ capacity)}
    {begin : Expr (declOf u) Γ Λ (.int firstLo firstHi)}
    {position : Expr (declOf u) Γ Λ (.int indexLo indexHi)}
    (readArray : lowWertE u Γ Λ fn er (.param array) = .ok ⟨.arr τ capacity, base⟩)
    (readFirst : lowWertE u Γ Λ fn er first = .ok ⟨.int firstLo firstHi, begin⟩)
    (readIndex : lowWertE u Γ Λ fn er index = .ok ⟨.int indexLo indexHi, position⟩)
    (lower : 0 ≤ firstLo + indexLo) (upper : firstHi + indexHi ≤ (capacity : Int) - 1) :
    lowWertE u Γ Λ fn er (.idx (.param array) (.add first index)) =
      .ok ⟨τ, .arrGet base (.widen lower upper (.add begin position))⟩ := by
  simp only [lowWertE, readArray, readFirst, readIndex, LowSide.plus, LowSide.wert,
    zahlVon, LowWert.zahl, idxW, dite_eq_left lower, dite_eq_left upper]

/-- For every model run, the original-array read returns the selected
    element of the half-open slice. The endpoint and index ranges prove
    all translated addresses valid without any runtime storage. -/
theorem eval_localArraySliceIndex {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi indexLo indexHi : Int}
    (base : Expr D Γ Λ (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi)) (position : Expr D Γ Λ (.int indexLo indexHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (indexBounds : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi)
    (initial world : World D) (env : Env D Γ) :
    let first := eval initial begin world env
    let last := eval initial finish world env
    let index := eval initial position world env
    ∃ valid : SliceOk capacity first.n.toNat last.n.toNat,
      ∃ inside : index.n.toNat < last.n.toNat - first.n.toNat,
        eval initial (.arrGet base (.widen (by omega)
          (by have low := last.lo_le; have high := last.le_hi; omega) (.add begin position))) world env =
          (BoundedSlice.ofArray (eval initial base world env) first.n.toNat last.n.toNat valid).get
            ⟨index.n.toNat, inside⟩ := by
  dsimp only
  have firstLo := (eval initial begin world env).lo_le
  have firstHi := (eval initial begin world env).le_hi
  have lastLo := (eval initial finish world env).lo_le
  have lastHi := (eval initial finish world env).le_hi
  have indexLo := (eval initial position world env).lo_le
  have indexHi := (eval initial position world env).le_hi
  refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
  simp only [eval, BoundedSlice.ofArray, arrSliceValue]
  apply congrArg (eval initial base world env)
  apply Fin.ext
  simp only [Zahl.fin, Zahl.weiter, Zahl.add]
  omega

/-- The two productive slice observations have jointly satisfiable
    source premises, with both endpoints admitting more than one value. -/
theorem runtimeSliceObservations_erfuellbar (τ : Ty) (capacity : Nat) (enough : 4 ≤ capacity) :
    ∃ scope : UCtx,
      uWertBody scope (.built "lenof" [.built "#slice" [.variable "a", .variable "i", .variable "j"]]) =
        .ok (.sub (.param "j") (.param "i")) ∧
      uWertBody scope (.index (.built "#slice" [.variable "a", .variable "i", .variable "j"]) (.variable "k")) =
        .ok (.idx (.param "a") (.add (.param "i") (.param "k"))) := by
  let scope : UCtx := {
    names := ["a", "i", "j", "k"], kinds := [.wert, .int, .int, .int]
    types := [.arr τ capacity, .int 0 1, .int 3 4, .int 0 1]
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have types : uSliceLocalType scope "a" = some (.arr τ capacity) ∧
      uSliceLocalType scope "i" = some (.int 0 1) ∧ uSliceLocalType scope "j" = some (.int 3 4) ∧
      uSliceLocalType scope "k" = some (.int 0 1) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have reads : uWertBlatt scope (.variable "a") = .ok (.param "a") ∧
      uWertBlatt scope (.variable "i") = .ok (.param "i") ∧
      uWertBlatt scope (.variable "j") = .ok (.param "j") ∧
      uWertBlatt scope (.variable "k") = .ok (.param "k") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  obtain ⟨arrayType, firstType, lastType, indexType⟩ := types
  obtain ⟨arrayRead, firstRead, lastRead, indexRead⟩ := reads
  have bounds : (0 : Int) ≤ 0 ∧ (1 : Int) ≤ 3 ∧ (4 : Int) ≤ capacity :=
    ⟨by decide, by decide, by omega⟩
  refine ⟨scope, ?_, ?_⟩
  · exact localArraySliceLength_erfuellbar scope (uWertBlatt scope) "a" "i" "j" τ capacity 0 1 3 4
      arrayType firstType lastType bounds ⟨arrayRead, firstRead, lastRead⟩
  · exact localArraySliceIndex_erfuellbar scope (uWertBlatt scope) "a" "i" "j" "k" τ capacity 0 1 3 4 0 1
      arrayType firstType lastType indexType bounds ⟨arrayRead, firstRead, lastRead⟩
      ⟨by decide, by decide, indexRead⟩

theorem uSliceLocalType_unknown (ctx : UCtx) (name : String)
    (unresolved : ctx.unknownRanges.contains name = true) : uSliceLocalType ctx name = none := by
  simp only [uSliceLocalType, unresolved, ite_true]

/-- A provisional local cannot be accepted as a slice operand even if a
    source constant has the same name. -/
theorem uSliceInteger_unknown (ctx : UCtx) (blatt : SExpr → Except String USide) (name : String)
    (unresolved : ctx.unknownRanges.contains name = true) :
    uSliceInteger ctx blatt (.variable name) = none := by
  simp only [uSliceInteger, uSliceLocalType_unknown ctx name unresolved, unresolved, ite_true]

/-- A resolved local operand retains its interval and its exact lexical
    read. A known non-integer binding cannot produce that operand. -/
theorem uSliceInteger_param {ctx : UCtx} {blatt : SExpr → Except String USide}
    {source : SExpr} {name : String} {lo hi : Int}
    (recognized : uSliceInteger ctx blatt source = some (lo, hi, .param name)) :
    source = .variable name ∧ uSliceLocalType ctx name = some (.int lo hi) ∧
      blatt (.variable name) = .ok (.param name) := by
  have notLiteral (expression : SExpr) :
      (uSchranke (uSliceConstants ctx) expression).map (fun value => (value, value, USide.lit value)) ≠
        some (lo, hi, USide.param name) := by
    cases uSchranke (uSliceConstants ctx) expression with
    | none => intro impossible; cases impossible
    | some value =>
      intro impossible
      have disjoint : USide.lit value = USide.param name :=
        congrArg (fun fields : Int × Int × USide => fields.2.2) (Option.some.inj impossible)
      cases disjoint
  cases source
  case «variable» current =>
    simp only [uSliceInteger] at recognized
    split at recognized
    · rename_i lower upper resolved
      split at recognized
      · rename_i localRead
        simp only [Option.some.injEq, Prod.mk.injEq, USide.param.injEq] at recognized
        obtain ⟨rfl, rfl, rfl⟩ := recognized
        exact ⟨rfl, resolved, localRead⟩
      · cases recognized
    · split at recognized
      · cases recognized
      · exact (notLiteral _ recognized).elim
  all_goals
    simp only [uSliceInteger] at recognized
    exact (notLiteral _ recognized).elim

/-- A varying local endpoint and static upper endpoint and index
    satisfy the productive slice checks together. -/
theorem mixedArraySliceObservations_erfuellbar (τ : Ty) (capacity : Nat) (enough : 4 ≤ capacity) :
    ∃ scope : UCtx,
      uWertBody scope (.built "lenof" [.built "#slice" [.variable "a", .variable "i", .lit 4]]) =
        .ok (.sub (.lit (Int.ofNat 4)) (.param "i")) ∧
      uWertBody scope (.index (.built "#slice" [.variable "a", .variable "i", .lit 4]) (.lit 1)) =
        .ok (.idx (.param "a") (.add (.param "i") (.lit (Int.ofNat 1)))) := by
  let scope : UCtx := {
    names := ["a", "i"], kinds := [.wert, .int], types := [.arr τ capacity, .int 0 1],
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have arrayType : uSliceLocalType scope "a" = some (.arr τ capacity) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have firstType : uSliceLocalType scope "i" = some (.int 0 1) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have arrayRead : uWertBlatt scope (.variable "a") = .ok (.param "a") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have firstRead : uWertBlatt scope (.variable "i") = .ok (.param "i") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have bounds : (0 : Int) ≤ 0 ∧ (1 : Int) ≤ Int.ofNat 4 ∧ Int.ofNat 4 ≤ capacity :=
    ⟨by decide, by decide, Int.ofNat_le.mpr enough⟩
  have position : (0 : Int) ≤ Int.ofNat 1 ∧ Int.ofNat 1 < Int.ofNat 4 - 1 := by decide
  refine ⟨scope, ?_, ?_⟩ <;>
    simp only [uWertBody, uRechne, uLocalArraySliceObservation, uFixedLocalArrayExtent, uSliceInteger,
      uSchranke, Option.map_some, bind, Option.bind,
      arrayType, firstType, arrayRead, firstRead, bounds, position, and_self, ite_true]

/-- A fixed length with a varying start lowers its observations directly,
    even when the endpoint intervals overlap. -/
theorem fixedSpanObservations_erfuellbar (τ : Ty) (capacity : Nat) (enough : 6 ≤ capacity) :
    ∃ scope : UCtx,
      let span := SExpr.built "#slice" [.variable "a", .variable "i", .bin "+" (.variable "i") (.lit 2)]
      uWertBody scope (.built "lenof" [span]) = .ok (.lit (Int.ofNat 2)) ∧
      uWertBody scope (.index span (.lit 1)) = .ok (.idx (.param "a") (.add (.param "i") (.lit (Int.ofNat 1)))) := by
  let scope : UCtx := {
    names := ["a", "i"], kinds := [.wert, .int], types := [.arr τ capacity, .int 0 4],
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have arrayType : uSliceLocalType scope "a" = some (.arr τ capacity) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have firstType : uSliceLocalType scope "i" = some (.int 0 4) := by
    simp [scope, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have arrayRead : uWertBlatt scope (.variable "a") = .ok (.param "a") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have firstRead : uWertBlatt scope (.variable "i") = .ok (.param "i") := by
    simp [scope, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have sameName : strEq "i" "i" = true := by simp [strEq]
  have fits : (0 : Int) ≤ Int.ofNat 2 ∧ (0 : Int) ≤ 0 ∧ 4 + Int.ofNat 2 ≤ capacity :=
    ⟨by decide, by decide, Int.ofNat_le.mpr enough⟩
  have extent : uFixedLocalArrayExtent scope (uWertBlatt scope) (.param "a") (.variable "i")
      (.bin "+" (.variable "i") (.lit 2)) = some (τ, 2, .param "i") := by
    simp only [uFixedLocalArrayExtent, sameName, Bool.not_true, Bool.false_eq_true, ite_false,
      arrayType, firstType, uSchranke, fits, and_self, ite_true, firstRead,
      show (Int.ofNat 2).toNat = 2 by decide]
  have position : (0 : Int) ≤ Int.ofNat 1 ∧ Int.ofNat 1 < (2 : Nat) := by decide
  refine ⟨scope, ?_, ?_⟩ <;>
    simp only [uWertBody, uRechne, uLocalArraySliceObservation, extent, uSliceInteger, uSchranke,
      Option.map_some, bind, Option.bind, arrayType, arrayRead, position, and_self, ite_true]

/-- A static literal substring admitted as a predicate argument lowers
    to the exact model subsequence at the checked byte bound. -/
theorem specTextSliceArgument_low {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (ctx : UCtx) (fn : UFn) (er : Option Ty) (text : String) (first last : Nat)
    (bounds : first ≤ last ∧ last ≤ text.toUTF8.toList.length) :
    let argument := SExpr.built "#slice" [.ext .text [text] [], .lit first, .lit last]
    let bytes := text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)
    uSpecValueArgument ctx (.str (last - first)) argument = .ok () ∧
      ∃ decoded, bytesZahl bytes = some decoded ∧
        ∃ inside : SliceOk decoded.length first last,
          lowWertE u Γ Λ fn er (.slice (.text bytes) first last) =
            .ok ⟨.str (last - first), .strLit (sliceValue decoded first last)
              (Nat.le_of_eq (sliceValue_length decoded first last inside))⟩ := by
  intro argument bytes
  obtain ⟨_, checked⟩ := specTextSliceArgument_erfuellbar ctx text first last bounds
  obtain ⟨decoded, valid⟩ := bytesZahl_uint8 text.toUTF8.toList
  have length := bytesZahl_laenge _ decoded valid
  rw [List.length_map] at length
  have inside : SliceOk decoded.length first last := ⟨bounds.1, length.symm ▸ bounds.2⟩
  refine ⟨checked, decoded, valid, inside, ?_⟩
  simp only [lowWertE, lowText, bytes, valid, Except.bind, bind]
  exact lowerSlice_string decoded (Nat.le_refl _) first last inside

end Gabbro.Grammatik.Parser.UebersetzeAllg
