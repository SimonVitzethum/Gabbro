module

public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze LowLevel.Construct

/-- The source length is an exact byte interval, and indexing translates
    the position into the original literal. -/
theorem textSliceObservations_source (ctx : UCtx) (blatt : SExpr → Except String USide)
    (text : String) (first last index : SExpr) (begin finish position : USide)
    (firstLo firstHi lastLo lastHi indexLo indexHi : Int)
    (readFirst : uSliceInteger ctx blatt first = some (firstLo, firstHi, begin))
    (readLast : uSliceInteger ctx blatt last = some (lastLo, lastHi, finish))
    (readIndex : uSliceInteger ctx blatt index = some (indexLo, indexHi, position))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ text.toUTF8.toList.length)
    (inside : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi) :
    let bytes := text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)
    let slice := SExpr.built "#slice" [.ext .text [text] [], first, last]
    uRechne ctx blatt (.built "lenof" [slice]) = .ok (.sub finish begin) ∧
      uRechne ctx blatt (.index slice index) = .ok (.idx (.text bytes) (.add begin position)) := by
  dsimp only
  constructor <;> rw [uRechne] <;>
    simp only [uSliceObservation, uSliceView, uRelativeSlice, readFirst, readLast, readIndex, bounds,
      inside, bind, Option.bind, ite_true]

/-- The actual body elaborator admits both observations with genuinely
    varying indices and endpoints for every literal long enough. -/
theorem textSliceObservations_erfuellbar (text : String) (enough : 4 ≤ text.toUTF8.toList.length) :
    ∃ scope : UCtx,
      let bytes := text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)
      let slice := SExpr.built "#slice" [.ext .text [text] [], .variable "i", .variable "j"]
      uWertBody scope (.built "lenof" [slice]) = .ok (.sub (.param "j") (.param "i")) ∧
        uWertBody scope (.index slice (.variable "k")) =
          .ok (.idx (.text bytes) (.add (.param "i") (.param "k"))) := by
  let scope : UCtx := {
    names := ["i", "j", "k"], kinds := [.int, .int, .int]
    types := [.int 0 1, .int 3 4, .int 0 1]
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  refine ⟨scope, textSliceObservations_source scope (uWertBlatt scope) text
    (.variable "i") (.variable "j") (.variable "k") (.param "i") (.param "j") (.param "k")
    0 1 3 4 0 1 ?_ ?_ ?_ ⟨by decide, by decide, by omega⟩ ⟨by decide, by decide⟩⟩
  all_goals
    simp [scope, uSliceInteger, uSliceLocalType, uValueType, strEq_apply_eq_decide, List.findIdx?_cons,
      uWertBlatt, uParamNr, uParamNrAux, uArtBei]

theorem lowWertE_textSliceIndex {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} (text : String) {first index : USide}
    {firstLo firstHi indexLo indexHi : Int}
    {begin : Expr (declOf u) Γ Λ (.int firstLo firstHi)}
    {position : Expr (declOf u) Γ Λ (.int indexLo indexHi)}
    (readFirst : lowWertE u Γ Λ fn er first = .ok ⟨.int firstLo firstHi, begin⟩)
    (readIndex : lowWertE u Γ Λ fn er index = .ok ⟨.int indexLo indexHi, position⟩) :
    ∃ decoded : List (Zahl 0 255), decoded.length = text.toUTF8.toList.length ∧
      lowWertE u Γ Λ fn er
        (.idx (.text (text.toUTF8.toList.map fun byte => Int.ofNat byte.toNat)) (.add first index)) =
        .ok ⟨.int 0 255, .strGet (.strLit decoded (Nat.le_refl _)) (.add begin position)⟩ := by
  obtain ⟨decoded, valid⟩ := bytesZahl_uint8 text.toUTF8.toList
  refine ⟨decoded, ?_, ?_⟩
  · rw [bytesZahl_laenge _ decoded valid, List.length_map]
  · simp only [lowWertE, readFirst, readIndex, lowText, valid, LowSide.plus, LowSide.wert,
      zahlVon, LowWert.zahl, idxW]

/-- The exact length and selected byte agree with model substring
    semantics for every environment of the typed endpoints. -/
theorem eval_textSliceObservations {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {capacity : Nat}
    {firstLo firstHi lastLo lastHi indexLo indexHi : Int}
    (base : Expr D Γ Λ (.str capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi)) (position : Expr D Γ Λ (.int indexLo indexHi))
    (initial world : World D) (env : Env D Γ)
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ (eval initial base world env).1.length)
    (inside : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi) :
    let value := eval initial base world env
    let first := eval initial begin world env
    let last := eval initial finish world env
    let index := eval initial position world env
    ∃ valid : SliceOk value.1.length first.n.toNat last.n.toNat,
      (eval initial (.sub finish begin) world env).n =
        ((strSliceValue value first.n.toNat last.n.toNat valid).1.length : Int) ∧
      eval initial (.strGet base (.add begin position)) world env =
        strGetW (strSliceValue value first.n.toNat last.n.toNat valid) index.n := by
  dsimp only
  have firstLo := (eval initial begin world env).lo_le
  have firstHi := (eval initial begin world env).le_hi
  have lastLo := (eval initial finish world env).lo_le
  have lastHi := (eval initial finish world env).le_hi
  have indexLo := (eval initial position world env).lo_le
  have indexHi := (eval initial position world env).le_hi
  refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
  · simp only [eval, Zahl.sub, strSliceValue, sliceValue_length _ _ _ (show SliceOk _ _ _ from
      ⟨by omega, by omega⟩)]
    omega
  · simp only [eval, Zahl.add]
    rw [← Int.toNat_of_nonneg (show 0 ≤ (eval initial position world env).n by omega),
      strSliceValue_get _ _ _ _ _ (by omega)]
    congr 1
    omega

end Gabbro.Grammatik.Parser.UebersetzeAllg
