module

public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

private theorem addressImmediate {address : Nat} (bound : address < 2 ^ 31) :
    lit32 (BitVec.ofNat 64 address).toInt = true := by
  have small : address < 2 ^ 64 := by omega
  have natural : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have signed : (BitVec.ofNat 64 address).toInt = (address : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [natural]; omega), natural]
  rw [signed, lit32, Bool.and_eq_true]
  exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩

private theorem elementImmediateShape :
    ∀ (length : Nat) (left right : Fin length → List Runner.W),
      (∀ index, (left index).map (fun word => lit32 word.toInt) = (right index).map (fun word => lit32 word.toInt)) →
      (elementEncoding length left).map (fun word => lit32 word.toInt) =
        (elementEncoding length right).map (fun word => lit32 word.toInt) := by
  intro length
  induction length with
  | zero => intro left right same; rfl
  | succ length ih =>
    intro left right same
    simp only [elementEncoding, List.map_append, same, ih _ _ (fun index => same index.succ)]

section
variable (original relocated : Lay D)
variable (first : ∀ fn, original.fa fn < 2 ^ 31) (second : ∀ fn, relocated.fa fn < 2 ^ 31)

include first second

mutual
/-- Relocation can change a reference word inside any encoded value.
    It cannot change the instruction budget for materializing that value. -/
theorem encodeWords_immediateShape :
    (type : Ty) → (value : Wert D type) →
    (encodeWords original type value).map (fun word => lit32 word.toInt) =
      (encodeWords relocated type value).map (fun word => lit32 word.toInt)
  | .fnptr _, value => by
    simp only [encodeWords, List.map_cons, List.map_nil, addressImmediate (first value.1),
      addressImmediate (second value.1)]
  | .sum cases, value => by
    simp only [encodeWords]
    split
    · rfl
    · have payload := encodeSumPayload_immediateShape cases value.1 value.2
      have width : (encodeSumPayload original cases value.1 value.2).length =
          (encodeSumPayload relocated cases value.1 value.2).length := by
        simpa only [List.length_map] using congrArg List.length payload
      simp only [List.map_append, payload, width]
  | .prod _ fields, value => by
    simp only [encodeWords]
    split
    · rfl
    · exact encodeProductFields_immediateShape fields value
  | .arr element length, value => by
    simp only [encodeWords]
    split
    · rfl
    · exact elementImmediateShape length _ _ (fun i =>
        encodeWords_immediateShape element (value i))
  | .int .., _ | .bool, _ | .opt .., _ | .why .., _ | .ref .., _ | .str .., _ | .fl .., _ | .ptr .., _ => by
    simp only [encodeWords]
  | .never, value => nomatch value
termination_by structural type => type

private theorem encodeSumPayload_immediateShape : (cases : List (Option Ty)) →
    (tag : Fin cases.length) → (value : Fall D.Fn D.passt cases tag) →
    (encodeSumPayload original cases tag value).map (fun word => lit32 word.toInt) =
      (encodeSumPayload relocated cases tag value).map (fun word => lit32 word.toInt)
  | [], tag, _ => Fin.elim0 tag
  | none :: _, ⟨0, _⟩, _ => rfl
  | some type :: _, ⟨0, _⟩, value =>
    encodeWords_immediateShape type value
  | _ :: tail, ⟨index + 1, bound⟩, value => by
    simpa only [encodeSumPayload] using
      encodeSumPayload_immediateShape tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩ value
termination_by structural cases => cases

private theorem encodeProductFields_immediateShape : (fields : List Ty) →
    (value : ProdVal D.Fn D.passt fields) →
    (encodeProductFields original fields value).map (fun word => lit32 word.toInt) =
      (encodeProductFields relocated fields value).map (fun word => lit32 word.toInt)
  | [], _ => rfl
  | type :: fields, value => by
    simp only [encodeProductFields, List.map_append,
      encodeWords_immediateShape type (ProdVal.hd value),
      encodeProductFields_immediateShape fields (ProdVal.tl value)]
termination_by structural fields => fields
end

theorem relocatedValue_measure (type : Ty) (value : Wert D type) (destination : Nat) :
    codeMeasure (constWords (encodeWords original type value) destination) =
      codeMeasure (constWords (encodeWords relocated type value) destination) :=
  constWords_measure (encodeWords_immediateShape original relocated first second type value) destination

end

/-- Global locations change with the world base. Their complete typed
    loads and stores use the same code and frame budgets at either base. -/
theorem globalAccess_measure (original relocated : Lay D) (global : D.Glob) (destination : Nat)
    (first : original.ga global + 8 * valueWords (D.gtyp global) < 2 ^ 31)
    (second : relocated.ga global + 8 * valueWords (D.gtyp global) < 2 ^ 31) :
    (globalValueC original global destination).map codeMeasure =
      (globalValueC relocated global destination).map codeMeasure ∧
    ∀ left right, codeMeasure left = codeMeasure right →
      (globalStoreC original global destination left).map codeMeasure =
        (globalStoreC relocated global destination right).map codeMeasure := by
  constructor
  · simp only [globalValueC, if_pos first, if_pos second, Option.map_some, codeMeasure, loadSpan_length]
  · intro left right same
    obtain ⟨length, frame⟩ := Prod.mk.inj same
    simp only [globalStoreC, if_pos first, if_pos second, Option.map_some, codeMeasure,
      List.length_append, storeSpan_length, length, frame]

/-- A column's absolute base is the sole relocated operand in its
    address calculation. The index code contributes its own budget. -/
theorem cellAddress_measure (original relocated : Lay D) (table : D.Tab) (field : D.Feld table)
    (destination : Nat) {left right : List II × Nat} (same : codeMeasure left = codeMeasure right)
    (first : original.col table field < 2 ^ 31) (second : relocated.col table field < 2 ^ 31) :
    (cellAddressC original table field destination left).map codeMeasure =
      (cellAddressC relocated table field destination right).map codeMeasure := by
  obtain ⟨length, frame⟩ := Prod.mk.inj same
  by_cases stride : 8 * valueWords (D.typ table field) < 2 ^ 31
  · simp only [cellAddressC, first, second, stride, and_self, ite_true, Option.map_some,
      codeMeasure, List.length_append, List.length_cons, List.length_nil, length, frame]
  · simp only [cellAddressC, first, second, stride, and_false, ite_false, Option.map_none]

private theorem codeMeasure_bind {left right : Option (List II × Nat)}
    {nextLeft nextRight : List II × Nat → Option (List II × Nat)}
    (before : left.map codeMeasure = right.map codeMeasure)
    (next : ∀ a b, codeMeasure a = codeMeasure b →
      (nextLeft a).map codeMeasure = (nextRight b).map codeMeasure) :
    (left.bind nextLeft).map codeMeasure = (right.bind nextRight).map codeMeasure := by
  cases left <;> cases right
  · rfl
  · cases before
  · cases before
  · exact next _ _ (Option.some.inj before)

/-- Complete indexed reads and writes compose the address budget with
    the same typed cell span, independently of its relocated address. -/
theorem cellAccess_measure (original relocated : Lay D) (table : D.Tab) (field : D.Feld table)
    (destination : Nat) {leftIndex rightIndex : List II × Nat}
    (indices : codeMeasure leftIndex = codeMeasure rightIndex)
    (first : original.col table field < 2 ^ 31) (second : relocated.col table field < 2 ^ 31) :
    (slotValueC original table field destination leftIndex).map codeMeasure =
      (slotValueC relocated table field destination rightIndex).map codeMeasure ∧
    ∀ leftValue rightValue, codeMeasure leftValue = codeMeasure rightValue →
      (slotStoreC original table field destination leftValue leftIndex).map codeMeasure =
        (slotStoreC relocated table field destination rightValue rightIndex).map codeMeasure := by
  have address := cellAddress_measure original relocated table field
    (destination + valueWords (D.typ table field)) indices first second
  constructor
  · unfold slotValueC
    apply codeMeasure_bind address
    intro left right measured
    obtain ⟨length, top⟩ := Prod.mk.inj measured
    simp only [pure, Option.pure_def, Option.map_some, codeMeasure, List.length_append, length, top]
  · intro leftValue rightValue values
    obtain ⟨valueLength, valueTop⟩ := Prod.mk.inj values
    unfold slotStoreC
    apply codeMeasure_bind address
    intro left right measured
    obtain ⟨length, top⟩ := Prod.mk.inj measured
    simp only [pure, Option.pure_def, Option.map_some, codeMeasure, List.length_append,
      length, top, valueLength, valueTop]

end Gabbro.Stage0.Senke
