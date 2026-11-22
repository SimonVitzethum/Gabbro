module

public import Stage0.Senke.Welt.Spans.IdleValue

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

theorem frei_withIdle (Γ : Ctx) (reserved : Nat) :
    frei (Γ.map tyR) reserved = frei Γ reserved := by
  simp only [frei, tyR, contextWords_mapNumbers]

theorem productOffset_withIdle {fields : List Ty} {ty : Ty} (field : FieldAt fields ty) :
    productOffset (field.mapNumbers (· + 1) id) = productOffset field := by
  induction field with
  | head => rfl
  | tail field ih => simp only [FieldAt.mapNumbers, productOffset, valueWords_mapNumbers, ih]

theorem globalValueC_withIdle (L : Lay D) (g : D.Glob) (dest : Nat) :
    globalValueC L.withIdle g dest = globalValueC L g dest := by
  simp only [globalValueC, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

theorem cellAddressC_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (dest : Nat) (index : List II × Nat) :
    cellAddressC L.withIdle t f dest index = cellAddressC L t f dest index := by
  simp only [cellAddressC, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

theorem slotValueC_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (dest : Nat) (index : List II × Nat) :
    slotValueC L.withIdle t f dest index = slotValueC L t f dest index := by
  simp only [slotValueC, Deklaration.mitRuhe, tyR, valueWords_mapNumbers, cellAddressC_withIdle]

private theorem wordCompatB_tyR : ∀ t : Ty, wordCompatB (tyR t) = wordCompatB t
  | .arr t 1 => wordCompatB_tyR t
  | .sum _ => sumFits_mapNumbers _ _ _
  | .arr _ 0 | .arr _ (_ + 2) | .ptr ⟨_, _, .table _⟩
  | .int .. | .bool | .opt .. | .why .. | .never | .fl .. | .fnptr .. | .ref .. | .str .. | .prod .. => rfl

private theorem aggregateFits_tyR (ty : Ty) : aggregateFits (tyR ty) = aggregateFits ty := by
  simp only [aggregateFits, wordCompatB_tyR, tyR, valueWords_mapNumbers]

private theorem slotC_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (dest : Nat) (index : List II × Nat) :
    slotC L.withIdle t f dest index = slotC L t f dest index := by
  have compat : aggregateFits (D.mitRuhe.typ t f) = aggregateFits (D.typ t f) := aggregateFits_tyR _
  simp only [slotC, compat, slotA, Lay.withIdle]
  with_unfolding_all rfl

theorem reachesL_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (dest : Nat)
    (left right : Option (List II × Nat)) :
    reachesL L.withIdle t f dest left right = reachesL L t f dest left right := by
  have travel : ∀ n a b, reachL L.withIdle t f dest n a b = reachL L t f dest n a b := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro a b
      simp only [reachL, funext (slotC_withIdle L t f dest), ih]
  simp only [reachesL, Deklaration.mitRuhe, travel]

theorem readBytesWideL_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t)
    (index : Nat → Option (List II × Nat)) (n dest : Nat) :
    readBytesWideL L.withIdle t f index n dest = readBytesWideL L t f index n dest := by
  have limb (ix : Nat → Option (List II × Nat)) : ∀ count offset d,
      readBytesL L.withIdle t f ix offset count d = readBytesL L t f ix offset count d := by
    intro count
    induction count with
    | zero => intros; rfl
    | succ count ih =>
      intro offset d
      simp only [readBytesL, slotC_withIdle, ih]
  have chunks (ix : Nat → Option (List II × Nat)) : ∀ count bytes offset d,
      readBytesWordsL L.withIdle t f ix count bytes offset d =
      readBytesWordsL L t f ix count bytes offset d := by
    intro count
    induction count with
    | zero => intros; rfl
    | succ count ih =>
      intro bytes offset d
      simp only [readBytesWordsL, limb, ih]
  simp only [readBytesWideL, chunks]

theorem sumSpanL_withIdle (cases : List (Option Ty)) (tag : Fin cases.length)
    (dest : Nat) (payload : Option (List II × Nat)) :
    sumSpanL (Ty.mapCases (· + 1) id cases)
      ⟨tag.val, by rw [Ty.mapCases_length]; exact tag.isLt⟩ dest payload =
      sumSpanL cases tag dest payload := by
  have size : ∀ c, payloadWords (c.map tyR) = payloadWords c := by
    intro c
    cases c <;> simp only [payloadWords, Option.map_none, Option.map_some, tyR, valueWords_mapNumbers]
  have width : valueWords (.sum (Ty.mapCases (· + 1) id cases)) = valueWords (.sum cases) :=
    valueWords_mapNumbers (· + 1) id (.sum cases)
  simp only [sumSpanL, width, Ty.mapCases_length, sumPayloadWords_mapCases, Ty.mapCases_get, size]

end Gabbro.Stage0.Senke
