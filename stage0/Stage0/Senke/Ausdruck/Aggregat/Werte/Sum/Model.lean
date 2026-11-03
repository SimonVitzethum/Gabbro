/- Separated sum values share the complete aggregate encoding of their payload. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- A bare case occupies no payload words. -/
def payloadWords : Option Ty → Nat
  | none => 0
  | some τ => valueWords τ

def payloadEncoding (L : Lay D) : (c : Option Ty) → Nutzlast D.Fn D.passt c → List Runner.W
  | none, _ => []
  | some τ, v => encodeWords L τ v

def PayloadValid (L : Lay D) : (c : Option Ty) → Nutzlast D.Fn D.passt c → Prop
  | none, _ => True
  | some τ, v => ValueValid L τ v

def PayloadAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) (s : Nat)
    (c : Option Ty) (v : Nutzlast D.Fn D.passt c) : Prop :=
  PayloadValid L c v ∧ WordsAt m fp s (payloadEncoding L c v)

@[simp] theorem payloadEncoding_length (L : Lay D) (c : Option Ty)
    (v : Nutzlast D.Fn D.passt c) : (payloadEncoding L c v).length = payloadWords c := by
  cases c with
  | none => rfl
  | some τ => exact encodeWords_length L τ (v : Wert D τ)

theorem payloadWords_bound : ∀ (cs : List (Option Ty)) (i : Fin cs.length),
    payloadWords (cs.get i) ≤ sumPayloadWords cs
  | [], i => Fin.elim0 i
  | none :: _, ⟨0, _⟩ => Nat.zero_le _
  | some τ :: _, ⟨0, _⟩ => Nat.le_max_left _ _
  | c :: cs, ⟨i + 1, hi⟩ => by
    have bound := payloadWords_bound cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    cases c <;> simp only [sumPayloadWords] <;> exact Nat.le_trans bound (by omega)

theorem encodeSumPayload_selected (L : Lay D) : ∀ (cs : List (Option Ty))
    (i : Fin cs.length) (v : Fall D.Fn D.passt cs i),
    encodeSumPayload L cs i v = payloadEncoding L (cs.get i) (Fall.toNutzlast _ _ _ _ v)
  | [], i, _ => Fin.elim0 i
  | none :: _, ⟨0, _⟩, _ => by
    rw [encodeSumPayload.eq_def] <;> rfl
  | some _ :: _, ⟨0, _⟩, _ => by
    rw [encodeSumPayload.eq_def] <;> rfl
  | c :: cs, ⟨i + 1, hi⟩, v => by
    cases c <;> rw [encodeSumPayload.eq_def, Fall.toNutzlast_succ] <;>
      exact encodeSumPayload_selected L cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v

theorem sumValid_selected (L : Lay D) : ∀ (cs : List (Option Ty))
    (i : Fin cs.length) (v : Fall D.Fn D.passt cs i),
    SumValid L cs i v ↔ PayloadValid L (cs.get i) (Fall.toNutzlast _ _ _ _ v)
  | [], i, _ => Fin.elim0 i
  | none :: _, ⟨0, _⟩, _ => Iff.rfl
  | some _ :: _, ⟨0, _⟩, _ => Iff.rfl
  | c :: cs, ⟨i + 1, hi⟩, v => by
    cases c <;> rw [SumValid.eq_def, Fall.toNutzlast_succ] <;>
      exact sumValid_selected L cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v

/-- The packed schema admits only absent payloads and bounded integers. Their model types
    already carry the range, and neither has additional representation obligations. -/
private theorem packedPayload_valid (L : Lay D) (c : Option Ty)
    (fits : (match c with
      | none => true
      | some (.int lo hi) => decide (hi - lo < 2 ^ 56)
      | some _ => false) = true)
    (v : Nutzlast D.Fn D.passt c) : PayloadValid L c v := by
  cases c with
  | none => trivial
  | some τ =>
    cases τ with
    | int lo hi =>
      change True
      trivial
    | bool | opt _ | sum _ | why _ | never | fl _ _ | fnptr _ | ptr _ | ref _ | arr _ _ | str _ | prod _ _ =>
      exact Bool.noConfusion fits

/-- Packed payloads have no recursive validity obligations: their schema admits
    only bare cases and bounded integers. -/
theorem packedSum_valid (L : Lay D) : ∀ (cs : List (Option Ty)), sumFits cs = true →
    ∀ (i : Fin cs.length) (v : Fall D.Fn D.passt cs i), SumValid L cs i v := by
  intro cs fits i v
  simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at fits
  apply (sumValid_selected L cs i v).mpr
  exact packedPayload_valid L (cs.get i) (fits.2 _ (List.get_mem cs i))
    (Fall.toNutzlast _ _ _ _ v)

theorem encodeWords_sum (L : Lay D) {cs : List (Option Ty)}
    (separate : sumFits cs = false) (v : Wert D (.sum cs)) :
    encodeWords L (.sum cs) v =
      integerEncoding (integerWords 0 (cs.length - 1)) v.1.val ++
      payloadEncoding L (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2) ++
      List.replicate (sumPayloadWords cs - payloadWords (cs.get v.1)) 0 := by
  simp only [encodeWords, separate, Bool.false_eq_true, ↓reduceIte,
    encodeSumPayload_selected, payloadEncoding_length, List.append_assoc]

theorem ValueAt.sum_payload {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {s : Nat}
    {cs : List (Option Ty)} {v : Wert D (.sum cs)} (separate : sumFits cs = false)
    (input : ValueAt L m fp s (.sum cs) v) :
    PayloadAt L m fp (s + integerWords 0 (cs.length - 1))
      (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2) := by
  refine ⟨(sumValid_selected L cs v.1 v.2).mp input.1, ?_⟩
  have words := input.2
  rw [encodeWords_sum L separate, List.append_assoc, wordsAt_append] at words
  have selected := (wordsAt_append _ _).mp words.2
  simpa only [integerEncoding_length] using selected.1

end Gabbro.Stage0.Senke
