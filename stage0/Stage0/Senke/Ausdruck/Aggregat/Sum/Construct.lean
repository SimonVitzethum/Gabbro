/- Generic construction proof: header, selected payload and deterministic padding. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Sum.Code
public import Stage0.Senke.Ausdruck.Aggregat.Materialize
public import Stage0.Senke.Welt.Spans.Cell
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- No payload representation is specialized here: the recursively proved
    complete value is embedded unchanged into the selected sum case. -/
theorem sumSpan_ok {cs : List (Option Ty)} (i : Fin cs.length)
    (v : Nutzlast D.Fn D.passt (cs.get i)) (separate : sumFits cs = false)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {fp : Runner.W} {K d top : Nat}
    {payload : Option (List II × Nat)} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ ca ta, payload = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + integerWords 0 (cs.length - 1)) ca ρ W reserved →
      Executes m pc fp K (d + integerWords 0 (cs.length - 1)) ca
        (fun m' => PayloadAt L m' fp (d + integerWords 0 (cs.length - 1)) (cs.get i) v))
    (made : sumSpanL cs i d payload = some (c, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.sum cs) ⟨i, Fall.ofNutzlast _ _ _ _ v⟩ := by
  simp only [sumSpanL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨child, childTop⟩, childMade, rfl, rfl⟩ := made
  let header := constWords (integerEncoding (integerWords 0 (cs.length - 1)) i.val) d
  let z := d + integerWords 0 (cs.length - 1) + payloadWords (cs.get i)
  let zeros := constWords (List.replicate (sumPayloadWords cs - payloadWords (cs.get i)) 0) z
  have pw := payloadWords_bound cs i
  have hw : 0 < integerWords 0 (cs.length - 1) := by unfold integerWords; omega
  have full : valueWords (.sum cs) = integerWords 0 (cs.length - 1) + sumPayloadWords cs := by
    simp only [valueWords, separate, Bool.false_eq_true, ↓reduceIte]
  have p : Pre L m pc fp K d (header.1 ++ (child ++ zeros.1)) ρ W reserved := by
    simpa only [header, zeros, z, List.append_assoc] using pre
  obtain ⟨m1, s1, ch1, tag⟩ := constWords_ok (L := L)
    (integerEncoding (integerWords 0 (cs.length - 1)) i.val) (by omega) p.left
  have p1 := p.next ch1 (by omega : d ≤ d + integerWords 0 (cs.length - 1)) (by omega)
  obtain ⟨m2, s2, ch2, valid, value⟩ := ih child childTop childMade (by omega) m1 _ p1.left
  have p2 := p1.next ch2 (by omega : d + integerWords 0 (cs.length - 1) ≤ z)
    (by dsimp only [z]; omega)
  obtain ⟨m3, s3, ch3, padding⟩ := constWords_ok (L := L)
    (List.replicate (sumPayloadWords cs - payloadWords (cs.get i)) 0) (by omega) p2
  have tag2 : WordsAt m2 fp d (integerEncoding (integerWords 0 (cs.length - 1)) i.val) :=
    tag.agree_low ch2 p1.frame.room (by simp only [integerEncoding_length]; omega) (by omega)
  have tag3 : WordsAt m3 fp d (integerEncoding (integerWords 0 (cs.length - 1)) i.val) :=
    tag2.agree_low ch3 p2.frame.room (by simp only [integerEncoding_length]; dsimp only [z]; omega) (by omega)
  have value3 := value.agree_low ch3 p2.frame.room
    (by simp only [payloadEncoding_length]; dsimp only [z]; omega) (by omega)
  refine ⟨m3, ?_, ch1.trans ((ch2.mono (by omega)).trans (ch3.mono (by dsimp only [z]; omega))), ?_, ?_⟩
  · simpa only [List.length_append, pc_add, BitVec.add_assoc] using s1.trans (s2.trans s3)
  · exact (sumValid_selected L cs i _).mpr (by simpa only [Fall.of_to] using valid)
  · rw [encodeWords_sum L separate, List.append_assoc, wordsAt_append, wordsAt_append]
    simpa only [Fall.of_to, integerEncoding_length, payloadEncoding_length, z] using
      And.intro tag3 (And.intro value3 padding)

end Gabbro.Stage0.Senke
