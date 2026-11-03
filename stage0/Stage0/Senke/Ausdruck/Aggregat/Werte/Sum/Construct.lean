/- Generic construction proof: header, selected payload and deterministic padding. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Code
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
  let result : Wert D (.sum cs) := ⟨i, Fall.ofNutzlast D.Fn D.passt cs i v⟩
  change max (max header.2 childTop) (max zeros.2 (d + valueWords (.sum cs))) ≤ K at fits
  simp only [Nat.max_le] at fits
  have pw := payloadWords_bound cs i
  have hw : 0 < integerWords 0 (cs.length - 1) := by unfold integerWords; omega
  have full : valueWords (.sum cs) = integerWords 0 (cs.length - 1) + sumPayloadWords cs := by
    simp only [valueWords, separate, Bool.false_eq_true, ↓reduceIte]
  have spanFits : d + integerWords 0 (cs.length - 1) + sumPayloadWords cs ≤ K := by
    simpa only [full, Nat.add_assoc] using fits.2.2
  have payloadBaseFits : d + integerWords 0 (cs.length - 1) ≤ K := by omega
  have paddingBaseFits : z ≤ K := by
    change d + integerWords 0 (cs.length - 1) + payloadWords (cs.get i) ≤ K
    omega
  have p : Pre L m pc fp K d (header.1 ++ (child ++ zeros.1)) ρ W reserved := by
    simpa only [header, zeros, z, List.append_assoc] using pre
  obtain ⟨m1, s1, ch1, tag⟩ := constWords_ok (L := L)
    (integerEncoding (integerWords 0 (cs.length - 1)) i.val) fits.1.1 p.left
  have p1 := p.next ch1 (by omega : d ≤ d + integerWords 0 (cs.length - 1)) (by omega)
  obtain ⟨m2, s2, ch2, valid, value⟩ := ih child childTop childMade fits.1.2 m1 _ p1.left
  have p2 := p1.next ch2 (by omega : d + integerWords 0 (cs.length - 1) ≤ z)
    payloadBaseFits
  obtain ⟨m3, s3, ch3, padding⟩ := constWords_ok (L := L)
    (List.replicate (sumPayloadWords cs - payloadWords (cs.get i)) 0) fits.2.1 p2
  have tag2 : WordsAt m2 fp d (integerEncoding (integerWords 0 (cs.length - 1)) i.val) :=
    tag.agree_low ch2 p1.frame.room (by simp only [integerEncoding_length]; omega) payloadBaseFits
  have tag3 : WordsAt m3 fp d (integerEncoding (integerWords 0 (cs.length - 1)) i.val) :=
    tag2.agree_low ch3 p2.frame.room (by simp only [integerEncoding_length]; dsimp only [z]; omega) paddingBaseFits
  have value3 := value.agree_low ch3 p2.frame.room
    (by simp only [payloadEncoding_length]; dsimp only [z]; omega) paddingBaseFits
  refine ⟨m3, ?_, ch1.trans ((ch2.mono (by omega)).trans (ch3.mono (by dsimp only [z]; omega))), ?_, ?_⟩
  · simpa only [header, zeros, z, List.length_append, pc_add] using s1.trans (s2.trans s3)
  · exact (sumValid_selected L cs i (Fall.ofNutzlast D.Fn D.passt cs i v)).mpr
      (by simpa only [Fall.to_of] using valid)
  · have encoding := encodeWords_sum L separate result
    change encodeWords L (.sum cs) result =
        integerEncoding (integerWords 0 (cs.length - 1)) i.val ++
        payloadEncoding L (cs.get i)
          (Fall.toNutzlast D.Fn D.passt cs i (Fall.ofNutzlast D.Fn D.passt cs i v)) ++
        List.replicate (sumPayloadWords cs - payloadWords (cs.get i)) 0 at encoding
    rw [Fall.to_of] at encoding
    change WordsAt m3 fp d (encodeWords L (.sum cs) result)
    rw [encoding, List.append_assoc, wordsAt_append, wordsAt_append]
    simpa only [integerEncoding_length, payloadEncoding_length, z] using
      And.intro tag3 (And.intro value3 padding)

end Gabbro.Stage0.Senke
