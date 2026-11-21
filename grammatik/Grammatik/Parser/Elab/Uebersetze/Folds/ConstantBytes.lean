module
public import Grammatik.Kern.Syntax.Typen.Teil1

@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The bytes of a string literal as values of `0 .. 255`. -/
def bytesZahl : List Int → Option (List (Zahl 0 255))
  | [] => some []
  | b :: bs =>
    if h : 0 ≤ b ∧ b ≤ 255 then (bytesZahl bs).map (⟨b, h.1, h.2⟩ :: ·) else none

theorem bytesZahl_laenge : ∀ (bs : List Int) (zs : List (Zahl 0 255)), bytesZahl bs = some zs → zs.length = bs.length
  | [], zs, h => by simp only [bytesZahl, Option.some.injEq] at h; subst h; rfl
  | b :: bs, zs, h => by
    unfold bytesZahl at h
    split at h
    · cases hz : bytesZahl bs with
      | none => rw [hz] at h; cases h
      | some ys =>
        rw [hz] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.length_cons, bytesZahl_laenge bs ys hz]
    · cases h

theorem bytesZahl_uint8 (bytes : List UInt8) :
    ∃ decoded, bytesZahl (bytes.map fun b => Int.ofNat b.toNat) = some decoded := by
  induction bytes with
  | nil => exact ⟨[], rfl⟩
  | cons b rest ih =>
    obtain ⟨tail, valid⟩ := ih
    have lower : 0 ≤ (Int.ofNat b.toNat) := Int.natCast_nonneg _
    have upper : (Int.ofNat b.toNat) ≤ 255 := by
      change (↑b.toNat : Int) ≤ 255
      have bound := b.toNat_lt
      omega
    refine ⟨⟨_, lower, upper⟩ :: tail, ?_⟩
    simp only [List.map_cons, bytesZahl, dite_eq_left (And.intro lower upper), valid, Option.map_some]

end Gabbro.Grammatik.Parser.UebersetzeAllg
