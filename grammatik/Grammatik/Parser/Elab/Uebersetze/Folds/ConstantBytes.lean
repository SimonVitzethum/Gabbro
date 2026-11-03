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

end Gabbro.Grammatik.Parser.UebersetzeAllg
