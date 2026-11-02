module

public import Grammatik.Kern.Semantik.Semantik.T1.Teil1
public import Grammatik.Kern.Syntax.Typen.Transport
public import Grammatik.Kern.Syntax.Typen.Fall

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- `summePasst` through its two digits. -/
theorem summePasst_eq (cs : List (Option Ty)) (n : Int) (i : Fin cs.length) (p : Int)
    (hs : sumWort cs = true) (hi : n % fallZahl cs = (i.val : Int)) (hp : n / fallZahl cs = p) :
    summePasst cs n = (nutzPasst (cs.get i) p).map fun x => ⟨i, Fall.ofNutzlast _ _ _ _ x⟩ := by
  have hk : 0 < cs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  unfold summePasst
  rw [if_pos hs, dif_pos hk]
  dsimp only
  rw [hp]
  generalize hI : (⟨(n % fallZahl cs).toNat, fall_marke_lt cs n hk⟩ : Fin cs.length) = I
  have e : I = i := by
    rw [← hI]
    apply Fin.ext
    show (n % fallZahl cs).toNat = i.val
    rw [hi, Int.toNat_natCast]
  subst e
  rfl

/-- Relocation preserves the scalar ABI boundary, including rejected typed schemas. -/
theorem sumWort_mapCases (sn tn : Nat → Nat) : ∀ cs,
    sumWort (Ty.mapCases sn tn cs) = sumWort cs
  | [] => rfl
  | none :: cs => sumWort_mapCases sn tn cs
  | some τ :: cs => by
    cases τ <;> first | exact sumWort_mapCases sn tn cs | rfl

section Relocation

variable {D D' : Deklaration} (sn tn : Nat → Nat)
  (pointer : ∀ n, {f : D.Fn // D.passt f n = true} →
    {f : D'.Fn // D'.passt f (sn n) = true})

/-- Scalar decoding commutes with the common complete-payload transport. -/
theorem nutzPasst_relocate (c : Option Ty) (n : Int) :
    nutzPasst (D := D') (c.map (Ty.mapNumbers sn tn)) n =
      (nutzPasst (D := D) c n).map (Nutzlast.relocate sn tn pointer c) := by
  cases c with
  | none => simp only [Option.map_none, nutzPasst]; split <;> rfl
  | some τ =>
    cases τ <;> simp only [Option.map_some, Ty.mapNumbers, nutzPasst]
    all_goals first | rfl | split <;> rfl

private theorem nutzPasst_cast {c c' : Option Ty} (h : c = c') (n : Int) :
    nutzPasst (D := D') c' n = (nutzPasst (D := D') c n).map (fun v => h ▸ v) := by
  subst c'
  cases nutzPasst (D := D') c n <;> rfl

/-- Decoding retains the mapped schema, selected tag and entire mapped payload.
    Non-scalar schemas are refused on both sides by the unchanged ABI guard. -/
theorem summePasst_relocate (cs : List (Option Ty)) (n : Int) :
    summePasst (D := D') (Ty.mapCases sn tn cs) n =
      (summePasst (D := D) cs n).map (Val.relocate sn tn pointer (.sum cs)) := by
  have guard := sumWort_mapCases sn tn cs
  by_cases hs : sumWort cs = true
  · have hs' : sumWort (Ty.mapCases sn tn cs) = true := guard.trans hs
    by_cases hk : 0 < cs.length
    · let i : Fin cs.length := ⟨(n % fallZahl cs).toNat, fall_marke_lt cs n hk⟩
      let j : Fin (Ty.mapCases sn tn cs).length :=
        ⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩
      have hpos : (0 : Int) < fallZahl cs := by unfold fallZahl; omega
      have hi : n % fallZahl cs = (i.val : Int) :=
        (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hpos))).symm
      have hj : n % fallZahl (Ty.mapCases sn tn cs) = (j.val : Int) := by
        simpa only [fallZahl, Ty.mapCases_length] using hi
      rw [summePasst_eq _ n j _ hs' hj rfl, summePasst_eq cs n i _ hs hi rfl]
      have payload₀ := nutzPasst_cast (D' := D')
        (Ty.mapCases_get sn tn cs i).symm (n / fallZahl cs)
      have radix : fallZahl (Ty.mapCases sn tn cs) = fallZahl cs := by
        simp only [fallZahl, Ty.mapCases_length]
      rw [radix, payload₀, nutzPasst_relocate sn tn pointer]
      cases hn : nutzPasst (D := D) (cs.get i) (n / fallZahl cs) with
      | none => rfl
      | some v =>
        simp only [Option.map_some, Val.relocate]
        exact (Val.relocateSum_mk sn tn pointer cs i v).symm
    · have hk' : ¬ 0 < (Ty.mapCases sn tn cs).length := by
        simpa only [Ty.mapCases_length] using hk
      simp only [summePasst, hs, hs', if_true, hk, hk', dif_neg, Option.map_none]
  · have hs' : ¬ sumWort (Ty.mapCases sn tn cs) = true := by rw [guard]; exact hs
    simp only [summePasst, hs, hs', if_false, Option.map_none]

/-- A nonzero selected tag and nonzero integer payload exercise the scalar law. -/
theorem summePasst_relocate_zeuge :
    summePasst (D := D') (Ty.mapCases sn tn [none, some (.int 2 9)]) 15 =
      some (Val.relocate sn tn pointer (.sum [none, some (.int 2 9)])
        ⟨⟨1, by decide⟩, ⟨7, by decide, by decide⟩⟩) := by
  rw [summePasst_relocate sn tn pointer]
  rfl

/-- Even selecting an empty case cannot bypass a typed schema's ABI refusal. -/
theorem summePasst_typed_refused_zeuge (n : Int) :
    summePasst (D := D') (Ty.mapCases sn tn [none, some (.fnptr 3)]) n = none := rfl

end Relocation

end Gabbro.Grammatik
