module
public import Bruecke.Kodierung.Glob
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The first-match static lookup returns a declaration bearing the requested name. -/
theorem globIdx_name : ∀ (gs : List UGlob) (n : String) (g : Fin gs.length),
    globIdx gs n = .ok g → (gs.get g).name = n
  | [], _, _, h => by cases h
  | x :: rest, n, g, h => by
      simp only [globIdx] at h
      split at h
      · rename_i hx
        cases h
        exact beq_iff_eq.mp hx
      · split at h
        · cases h
        · rename_i j hj
          cases h
          exact globIdx_name rest n j hj

variable (u : UProg)

/-- A checked static store updates the static relation and preserves every slot. -/
theorem wgrel_storeGlob {σ : World (declOf u)} {w : Gabbro.Body.World}
    (h : WGRel u σ w) (n : String) (i : Fin u.globs.length)
    (hi : globIdx u.globs n = .ok i) (x : Wert (declOf u) ((declOf u).gtyp i)) :
    WGRel u (σ.storeGlob i x)
      (Gabbro.Body.store w (.global n) (valOf ((declOf u).gtyp i) x)) := by
  constructor
  · intro c k fld v hv
    have hs := wrel_slots u (σ' := σ.storeGlob i x) rfl h.1 c k fld v hv
    exact (Gabbro.Body.store_elsewhere _ _ _ _ (by intro e; cases e)).trans hs
  · intro n' v hv
    unfold globWert at hv
    split at hv
    · cases hv
    · rename_i j hj
      cases ht : (globAt u j).ty with
      | int lo hi' =>
        simp only [ht, Option.some.injEq] at hv
        subst v
        by_cases hn : n' = n
        · subst n'
          rw [hi] at hj
          cases hj
          rw [Gabbro.Body.store_here]
          exact congrArg (valOf _) (storeGlob_hit σ i x).symm
        · have hp : Gabbro.Body.Place.global n' ≠ .global n := by
            intro he
            cases he
            exact hn rfl
          rw [Gabbro.Body.store_elsewhere _ _ _ _ hp]
          have hji : j ≠ i := by
            intro he
            subst j
            exact hn ((globIdx_name u.globs n' i hj).symm.trans
              (globIdx_name u.globs n i hi))
          rw [storeGlob_andere σ i x j hji]
          apply h.2
          simp only [globWert, hj, ht]
      | bool => simp only [ht, reduceCtorEq] at hv
      | wert ty => simp only [ht, reduceCtorEq] at hv

end Gabbro.Bruecke
