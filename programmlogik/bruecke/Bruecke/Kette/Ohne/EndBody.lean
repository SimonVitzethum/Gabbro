module
public import Bruecke.Kette.Ohne.Blatt
@[expose] public section

/-!
# An ending block read by `endBodyZ` lowers without `locks`

The error body of a `narrow` is read by `endBodyZ`; along the same view as `endBodyZ_sim`, its
lowered ending contains no `locks` block and no scoped return.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem endBodyZ_ohne {loopMode : Bool} (hT : TabEindeutig u) (c : Fin u.fns.length) :
    ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (rest : List UStmt) (bs : List Gabbro.Body.Stmt),
      Sicht u ft fn →
      lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
      endBodyZ u k ft ns ss = some (bs, rest) → ending.ohneLocks = true
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, bs, hV, hG, hB => by
    cases endBodyZ_view hB with
    | @ret r ss b hr =>
      rw [lowEndL_succ] at hG
      simp only [lowEndStep] at hG
      cases hg : lowRetEnd (l := loopMode) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hG; cases hG
      | ok e =>
        simp only [hg, Except.map] at hG
        cases hG
        exact lowRetEnd_ohne hg
    | control leave x ss =>
      obtain ⟨hl, hE, -⟩ := lowEnd_control_ok hG
      rw [hE]
      exact controlEnd_ohne leave hl
    | @leaf st ss b ys tail hleaf hs hys =>
      obtain ⟨Λ', gs, nextB, hgs, hnext, rfl⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      simp only [Endblock.ohneLocks, Bool.and_eq_true]
      exact ⟨lowStmtL_einzeln_ohne hT (endLeafB_ok hleaf) hgs,
        endBodyZ_ohne hT c n k ss fn ft ns nextB rest ys hV hnext hys⟩
    | @binding st ss b ft' ns' ys tail hl hs hys =>
      cases st
      case bind x d v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bind hs
        obtain ⟨ls, nextB, hv, hnext, rfl⟩ := lowEnd_bind_ok hG
        simp only [Endblock.ohneLocks]
        exact endBodyZ_ohne hT c n k ss (fn.mitBindung x ls.range) (ft.mitBindung x (0, 0)) (ns.push x)
          nextB rest ys (hV.bind x (0, 0) ls.range) hnext hys
      case bindMut x lo hi v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bindMut hs
        obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindMut_ok hG
        simp only [Endblock.ohneLocks]
        exact endBodyZ_ohne hT c n k ss (fn.mitBindung x (lo, hi)) (ft.mitBindung x (lo, hi)) (ns.push x)
          nextB rest ys (hV.bind x (lo, hi) (lo, hi)) hnext hys
      case bindB x v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bindB hs
        obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindB_ok hG
        simp only [Endblock.ohneLocks]
        exact endBodyZ_ohne hT c n k ss (fn.mitBindungB x) (ft.mitBindungB x) (ns.push x)
          nextB rest ys (hV.bindB x) hnext hys
      all_goals cases hl
    | @record x d v ss id fs e ys tail ht he hys =>
      obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindRecord_ok
        ((recordBinderType_sicht hV d v).symm.trans ht) hG
      simp only [Endblock.ohneLocks]
      exact endBodyZ_ohne hT c n k ss (fn.mitWert x (.prod id fs)) (ft.mitWert x (.prod id fs)) (ns.push x)
        nextB rest ys (hV.bindRecord x id fs) hnext hys

end Gabbro.Bruecke
