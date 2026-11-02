module

public import Grammatik.Bausteine.Walk.Abbildung
public import Grammatik.Bausteine.Walk.Position

@[expose] public section

/-
  File:       Grammatik/Bausteine/Walk/CorrectnessEnum.lean
  Subject:    C01, the mapping enumeration whole-proof: the pure enumeration (`Abbildung.lean`)
              is exact -- every emitted visit is a `WalkHit` pair and every `WalkHit` pair is
              emitted, with no duplicate paths and `(level, index)` injectivity -- witnessed on
              a non-degenerate two-level mapping. The generated run follows this enumeration
              under `WalkRunOk`; that half lives in `Correctness.lean`.
-/

namespace Gabbro.Grammatik

/-! ## 1. The active index suffix determines the path -/

/-- Two paths of at most `levels` entries with the same level and the same `index` array are equal:
    the level gives the length, and `walkIndexAt_path` recovers every entry from the active suffix. -/
theorem walkIndex_inj {N : Nat} (levels : Nat) (p q : List (Fin N))
    (hp : p.length ≤ levels) (hq : q.length ≤ levels)
    (hlevel : levels - p.length = levels - q.length)
    (hindex : ∀ ell, walkIndexAt levels p ell = walkIndexAt levels q ell) :
    p = q := by
  have hlen : p.length = q.length := by omega
  apply List.ext_getElem?
  intro n
  by_cases hn : n < p.length
  · have hnq : n < q.length := hlen ▸ hn
    have e1 := walkIndexAt_path levels p n hp hn
    have e2 := walkIndexAt_path levels q n (hlen ▸ hp) (hlen ▸ hn)
    have h := hindex (levels - 1 - n)
    rw [e1, e2] at h
    have g1 : ((p[n]?).map Fin.val).getD 0 = (p[n]'hn).val := by
      rw [List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
    have g2 : ((q[n]?).map Fin.val).getD 0 = (q[n]'hnq).val := by
      rw [List.getElem?_eq_getElem hnq, Option.map_some, Option.getD_some]
    rw [g1, g2] at h
    have hfin : p[n]'hn = q[n]'hnq := Fin.ext h
    have r1 : p[n]? = some (p[n]'hn) := List.getElem?_eq_getElem hn
    have r2 : q[n]? = some (q[n]'hnq) := List.getElem?_eq_getElem hnq
    rw [r1, r2, hfin]
  · have hnq : ¬ n < q.length := by omega
    have r1 : p[n]? = none := List.getElem?_eq_none (by omega)
    have r2 : q[n]? = none := List.getElem?_eq_none (by omega)
    rw [r1, r2]

/-! ## 2. The enumeration whole-proof, by induction over the mapping levels -/

/-- A walk hit determines its entry: the same path never yields two entries. -/
theorem walkHit_det {α : Type} {N : Nat} {T : WalkTree α N} {l : Nat} {tbl : Fin N → α}
    {p : List (Fin N)} {m : α} (h : WalkHit T l tbl p m) :
    ∀ {n : α}, WalkHit T l tbl p n → m = n := by
  induction h with
  | leaf hl =>
      intro n hn
      cases hn with
      | leaf _ => rfl
      | down hl' _ _ _ => exact absurd hl' (by rw [hl]; simp)
  | down hl hd hdn h ih =>
      intro n hn
      cases hn with
      | leaf hl' => exact absurd hl (by rw [hl']; simp)
      | down hl₂ hd₂ hdn₂ h' => have heq := hdn.symm.trans hdn₂; cases heq; exact ih h'

/-- **The mapping whole-proof**: emitted visits equal all reachable qualifying path/entry pairs --
    sound (`WalkHit` for every emitted pair), complete (every `WalkHit` pair is emitted), no duplicate
    paths, and `(level, index)` injectivity (the active suffix determines the path, so distinct mappings
    never share their coordinates). Proved by induction over the mapping levels. -/
theorem walkMappings_correct {α : Type} {N : Nat} (T : WalkTree α N) (levels : Nat) :
    ∀ (l : Nat) (tbl : Fin N → α),
      (∀ (p : List (Fin N)) (m : α), (p, m) ∈ visitT T l tbl ↔ WalkHit T l tbl p m) ∧
      (visitT T l tbl).Pairwise (fun x y => x.1 ≠ y.1) ∧
      (∀ (p q : List (Fin N)) (m n : α),
        (p, m) ∈ visitT T l tbl → (q, n) ∈ visitT T l tbl →
        p.length ≤ levels → q.length ≤ levels →
        levels - p.length = levels - q.length →
        (∀ ell, walkIndexAt levels p ell = walkIndexAt levels q ell) → p = q ∧ m = n)
  | 0, tbl =>
      ⟨visitT_mem_iff T 0 tbl, visitT_pfade T 0 tbl, fun p q m n hp hq hpl hql hlevel hindex => by
        have hpq := walkIndex_inj levels p q hpl hql hlevel hindex
        subst hpq
        exact ⟨rfl, walkHit_det ((visitT_mem_iff T 0 tbl p m).mp hp)
          ((visitT_mem_iff T 0 tbl p n).mp hq)⟩⟩
  | l + 1, tbl =>
      ⟨visitT_mem_iff T (l + 1) tbl, visitT_pfade T (l + 1) tbl,
        fun p q m n hp hq hpl hql hlevel hindex => by
        have hpq := walkIndex_inj levels p q hpl hql hlevel hindex
        subst hpq
        exact ⟨rfl, walkHit_det ((visitT_mem_iff T (l + 1) tbl p m).mp hp)
          ((visitT_mem_iff T (l + 1) tbl p n).mp hq)⟩⟩

/-- Witnesses of the mapping whole-proof on a non-degenerate two-level mapping: a root with one
    leaf entry and one descendable entry whose two child entries are leaves. -/
def zeugeWalkKind : Fin 2 → Nat
  | ⟨0, _⟩ => 20
  | ⟨1, _⟩ => 21

def zeugeWalkTbl : Fin 2 → Nat
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 11

def zeugeWalkT : WalkTree Nat 2 where
  leaf := fun e => e == 10 || e == 20 || e == 21
  dwhen := fun e => e == 11
  down := fun e => if e == 11 then some zeugeWalkKind else none

theorem zeugeWalkT_down : zeugeWalkT.down 11 = some zeugeWalkKind := rfl

/-- The generic whole-proof on the two-level fixture: soundness, completeness, no duplicate paths,
    and the exact enumeration `[[0], 10), ([1, 0], 20), ([1, 1], 21)]`. -/
theorem walkMappings_correct_zeuge :
    (∀ (p : List (Fin 2)) (m : Nat),
      (p, m) ∈ visitT zeugeWalkT 1 zeugeWalkTbl ↔ WalkHit zeugeWalkT 1 zeugeWalkTbl p m) ∧
    (visitT zeugeWalkT 1 zeugeWalkTbl).Pairwise (fun x y => x.1 ≠ y.1) ∧
    (visitT zeugeWalkT 1 zeugeWalkTbl = [([0], 10), ([1, 0], 20), ([1, 1], 21)]) := by
  obtain ⟨hmem, hnodup, _⟩ := walkMappings_correct zeugeWalkT 2 1 zeugeWalkTbl
  exact ⟨hmem, hnodup, by decide⟩

end Gabbro.Grammatik
