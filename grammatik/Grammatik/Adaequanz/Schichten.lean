/-
  File:      Grammatik/Adaequanz/Schichten.lean
  Subject:   THE TEST SET, CONSTRUCTED: access trees, layers, distinguishing contexts, and its size as a formula.

    * `tupel k L`   every tuple `Fin k → α` over the list `L` (length `|L|^k`, `tupel_laenge`).
    * `schicht d`   layer `d`: layer 0 is the ACCESS trees (one tree per spec state); layer `d + 1` adds every
                    constructor applied to children from layer `d`. Layer 1 is the transition cover: every
                    CELL (constructor x tuple of child states) applied to access trees.
    * `testmenge W d`  every tree of layer `d` placed in every context of `W` (the distinguishing contexts).

  THE FORMULA (`testmenge_laenge`): with `n` access trees and the constructor list `ks`,

      N 0 = n,   N (d + 1) = N d + sum over k in ks of (N d) ^ (ar k),     |testmenge W d| = |W| * N d.

  The sufficiency theorem uses `d = m - n + 1` for implementations with at most `m` states; `m = n` gives
  `|W| * (n + sum_k n ^ ar k)`: the access trees and the cells, each in each distinguishing context. The lists
  may repeat a tree, so the SET is at most this long.
-/
import Grammatik.Adaequanz.Baum

namespace Gabbro.Grammatik.Adaequanz

variable {σ : Sig}

/-! ## Tuples over a list -/

/-- Every tuple `Fin k → α` whose entries come from `L`. -/
def tupel {α : Type} : (k : Nat) → List α → List (Fin k → α)
  | 0, _ => [Fin.elim0]
  | k + 1, L => L.flatMap fun x => (tupel k L).map (Fin.cons x)

theorem tupel_laenge {α : Type} (k : Nat) (L : List α) : (tupel k L).length = L.length ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [tupel, List.length_flatMap, List.length_map, ih]
      rw [List.map_const', List.sum_replicate, smul_eq_mul, Nat.pow_succ, Nat.mul_comm]

theorem mem_tupel {α : Type} {k : Nat} {L : List α} {f : Fin k → α} : f ∈ tupel k L ↔ ∀ i, f i ∈ L := by
  induction k with
  | zero =>
      simp only [tupel, List.mem_singleton]
      exact ⟨fun _ i => i.elim0, fun _ => funext fun i => i.elim0⟩
  | succ k ih =>
      simp only [tupel, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x, hx, g, hg, rfl⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx
        · simpa using (ih.mp hg) j
      · intro h
        refine ⟨f 0, h 0, Fin.tail f, ih.mpr fun j => h j.succ, ?_⟩
        exact Fin.cons_self_tail f

/-! ## Layers and the test set -/

/-- **Layer `d`**: the access trees `a`, then every constructor of `ks` over children of the layer below. -/
def schicht (ks : List σ.K) (a : List (Baum σ)) : Nat → List (Baum σ)
  | 0 => a
  | d + 1 => schicht ks a d ++ ks.flatMap fun k => (tupel (σ.ar k) (schicht ks a d)).map (Baum.knoten k)

/-- **The test set of depth `d`**: every tree of layer `d` in every context of `W`. -/
def testmenge (ks : List σ.K) (a : List (Baum σ)) (W : List (Kontext σ)) (d : Nat) : List (Baum σ) :=
  W.flatMap fun K => (schicht ks a d).map K.ein

/-- The size of layer `d`, as a number: `N 0 = n`, `N (d+1) = N d + Σ_k (N d)^(ar k)`. -/
def anzahl (ks : List σ.K) (n : Nat) : Nat → Nat
  | 0 => n
  | d + 1 => anzahl ks n d + (ks.map fun k => anzahl ks n d ^ σ.ar k).sum

theorem schicht_laenge (ks : List σ.K) (a : List (Baum σ)) (d : Nat) :
    (schicht ks a d).length = anzahl ks a.length d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [schicht, anzahl, List.length_append, List.length_flatMap, List.length_map, tupel_laenge, ih]

/-- **The size formula**: `|testmenge W d| = |W| * N d`. -/
theorem testmenge_laenge (ks : List σ.K) (a : List (Baum σ)) (W : List (Kontext σ)) (d : Nat) :
    (testmenge ks a W d).length = W.length * anzahl ks a.length d := by
  simp only [testmenge, List.length_flatMap, List.length_map, schicht_laenge]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

/-- The spec-states case `m = n` (depth 1): the access trees and every cell, in every context. -/
theorem anzahl_eins (ks : List σ.K) (n : Nat) :
    anzahl ks n 1 = n + (ks.map fun k => n ^ σ.ar k).sum := rfl

/-! ## Membership -/

theorem schicht_mono (ks : List σ.K) (a : List (Baum σ)) {d e : Nat} (h : d ≤ e) {t : Baum σ}
    (ht : t ∈ schicht ks a d) : t ∈ schicht ks a e := by
  induction h with
  | refl => exact ht
  | step _ ih => exact List.mem_append_left _ ih

theorem knoten_mem_schicht (ks : List σ.K) (hks : ∀ k, k ∈ ks) (a : List (Baum σ)) (d : Nat) (k : σ.K)
    (ch : Fin (σ.ar k) → Baum σ) (h : ∀ i, ch i ∈ schicht ks a d) : Baum.knoten k ch ∈ schicht ks a (d + 1) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, hks k, List.mem_map.mpr ⟨ch, mem_tupel.mpr h, rfl⟩⟩)

theorem ein_mem_testmenge (ks : List σ.K) (a : List (Baum σ)) {W : List (Kontext σ)} {d : Nat}
    {K : Kontext σ} (hK : K ∈ W) {t : Baum σ} (ht : t ∈ schicht ks a d) : K.ein t ∈ testmenge ks a W d :=
  List.mem_flatMap.mpr ⟨K, hK, List.mem_map.mpr ⟨t, ht, rfl⟩⟩

end Gabbro.Grammatik.Adaequanz
