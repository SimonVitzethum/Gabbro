/-
  File:      Grammatik/Adaequanz/Minimal.lean
  Subject:   THEOREM 2 (MINIMALITY): lower bounds on every sufficient test set, by one planted implementation
             per CELL that is wrong exactly there.

  A CELL is a constructor with a tuple of child states of the spec (`Zelle`); the cell of a tree is its root
  constructor with its children's spec states (`S.zelle`). Two planted implementations per cell `z`, both
  tree automata (so program-neutral), both equal to the spec except at `z`:

    * `wurzelMutant` (`n + 1` states: one fresh state for "the root is the cell `z`"): wrong EXACTLY on the
      trees whose root cell is `z` (`wurzelMutant_sem`). So every test set sufficient for implementations
      with `m ≥ n + 1` states contains, for EVERY cell, a tree whose ROOT is that cell (`wurzel_noetig`);
      no tree has two root cells, so the set has at least `Σ_k n ^ ar k` trees (`wurzel_schranke`).
    * `flaggenMutant` (`2 n` states: the spec state and one bit "the cell `z` occurs"): wrong EXACTLY on the
      trees that CONTAIN the cell `z` anywhere (`flaggenMutant_sem`). So for `m ≥ 2 n` the test set covers
      every cell (`flagge_noetig`); here one tree may cover many cells, so the bound is the cover number.

  The cell count is the number of transition-cover trees of `testmenge` (layer 1 without layer 0), so for
  `m = n + 1` the constructed set is optimal up to the factor `|W| * N 2 / Σ_k n ^ ar k`; for `m = n` no
  implementation with a fresh state is in the class and these mutants say nothing (stated in CHECKER.md).
-/
import Grammatik.Adaequanz.Hinlaenglich

namespace Gabbro.Grammatik.Adaequanz

set_option linter.unusedSectionVars false

variable {σ : Sig} {Q O : Type}

/-- **A cell**: a constructor with a tuple of child states. -/
abbrev Zelle (σ : Sig) (Q : Type) := Σ k : σ.K, Fin (σ.ar k) → Q

namespace Automat

variable (S : Automat σ Q O)

/-- The cell at the root of a tree: its constructor with its children's states. -/
def zelle : Baum σ → Zelle σ Q
  | .knoten k ch => ⟨k, fun i => S.lauf (ch i)⟩

/-- The state a cell leads to. -/
def zwert (z : Zelle σ Q) : Q := S.δ z.1 z.2

theorem lauf_zelle (t : Baum σ) : S.lauf t = S.zwert (S.zelle t) := by
  cases t; rfl

end Automat

/-- The witness of a cell: the constructor over the access trees of its child states. -/
def zeuge (acc : Q → Baum σ) (z : Zelle σ Q) : Baum σ := .knoten z.1 fun i => acc (z.2 i)

theorem zelle_zeuge {S : Automat σ Q O} {acc : Q → Baum σ} (hacc : ∀ q, S.lauf (acc q) = q) (z : Zelle σ Q) :
    S.zelle (zeuge acc z) = z := by
  obtain ⟨k, q⟩ := z
  simp [Automat.zelle, zeuge, hacc]

/-! ## The root mutant -/

section Wurzel

variable [DecidableEq σ.K] [DecidableEq Q] (S : Automat σ Q O) (z0 : Zelle σ Q) (kipp : O → O)

/-- **The root mutant of `z0`**: the spec, with one fresh state `none` for a node whose cell is `z0`; the
    fresh state behaves like the state of `z0` everywhere except in the output, which `kipp` changes. -/
def wurzelMutant : Automat σ (Option Q) O where
  δ k p := if (⟨k, fun i => (p i).getD (S.zwert z0)⟩ : Zelle σ Q) = z0 then none
    else some (S.δ k fun i => (p i).getD (S.zwert z0))
  aus o := match o with
    | none => kipp (S.aus (S.zwert z0))
    | some q => S.aus q

theorem wurzelMutant_δ (k : σ.K) (p : Fin (σ.ar k) → Option Q) :
    (wurzelMutant S z0 kipp).δ k p = if (⟨k, fun i => (p i).getD (S.zwert z0)⟩ : Zelle σ Q) = z0 then none
      else some (S.δ k fun i => (p i).getD (S.zwert z0)) := rfl

theorem wurzelMutant_aus_none : (wurzelMutant S z0 kipp).aus none = kipp (S.aus (S.zwert z0)) := rfl

theorem wurzelMutant_aus_some (q : Q) : (wurzelMutant S z0 kipp).aus (some q) = S.aus q := rfl

theorem wurzelMutant_wert (t : Baum σ) : ((wurzelMutant S z0 kipp).lauf t).getD (S.zwert z0) = S.lauf t := by
  induction t with
  | knoten k ch ih =>
      have hw : (fun i => ((wurzelMutant S z0 kipp).lauf (ch i)).getD (S.zwert z0)) = fun i => S.lauf (ch i) :=
        funext ih
      rw [Automat.lauf_knoten (wurzelMutant S z0 kipp), wurzelMutant_δ, hw, Automat.lauf_knoten S]
      by_cases h : (⟨k, fun i => S.lauf (ch i)⟩ : Zelle σ Q) = z0
      · rw [if_pos h, Option.getD_none, ← h]; rfl
      · rw [if_neg h]; rfl

/-- **The root mutant is wrong exactly on the trees whose root cell is `z0`.** -/
theorem wurzelMutant_sem (t : Baum σ) :
    (wurzelMutant S z0 kipp).sem t = if S.zelle t = z0 then kipp (S.sem t) else S.sem t := by
  cases t with
  | knoten k ch =>
      have hw : (fun i => ((wurzelMutant S z0 kipp).lauf (ch i)).getD (S.zwert z0)) = fun i => S.lauf (ch i) :=
        funext fun i => wurzelMutant_wert S z0 kipp (ch i)
      have hz : S.zelle (Baum.knoten k ch) = ⟨k, fun i => S.lauf (ch i)⟩ := rfl
      rw [hz]
      unfold Automat.sem
      rw [Automat.lauf_knoten (wurzelMutant S z0 kipp), wurzelMutant_δ, hw]
      by_cases h : (⟨k, fun i => S.lauf (ch i)⟩ : Zelle σ Q) = z0
      · rw [if_pos h, if_pos h, wurzelMutant_aus_none, S.lauf_zelle (Baum.knoten k ch), hz, h]
      · rw [if_neg h, if_neg h, wurzelMutant_aus_some, Automat.lauf_knoten S]

/-- The root mutant passes every test set without a tree rooted at `z0`. -/
theorem wurzelMutant_besteht (M : List (Baum σ)) (h : ∀ p ∈ M, S.zelle p ≠ z0) :
    ∀ p ∈ M, (wurzelMutant S z0 kipp).sem p = S.sem p := fun p hp => by
  rw [wurzelMutant_sem, if_neg (h p hp)]

theorem wurzelMutant_falsch {acc : Q → Baum σ} (hacc : ∀ q, S.lauf (acc q) = q) (hkipp : ∀ o, kipp o ≠ o) :
    (wurzelMutant S z0 kipp).sem (zeuge acc z0) ≠ S.sem (zeuge acc z0) := by
  rw [wurzelMutant_sem, if_pos (zelle_zeuge hacc z0)]
  exact hkipp _

end Wurzel

/-- A test set is SUFFICIENT for the implementations with at most `m` states. -/
def Hinreichend (S : Automat σ Q O) (M : List (Baum σ)) (m : Nat) : Prop :=
  ∀ (Q' : Type) [Fintype Q'] (I : Automat σ Q' O), Fintype.card Q' ≤ m →
    (∀ p ∈ M, I.sem p = S.sem p) → ∀ t, I.sem t = S.sem t

section Schranke

variable [DecidableEq σ.K] [DecidableEq Q] [Fintype Q] {S : Automat σ Q O} {acc : Q → Baum σ}
  (hacc : ∀ q, S.lauf (acc q) = q) {kipp : O → O} (hkipp : ∀ o, kipp o ≠ o)

include hacc hkipp

/-- **Every cell must be the ROOT of a test** (implementations with `m ≥ n + 1` states). -/
theorem wurzel_noetig {M : List (Baum σ)} {m : Nat} (hm : Fintype.card Q + 1 ≤ m) (hM : Hinreichend S M m)
    (z : Zelle σ Q) : ∃ p ∈ M, S.zelle p = z := by
  by_contra h
  push Not at h
  have hc : Fintype.card (Option Q) ≤ m := by rw [Fintype.card_option]; exact hm
  exact wurzelMutant_falsch S z kipp hacc hkipp
    (hM (Option Q) (wurzelMutant S z kipp) hc (wurzelMutant_besteht S z kipp M h) _)

/-- **THEOREM 2a (lower bound, `m ≥ n + 1`)**: a sufficient test set has at least `Σ_k n ^ ar k` trees, the
    number of cells. -/
theorem wurzel_schranke [Fintype σ.K] {M : List (Baum σ)} {m : Nat} (hm : Fintype.card Q + 1 ≤ m)
    (hM : Hinreichend S M m) : ∑ k : σ.K, Fintype.card Q ^ σ.ar k ≤ M.length := by
  classical
  choose f hf hfz using wurzel_noetig hacc hkipp hm hM
  have hinj : Function.Injective f := fun z z' h => by rw [← hfz z, ← hfz z', h]
  have hcard : Fintype.card (Zelle σ Q) = ∑ k : σ.K, Fintype.card Q ^ σ.ar k := by
    simp [Zelle, Fintype.card_sigma]
  rw [← hcard]
  calc Fintype.card (Zelle σ Q) = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ M.toFinset.card := Finset.card_le_card fun p hp => by
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
        exact List.mem_toFinset.mpr (hf z)
    _ ≤ M.length := List.toFinset_card_le M

end Schranke

/-! ## The flag mutant -/

/-- The tree CONTAINS the cell `z0`: at its root or below. -/
inductive Enthaelt (S : Automat σ Q O) (z0 : Zelle σ Q) : Baum σ → Prop
  | hier {k : σ.K} {ch : Fin (σ.ar k) → Baum σ} :
      (⟨k, fun i => S.lauf (ch i)⟩ : Zelle σ Q) = z0 → Enthaelt S z0 (.knoten k ch)
  | unten {k : σ.K} {ch : Fin (σ.ar k) → Baum σ} (i : Fin (σ.ar k)) :
      Enthaelt S z0 (ch i) → Enthaelt S z0 (.knoten k ch)

section Flagge

variable [DecidableEq σ.K] [DecidableEq Q] (S : Automat σ Q O) (z0 : Zelle σ Q) (kipp : O → O)

/-- **The flag mutant of `z0`**: the spec state and one bit, set when the cell `z0` occurs; a set bit
    changes the output by `kipp`. -/
def flaggenMutant : Automat σ (Q × Bool) O where
  δ k p := (S.δ k fun i => (p i).1,
    decide ((⟨k, fun i => (p i).1⟩ : Zelle σ Q) = z0) || (List.finRange (σ.ar k)).any fun i => (p i).2)
  aus x := if x.2 then kipp (S.aus x.1) else S.aus x.1

theorem flaggenMutant_δ (k : σ.K) (p : Fin (σ.ar k) → Q × Bool) :
    (flaggenMutant S z0 kipp).δ k p = (S.δ k fun i => (p i).1,
      decide ((⟨k, fun i => (p i).1⟩ : Zelle σ Q) = z0) || (List.finRange (σ.ar k)).any fun i => (p i).2) := rfl

theorem flaggenMutant_aus (x : Q × Bool) :
    (flaggenMutant S z0 kipp).aus x = if x.2 = true then kipp (S.aus x.1) else S.aus x.1 := rfl

theorem flaggenMutant_fst (t : Baum σ) : ((flaggenMutant S z0 kipp).lauf t).1 = S.lauf t := by
  induction t with
  | knoten k ch ih =>
      rw [Automat.lauf_knoten (flaggenMutant S z0 kipp), flaggenMutant_δ, Automat.lauf_knoten S]
      show (S.δ k fun i => ((flaggenMutant S z0 kipp).lauf (ch i)).1) = _
      rw [funext ih]

theorem flaggenMutant_snd (t : Baum σ) : ((flaggenMutant S z0 kipp).lauf t).2 = true ↔ Enthaelt S z0 t := by
  induction t with
  | knoten k ch ih =>
      have h1 : (fun i => ((flaggenMutant S z0 kipp).lauf (ch i)).1) = fun i => S.lauf (ch i) :=
        funext fun i => flaggenMutant_fst S z0 kipp (ch i)
      rw [Automat.lauf_knoten (flaggenMutant S z0 kipp), flaggenMutant_δ]
      show (decide ((⟨k, fun i => ((flaggenMutant S z0 kipp).lauf (ch i)).1⟩ : Zelle σ Q) = z0) ||
        (List.finRange (σ.ar k)).any fun i => ((flaggenMutant S z0 kipp).lauf (ch i)).2) = true ↔ _
      rw [h1]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_finRange, true_and]
      constructor
      · rintro (h | ⟨i, hi⟩)
        · exact Enthaelt.hier h
        · exact Enthaelt.unten i ((ih i).mp hi)
      · intro h
        cases h with
        | hier h => exact Or.inl h
        | unten i h => exact Or.inr ⟨i, (ih i).mpr h⟩

/-- **The flag mutant is wrong exactly on the trees that contain `z0`.** -/
theorem flaggenMutant_sem (t : Baum σ) [Decidable (Enthaelt S z0 t)] :
    (flaggenMutant S z0 kipp).sem t = if Enthaelt S z0 t then kipp (S.sem t) else S.sem t := by
  have h1 := flaggenMutant_fst S z0 kipp t
  have h2 := flaggenMutant_snd S z0 kipp t
  unfold Automat.sem
  rw [flaggenMutant_aus]
  by_cases h : Enthaelt S z0 t
  · rw [if_pos (h2.mpr h), if_pos h, h1]
  · have hb : ¬ ((flaggenMutant S z0 kipp).lauf t).2 = true := fun hb => h (h2.mp hb)
    rw [if_neg hb, if_neg h, h1]

end Flagge

section FlaggeSchranke

variable [DecidableEq σ.K] [DecidableEq Q] [Fintype Q] {S : Automat σ Q O} {acc : Q → Baum σ}
  (hacc : ∀ q, S.lauf (acc q) = q) {kipp : O → O} (hkipp : ∀ o, kipp o ≠ o)

include hacc hkipp

/-- **THEOREM 2b (cover, `m ≥ 2 n`)**: a sufficient test set contains every cell somewhere. -/
theorem flagge_noetig {M : List (Baum σ)} {m : Nat} (hm : 2 * Fintype.card Q ≤ m) (hM : Hinreichend S M m)
    (z : Zelle σ Q) : ∃ p ∈ M, Enthaelt S z p := by
  classical
  by_contra h
  push Not at h
  have hc : Fintype.card (Q × Bool) ≤ m := by
    rw [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]; exact hm
  have hpass : ∀ p ∈ M, (flaggenMutant S z kipp).sem p = S.sem p := fun p hp => by
    rw [flaggenMutant_sem, if_neg (h p hp)]
  have hall := hM (Q × Bool) (flaggenMutant S z kipp) hc hpass (zeuge acc z)
  have he : Enthaelt S z (zeuge acc z) := Enthaelt.hier (by
    have := zelle_zeuge hacc z
    simpa [Automat.zelle, zeuge] using this)
  rw [flaggenMutant_sem, if_pos he] at hall
  exact hkipp _ hall

end FlaggeSchranke

end Gabbro.Grammatik.Adaequanz
