/-
  Audit 46, probe F5: `hlock_prog`/`hforeign` make lock-only the only case (e).

  Claim (pattern e, filed as medium severity): `kette_zwei_aus_lauf`
  (KetteMehrfadenC.lean:766-869) concludes the two-thread joint run only under
  `hlock_prog` (every pointed-to atom is `take`/`rel`, never `leaf`) and
  `hforeign` (every other thread has empty program text). Read through the
  `PCAtom` definition (`Maschine.lean:1268-1272`: `leaf` carries the statement
  footprint, `take`/`rel` carry only the lock): a `take`/`rel` atom touches no
  carrier (`PCAtom.carriers` is `[]` there) and names no marks. So the covered
  class is programs whose threads perform only lock operations -- no writes,
  no reads, no calls, no marks. Any ordinary program (a thread that writes a
  slot, fires a leaf, or runs a third thread with nonempty text) fails the
  premise outright: the leaf routing dies by `cases hL'` (lines 826-827) and
  the foreign routing by `simp at hpc` against `prog g0 = []` (lines 861-866).

  Demonstrated below from the DEFINITIONS: lock atoms touch no carrier, so a
  `hlock_prog`-shaped program text is carrier-free; and a one-`leaf` text
  cannot satisfy the lock-only predicate. Both use every binder.
-/
import Grammatik.Maschine

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Lock atoms are carrier-free by definition: the routing that needs an atom
    can never reach a carrier through `take`/`rel`. -/
theorem audit46_lock_atoms_touch_nothing
    (L : D.Lock) :
    PCAtom.carriers (D := D) (PCAtom.take L) = [] ∧
      PCAtom.carriers (D := D) (PCAtom.rel L) = [] :=
  ⟨rfl, rfl⟩

/-- A program text containing a `leaf` atom is NOT lock-only: the universal
    lock-shape predicate fails at that position. So any writing/reading
    thread falls outside `kette_zwei_aus_lauf`. -/
theorem audit46_leaf_breaks_lock_only
    (atoms : List (PCAtom D)) (k : Nat)
    (Λ : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hk : atoms[k]? = some (PCAtom.leaf Λ cs)) :
    ¬ ∀ (n : Nat) (a : PCAtom D), atoms[n]? = some a →
      ((∃ L : D.Lock, a = PCAtom.take L) ∨ (∃ L : D.Lock, a = PCAtom.rel L)) := by
  intro hall
  obtain ⟨L, hL⟩ | ⟨L, hL⟩ := hall k (PCAtom.leaf Λ cs) hk
  · cases hL
  · cases hL

/-
CUTS:
- The two lemmas pin the DEFINITIONAL sides (carrier-free lock atoms; leaf
  breaks lock-only). That `kette_zwei_aus_lauf` routes exactly these ways is
  proof-term reading (leaf case `cases hL'`, foreign case `simp at hpc`),
  cited, not re-proved: re-proving the whole induction would duplicate the file.
- No claim that lock-only programs are uninteresting: the file header discloses
  the scope ("covers LOCK-ONLY programs", line 15). The finding is SATZKARTE
  fit: `hJw`/`hJsf` for ordinary (writing) programs stay owed, as §3-flag-5 says.
-/
#print axioms Gabbro.Grammatik.audit46_lock_atoms_touch_nothing
#print axioms Gabbro.Grammatik.audit46_leaf_breaks_lock_only
