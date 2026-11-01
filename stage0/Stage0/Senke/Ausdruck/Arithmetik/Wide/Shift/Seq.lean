/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Seq.lean
  Subject:   Per-limb pieces in a chosen order: the generic effect of a sequence of in-place updates.

  A multiword shift, a limb selection or a conditional negation updates every limb of an operand in
  place from the limb itself, one neighbouring limb and a few persistent slots. `seqC P l` runs the
  piece `P j` for every `j` of `l`, in that order. When no piece reads a limb that an earlier piece of
  the sequence wrote, every limb ends with its own piece formula applied to the ORIGINAL valuation;
  this is the one argument behind descending (shift left) and ascending (shift right) chains.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Bits
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

@[simp] theorem seqC_nil (P : Nat → List II) : seqC P [] = [] := rfl
@[simp] theorem seqC_cons (P : Nat → List II) (j : Nat) (l : List Nat) :
    seqC P (j :: l) = P j ++ seqC P l := rfl

theorem seqC_length (P : Nat → List II) (n : Nat) (hP : ∀ j, (P j).length = n) :
    ∀ l : List Nat, (seqC P l).length = n * l.length
  | [] => by simp
  | j :: l => by simp only [seqC_cons, List.length_append, hP, seqC_length P n hP l, List.length_cons, Nat.mul_succ, Nat.add_comm]

theorem seqC_aluIns {K d : Nat} (P : Nat → List II) (l : List Nat)
    (hP : ∀ j ∈ l, ∀ i ∈ P j, AluIns K d i) : ∀ i ∈ seqC P l, AluIns K d i := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons j l ih =>
    intro i hi
    simp only [seqC_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hP j (List.mem_cons_self ..) i hi
    · exact ih (fun j hj => hP j (List.mem_cons_of_mem _ hj)) i hi

/-- The effect of a sequence of in-place limb pieces.

    `P j` writes the limb slot `a + j` and temporaries (`isT`) only and computes `F j`; `F j` reads
    the slots `R j` only. If no piece of the sequence reads a limb written before it, every limb of
    the sequence receives `F j` of the original valuation and everything else but temporaries is kept.
    The hypotheses are needed for the members of the sequence only (`ok`). -/
theorem seqC_value (P : Nat → List II) (F : Nat → (Nat → Runner.W) → Runner.W) (R : Nat → Nat → Prop)
    (isT ok : Nat → Prop) (a : Nat)
    (hP : ∀ j, ok j → ∀ s, aluRun (P j) s (a + j) = F j s)
    (hoth : ∀ j, ok j → ∀ s i, i ≠ a + j → ¬ isT i → aluRun (P j) s i = s i)
    (hR : ∀ j, ok j → ∀ s s', (∀ i, R j i → s i = s' i) → F j s = F j s')
    (hRT : ∀ j, ok j → ∀ i, R j i → ¬ isT i)
    (hT : ∀ j, ok j → ¬ isT (a + j)) :
    ∀ (l : List Nat), (∀ j ∈ l, ok j) → l.Nodup → l.Pairwise (fun j' j => ¬ R j (a + j')) → ∀ s,
      (∀ j ∈ l, aluRun (seqC P l) s (a + j) = F j s) ∧
      (∀ i, ¬ isT i → (∀ j ∈ l, i ≠ a + j) → aluRun (seqC P l) s i = s i)
  | [], _, _, _, s => ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl⟩
  | j :: l, hok, hnd, hpw, s => by
    obtain ⟨hjl, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hpj, hpw'⟩ := List.pairwise_cons.mp hpw
    have hokj : ok j := hok j (List.mem_cons_self ..)
    have run : aluRun (seqC P (j :: l)) s = aluRun (seqC P l) (aluRun (P j) s) := by
      simp only [seqC_cons, aluRun_append]
    obtain ⟨ih1, ih2⟩ := seqC_value P F R isT ok a hP hoth hR hRT hT l
      (fun j' hj' => hok j' (List.mem_cons_of_mem _ hj')) hnd' hpw' (aluRun (P j) s)
    refine ⟨fun j' hj' => ?_, fun i hiT hne => ?_⟩
    · rw [run]
      rcases List.mem_cons.mp hj' with rfl | hj'
      · rw [ih2 (a + j') (hT j' hokj) (fun j'' hj'' h => hjl (by
          have : j' = j'' := by omega
          exact this ▸ hj'')), hP j' hokj]
      · rw [ih1 j' hj']
        apply hR j' (hok j' (List.mem_cons_of_mem _ hj'))
        intro i hi
        exact hoth j hokj s i (fun h => hpj j' hj' (h ▸ hi)) (hRT j' (hok j' (List.mem_cons_of_mem _ hj')) i hi)
    · rw [run, ih2 i hiT (fun j'' hj'' => hne j'' (List.mem_cons_of_mem _ hj''))]
      exact hoth j hokj s i (hne j (List.mem_cons_self ..)) hiT

end Gabbro.Stage0.Senke
