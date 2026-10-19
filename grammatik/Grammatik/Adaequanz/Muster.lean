/-
  File:      Grammatik/Adaequanz/Muster.lean
  Subject:   THEOREM 4 (CONJUNCTIVE CHECKERS: THE EXACT ANSWER). The checker's verdict is a CONJUNCTION over the
             cells a program contains: a local typing rule at a node, or a whole-program pattern (a tuple of
             functions, carriers and locks with their call-graph relations, as the ten components of `AkzeptiertX`
             are). An implementation is a table `φ : Z → Bool` of the cells it admits, and it accepts `p` iff it
             admits every cell of `p` (`akzeptiert`). This is the class of TODO Phase C item 8: "its correctness
             statement splits per constructor" and "the whole-program conditions are explicit patterns".

  A refused program has a BAD cell (`φ_S z = false`); two bad cells in one program MASK each other: an
  implementation that wrongly admits one of them still refuses the program. Hence:

    * `muster_hinlaenglich`: if every cell `z` has a CANONICAL program `A z` whose cells occur in every
      program that contains `z` (the program class is closed under isolating a cell), the canonical programs
      form a sufficient test set.
    * `schlecht_noetig`: a bad cell that is the ONLY bad cell of some program must be the only bad cell of a
      test; two such cells never share a test (`schlecht_getrennt`).
    * `gut_noetig`: a good cell that occurs in an accepted program must occur in an ACCEPTED test.
    * `muster_schranke`: so every sufficient set has at least (number of isolable bad cells) + 1 programs when
      some valid program exists; the canonical set has (number of realizable cells). Single-fault refusals are
      exactly the tests the bad cells need, and valid programs may share all good cells.
-/
import Grammatik.Adaequanz.Ueberdeckung

namespace Gabbro.Grammatik.Adaequanz

variable {P Z : Type} (T : P → Z → Prop)

/-- The verdict of the table `φ`: every cell of `p` is admitted. -/
def akzeptiert (φ : Z → Bool) (p : P) : Prop := ∀ z, T p z → φ z = true

/-- A test set is sufficient for the conjunctive checkers. -/
def MusterHinreichend (φS : Z → Bool) (M : List P) : Prop :=
  ∀ φ : Z → Bool, (∀ p ∈ M, akzeptiert T φ p ↔ akzeptiert T φS p) → ∀ p, akzeptiert T φ p ↔ akzeptiert T φS p

/-- **Theorem 4a (sufficiency of the canonical programs).** -/
theorem muster_hinlaenglich (φS : Z → Bool) (A : Z → P) (hA : ∀ z, T (A z) z)
    (hzu : ∀ p z, T p z → ∀ z', T (A z) z' → T p z') (M : List P) (hM : ∀ z, (∃ p, T p z) → A z ∈ M) :
    MusterHinreichend T φS M := by
  intro φ hpass p
  have hgleich : ∀ z, (∃ p, T p z) → (akzeptiert T φ (A z) ↔ akzeptiert T φS (A z)) :=
    fun z hz => hpass _ (hM z hz)
  constructor
  · intro hI
    by_contra hS
    simp only [akzeptiert, not_forall] at hS
    obtain ⟨z, hz, hzf⟩ := hS
    -- the canonical program of `z` has I-admitted cells only, and `z` is S-bad there
    have hIA : akzeptiert T φ (A z) := fun z' hz' => hI z' (hzu p z hz z' hz')
    have := (hgleich z ⟨p, hz⟩).mp hIA z (hA z)
    exact hzf this
  · intro hS
    by_contra hI
    simp only [akzeptiert, not_forall] at hI
    obtain ⟨z, hz, hzf⟩ := hI
    have hSA : akzeptiert T φS (A z) := fun z' hz' => hS z' (hzu p z hz z' hz')
    have := (hgleich z ⟨p, hz⟩).mpr hSA z (hA z)
    exact hzf this

/-- `z` is the only bad cell of `p`. -/
def NurSchlecht (φS : Z → Bool) (p : P) (z : Z) : Prop :=
  T p z ∧ φS z = false ∧ ∀ z', T p z' → z' ≠ z → φS z' = true

open Classical in
/-- The table `φS` with one cell changed. -/
noncomputable def umschalten (φS : Z → Bool) (z0 : Z) (b : Bool) : Z → Bool :=
  fun z => if z = z0 then b else φS z

/-- **Theorem 4b (a bad cell needs its own single-fault test).** -/
theorem schlecht_noetig {φS : Z → Bool} {M : List P} (hM : MusterHinreichend T φS M) {z : Z} {p0 : P}
    (h0 : NurSchlecht T φS p0 z) : ∃ p ∈ M, NurSchlecht T φS p z := by
  classical
  by_contra hne
  push Not at hne
  -- the table that admits `z`
  have hpass : ∀ p ∈ M, akzeptiert T (umschalten φS z true) p ↔ akzeptiert T φS p := by
    intro p hp
    by_cases hzp : T p z
    · -- `z` is not the only bad cell of `p`: some other bad cell refuses `p` under both tables
      have hn := hne p hp
      have hother : ∃ z', T p z' ∧ z' ≠ z ∧ φS z' = false := by
        by_contra hk
        push Not at hk
        exact hn ⟨hzp, h0.2.1, fun z' h1 h2 => by
          cases hb : φS z'
          · exact absurd hb (hk z' h1 h2)
          · rfl⟩
      obtain ⟨z', hz', hne', hf⟩ := hother
      constructor
      · intro h; have := h z' hz'; simp [umschalten, hne', hf] at this
      · intro h; have := h z' hz'; simp [hf] at this
    · constructor
      · intro h z' hz'
        have := h z' hz'
        have hne' : z' ≠ z := fun he => hzp (he ▸ hz')
        simpa [umschalten, hne'] using this
      · intro h z' hz'
        have hne' : z' ≠ z := fun he => hzp (he ▸ hz')
        simpa [umschalten, hne'] using h z' hz'
  have hall := (hM _ hpass p0).mp (fun z' hz' => by
    by_cases he : z' = z
    · simp [umschalten, he]
    · simpa [umschalten, he] using h0.2.2 z' hz' he)
  have := hall z h0.1
  rw [h0.2.1] at this
  exact Bool.false_ne_true this

/-- Two isolable bad cells never share a test. -/
theorem schlecht_getrennt {φS : Z → Bool} {p : P} {z z' : Z} (h : NurSchlecht T φS p z)
    (h' : NurSchlecht T φS p z') : z = z' := by
  by_contra hne
  have := h.2.2 z' h'.1 (Ne.symm hne)
  rw [h'.2.1] at this
  exact Bool.false_ne_true this

/-- **Theorem 4c (a good cell needs an accepted test).** -/
theorem gut_noetig {φS : Z → Bool} {M : List P} (hM : MusterHinreichend T φS M) {z : Z} {p0 : P}
    (hz0 : T p0 z) (hp0 : akzeptiert T φS p0) : ∃ p ∈ M, T p z ∧ akzeptiert T φS p := by
  classical
  by_contra hne
  push Not at hne
  have hpass : ∀ p ∈ M, akzeptiert T (umschalten φS z false) p ↔ akzeptiert T φS p := by
    intro p hp
    by_cases hzp : T p z
    · have hn := hne p hp hzp
      constructor
      · intro h; have := h z hzp; simp [umschalten] at this
      · intro h; exact absurd h hn
    · constructor
      · intro h z' hz'
        have hne' : z' ≠ z := fun he => hzp (he ▸ hz')
        simpa [umschalten, hne'] using h z' hz'
      · intro h z' hz'
        have hne' : z' ≠ z := fun he => hzp (he ▸ hz')
        simpa [umschalten, hne'] using h z' hz'
  have := (hM _ hpass p0).mpr hp0 z hz0
  simp [umschalten] at this

/-- **Theorem 4d (the count)**: a sufficient set has at least one test per isolable bad cell, and one more
    (an accepted test) when some accepted program has a cell. -/
theorem muster_schranke {φS : Z → Bool} {M : List P} (hM : MusterHinreichend T φS M) (B : Finset Z)
    (hB : ∀ z ∈ B, ∃ p0, NurSchlecht T φS p0 z) {g : Z} {pg : P} (hg : T pg g) (hpg : akzeptiert T φS pg) :
    B.card + 1 ≤ M.length := by
  classical
  choose f hf hfz using fun z : B => schlecht_noetig T hM (hB z z.2).choose_spec
  obtain ⟨pv, hpv, -, hpvok⟩ := gut_noetig T hM hg hpg
  have hinj : Function.Injective f := fun z z' he =>
    Subtype.ext (schlecht_getrennt T (hfz z) (he ▸ hfz z'))
  have hnot : pv ∉ Finset.univ.image f := fun hmem => by
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hmem
    have h1 := hfz z
    rw [hz] at h1
    have := hpvok z h1.1
    rw [h1.2.1] at this
    exact Bool.false_ne_true this
  calc B.card + 1 = (insert pv (Finset.univ.image f)).card := by
        rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj, Finset.card_univ,
          Fintype.card_coe]
    _ ≤ M.toFinset.card := Finset.card_le_card fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact List.mem_toFinset.mpr hpv
        · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
          exact List.mem_toFinset.mpr (hf z)
    _ ≤ M.length := List.toFinset_card_le M

end Gabbro.Grammatik.Adaequanz
