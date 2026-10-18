import Grammatik.Code.Refine.Env

/-
  File:      Grammatik/Code/Refine/Frame.lean
  Subject:   TRACK L, PHASE L1 -- THE FRAME OF A RUN, `Fr`.

  A run from `(m, rs)` to `(m', rs')` has the frame `Fr lay cenv r0 m rs m' rs'` when it leaves
  registers below `r0` untouched, only grows the memory, and keeps every block that existed, is no
  table, no global and no cell of the local variables `cenv` (`Own`). A statement that writes a
  local (`store` into its cell), a table or a global is a run with this frame; so is a whole
  function run from the point of view of its caller.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration)

variable {D : Deklaration}

/-- The cells of the local variables: the blocks their registers point to. -/
def Own (cenv : List Reg) (rs : Regs) (b : Nat) : Prop := ∃ r ∈ cenv, rs r = some (.ptr b 0)

/-- **The frame of a run** from `(m, rs)` to `(m', rs')`: registers below `r0` are untouched, the
    memory only grows, and a block that existed, is no table, no global and no cell of the locals
    `cenv`, keeps what it held. -/
def Fr (lay : Layout D) (cenv : List Reg) (r0 : Nat) (m : Mem) (rs : Regs) (m' : Mem) (rs' : Regs) : Prop :=
  (∀ x, x < r0 → rs' x = rs x) ∧ m.next ≤ m'.next ∧
  ∀ b, Fresh lay b → b < m.next → ¬ Own cenv rs b → ∀ o t v, m.load b o t = some v → m'.load b o t = some v

/-- What a call leaves of its caller's memory: it only grows, and a block that existed and is no table
    and no global keeps what it held. -/
def Keep (lay : Layout D) (m m' : Mem) : Prop :=
  m.next ≤ m'.next ∧
    ∀ b, Fresh lay b → b < m.next → ∀ o t v, m.load b o t = some v → m'.load b o t = some v

section Frame

variable {lay : Layout D} {cenv : List Reg}

/-- Two runs in a row (the second starts where the first ends): the frames compose. -/
theorem fr_trans {r0 r1 : Nat} {m m1 m2 : Mem} {rs rs1 rs2 : Regs}
    (h1 : Fr lay cenv r0 m rs m1 rs1) (h2 : Fr lay cenv r1 m1 rs1 m2 rs2) (hle : r0 ≤ r1)
    (hc : ∀ x ∈ cenv, x < r0) : Fr lay cenv r0 m rs m2 rs2 := by
  obtain ⟨a1, n1, l1⟩ := h1
  obtain ⟨a2, n2, l2⟩ := h2
  refine ⟨fun x hx => by rw [a2 x (Nat.lt_of_lt_of_le hx hle), a1 x hx], Nat.le_trans n1 n2, ?_⟩
  intro b hf hb hown o t v hl
  refine l2 b hf (Nat.lt_of_lt_of_le hb n1) ?_ o t v (l1 b hf hb hown o t v hl)
  rintro ⟨r, hr, hrs⟩
  exact hown ⟨r, hr, by rw [← a1 r (hc r hr)]; exact hrs⟩

/-- A run that changes registers only. -/
theorem fr_regs {r0 : Nat} {m : Mem} {rs rs' : Regs} (hag : ∀ x, x < r0 → rs' x = rs x) :
    Fr lay cenv r0 m rs m rs' := ⟨hag, Nat.le_refl _, fun _ _ _ _ _ _ _ hl => hl⟩

/-- A run that stores into a table, a global or a cell of the locals. -/
theorem fr_store {r0 : Nat} {m m' : Mem} {rs rs' : Regs} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (hst : m.store b o t v = some m') (hb : ¬ Fresh lay b ∨ Own cenv rs b)
    (hag : ∀ x, x < r0 → rs' x = rs x) : Fr lay cenv r0 m rs m' rs' := by
  refine ⟨hag, Nat.le_of_eq (store_next hst).symm, ?_⟩
  intro b' hf _ hown o' t' v' hl
  have hne : b' ≠ b := by
    rintro rfl
    rcases hb with hb | hb
    · exact hb hf
    · exact hown hb
  rw [load_store_other hst (Or.inl hne)]
  exact hl

/-- The scope of a bound local: a frame over the whole `let`, from the frame of the binding step and
    the frame of the scope (whose environment has the new cell on top). The new cell was allocated
    at or above the old `next`. -/
theorem fr_bind {a : Reg} {r0 ri : Nat} {m m1 m' : Mem} {rs rs3 rs' : Regs}
    (hF1 : Fr lay cenv r0 m rs m1 rs3) (hcell : ∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b)
    (hca : ∀ x ∈ cenv, x < r0) (hri : r0 ≤ ri) (hF2 : Fr lay (a :: cenv) ri m1 rs3 m' rs') :
    Fr lay cenv r0 m rs m' rs' := by
  obtain ⟨a1, n1, l1⟩ := hF1
  obtain ⟨a2, n2, l2⟩ := hF2
  refine ⟨fun x hx => by rw [a2 x (Nat.lt_of_lt_of_le hx hri), a1 x hx], Nat.le_trans n1 n2, ?_⟩
  intro b hf hb hown o t v hl
  refine l2 b hf (Nat.lt_of_lt_of_le hb n1) ?_ o t v (l1 b hf hb hown o t v hl)
  rintro ⟨r, hr, hrs⟩
  rcases List.mem_cons.mp hr with rfl | hr'
  · have := hcell b hrs
    omega
  · exact hown ⟨r, hr', by rw [← a1 r (hca r hr')]; exact hrs⟩

end Frame

end Gabbro.Code.Lower
