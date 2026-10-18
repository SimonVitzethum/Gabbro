import Grammatik.Code.Refine.Mono

/-
  File:      Grammatik/Code/Refine/Labels.lean
  Subject:   TRACK L, PHASE L1 -- THE LABELS OF A LOWERING ARE DISTINCT.

  `LblWf lb st st' blks`: the label counter did not fall, the labels of the blocks are pairwise
  distinct, and every label is the entry label `lb` or one the counter handed out (`st.l <= l <
  st'.l`). With `lb < st.l` (the entry label is not one the lowering allocates itself) this is
  what `blk_of_nodup` needs: the labels of a lowered function are distinct BY CONSTRUCTION, so
  the closing function theorem does not assume it.

  NOTE: labels are compared as `Nat` throughout (`omega` does not see through the abbreviation).
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)

/-- The label of a block, as a `Nat` (`omega` does not see through the abbreviation `Lbl`). -/
def _root_.Gabbro.Code.Block.nl (b : Block) : Nat := b.lbl

/-- The label facts of a lowering result. -/
def LblWf (lb : Nat) (st st' : St) (blks : List Block) : Prop :=
  st.l ≤ st'.l ∧ (blks.map Block.lbl).Nodup ∧
    ∀ b ∈ blks, b.nl = lb ∨ (st.l ≤ b.nl ∧ b.nl < st'.l)

theorem lw_single {lb : Nat} {st st' : St} {b : Block} (hb : b.nl = lb) (hl : st.l ≤ st'.l) :
    LblWf lb st st' [b] := by
  refine ⟨hl, by simp, ?_⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact Or.inl hb

/-- `b :: (b1 ++ b2)`, where `b1` and `b2` live in disjoint label ranges above `lb`. -/
theorem lw_head_app {lb : Nat} {b : Block} {b1 b2 : List Block} {a1 a2 : Nat → Prop}
    (hb : b.nl = lb) (hlt : ∀ x, a1 x → x ≠ lb) (hlt2 : ∀ x, a2 x → x ≠ lb)
    (n1 : (b1.map Block.lbl).Nodup) (n2 : (b2.map Block.lbl).Nodup)
    (h1 : ∀ x ∈ b1, a1 x.lbl) (h2 : ∀ x ∈ b2, a2 x.lbl) (hd : ∀ x, a1 x → ¬ a2 x) :
    ((b :: (b1 ++ b2)).map Block.lbl).Nodup := by
  rw [List.map_cons, List.nodup_cons, List.map_append, List.nodup_append]
  refine ⟨?_, n1, n2, ?_⟩
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
      have := hlt y.nl (h1 y hy)
      have e' : y.nl = b.nl := e
      omega
    · obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
      have := hlt2 y.nl (h2 y hy)
      have e' : y.nl = b.nl := e
      omega
  · intro x hx y hy e
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact hd _ (h1 u hu) (e ▸ h2 v hv)

/-- `b :: b1`, where `b1` lives above `lb`. -/
theorem lw_head {lb : Nat} {b : Block} {b1 : List Block} {a1 : Nat → Prop}
    (hb : b.nl = lb) (hlt : ∀ x, a1 x → x ≠ lb)
    (n1 : (b1.map Block.lbl).Nodup) (h1 : ∀ x ∈ b1, a1 x.lbl) :
    ((b :: b1).map Block.lbl).Nodup := by
  rw [List.map_cons, List.nodup_cons]
  refine ⟨?_, n1⟩
  intro hm
  obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
  have := hlt y.nl (h1 y hy)
  have e' : y.nl = b.nl := e
  omega

/-- `b1 ++ b2` in disjoint label ranges. -/
theorem lw_app {b1 b2 : List Block} {a1 a2 : Nat → Prop}
    (n1 : (b1.map Block.lbl).Nodup) (n2 : (b2.map Block.lbl).Nodup)
    (h1 : ∀ x ∈ b1, a1 x.lbl) (h2 : ∀ x ∈ b2, a2 x.lbl) (hd : ∀ x, a1 x → ¬ a2 x) :
    ((b1 ++ b2).map Block.lbl).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨n1, n2, ?_⟩
  intro x hx y hy e
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  exact hd _ (h1 u hu) (e ▸ h2 v hv)

/-- The shape both `ite` and `check` have: a head block, then two lowered parts, the first with entry
    label `st.l` and labels from `st.l + 2`, the second with entry label `st.l + 1` and labels
    from the end of the first. -/
theorem lw_two {lb : Nat} {st s1 s2 : St} {b : Block} {b1 b2 : List Block} (hb : b.nl = lb)
    (hlt : lb < st.l) (m1 : st.l + 2 ≤ s1.l) (m2 : s1.l ≤ s2.l)
    (W1 : (b1.map Block.lbl).Nodup ∧ ∀ x ∈ b1, x.nl = st.l ∨ (st.l + 2 ≤ x.nl ∧ x.nl < s1.l))
    (W2 : (b2.map Block.lbl).Nodup ∧ ∀ x ∈ b2, x.nl = st.l + 1 ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b :: (b1 ++ b2)) := by
  obtain ⟨n1, a1⟩ := W1
  obtain ⟨n2, a2⟩ := W2
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head_app (a1 := fun x => x = st.l ∨ (st.l + 2 ≤ x ∧ x < s1.l))
      (a2 := fun x => x = st.l + 1 ∨ (s1.l ≤ x ∧ x < s2.l)) hb ?_ ?_ n1 n2 ?_ ?_ ?_
    · intro x hx; omega
    · intro x hx; omega
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  · intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact Or.inl hb
    · have := a1 x hx; omega
    · have := a2 x hx; omega

/-- A statement or end block followed by the rest: `lowerS`'s part has entry label `lb` and labels
    from `st.l + 1`, the rest has entry label `st.l` and labels from the end of the first. -/
theorem lw_seq {lb : Nat} {st s1 s2 : St} {b1 b2 : List Block} (hlt : lb < st.l)
    (m1 : st.l + 1 ≤ s1.l) (m2 : s1.l ≤ s2.l)
    (W1 : (b1.map Block.lbl).Nodup ∧ ∀ x ∈ b1, x.nl = lb ∨ (st.l + 1 ≤ x.nl ∧ x.nl < s1.l))
    (W2 : (b2.map Block.lbl).Nodup ∧ ∀ x ∈ b2, x.nl = st.l ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b1 ++ b2) := by
  obtain ⟨n1, a1⟩ := W1
  obtain ⟨n2, a2⟩ := W2
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_app (a1 := fun x => x = lb ∨ (st.l + 1 ≤ x ∧ x < s1.l))
      (a2 := fun x => x = st.l ∨ (s1.l ≤ x ∧ x < s2.l)) n1 n2 ?_ ?_ ?_
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := a1 x hx; omega
    · have := a2 x hx; omega

/-- A head block `lb` jumping on to a lowered part with entry label `st.l`, labels from `st.l + 1`. -/
theorem lw_bind {lb : Nat} {st s2 : St} {b : Block} {b2 : List Block} (hb : b.nl = lb)
    (hlt : lb < st.l) (m2 : st.l + 1 ≤ s2.l)
    (W2 : (b2.map Block.lbl).Nodup ∧ ∀ x ∈ b2, x.nl = st.l ∨ (st.l + 1 ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b :: b2) := by
  obtain ⟨n2, a2⟩ := W2
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head (a1 := fun x => x = st.l ∨ (st.l + 1 ≤ x ∧ x < s2.l)) hb ?_ n2 ?_
    · intro x hx; omega
    · intro x hx; exact a2 x hx
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl hb
    · have := a2 x hx; omega

/-- The shape of `narrow`: a test block `lb`, a bind block `st.l + 1`, then the `else` end block (entry
    label `st.l`, labels from `st.l + 3`) and the rest (entry label `st.l + 2`, labels from the end of
    the first). -/
theorem lw_narrow {lb : Nat} {st s1 s2 : St} {b0 b1 : Block} {be br : List Block}
    (hb0 : b0.nl = lb) (hb1 : b1.nl = st.l + 1) (hlt : lb < st.l) (m1 : st.l + 3 ≤ s1.l)
    (m2 : s1.l ≤ s2.l)
    (W1 : (be.map Block.lbl).Nodup ∧ ∀ x ∈ be, x.nl = st.l ∨ (st.l + 3 ≤ x.nl ∧ x.nl < s1.l))
    (W2 : (br.map Block.lbl).Nodup ∧ ∀ x ∈ br, x.nl = st.l + 2 ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b0 :: b1 :: (be ++ br)) := by
  obtain ⟨n1, a1⟩ := W1
  obtain ⟨n2, a2⟩ := W2
  have nd : ((b1 :: (be ++ br)).map Block.lbl).Nodup := by
    refine lw_head_app (a1 := fun x => x = st.l ∨ (st.l + 3 ≤ x ∧ x < s1.l))
      (a2 := fun x => x = st.l + 2 ∨ (s1.l ≤ x ∧ x < s2.l)) hb1 ?_ ?_ n1 n2 ?_ ?_ ?_
    · intro x hx; omega
    · intro x hx; omega
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head (a1 := fun x => x = st.l + 1 ∨ x = st.l ∨ (st.l + 2 ≤ x ∧ x < s2.l)) hb0 ?_ nd ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact Or.inl hb1
      · have := a1 x hx
        show x.nl = st.l + 1 ∨ x.nl = st.l ∨ (st.l + 2 ≤ x.nl ∧ x.nl < s2.l)
        omega
      · have := a2 x hx
        show x.nl = st.l + 1 ∨ x.nl = st.l ∨ (st.l + 2 ≤ x.nl ∧ x.nl < s2.l)
        omega
  · intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | hx | hx
    · exact Or.inl hb0
    · right; omega
    · have := a1 x hx; right; omega
    · have := a2 x hx; right; omega

/-- The shape of `traverse`: an initialising block `lb`, a test block `st.l`, a bind block `st.l + 1`, an
    increment block `st.l + 2`, and the lowered body (entry label `st.l + 3`, labels from `st.l + 4`). -/
theorem lw_loop {lb : Nat} {st s1 : St} {b0 bH bB bI : Block} {bb : List Block}
    (h0 : b0.nl = lb) (hH : bH.nl = st.l) (hB : bB.nl = st.l + 1) (hI : bI.nl = st.l + 2)
    (hlt : lb < st.l) (m1 : st.l + 4 ≤ s1.l)
    (W : (bb.map Block.lbl).Nodup ∧ ∀ x ∈ bb, x.nl = st.l + 3 ∨ (st.l + 4 ≤ x.nl ∧ x.nl < s1.l)) :
    LblWf lb st s1 (b0 :: bH :: bB :: bI :: bb) := by
  obtain ⟨n, a⟩ := W
  have nd1 : ((bI :: bb).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => x = st.l + 3 ∨ (st.l + 4 ≤ x ∧ x < s1.l)) hI ?_ n ?_
    · intro x hx; omega
    · intro x hx; exact a x hx
  have nd2 : ((bB :: bI :: bb).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 2 ≤ x ∧ x < s1.l) hB ?_ nd1 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · show st.l + 2 ≤ x.nl ∧ x.nl < s1.l; omega
      · have := a x hx; show st.l + 2 ≤ x.nl ∧ x.nl < s1.l; omega
  have nd3 : ((bH :: bB :: bI :: bb).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 1 ≤ x ∧ x < s1.l) hH ?_ nd2 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · show st.l + 1 ≤ x.nl ∧ x.nl < s1.l; omega
      · show st.l + 1 ≤ x.nl ∧ x.nl < s1.l; omega
      · have := a x hx; show st.l + 1 ≤ x.nl ∧ x.nl < s1.l; omega
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head (a1 := fun x => st.l ≤ x ∧ x < s1.l) h0 ?_ nd3 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · show st.l ≤ x.nl ∧ x.nl < s1.l; omega
      · show st.l ≤ x.nl ∧ x.nl < s1.l; omega
      · show st.l ≤ x.nl ∧ x.nl < s1.l; omega
      · have := a x hx; show st.l ≤ x.nl ∧ x.nl < s1.l; omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact Or.inl h0
    · right; omega
    · right; omega
    · right; omega
    · have := a x hx; right; omega

/-- The shape of `retry`: an initialising block `lb`, the test block `st.l`, the pass-count block
    `st.l + 1`, the increment block `st.l + 3`, the lowered body (entry label `st.l + 4`, labels from
    `st.l + 5`) and the lowered overflow block (entry label `st.l + 2`, labels from the end of the body). -/
theorem lw_retry {lb : Nat} {st s1 s2 : St} {b0 bH bT bI : Block} {bb bo : List Block}
    (h0 : b0.nl = lb) (hH : bH.nl = st.l) (hT : bT.nl = st.l + 1) (hI : bI.nl = st.l + 3)
    (hlt : lb < st.l) (m1 : st.l + 5 ≤ s1.l) (m2 : s1.l ≤ s2.l)
    (W1 : (bb.map Block.lbl).Nodup ∧ ∀ x ∈ bb, x.nl = st.l + 4 ∨ (st.l + 5 ≤ x.nl ∧ x.nl < s1.l))
    (W2 : (bo.map Block.lbl).Nodup ∧ ∀ x ∈ bo, x.nl = st.l + 2 ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b0 :: bH :: bT :: bI :: (bb ++ bo)) := by
  obtain ⟨n1, a1⟩ := W1
  obtain ⟨n2, a2⟩ := W2
  have nd0 : ((bb ++ bo).map Block.lbl).Nodup := by
    refine lw_app (a1 := fun x => x = st.l + 4 ∨ (st.l + 5 ≤ x ∧ x < s1.l))
      (a2 := fun x => x = st.l + 2 ∨ (s1.l ≤ x ∧ x < s2.l)) n1 n2 ?_ ?_ ?_
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  have hmem : ∀ x ∈ bb ++ bo, x.nl = st.l + 2 ∨ (st.l + 4 ≤ x.nl ∧ x.nl < s2.l) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := a1 x hx; omega
    · have := a2 x hx; omega
  have nd1 : ((bI :: (bb ++ bo)).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => x = st.l + 2 ∨ (st.l + 4 ≤ x ∧ x < s2.l)) hI ?_ nd0 ?_
    · intro x hx; omega
    · intro x hx; exact hmem x hx
  have nd2 : ((bT :: bI :: (bb ++ bo)).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 2 ≤ x ∧ x < s2.l) hT ?_ nd1 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · show st.l + 2 ≤ x.nl ∧ x.nl < s2.l; omega
      · have := hmem x hx; show st.l + 2 ≤ x.nl ∧ x.nl < s2.l; omega
  have nd3 : ((bH :: bT :: bI :: (bb ++ bo)).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 1 ≤ x ∧ x < s2.l) hH ?_ nd2 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · show st.l + 1 ≤ x.nl ∧ x.nl < s2.l; omega
      · show st.l + 1 ≤ x.nl ∧ x.nl < s2.l; omega
      · have := hmem x hx; show st.l + 1 ≤ x.nl ∧ x.nl < s2.l; omega
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head (a1 := fun x => st.l ≤ x ∧ x < s2.l) h0 ?_ nd3 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · show st.l ≤ x.nl ∧ x.nl < s2.l; omega
      · show st.l ≤ x.nl ∧ x.nl < s2.l; omega
      · show st.l ≤ x.nl ∧ x.nl < s2.l; omega
      · have := hmem x hx; show st.l ≤ x.nl ∧ x.nl < s2.l; omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact Or.inl h0
    · right; omega
    · right; omega
    · right; omega
    · have := hmem x hx; right; omega

/-- One more arm in front of the arms that follow: the first arm has entry label `lb` and the counter's
    labels, the rest have the entry labels `lb + 1 ..` and labels from the end of the first arm. -/
theorem lw_arm_cons {lb n' : Nat} {st s1 s2 : St} {b1 b2 : List Block} (hn : lb + (n' + 1) ≤ st.l)
    (W1 : LblWf lb st s1 b1)
    (W2 : s1.l ≤ s2.l ∧ (b2.map Block.lbl).Nodup ∧
      ∀ x ∈ b2, (lb + 1 ≤ x.nl ∧ x.nl < lb + 1 + n') ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    st.l ≤ s2.l ∧ ((b1 ++ b2).map Block.lbl).Nodup ∧
      ∀ x ∈ b1 ++ b2, (lb ≤ x.nl ∧ x.nl < lb + (n' + 1)) ∨ (st.l ≤ x.nl ∧ x.nl < s2.l) := by
  obtain ⟨m1, n1, a1⟩ := W1
  obtain ⟨m2, n2, a2⟩ := W2
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_app (a1 := fun x => x = lb ∨ (st.l ≤ x ∧ x < s1.l))
      (a2 := fun x => (lb + 1 ≤ x ∧ x < lb + 1 + n') ∨ (s1.l ≤ x ∧ x < s2.l)) n1 n2 ?_ ?_ ?_
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := a1 x hx; omega
    · have := a2 x hx; omega

variable [Conf] {D : Deklaration}

theorem lowerErg_lbl (lay : Layout D) (cenv : List Reg) {Γ : Ctx} {Λ : List (Res D)} {eo : Option GTy}
    (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErg lay cenv e lb st = some (blks, st')) : LblWf lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErg, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | val e =>
      simp only [lowerErg] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)

theorem lowerErgF_lbl (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErgF lay cenv n e lb st = some (blks, st')) : LblWf lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErgF] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact lw_single rfl (Nat.le_refl _)
      · simp at h
  | @val τ e =>
      cases τ with
      | int lo hi =>
          simp only [lowerErgF] at h
          rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
          · simp [he] at h
          simp only [he] at h
          split at h
          · rcases hnc : numCode lo hi (retW n (some (.int lo hi))) (n + 1) 0 oe r1 with ⟨cn, on, r2⟩
            rw [hnc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact lw_single rfl (Nat.le_refl _)
          · simp at h
      | _ => simp [lowerErgF] at h

theorem lowerRet_lbl (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerRet lay cenv n e lb st = some (blks, st')) : LblWf lb st st' blks := by
  unfold lowerRet at h
  by_cases hn : n = 0
  · rw [if_pos hn] at h
    exact lowerErg_lbl lay cenv e lb st st' blks h
  · rw [if_neg hn] at h
    exact lowerErgF_lbl lay cenv n e lb st st' blks h

theorem lowerWhy_lbl (n : Nat) (eo : Option GTy) (r : Nat) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerWhy n eo r lb st = some (blks, st')) : LblWf lb st st' blks := by
  unfold lowerWhy at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lw_single rfl (Nat.le_refl _)
  · simp at h

variable {V : Vertrag D}

mutual

theorem lowerS_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block), (lb : Nat) < st.l →
      lowerS lay cenv lv s lb k st = some (blks, st') → LblWf lb st st' blks
  | _, _, _, _, .assignSlot t f i e _ _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      repeat (split at h <;> try (simp at h; done))
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .assignThru p t _ f i e _ _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      repeat (split at h <;> try (simp at h; done))
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .assignGlob g e _ _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      repeat (split at h <;> try (simp at h; done))
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      repeat (split at h <;> try (simp at h; done))
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .ite c tb eb, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      simp only [hc] at h
      rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
      · simp [hb2] at h
      simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, n1, a1⟩ := lowerB_lbl lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ s1 bt
        (by show (st.l : Nat) < st.l + 2; omega) hb1
      have m1' : st.l + 2 ≤ s1.l := m1
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay cenv lv eb (st.l + 1) k s1 s2 be
        (by show (st.l + 1 : Nat) < s1.l; omega) hb2
      exact lw_two (b := ⟨lb, [], cc, .br oc st.l (st.l + 1)⟩) rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
  | _, _, _, _, .ret e _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      exact lowerRet_lbl lay cenv V.gruende e lb st st' blks h
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .onOption (n := n) o p a, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      rcases ho : lowerE lay cenv o st.r with _ | ⟨co, oo, r1⟩
      · simp [ho] at h
      simp only [ho] at h
      split at h
      · rcases hv : cvtG (.int (-1) (n - 1)) (.int 0 (n - 1)) oo r1 with _ | ⟨cv, ov, r2⟩
        · simp [hv] at h
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (n - 1)) ov r2 with _ | ⟨cb, c, r3⟩
        · simp [hb] at h
        simp only [hb] at h
        rcases hb1 : lowerB lay cenv lv a st.l k ⟨r3, st.l + 3⟩ with _ | ⟨ba, s1⟩
        · simp [hb1] at h
        simp only [hb1] at h
        rcases hb2 : lowerB lay (c :: cenv) lv p (st.l + 2) k s1 with _ | ⟨bp, s2⟩
        · simp [hb2] at h
        simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m1, n1, a1⟩ := lowerB_lbl lay cenv lv a st.l k ⟨r3, st.l + 3⟩ s1 ba
          (by show (st.l : Nat) < st.l + 3; omega) hb1
        have m1' : st.l + 3 ≤ s1.l := m1
        obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay (c :: cenv) lv p (st.l + 2) k s1 s2 bp
          (by show (st.l + 2 : Nat) < s1.l; omega) hb2
        exact lw_narrow (b0 := ⟨lb, [], co, .brc .slt (Ar.wid (-1) (n - 1)) oo
            (.int (Ar.wid (-1) (n - 1)) 0) st.l (st.l + 1)⟩)
          (b1 := ⟨st.l + 1, [], cv ++ cb, .jmp (st.l + 2)⟩) rfl rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
      · simp at h
  | _, _, _, _, .onTag (cs := cs) v arms, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      rcases hv : lowerE lay cenv v st.r with _ | ⟨cv, ov, r1⟩
      · simp [hv] at h
      simp only [hv] at h
      split at h
      · rcases hga : lowerAr lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms (st.l + 1) k
            ⟨r1 + 1, st.l + 1 + cs.length⟩ with _ | ⟨ba, s1⟩
        · simp [hga] at h
        simp only [hga, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m1, n1, a1⟩ := lowerAr_lbl lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms
          (st.l + 1) k ⟨r1 + 1, st.l + 1 + cs.length⟩ s1 ba
          (by show (st.l + 1 : Nat) + cs.length ≤ st.l + 1 + cs.length; omega) hga
        have m1' : st.l + 1 + cs.length ≤ s1.l := m1
        have hlt' : @LT.lt Nat instLTNat lb st.l := hlt
        have a1' : ∀ x ∈ ba, (st.l + 1 ≤ x.nl ∧ x.nl < st.l + 1 + cs.length) ∨
            (st.l + 1 + cs.length ≤ x.nl ∧ x.nl < s1.l) := a1
        have nd1 : (((⟨st.l, [], [], .dead⟩ : Block) :: ba).map Block.lbl).Nodup := by
          refine lw_head (lb := st.l) (a1 := fun x => st.l + 1 ≤ x ∧ x < s1.l) rfl ?_ n1 ?_
          · intro x hx; omega
          · intro x hx
            have := a1' x hx
            show st.l + 1 ≤ x.nl ∧ x.nl < s1.l
            omega
        refine ⟨by omega, ?_, ?_⟩
        · refine lw_head (lb := lb) (a1 := fun x => st.l ≤ x ∧ x < s1.l) (b := ⟨lb, [], cv ++ [.bin r1 .urem
              (Ar.wid 0 (sumTop cs)) ov (.int (Ar.wid 0 (sumTop cs)) (cs.length : Int))],
              .sw (Ar.wid 0 (sumTop cs)) (.reg r1) st.l
              ((List.range cs.length).map fun (i : Nat) => ((i : Int), (st.l + 1 + i : Nat)))⟩) rfl ?_ nd1 ?_
          · intro x hx; omega
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨Nat.le_refl _, by show st.l < s1.l; omega⟩
            · have := a1' x hx
              show st.l ≤ x.nl ∧ x.nl < s1.l
              omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact Or.inl rfl
          · exact Or.inr ⟨Nat.le_refl _, by show st.l < s1.l; omega⟩
          · have := a1' x hx; right; omega
      · simp at h
  | _, _, _, _, .onWhy (n := n) r arms, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      rcases hr : lowerE lay cenv r st.r with _ | ⟨cr, orr, r1⟩
      · simp [hr] at h
      simp only [hr] at h
      split at h
      · rcases hga : lowerGA lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ with _ | ⟨ba, s1⟩
        · simp [hga] at h
        simp only [hga, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m1, n1, a1⟩ := lowerGA_lbl lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ s1 ba
          (by show (st.l + 1 : Nat) + n ≤ st.l + 1 + n; omega) hga
        have m1' : st.l + 1 + n ≤ s1.l := m1
        have hlt' : @LT.lt Nat instLTNat lb st.l := hlt
        have a1' : ∀ x ∈ ba, (st.l + 1 ≤ x.nl ∧ x.nl < st.l + 1 + n) ∨ (st.l + 1 + n ≤ x.nl ∧ x.nl < s1.l) := a1
        have nd1 : (((⟨st.l, [], [], .dead⟩ : Block) :: ba).map Block.lbl).Nodup := by
          refine lw_head (lb := st.l) (a1 := fun x => st.l + 1 ≤ x ∧ x < s1.l) rfl ?_ n1 ?_
          · intro x hx; omega
          · intro x hx
            have := a1' x hx
            show st.l + 1 ≤ x.nl ∧ x.nl < s1.l
            omega
        refine ⟨by omega, ?_, ?_⟩
        · refine lw_head (lb := lb) (a1 := fun x => st.l ≤ x ∧ x < s1.l) (b := ⟨lb, [], cr, .sw (Ar.wid 0 ((n : Int) - 1)) orr st.l
              ((List.range n).map fun (i : Nat) => ((i : Int), (st.l + 1 + i : Nat)))⟩) rfl ?_ nd1 ?_
          · intro x hx; omega
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨Nat.le_refl _, by show st.l < s1.l; omega⟩
            · have := a1' x hx
              show st.l ≤ x.nl ∧ x.nl < s1.l
              omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact Or.inl rfl
          · exact Or.inr ⟨Nat.le_refl _, by show st.l < s1.l; omega⟩
          · have := a1' x hx; right; omega
      · simp at h
  | _, _, _, _, .call f args _ _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .callInd .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .traverse t _ body, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      by_cases hc : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
      · simp only [hc, and_self, if_true] at h
        rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
          _ | ⟨cv, ov, r1⟩
        · simp [hv] at h
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
        · simp [hb] at h
        simp only [hb] at h
        rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
          _ | ⟨bb, s1⟩
        · simp [hb2] at h
        simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb
          (by show (st.l + 3 : Nat) < st.l + 4; omega) hb2
        have m2' : st.l + 4 ≤ s1.l := m2
        exact lw_loop (b0 := ⟨lb, [], _, .jmp st.l⟩) (bH := ⟨st.l, [], [], _⟩) (bB := ⟨st.l + 1, [], cv ++ cb, .jmp (st.l + 3)⟩)
          (bI := ⟨st.l + 2, [], _, .jmp st.l⟩) rfl rfl rfl rfl hlt m2' ⟨n2, a2⟩
      · simp [hc] at h
  | _, _, _, _, .retry n bis body ueb, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      by_cases hc : retryOk n = true
      · simp only [hc, if_true] at h
        rcases hcb : lowerE lay cenv bis (st.r + 1) with _ | ⟨cb, ob, r1⟩
        · simp [hcb] at h
        simp only [hcb] at h
        rcases hb1 : lowerB lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ with _ | ⟨bb, s1⟩
        · simp [hb1] at h
        simp only [hb1] at h
        rcases hb2 : lowerB lay cenv lv ueb (st.l + 2) k s1 with _ | ⟨bo, s2⟩
        · simp [hb2] at h
        simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m1, n1, a1⟩ := lowerB_lbl lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb
          (by show (st.l + 4 : Nat) < st.l + 5; omega) hb1
        have m1' : st.l + 5 ≤ s1.l := m1
        obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay cenv lv ueb (st.l + 2) k s1 s2 bo
          (by show (st.l + 2 : Nat) < s1.l; omega) hb2
        exact lw_retry (b0 := ⟨lb, [], _, .jmp st.l⟩) (bH := ⟨st.l, [], cb, _⟩) (bT := ⟨st.l + 1, [], [], _⟩)
          (bI := ⟨st.l + 3, [], _, .jmp st.l⟩) rfl rfl rfl rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
      · simp [hc] at h
  | _, _, _, _, .forever _ _ body, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      exact lowerB_lbl lay cenv (k, lb) body lb lb st st' blks hlt h
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .retWhy r _, lb, k, st, st', blks, hlt, h => by
      simp only [lowerS] at h
      exact lowerWhy_lbl V.gruende V.erg r.val lb st st' blks h
  | _, _, _, _, .leave .., lb, k, st, st', blks, hlt, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .next .., lb, k, st, st', blks, hlt, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)

theorem lowerB_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block), (lb : Nat) < st.l →
      lowerB lay cenv lv b lb k st = some (blks, st') → LblWf lb st st' blks
  | _, _, _, _, .nil, lb, k, st, st', blks, hlt, h => by
      simp only [lowerB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, hlt, h => by
      simp only [lowerB] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      simp only [hs] at h
      rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, n1, a1⟩ := lowerS_lbl lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1
        (Nat.lt_succ_of_lt hlt) hs
      have m1' : st.l + 1 ≤ s1.l := m1
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay cenv lv rest st.l k s1 s2 b2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) m1') hr
      exact lw_seq hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) e rest, lb, k, st, st', blks, hlt, h => by
      simp only [lowerB] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2
        (by show (st.l : Nat) < st.l + 1; omega) hr
      exact lw_bind (b := ⟨lb, [], ce ++ cb, .jmp st.l⟩) rfl hlt (by exact m2) ⟨n2, a2⟩
  | _, _, _, _, .check c sonst rest, lb, k, st, st', blks, hlt, h => by
      simp only [lowerB] at h
      rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      simp only [hc] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, n1, a1⟩ := lowerEnd_lbl lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ s1 be
        (by show (st.l : Nat) < st.l + 2; omega) hb1
      have m1' : st.l + 2 ≤ s1.l := m1
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay cenv lv rest (st.l + 1) k s1 s2 br
        (by show (st.l + 1 : Nat) < s1.l; omega) hb2
      exact lw_two (b := ⟨lb, [], cc, .br oc (st.l + 1) st.l⟩) rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) f args _ _ _ rest, lb, k, st, st', blks, hlt, h => by
      simp only [lowerB] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      simp only [hla] at h
      rcases hb : bindCode τ (.reg r1) (r1 + 1) with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2
        (by show (st.l : Nat) < st.l + 1; omega) hr
      exact lw_bind (b := ⟨lb, [], ca ++ [.call (some r1) (lay.fno f) ops] ++ cb, .jmp st.l⟩) rfl hlt (by exact m2)
        ⟨n2, a2⟩
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindCallElse .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) e lo' hi' sonst rest, lb, k, st, st', blks,
      hlt, h => by
      simp only [lowerB] at h
      rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
        _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      simp only [hc] at h
      rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
      · simp [he] at h
      simp only [he] at h
      rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
      · simp [hv] at h
      simp only [hv] at h
      rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, n1, a1⟩ := lowerEnd_lbl lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ s1 be
        (by show (st.l : Nat) < st.l + 3; omega) hb1
      have m1' : st.l + 3 ≤ s1.l := m1
      obtain ⟨m2, n2, a2⟩ := lowerB_lbl lay (a :: cenv) lv rest (st.l + 2) k s1 s2 br
        (by show (st.l + 2 : Nat) < s1.l; omega) hb2
      exact lw_narrow (b0 := ⟨lb, [], cc, .br oc (st.l + 1) st.l⟩) (b1 := ⟨st.l + 1, [], ce ++ cv ++ cb, .jmp (st.l + 2)⟩)
        rfl rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
  | _, _, _, _, .float .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h

theorem lowerEnd_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block), (lb : Nat) < st.l →
      lowerEnd lay cenv lv b lb st = some (blks, st') → LblWf lb st st' blks
  | _, _, _, .ret e _, lb, st, st', blks, hlt, h => by
      simp only [lowerEnd] at h
      exact lowerRet_lbl lay cenv V.gruende e lb st st' blks h
  | _, _, _, .cons s rest, lb, st, st', blks, hlt, h => by
      simp only [lowerEnd] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      simp only [hs] at h
      rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, n1, a1⟩ := lowerS_lbl lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1
        (Nat.lt_succ_of_lt hlt) hs
      have m1' : st.l + 1 ≤ s1.l := m1
      obtain ⟨m2, n2, a2⟩ := lowerEnd_lbl lay cenv lv rest st.l s1 s2 b2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) m1') hr
      exact lw_seq hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) e rest, lb, st, st', blks, hlt, h => by
      simp only [lowerEnd] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerEnd lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m2, n2, a2⟩ := lowerEnd_lbl lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ s2 b2
        (by show (st.l : Nat) < st.l + 1; omega) hr
      exact lw_bind (b := ⟨lb, [], ce ++ cb, .jmp st.l⟩) rfl hlt (by exact m2) ⟨n2, a2⟩
  | _, _, _, .retWhy r _, lb, st, st', blks, hlt, h => by
      simp only [lowerEnd] at h
      exact lowerWhy_lbl V.gruende V.erg r.val lb st st' blks h
  | _, _, _, .leave .., lb, st, st', blks, hlt, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, .next .., lb, st, st', blks, hlt, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | _, _, _, .bindAxiom .., lb, st, st', blks, hlt, h => by
      simp [lowerEnd] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, hlt, h => by
      simp [lowerEnd] at h

/-- The arms of a `match` on a tagged value: arm `i` has entry label `lb + i` (below `st.l`), the counter
    hands out labels from `st.l`; all labels are distinct. -/
theorem lowerAr_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat)
    (ov : Opd) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (lb k : Nat) (st st' : St) (blks : List Block),
      lb + cs.length ≤ st.l → lowerAr lay cenv lv top W L ov arms lb k st = some (blks, st') →
      st.l ≤ st'.l ∧ (blks.map Block.lbl).Nodup ∧
        ∀ x ∈ blks, (lb ≤ x.nl ∧ x.nl < lb + cs.length) ∨ (st.l ≤ x.nl ∧ x.nl < st'.l)
  | _, _, _, _, _, .nil, lb, k, st, st', blks, hn, h => by
      simp only [lowerAr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, by simp⟩
  | _, _, _, _, _, .cons (c := none) (cs := cs') b rest, lb, k, st, st', blks, hn, h => by
      simp only [lowerAr] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hn' : lb + (cs'.length + 1) ≤ st.l := hn
      have W1 := lowerB_lbl lay cenv lv b lb k st s1 b1 (show @LT.lt Nat instLTNat lb st.l by omega) hb
      obtain ⟨m2, n2, a2⟩ := lowerAr_lbl lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2
        (by show lb + 1 + cs'.length ≤ s1.l; have := W1.1; omega) hr
      exact lw_arm_cons (n' := cs'.length) hn' W1 ⟨m2, n2, a2⟩
  | _, _, _, _, _, .cons (c := some (lo, hi)) (cs := cs') b rest, lb, k, st, st', blks, hn, h => by
      simp only [lowerAr] at h
      rcases hp : payCode top W L lo hi ov st.r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      simp only [hp] at h
      rcases hb : bindCode (.int lo hi) op r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ with _ | ⟨bb, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hn' : lb + (cs'.length + 1) ≤ st.l := hn
      obtain ⟨m1, n1, a1⟩ := lowerB_lbl lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ s1 bb
        (by show (st.l : Nat) < st.l + 1; omega) hb1
      have m1' : st.l + 1 ≤ s1.l := m1
      have W1 : LblWf lb st s1 (⟨lb, [], cp ++ cb, .jmp st.l⟩ :: bb) :=
        lw_bind (b := ⟨lb, [], cp ++ cb, .jmp st.l⟩) rfl
          (show @LT.lt Nat instLTNat lb st.l by omega) m1' ⟨n1, a1⟩
      obtain ⟨m2, n2, a2⟩ := lowerAr_lbl lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2
        (by show lb + 1 + cs'.length ≤ s1.l; have := W1.1; omega) hr
      exact lw_arm_cons (n' := cs'.length) hn' W1 ⟨m2, n2, a2⟩

/-- The arms of a `match` on a reason: arm `i` has entry label `lb + i` (below `st.l`), the counter hands
    out labels from `st.l`; all labels are distinct. -/
theorem lowerGA_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (lb k : Nat) (st st' : St) (blks : List Block),
      lb + n ≤ st.l → lowerGA lay cenv lv arms lb k st = some (blks, st') →
      st.l ≤ st'.l ∧ (blks.map Block.lbl).Nodup ∧
        ∀ x ∈ blks, (lb ≤ x.nl ∧ x.nl < lb + n) ∨ (st.l ≤ x.nl ∧ x.nl < st'.l)
  | _, _, _, _, _, .nil, lb, k, st, st', blks, hn, h => by
      simp only [lowerGA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, by simp⟩
  | _, _, _, _, _, .cons (n := n') b rest, lb, k, st, st', blks, hn, h => by
      simp only [lowerGA] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerGA lay cenv lv rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hn' : lb + (n' + 1) ≤ st.l := hn
      obtain ⟨m1, n1, a1⟩ := lowerB_lbl lay cenv lv b lb k st s1 b1 (show @LT.lt Nat instLTNat lb st.l by omega) hb
      obtain ⟨m2, n2, a2⟩ := lowerGA_lbl lay cenv lv rest (lb + 1) k s1 s2 b2
        (by show lb + 1 + n' ≤ s1.l; omega) hr
      refine ⟨by omega, ?_, ?_⟩
      · refine lw_app (a1 := fun x => x = lb ∨ (st.l ≤ x ∧ x < s1.l))
          (a2 := fun x => (lb + 1 ≤ x ∧ x < lb + 1 + n') ∨ (s1.l ≤ x ∧ x < s2.l)) n1 n2 ?_ ?_ ?_
        · intro x hx; exact a1 x hx
        · intro x hx; exact a2 x hx
        · intro x hx hy; omega
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := a1 x hx; omega
        · have := a2 x hx; omega

end

end Gabbro.Code.Lower
