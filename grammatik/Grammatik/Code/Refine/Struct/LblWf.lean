import Grammatik.Code.Lower.Stmt

/-
  File:      Grammatik/Code/Refine/LblWf.lean
  Subject:   TRACK L, PHASE L1 -- THE LABEL FACTS (`LblWf`) and the lemmas that assemble them: how the labels of a
             head block and of lowered parts in disjoint ranges are distinct (`lw_single`, `lw_head`, `lw_app`,
             `lw_two`, `lw_seq`, `lw_bind`, `lw_narrow`, `lw_loop`, `lw_retry`, `lw_else`, `lw_arm_cons`).
             Pure arithmetic on labels; nothing here knows a statement.
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
  refine ⟨hl, by simp only [List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
  and_self], ?_⟩
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

/-- The shape of a call with a failure channel: a head block `lb` (call, case number, branch), the value arm's
    entry `st.l` and the reason arm's entry `st.l + 1`, then the value continuation (entry `st.l + 2`, labels from
    `st.l + 4`) and the reason continuation (entry `st.l + 3`, labels from the end of the first). -/
theorem lw_else {lb : Nat} {st s1 s2 : St} {b0 bA bB : Block} {bo be : List Block}
    (hb0 : b0.nl = lb) (hA : bA.nl = st.l) (hB : bB.nl = st.l + 1) (hlt : lb < st.l) (m1 : st.l + 4 ≤ s1.l)
    (m2 : s1.l ≤ s2.l)
    (W1 : (bo.map Block.lbl).Nodup ∧ ∀ x ∈ bo, x.nl = st.l + 2 ∨ (st.l + 4 ≤ x.nl ∧ x.nl < s1.l))
    (W2 : (be.map Block.lbl).Nodup ∧ ∀ x ∈ be, x.nl = st.l + 3 ∨ (s1.l ≤ x.nl ∧ x.nl < s2.l)) :
    LblWf lb st s2 (b0 :: bA :: bB :: (bo ++ be)) := by
  obtain ⟨n1, a1⟩ := W1
  obtain ⟨n2, a2⟩ := W2
  have hmem : ∀ x ∈ bo ++ be, x.nl = st.l + 2 ∨ x.nl = st.l + 3 ∨ (st.l + 4 ≤ x.nl ∧ x.nl < s2.l) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := a1 x hx; omega
    · have := a2 x hx; omega
  have nd0 : ((bo ++ be).map Block.lbl).Nodup := by
    refine lw_app (a1 := fun x => x = st.l + 2 ∨ (st.l + 4 ≤ x ∧ x < s1.l))
      (a2 := fun x => x = st.l + 3 ∨ (s1.l ≤ x ∧ x < s2.l)) n1 n2 ?_ ?_ ?_
    · intro x hx; exact a1 x hx
    · intro x hx; exact a2 x hx
    · intro x hx hy; omega
  have nd1 : ((bB :: (bo ++ be)).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 2 ≤ x ∧ x < s2.l) hB ?_ nd0 ?_
    · intro x hx; omega
    · intro x hx
      have := hmem x hx
      show st.l + 2 ≤ x.nl ∧ x.nl < s2.l
      omega
  have nd2 : ((bA :: bB :: (bo ++ be)).map Block.lbl).Nodup := by
    refine lw_head (a1 := fun x => st.l + 1 ≤ x ∧ x < s2.l) hA ?_ nd1 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · show st.l + 1 ≤ x.nl ∧ x.nl < s2.l
        omega
      · have := hmem x hx
        show st.l + 1 ≤ x.nl ∧ x.nl < s2.l
        omega
  refine ⟨by omega, ?_, ?_⟩
  · refine lw_head (a1 := fun x => st.l ≤ x ∧ x < s2.l) hb0 ?_ nd2 ?_
    · intro x hx; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · show st.l ≤ x.nl ∧ x.nl < s2.l
        omega
      · show st.l ≤ x.nl ∧ x.nl < s2.l
        omega
      · have := hmem x hx
        show st.l ≤ x.nl ∧ x.nl < s2.l
        omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact Or.inl hb0
    · right; omega
    · right; omega
    · have := hmem x hx; right; omega


end Gabbro.Code.Lower
