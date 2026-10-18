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

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr)

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
      exact lowerErg_lbl lay cenv e lb st st' blks h
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .onOption .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .onTag .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .onWhy .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .call .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .callInd .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .traverse .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
  | _, _, _, _, .retry .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
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
  | _, _, _, _, .retWhy .., lb, k, st, st', blks, hlt, h => by
      simp [lowerS] at h
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
  | _, _, _, _, .bindCall .., lb, k, st, st', blks, hlt, h => by
      simp [lowerB] at h
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
      exact lowerErg_lbl lay cenv e lb st st' blks h
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
  | _, _, _, .retWhy .., lb, st, st', blks, hlt, h => by
      simp [lowerEnd] at h
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

end

end Gabbro.Code.Lower
