/-
  File:      Grammatik/Isabelle/OptionSonderwert.lean
  Port of:   beweise/Option_Sonderwert.thy (template `option.sonderwert`, S1)

  The entry reads: the special value `N` lies OUTSIDE the index domain
  `0 ..< N`, and no generated computation reaches it -- so lowering
  `option index into T` to a bare machine word is lossless. TO BE SHOWN is
  both: the disjointness AND that no operation can produce the special value.

  Proven here: the disjointness with the flushed-out premise `N < 2^w` (the
  machine word, M-1: at `N = 2^w` the special value collapses onto zero --
  and zero is the FIRST valid slot), plus injectivity of both the plain and
  the word-level encoding. NOT proven here: that no generated computation
  reaches the special value (M-2) -- a statement about `emit.rs`, whose object
  is a program in Rust, not a set. Named in the Bridge section, not faked.

  Adaptations (same content, Lean core without mathlib):
  - `indextyp N` becomes the predicate `fun i => i < N` (Isabelle: a set).
    Same membership facts.
-/

namespace Gabbro.Grammatik.Isabelle.OptionSonderwert

/-- An index. (Isabelle: `type_synonym idx = nat`.) -/
abbrev Idx := Nat

/-- The index type of `table T count N`: `{i. i < N}`.
    (Isabelle: `indextyp`.) -/
def indextyp (N : Nat) (i : Idx) : Prop := i < N

/-- The encoding: `None` is `N` itself, `Some i` is `i`.
    (Isabelle: `kodiere`.) -/
def kodiere (N : Nat) : Option Idx → Nat
  | none => N
  | some i => i

/-! ## The first half: disjointness -/

/-- The special value is outside. (Isabelle: `sonderwert_ausserhalb`.) -/
theorem sonderwert_ausserhalb (N : Nat) : ¬ indextyp N N := by
  simp [indextyp]

/-- The encoding is injective on the valid range.
    (Isabelle: `kodiere_injektiv`.) -/
theorem kodiere_injektiv (N : Nat) (x y : Option Idx)
    (hx : ∀ i, x = some i → indextyp N i)
    (hy : ∀ i, y = some i → indextyp N i)
    (hgleich : kodiere N x = kodiere N y) : x = y := by
  revert hx hy hgleich
  cases x with
  | none =>
    cases y with
    | none =>
      intro _ _ _
      rfl
    | some j =>
      intro hx hy hgleich
      have hlt : j < N := hy j rfl
      have e1 : kodiere N none = N := rfl
      have e2 : kodiere N (some j) = j := rfl
      have heq : N = j := e1.symm.trans (hgleich.trans e2)
      exfalso
      exact absurd heq (Ne.symm (Nat.ne_of_lt hlt))
  | some i =>
    cases y with
    | none =>
      intro hx hy hgleich
      have hlt : i < N := hx i rfl
      have e1 : kodiere N (some i) = i := rfl
      have e2 : kodiere N none = N := rfl
      have heq : i = N := e1.symm.trans (hgleich.trans e2)
      exfalso
      exact absurd heq (Nat.ne_of_lt hlt)
    | some j =>
      intro hx hy hgleich
      have e1 : kodiere N (some i) = i := rfl
      have e2 : kodiere N (some j) = j := rfl
      have heq : i = j := e1.symm.trans (hgleich.trans e2)
      rw [heq]

/-! ## M-1 -- the premise the entry does not name: the machine word -/

/-- The encoding through a `w`-bit machine word: everything modulo `2^w`.
    (Isabelle: `kodiere_wort`.) -/
def kodiereWort (w N : Nat) (x : Option Idx) : Nat :=
  kodiere N x % 2 ^ w

/-- At `N = 2^w` the special value collapses onto zero -- and zero is the
    FIRST valid slot. (Isabelle: `sonderwert_kollidiert_bei_vollem_wort`.) -/
theorem sonderwert_kollidiert_bei_vollem_wort (w N : Nat)
    (hN : N = 2 ^ w) (_hpos : N > 0) :
    kodiereWort w N none = kodiereWort w N (some 0) := by
  simp only [kodiereWort, kodiere, hN, Nat.mod_self, Nat.zero_mod]

/-- With the premise the promise holds: the table must be STRICTLY shorter
    than the machine word carrying its index.
    (Isabelle: `kodiere_wort_injektiv`.) -/
theorem kodiere_wort_injektiv (w N : Nat) (x y : Option Idx)
    (klein : N < 2 ^ w)
    (gx : ∀ i, x = some i → indextyp N i)
    (gy : ∀ i, y = some i → indextyp N i)
    (gleich : kodiereWort w N x = kodiereWort w N y) : x = y := by
  have schranke : ∀ z : Option Idx,
      (∀ i, z = some i → indextyp N i) → kodiere N z < 2 ^ w := by
    intro z hz
    cases z with
    | none =>
      have e : kodiere N none = N := rfl
      rw [e]
      exact klein
    | some i =>
      have hlt : i < N := hz i rfl
      have e : kodiere N (some i) = i := rfl
      rw [e]
      exact Nat.lt_trans hlt klein
  have h1 := schranke x gx
  have h2 := schranke y gy
  have hmod : kodiere N x = kodiere N y := by
    simp only [kodiereWort] at gleich
    exact Nat.mod_eq_of_lt h1 |>.symm.trans (gleich.trans (Nat.mod_eq_of_lt h2))
  exact kodiere_injektiv N x y gx gy hmod

/-! ## Witness: the encoding on a concrete instance -/

/-- Witness: at `N = 3, w = 2`, `None` encodes to `3` apart from every valid
    `Some`, while at `N = 4 = 2^2` it collapses onto `Some 0`. Both halves of
    M-1 on a concrete instance. No lemma above quantifies over syntax, so the
    inhabitation obligation is vacuous. -/
theorem kodiere_zeuge :
    kodiere 3 none = 3 ∧ kodiere 3 (some 2) = 2 ∧
    kodiere 3 none ≠ kodiere 3 (some 2) ∧
    kodiereWort 2 4 none = kodiereWort 2 4 (some 0) := by
  refine ⟨rfl, rfl, by decide, ?_⟩
  exact sonderwert_kollidiert_bei_vollem_wort 2 4 rfl (by decide)

/-! ## Bridge

  `SchablonenT5Sem.lean` §4 ties `option.sonderwert` to the Lean model:
  `Expr.some` / `Expr.none` evaluate to `Option.some` / `Option.none`, so a
  `Some`-constructed value is always apart from `None`
  (`sonderwert_disjoint`), with the payload in range (`sonderwert_schranke`
  via `indexschranke_eval`). That file states precisely what has NO
  counterpart here: the word half (`N < 2^w`, collapse at `N = 2^w`) -- the
  model has no machine-word lowering. The two files are complementary halves
  of the same template: disjointness here (abstract, with the word premise),
  disjointness there (over `eval`).
  M-2 stays open on both sides: that no GENERATED computation reaches the
  special value is a statement about `emit.rs`, provable in neither register.
  Named, not faked. -/

#print axioms Gabbro.Grammatik.Isabelle.OptionSonderwert.sonderwert_ausserhalb
#print axioms Gabbro.Grammatik.Isabelle.OptionSonderwert.kodiere_injektiv
#print axioms Gabbro.Grammatik.Isabelle.OptionSonderwert.sonderwert_kollidiert_bei_vollem_wort
#print axioms Gabbro.Grammatik.Isabelle.OptionSonderwert.kodiere_wort_injektiv
#print axioms Gabbro.Grammatik.Isabelle.OptionSonderwert.kodiere_zeuge

end Gabbro.Grammatik.Isabelle.OptionSonderwert
