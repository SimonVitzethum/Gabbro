/-
  File:      Grammatik/Isabelle/Table_Absenkung.lean
  Part of:   Gabbro -- Lean port of `beweise/Table_Absenkung.thy`
             (template `table.absenkung`, S15; lane 168).

  What this file is: the COUNT, and only it. `table T count N` produces an
  index type `{i. i < N}` (proved in `Table_Indexschranke`) and a C array
  `T_slot slots[N]`; a C array of length `m` has the valid indices
  `{i. i < m}`. Both halves of the entry are proved separately -- `m < N`
  leaves an index without storage (the dangerous direction), `m > N`
  leaves storage without an index -- and together they are the exact cover.
  From `m = N` plus the index bound, no access of the generated program
  leaves the array.

  Model notes: Isabelle sets `{i. i < N}` are predicates `Nat -> Prop`
  here; set equality is predicate (function) equality. The four statements
  quantify over pure naturals only, so there are no syntax premises to
  witness; the two `exists` conclusions are already witnessed inside the
  proofs (`m` and `N` respectively).

  No bridge to the model semantics: the layout half (`M-3`, "the lowering
  allocates N slots") is about `emit.rs`, which has no counterpart in the
  Lean grammar model. The template's carrying half over the real semantics
  is already tied in `Grammatik.SchablonenT5Sem` (section 2); the standalone
  index sets here admit no direct embedding into `Expr ... (.index n)`.
-/

namespace Gabbro.Grammatik.TableAbsenkung

/-- The index type of `table T count N`: `{i. i < N}`. -/
def indextyp (N : Nat) : Nat → Prop :=
  fun i => i < N

/-- The valid indices of a C array of length `m`: `{i. i < m}`. -/
def feldindizes (m : Nat) : Nat → Prop :=
  fun i => i < m

/-- M-1, first half: `m < N` leaves an index without storage.
    Witness: `m` itself. -/
theorem zu_kurz_laesst_einen_index_ohne_speicher {m N : Nat} (h : m < N) :
    ∃ i, indextyp N i ∧ ¬ feldindizes m i :=
  ⟨m, h, Nat.lt_irrefl _⟩

/-- M-1, second half: `m > N` leaves storage without an index.
    Witness: `N` itself. -/
theorem zu_lang_laesst_speicher_ohne_index {m N : Nat} (h : N < m) :
    ∃ i, feldindizes m i ∧ ¬ indextyp N i :=
  ⟨N, h, Nat.lt_irrefl _⟩

/-- The promise itself: exact cover means the two predicates coincide
    exactly when `m = N`. -/
theorem absenkung_deckt_genau {m N : Nat} :
    feldindizes m = indextyp N ↔ m = N := by
  constructor
  · intro h
    have hall : ∀ i, (i < m) ↔ (i < N) := fun i => by
      have e := congrFun h i
      simp [feldindizes, indextyp] at e
      exact e
    rcases Nat.lt_trichotomy m N with hlt | heq | hgt
    · exact absurd ((hall m).mpr hlt) (Nat.lt_irrefl _)
    · exact heq
    · exact absurd ((hall N).mp hgt) (Nat.lt_irrefl _)
  · intro h
    subst h
    rfl

/-- The content: with `m = N`, every index in the type (M103, from
    `table.indexschranke`) is a valid array access. -/
theorem kein_zugriff_laeuft_aus_dem_feld {m N i : Nat}
    (hlaenge : m = N) (hm103 : indextyp N i) : feldindizes m i := by
  subst hlaenge
  exact hm103

end Gabbro.Grammatik.TableAbsenkung
