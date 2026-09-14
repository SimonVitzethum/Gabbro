/-
  File:      Grammatik/Isabelle/Table_Indexschranke.lean
  Part of:   Gabbro -- Lean port of `beweise/Table_Indexschranke.thy`
             (template `table.indexschranke`, S12; lane 168).

  What this file is: the index bound as a promise about WRITE SITES, not
  about the type. `table T count N` generates `index into T`; the claim
  "covers exactly the occupied slots" is washed out here: only one
  direction holds (every occupied slot is in the type), the converse is
  refuted by counterexample (the empty table over a nonempty type), and
  the carrying half is that every generated write site stays inside.

  Model notes: Isabelle `finite S` is `Endlich` below (an explicit bound
  list; `List.range N` is the bound). Isabelle polymorphism `'a option`
  is `Option α` with `variable {α}`. The `N`-slots-are-allocated half
  (M-3) is about emission and has no formal counterpart -- same boundary
  as in the theory.

  No bridge to the model semantics: `World.slots` in `Semantik.lean` is
  total (slots are never unoccupied), so the occupancy half
  (`belegt_liegt_im_indextyp`) has no counterpart there -- this is already
  documented in `Grammatik.SchablonenT5Sem` (section 1), which ties the
  carrying half to the real expression semantics.
-/

namespace Gabbro.Grammatik.TableIndexschranke

variable {α : Type}

/-- The index type of `table T count N`: `{i. i < N}`. -/
def indextyp (N : Nat) : Nat → Prop :=
  fun i => i < N

/-- Finiteness, stated with an explicit bound list (no set library). -/
def Endlich (p : Nat → Prop) : Prop :=
  ∃ l : List Nat, ∀ i, p i → i ∈ l

theorem indextyp_endlich (N : Nat) : Endlich (indextyp N) :=
  ⟨List.range N, fun _i hi => List.mem_range.mpr hi⟩

set_option linter.unusedVariables false in
theorem indextyp_schranke {N i : Nat} (h : indextyp N i) : i < N :=
  h

/-- A slot is occupied when it holds a value. -/
def belegt (σ : Nat → Option α) (i : Nat) : Prop :=
  σ i ≠ none

/-- Well-formed: every occupied slot is inside the index type. -/
def wohlgeformt (N : Nat) (σ : Nat → Option α) : Prop :=
  ∀ i, belegt σ i → indextyp N i

/-- M-1, the direction that holds: an occupied slot is in the type. -/
theorem belegt_liegt_im_indextyp {N : Nat} {σ : Nat → Option α} {i : Nat}
    (hwf : wohlgeformt N σ) (hb : belegt σ i) : indextyp N i :=
  hwf i hb

/-- M-1, the converse FAILS: an index in the type need not be occupied.
    Counterexample: the empty table over a nonempty type. -/
theorem indextyp_deckt_nicht_nur_belegte {N : Nat} (hN : N > 0) :
    ∃ σ : Nat → Option α, ∃ i, wohlgeformt N σ ∧ indextyp N i ∧ ¬ belegt σ i := by
  refine ⟨fun _ => none, 0, ?_, hN, ?_⟩
  · intro i hb
    exact absurd rfl hb
  · intro hb
    exact absurd rfl hb

/-- M-2: every generated write site stays inside the type. -/
def schreibstellen_im_typ (N : Nat) (σ : Nat → Option α)
    (feld : Nat → Option Nat) : Prop :=
  ∀ i d, belegt σ i → feld i = some d → indextyp N d

theorem kette_bleibt_im_typ {N : Nat} {σ : Nat → Option α}
    {feld : Nat → Option Nat} {i d : Nat}
    (h : schreibstellen_im_typ N σ feld) (hb : belegt σ i)
    (hfd : feld i = some d) : d < N :=
  h i d hb hfd

/-- The junction to S4: `im_bereich` is `schreibstellen_im_typ` over two
    fields instead of one. -/
theorem im_bereich_folgt_aus_indexschranke {N : Nat} {σ : Nat → Option α}
    {erstes naechstes : Nat → Option Nat} {i : Nat}
    (hfc : schreibstellen_im_typ N σ erstes)
    (hns : schreibstellen_im_typ N σ naechstes)
    (hb : belegt σ i) :
    (∀ d, erstes i = some d → d < N) ∧ (∀ d, naechstes i = some d → d < N) :=
  ⟨fun _d hd => kette_bleibt_im_typ hfc hb hd,
   fun _d hd => kette_bleibt_im_typ hns hb hd⟩

/-! ## Witnesses: one concrete table instantiating every syntax premise.

The table has one occupied slot (`0`, holding `()`), capacity `5`, and a
single link field pointing at `2`. -/

/-- The witness table: slot `0` occupied, everything else free. -/
def zσ : Nat → Option Unit :=
  fun i => if i = 0 then some () else none

/-- The witness link field: slot `0` points at `2`. -/
def zfeld : Nat → Option Nat :=
  fun i => if i = 0 then some 2 else none

theorem zσ_wohlgeformt : wohlgeformt 5 zσ := by
  intro i hb
  have hi0 : i = 0 := by
    by_cases hne : i = 0
    · exact hne
    · have hb' : (if i = 0 then (some () : Option Unit) else none) ≠ none := hb
      rw [if_neg hne] at hb'
      exact absurd rfl hb'
  subst hi0
  show (0 : Nat) < 5
  decide

theorem zσ_belegt : belegt zσ 0 := by
  have h' : (if (0 : Nat) = 0 then (some () : Option Unit) else none) ≠ none := by
    simp
  exact h'

theorem zfeld_schreibstellen : schreibstellen_im_typ 5 zσ zfeld := by
  intro i d hb hd
  have hi0 : i = 0 := by
    by_cases hne : i = 0
    · exact hne
    · have hb' : (if i = 0 then (some () : Option Unit) else none) ≠ none := hb
      rw [if_neg hne] at hb'
      exact absurd rfl hb'
  subst hi0
  have hd' : (if (0 : Nat) = 0 then (some 2 : Option Nat) else none) = some d := hd
  rw [if_pos rfl] at hd'
  have hd2 : d = 2 := (Option.some_inj.mp hd').symm
  subst hd2
  show (2 : Nat) < 5
  decide

theorem belegt_liegt_im_indextyp_zeuge : indextyp 5 0 :=
  belegt_liegt_im_indextyp zσ_wohlgeformt zσ_belegt

theorem indextyp_deckt_nicht_nur_belegte_zeuge :
    ∃ σ : Nat → Option Unit, ∃ i,
      wohlgeformt 1 σ ∧ indextyp 1 i ∧ ¬ belegt σ i :=
  indextyp_deckt_nicht_nur_belegte (by decide)

theorem kette_bleibt_im_typ_zeuge : 2 < 5 :=
  kette_bleibt_im_typ zfeld_schreibstellen zσ_belegt rfl

theorem im_bereich_folgt_aus_indexschranke_zeuge :
    (∀ d, zfeld 0 = some d → d < 5) ∧ (∀ d, zfeld 0 = some d → d < 5) :=
  im_bereich_folgt_aus_indexschranke zfeld_schreibstellen
    zfeld_schreibstellen zσ_belegt

end Gabbro.Grammatik.TableIndexschranke
