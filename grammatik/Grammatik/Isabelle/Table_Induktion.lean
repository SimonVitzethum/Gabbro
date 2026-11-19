/-
  File:      Grammatik/Isabelle/Table_Induktion.lean
  Part of:   Gabbro -- Lean port of `grammatik/Beweise/Table_Induktion.thy`
             (template `table.induktion`, S4; lane 168).

  What this file is: the induction schema the generator owes, in the
  sharpened form with side conditions N-1 to N-4 standing separately.
  Well-foundedness is a HYPOTHESIS, not a result (the declaration must
  name the carrying invariant); the base case is absorbed (no separate
  empty-set clause); the generator writes TWO premises out of `kante`,
  one per field; and finiteness does NOT fall out of this declaration --
  it needs the index bound from `Table_Indexschranke` (S12).

  Model notes: the `slot` record is a Lean structure; `kante` is a
  relation `Nat -> Nat -> Prop` (Isabelle `(idx x idx) set`);
  `wf (kante σ)` is `WellFounded (kante σ)`; `im_bereich` (an Isabelle
  `bool`) is a `Prop`; finiteness is the explicit-bound-list `Endlich`
  from `Table_Indexschranke` (restated here to keep the file
  self-contained).

  No bridge to the model semantics: the schema is about the generator's
  induction principle over its own slot model, which has no counterpart
  in `Semantik.lean`.
-/

module

@[expose] public section

namespace Gabbro.Grammatik.TableInduktion

set_option linter.unusedVariables false

/-- A `table T count N` slot with two link fields. -/
structure Slot where
  first_child : Option Nat
  next_sibling : Option Nat

/-- The table state: an index maps to a slot; `none` means unoccupied. -/
abbrev Tabelle : Type :=
  Nat → Option Slot

/-- The primitive edge, with TWO kinds (N-4): one per field. `(d, s)` in
    Isabelle is `kante σ d s` here. -/
def kante (σ : Tabelle) : Nat → Nat → Prop :=
  fun d s =>
    (∃ sl, σ s = some sl ∧ sl.first_child = some d) ∨
    (∃ sl, σ s = some sl ∧ sl.next_sibling = some d)

/-- The generated schema, the one line the generator gets:
    well-foundedness as hypothesis, the step, and the conclusion. -/
theorem table_induktion {σ : Tabelle} {P : Nat → Prop} {s : Nat}
    (wf : WellFounded (kante σ))
    (schritt : ∀ s, (∀ d, kante σ d s → P d) → P s) : P s :=
  wf.induction s schritt

/-- N-3: the base case is ABSORBED. For a leaf the premise holds
    vacuously; no separate empty-set clause is needed. -/
theorem blatt_ohne_eigene_klausel {σ : Tabelle} {P : Nat → Prop} {s : Nat}
    (wf : WellFounded (kante σ))
    (schritt : ∀ s, (∀ d, kante σ d s → P d) → P s)
    (blatt : ∀ d, ¬ kante σ d s) : P s := by
  have h : ∀ d, kante σ d s → P d := fun d hd => absurd hd (blatt d)
  exact schritt s h

/-- N-4: the generator writes TWO premises out of `kante`, one per
    field, plus the empty-slot case. -/
theorem table_induktion_zwei_kanten {σ : Tabelle} {P : Nat → Prop} {s : Nat}
    (wf : WellFounded (kante σ))
    (kind : ∀ s sl, σ s = some sl →
      (∀ d, sl.first_child = some d → P d) →
      (∀ d, sl.next_sibling = some d → P d) → P s)
    (leer : ∀ s, σ s = none → P s) : P s := by
  refine table_induktion (s := s) wf (fun s ih => ?_)
  cases hs : σ s with
  | none => exact leer s hs
  | some sl =>
    have h1 : ∀ d, sl.first_child = some d → P d := by
      intro d hd
      apply ih d
      exact Or.inl ⟨sl, hs, hd⟩
    have h2 : ∀ d, sl.next_sibling = some d → P d := by
      intro d hd
      apply ih d
      exact Or.inr ⟨sl, hs, hd⟩
    exact kind s sl hs h1 h2

/-- N-1: the range condition -- link fields stay inside the table.
    Exactly `schreibstellen_im_typ` over two fields; owed by S12. -/
def im_bereich (N : Nat) (σ : Tabelle) : Prop :=
  ∀ s sl, σ s = some sl →
    (∀ d, sl.first_child = some d → d < N) ∧
    (∀ d, sl.next_sibling = some d → d < N)

theorem kante_bleibt_im_bereich {N : Nat} {σ : Tabelle} {d s : Nat}
    (hbm : im_bereich N σ) (hks : kante σ d s) : d < N := by
  rcases hks with ⟨sl, hs, hd⟩ | ⟨sl, hs, hd⟩
  · exact (hbm s sl hs).1 d hd
  · exact (hbm s sl hs).2 d hd

/-- Finiteness, stated with an explicit bound list (no set library). -/
def Endlich (p : Nat → Prop) : Prop :=
  ∃ l : List Nat, ∀ i, p i → i ∈ l

theorem traeger_endlich {N : Nat} {σ : Tabelle}
    (hbm : im_bereich N σ) : Endlich (fun d => ∃ s, kante σ d s) := by
  refine ⟨List.range N, fun _d hd => List.mem_range.mpr ?_⟩
  obtain ⟨s, hks⟩ := hd
  exact kante_bleibt_im_bereich hbm hks

/-! ## Witnesses: the empty table instantiates every syntax premise.

Over the empty table the edge relation is empty (hence well-founded),
every slot case is vacuous, and `im_bereich` holds trivially. -/

/-- The witness table: nothing occupied. -/
def zσ : Tabelle :=
  fun _ => none

theorem zσ_kante_leer (d s : Nat) : ¬ kante zσ d s := by
  intro h
  rcases h with ⟨sl, hs, _⟩ | ⟨sl, hs, _⟩
  · have hs' : (none : Option Slot) = some sl := hs
    cases hs'
  · have hs' : (none : Option Slot) = some sl := hs
    cases hs'

theorem zσ_wf : WellFounded (kante zσ) :=
  WellFounded.intro fun a => Acc.intro a (fun y hy => absurd hy (zσ_kante_leer y a))

theorem zσ_im_bereich (N : Nat) : im_bereich N zσ := by
  intro s sl hs
  have hs' : (none : Option Slot) = some sl := hs
  cases hs'

/-! ## Satisfiability of the well-foundedness premise (stream E12) -/

/-- Two occupied slots: slot 0 has slot 1 as its first child, slot 1 is a leaf. -/
def zweiKnoten : Tabelle := fun i =>
  if i = 0 then some ⟨some 1, none⟩ else if i = 1 then some ⟨none, none⟩ else none

theorem kante_zweiKnoten {d s : Nat} (h : kante zweiKnoten d s) : s = 0 ∧ d = 1 := by
  rcases h with ⟨sl, hs, hd⟩ | ⟨sl, hs, hd⟩
  · unfold zweiKnoten at hs
    split at hs
    · cases hs
      cases hd
      exact ⟨by assumption, rfl⟩
    · split at hs
      · cases hs
        cases hd
      · cases hs
  · unfold zweiKnoten at hs
    split at hs
    · cases hs
      cases hd
    · split at hs
      · cases hs
        cases hd
      · cases hs

/-- **Satisfiability of the well-foundedness premise**: the edge relation of a table with a real parent-child edge
    is well founded, so `table_induktion` and its relatives are not instantiated vacuously. -/
theorem table_induktion_erfuellbar : ∃ σ : Tabelle, WellFounded (kante σ) ∧ ∃ d s, kante σ d s := by
  refine ⟨zweiKnoten, ?_, 1, 0, Or.inl ⟨_, rfl, rfl⟩⟩
  have smaller : ∀ d s, kante zweiKnoten d s →
      (fun n : Nat => if n = 0 then 1 else 0) d < (fun n : Nat => if n = 0 then 1 else 0) s := by
    intro d s h
    obtain ⟨hs, hd⟩ := kante_zweiKnoten h
    subst hs
    subst hd
    decide
  exact Subrelation.wf (fun {d s} h => smaller d s h) (InvImage.wf _ Nat.lt_wfRel.wf)

end Gabbro.Grammatik.TableInduktion
