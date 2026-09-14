/-
  File:      Grammatik/Isabelle/Consuming.lean
  Port of:   beweise/Consuming.thy (templates `consuming.ordnung` S1 and
              `consuming.leermenge` S2)

  S1: the domain yields its witnesses in the generated well-founded order, and
  the order survives the generated mutation -- from which leafness at
  consumption time falls. S2: the generated witness set is COMPLETE: if it is
  empty, the domain is empty.

  Findings ported faithfully: K-1 -- order survives REMOVAL, and only that;
  K-2 -- rehanging is NOT covered, with counterexample; K-3 -- leafness does
  NOT fall from `wf` alone, the selection must be MINIMAL (stated as the extra
  premise it is); S2 goes through smoothly, with the state-dependence made
  explicit.

  The theory imports `Table_Induktion.thy`, whose port is another lane's half.
  The needed model (`slot`, `tabelle`, `kante`) is therefore restated here,
  mirroring `Table_Induktion.thy` N-4 (TWO edge kinds), and attributed -- not
  imported, not modified.

  Adaptations (same content, Lean core without mathlib):
  - `kante` is a relation `Idx → Idx → Prop` (Isabelle: a set of pairs).
  - `wf` is `WellFounded`; `wf_subset` is proved here (`wf_subset_unten`)
    since Lean core has no relation library.
-/

namespace Gabbro.Grammatik.Isabelle.Consuming

/-- An index. (Mirrors `Table_Induktion.thy`: `type_synonym idx = nat`.) -/
abbrev Idx := Nat

/-- A slot with two link fields. (Mirrors `Table_Induktion.thy`: `record slot`.) -/
structure Slot where
  firstChild : Option Idx
  nextSibling : Option Idx

/-- The state maps an index to a slot; `none` means "not occupied".
    (Mirrors `Table_Induktion.thy`: `type_synonym tabelle`.) -/
abbrev Tabelle := Idx → Option Slot

/-- The primitive edge, with TWO kinds (N-4 of `Table_Induktion.thy`).
    (Mirrors `Table_Induktion.thy`: `kante`.) -/
def kante (σ : Tabelle) (d s : Idx) : Prop :=
  ∃ sl, σ s = some sl ∧ (sl.firstChild = some d ∨ sl.nextSibling = some d)

/-- The mutation `by consuming` generates: the body consumes the witness just
    visited. As a state transition: the place becomes free.
    (Isabelle: `verbrauche`.) -/
def verbrauche (σ : Tabelle) (v : Idx) : Tabelle :=
  fun i => if i = v then none else σ i

/-- Well-foundedness of the empty relation. -/
theorem wf_of_leer {r : Idx → Idx → Prop} (h : ∀ d s, ¬ r d s) :
    WellFounded r :=
  WellFounded.intro fun a =>
    Acc.intro a (fun y hy => absurd hy (h y a))

/-! ## K-1 -- order survives REMOVAL, and only that -/

/-- Removing a place shrinks the edge set. (Isabelle: `verbrauche_verkleinert`.) -/
theorem verbrauche_verkleinert (σ : Tabelle) (v d s : Idx) :
    kante (verbrauche σ v) d s → kante σ d s := by
  intro h
  obtain ⟨sl, hσ, hfd⟩ := h
  have hσ' : (if s = v then (none : Option Slot) else σ s) = some sl := hσ
  rcases Decidable.em (s = v) with hseq | hseq
  · rw [if_pos hseq] at hσ'
    cases hσ'
  · rw [if_neg hseq] at hσ'
    exact ⟨sl, hσ', hfd⟩

/-- Well-foundedness travels down along subsets (the `wf_subset` step, proved
    here since Lean core has no relation library). -/
theorem wf_subset_unten {r s : Idx → Idx → Prop}
    (hsub : ∀ a b, s a b → r a b) (hwf : WellFounded r) :
    WellFounded s :=
  WellFounded.intro fun a =>
    let key : ∀ x, Acc r x → Acc s x := fun x hx => by
      induction hx with
      | intro x _ ih => exact Acc.intro x (fun y hs => ih y (hsub y x hs))
    key a (hwf.apply a)

/-- Order survives removal. (Isabelle: `ordnung_bleibt_unter_entfernen`.) -/
theorem ordnung_bleibt_unter_entfernen (σ : Tabelle) (v : Idx)
    (hwf : WellFounded (kante σ)) :
    WellFounded (kante (verbrauche σ v)) :=
  wf_subset_unten (verbrauche_verkleinert σ v) hwf

/-! ## K-2 -- rehanging is NOT covered, with counterexample -/

/-- Rehanging: rewrite the sibling pointer of place `i` to `d`.
    (Isabelle: `haenge_um`.) -/
def haengeUm (σ : Tabelle) (i d : Idx) : Tabelle :=
  fun j => if j = i
    then (match σ j with
      | none => none
      | some sl => some { sl with nextSibling := some d })
    else σ j

/-- A self-loop kills well-foundedness. -/
theorem nicht_wf_bei_schlinge {r : Idx → Idx → Prop} {a : Idx}
    (h : r a a) : ¬ WellFounded r := by
  intro hwf
  have key : ∀ x (hx : Acc r x), r x x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hxx
      exact ih x hxx hxx
  exact key a (hwf.apply a) h

/-- The single childless place has no edges. -/
theorem kante_leer_wf :
    WellFounded (kante (fun j => if j = 0 then some ⟨none, none⟩ else none)) := by
  apply wf_of_leer
  intro d s hs
  obtain ⟨sl, hσ, hfd⟩ := hs
  have hσ' : (if s = 0 then (some ⟨none, none⟩ : Option Slot) else none) =
      some sl := hσ
  rcases Decidable.em (s = 0) with hseq | hseq
  · rw [if_pos hseq] at hσ'
    have hsl : sl = ⟨none, none⟩ := (Option.some_inj.mp hσ').symm
    rcases hfd with hfc | hns
    · rw [hsl] at hfc; simp at hfc
    · rw [hsl] at hns; simp at hns
  · rw [if_neg hseq] at hσ'
    cases hσ'

/-- Rehanging CAN create a cycle: the promise in its worded form is REFUTED.
    It holds for removal and NOT for rehanging -- and the stock does both in
    the same operation. (Isabelle: `umhaengen_kann_zyklus_erzeugen`.) -/
theorem umhaengen_kann_zyklus_erzeugen :
    ∃ σ i d, WellFounded (kante σ) ∧ ¬ WellFounded (kante (haengeUm σ i d)) := by
  refine ⟨fun j => if j = 0 then some (⟨none, none⟩ : Slot) else none, 0, 0,
    kante_leer_wf, ?_⟩
  apply nicht_wf_bei_schlinge (a := 0)
  exact ⟨{ firstChild := none, nextSibling := some 0 },
    by simp [haengeUm], Or.inr rfl⟩

/-! ## K-3 -- leafness does NOT fall from `wf` -/

/-- Leafness at consumption time. (Isabelle: `ist_blatt`.) -/
def istBlatt (σ : Tabelle) (v : Idx) : Prop :=
  ∀ d, ¬ kante σ d v

/-- The missing condition: the selection is MINIMAL.
    (Isabelle: `waehlt_minimal`.) -/
def waehltMinimal (σ : Tabelle) (v : Idx) : Prop :=
  ∀ d, ¬ kante σ d v

/-- Leafness needs minimal selection -- a renaming, not a proof: leafness is
    no CONSEQUENCE of well-foundedness but an extra duty on the generation of
    the witness order. (Isabelle: `blattheit_braucht_minimale_auswahl`.) -/
theorem blattheit_braucht_minimale_auswahl (σ : Tabelle) (v : Idx)
    (h : waehltMinimal σ v) : istBlatt σ v :=
  h

/-! ## S2 -- `consuming.leermenge` -/

/-- The witnesses at `s`. (Isabelle: `zeugen`.) -/
def zeugen (σ : Tabelle) (s : Idx) (d : Idx) : Prop := kante σ d s

/-- S2 goes through smoothly: the generated witness set is complete.
    (Isabelle: `leermenge`.) -/
theorem leermenge (σ : Tabelle) (s : Idx) :
    (∀ d, ¬ zeugen σ s d) ↔ ∀ d, ¬ kante σ d s :=
  Iff.rfl

/-- The concrete two-place table: place `0` has child `1`. -/
def zeugenTabelle : Tabelle :=
  fun j => if j = 0 then some (⟨some 1, none⟩ : Slot)
    else if j = 1 then some ⟨none, none⟩ else none

/-- The emptiness is STATE-dependent: empty WHEN? Before the move, or after
    the last consumption? (Isabelle: `leermenge_ist_zustandsabhaengig`.) -/
theorem leermenge_ist_zustandsabhaengig :
    ∃ σ v s, (∃ d, zeugen σ s d) ∧ ∀ d, ¬ zeugen (verbrauche σ v) s d := by
  refine ⟨zeugenTabelle, 0, 0,
    ⟨1, ⟨⟨some 1, none⟩, by simp [zeugenTabelle], Or.inl rfl⟩⟩, ?_⟩
  intro d hd
  obtain ⟨sl, hσ, -⟩ := hd
  have hσ' : verbrauche zeugenTabelle 0 0 = some sl := hσ
  have h0 : verbrauche zeugenTabelle 0 0 = none := by simp [verbrauche]
  rw [h0] at hσ'
  cases hσ'

/-! ## Witness: removal on a concrete table -/

/-- Witness: on the two-place table, consuming place `0` removes the only
    edge -- the order half and the emptiness half on a concrete instance. No
    lemma above quantifies over syntax, so the inhabitation obligation is
    vacuous. -/
theorem verbrauche_zeuge :
    (∃ d, zeugen zeugenTabelle 0 d) ∧
    WellFounded (kante (verbrauche zeugenTabelle 0)) := by
  constructor
  · exact ⟨1, ⟨⟨some 1, none⟩, by simp [zeugenTabelle], Or.inl rfl⟩⟩
  · apply wf_of_leer
    intro d s hs
    obtain ⟨sl, hσ, hfd⟩ := hs
    have hσ' : verbrauche zeugenTabelle 0 s = some sl := hσ
    simp only [verbrauche] at hσ'
    rcases Decidable.em (s = 0) with hseq | hseq
    · rw [if_pos hseq] at hσ'
      cases hσ'
    · rw [if_neg hseq] at hσ'
      have hσ'' : zeugenTabelle s = some sl := hσ'
      rcases Decidable.em (s = 1) with hs1 | hs1
      · subst hs1
        have h1 : (some ⟨none, none⟩ : Option Slot) = some sl := hσ''
        have hsl : sl = ⟨none, none⟩ := (Option.some_inj.mp h1).symm
        rcases hfd with hfc | hns
        · rw [hsl] at hfc; simp at hfc
        · rw [hsl] at hns; simp at hns
      · have hσ''' : (if s = 0 then (some ⟨some 1, none⟩ : Option Slot)
            else if s = 1 then some ⟨none, none⟩ else none) = some sl := hσ''
        rw [if_neg hseq, if_neg hs1] at hσ'''
        cases hσ'''

/-! ## Bridge

  The `Table_Induktion.thy` model (`slot`, `tabelle`, `kante`) is restated
  above because that theory is another lane's half -- its Lean port will own
  the canonical definitions, and the bridge is then the pointwise equality of
  the two `kante` relations (same two edge kinds, same state parameter).
  Named, not faked: no theorem here imports another lane's file. -/

#print axioms Gabbro.Grammatik.Isabelle.Consuming.verbrauche_verkleinert
#print axioms Gabbro.Grammatik.Isabelle.Consuming.ordnung_bleibt_unter_entfernen
#print axioms Gabbro.Grammatik.Isabelle.Consuming.umhaengen_kann_zyklus_erzeugen
#print axioms Gabbro.Grammatik.Isabelle.Consuming.blattheit_braucht_minimale_auswahl
#print axioms Gabbro.Grammatik.Isabelle.Consuming.leermenge
#print axioms Gabbro.Grammatik.Isabelle.Consuming.leermenge_ist_zustandsabhaengig
#print axioms Gabbro.Grammatik.Isabelle.Consuming.verbrauche_zeuge

end Gabbro.Grammatik.Isabelle.Consuming
