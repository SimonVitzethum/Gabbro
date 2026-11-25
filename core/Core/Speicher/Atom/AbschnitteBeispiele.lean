/-
  File:      core/Core/Speicher/Atom/AbschnitteBeispiele.lean
  Subject:   THE LOCK-SECTION STATEMENT IS SATISFIABLE AND NOT TRIVIAL (MK-04).
             * `rennfreiAusLokal_erfuellbar`: two threads each take the lock word (an acquire read), write the plain `x` and
               release the lock word (a release write); the second acquire reads the first release. Every premise of
               `Abschnitte` holds, the two plain writes conflict, and `rennfrei_aus_abschnitten` orders them.
             * `rennfreiAusLokal_nichtTrivial`: WITHOUT the lock, two threads write the plain `x` and nothing orders
               them: the graph is consistent (a run of the memory model), it has a race, and no guard map and no
               windows can make it satisfy the discipline. The memory model represents the racy program; only the
               checker's lock rule excludes it.
-/
module

public import Core.Speicher.Atom.Abschnitte

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Atom

/-! ### The graph without a lock -/

/-- Two plain writes of the same location by two threads, ordered by nothing; the modification order puts the
    second after the first. -/
@[reducible] def rennGraph : Graph Bool Bool Nat :=
  ⟨fun _ => ⟨.schreiben, false, .na, 0, 1⟩, fun _ _ => False, fun _ _ => False,
    fun a b => a = false ∧ b = true⟩

theorem rennGraph_wf : rennGraph.Wohlgeformt where
  po_trans := fun _ _ _ h _ => False.elim h
  po_irrefl := fun _ h => h
  rf_schreibt := fun _ _ h => False.elim h
  rf_liest := fun _ _ h => False.elim h
  rf_ort := fun _ _ h => False.elim h
  rf_wert := fun _ _ h => False.elim h
  rf_eindeutig := fun _ _ _ h => False.elim h
  mo_schreibt := fun _ _ _ => ⟨trivial, trivial⟩
  mo_ort := fun _ _ _ => rfl
  mo_trans := by
    intro a b c
    show (a = false ∧ b = true) → (b = false ∧ c = true) → (a = false ∧ c = true)
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ (a = false ∧ a = true)
    cases a <;> decide
  mo_total := by
    intro a b _ _ _ hne
    show (a = false ∧ b = true) ∨ (b = false ∧ a = true)
    cases a <;> cases b <;> first | decide | exact absurd rfl hne

/-- Nothing in this graph synchronises, so nothing happens before anything. -/
theorem rennGraph_hb (a b : Bool) : ¬ rennGraph.hb a b := by
  intro h
  obtain ⟨c, hc⟩ := transGen_kopf h
  rcases hc with hpo | hsw
  · exact hpo
  · obtain ⟨w, x, r, _, _, hrf, _⟩ := hsw
    exact False.elim hrf

theorem rennGraph_konsistent : rennGraph.Konsistent where
  wf := rennGraph_wf
  hb_irrefl := fun a h => rennGraph_hb a a h
  kohaerent := fun a b h _ => rennGraph_hb a b h
  atomar := fun _ _ _ h => False.elim h
  liest_vorher := fun _ _ h => False.elim h
  psc := fun a h => by
    obtain ⟨_, hk⟩ := transGen_kopf h
    have na : Modus.na = Modus.sc := Graph.psc_sc_links hk
    cases na
  ohneLB := fun a h => by
    obtain ⟨_, hk⟩ := transGen_kopf h
    rcases hk with hk | hk <;> exact hk

theorem rennGraph_nicht_rennfrei : ¬ rennGraph.RennfreiAuf (fun _ => True) := by
  intro h
  rcases h false true trivial trivial ⟨by decide, rfl, Or.inl trivial⟩ (Or.inl rfl) with hb | hb <;>
    exact rennGraph_hb _ _ hb

/-! ### The graph with the lock -/

/-- Thread 1: `a1` (acquire the lock word), `w1` (plain write of `x`), `b1` (release the lock word). Thread 2:
    `a2`, `w2`, `b2`; the acquire `a2` reads the release `b1`. -/
inductive AbEv where
  | a1
  | w1
  | b1
  | a2
  | w2
  | b2
  deriving DecidableEq, Repr

open AbEv

/-- Location `false` is the plain `x`, location `true` the lock word. -/
def abLab : AbEv → Etikett Bool Nat
  | a1 => ⟨.lesen, true, .ra, 0, 0⟩
  | w1 => ⟨.schreiben, false, .na, 0, 1⟩
  | b1 => ⟨.schreiben, true, .ra, 0, 1⟩
  | a2 => ⟨.lesen, true, .ra, 1, 0⟩
  | w2 => ⟨.schreiben, false, .na, 1, 2⟩
  | b2 => ⟨.schreiben, true, .ra, 1, 2⟩

@[reducible] def abPo (a b : AbEv) : Prop :=
  (a = a1 ∧ b = w1) ∨ (a = a1 ∧ b = b1) ∨ (a = w1 ∧ b = b1) ∨
    (a = a2 ∧ b = w2) ∨ (a = a2 ∧ b = b2) ∨ (a = w2 ∧ b = b2)

@[reducible] def abRf (a b : AbEv) : Prop := a = b1 ∧ b = a2

@[reducible] def abMo (a b : AbEv) : Prop := (a = w1 ∧ b = w2) ∨ (a = b1 ∧ b = b2)

@[reducible] def abGraph : Graph AbEv Bool Nat := ⟨abLab, abPo, abRf, abMo⟩

/-- The only lock window shapes of this graph: `(a1, b1)` and `(a2, b2)`, of the lock word. -/
theorem abFenster_eindeutig {l : Bool} {a b : AbEv} (f : abGraph.Fenster l a b) :
    l = true ∧ ((a = a1 ∧ b = b1) ∨ (a = a2 ∧ b = b2)) := by
  have hp : abPo a b := f.po
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim f.frei_stark
  · exact ⟨f.erwerb_ort.symm, Or.inl ⟨rfl, rfl⟩⟩
  · exact False.elim f.erwerb_liest
  · exact False.elim f.frei_stark
  · exact ⟨f.erwerb_ort.symm, Or.inr ⟨rfl, rfl⟩⟩
  · exact False.elim f.erwerb_liest

theorem abFenster₁ : abGraph.Fenster true a1 b1 :=
  ⟨trivial, trivial, rfl, trivial, trivial, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem abFenster₂ : abGraph.Fenster true a2 b2 :=
  ⟨trivial, trivial, rfl, trivial, trivial, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩

/-- The lock word `true` guards the plain location `false`. -/
def abSchloss : Bool → Option Bool
  | false => some true
  | true => none

/-- The first release hands over to the second acquire. -/
theorem abUebergabe : abGraph.Uebergabe b1 a2 :=
  ⟨b1, .selbst trivial (Modus.stark_atomar trivial), ⟨rfl, rfl⟩⟩

theorem abAbschnitte : abGraph.Abschnitte abSchloss (fun _ => True) where
  geschuetzt := by
    intro i _ hna
    have hna' : (abLab i).modus = .na := hna
    cases i <;> first | exact ⟨true, rfl⟩ | exact absurd hna' (by decide)
  fenster := by
    intro i _ l hl
    cases i with
    | w1 =>
      have : l = true := (Option.some.inj hl).symm
      subst this
      exact ⟨a1, b1, abFenster₁, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | w2 =>
      have : l = true := (Option.some.inj hl).symm
      subst this
      exact ⟨a2, b2, abFenster₂, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩
    | a1 => cases hl
    | b1 => cases hl
    | a2 => cases hl
    | b2 => cases hl
  ausschluss := by
    intro l c₁ d₁ c₂ d₂ f₁ f₂
    obtain ⟨_, h1⟩ := abFenster_eindeutig f₁
    obtain ⟨_, h2⟩ := abFenster_eindeutig f₂
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl abUebergabe)
    · exact Or.inr (Or.inr abUebergabe)
    · exact Or.inl ⟨rfl, rfl⟩
  innerhalb := by
    intro l c d i j f hai hib haj hjb _ _
    obtain ⟨_, hw⟩ := abFenster_eindeutig f
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 : abPo a1 i := hai
      have h2 : abPo i b1 := hib
      have h3 : abPo a1 j := haj
      have h4 : abPo j b1 := hjb
      clear hai hib haj hjb
      revert h1 h2 h3 h4
      cases i <;> cases j <;> first
        | (intro _ _ _ _; exact Or.inl rfl)
        | (intro x _ _ _; exact absurd x (by decide))
        | (intro _ x _ _; exact absurd x (by decide))
        | (intro _ _ x _; exact absurd x (by decide))
        | (intro _ _ _ x; exact absurd x (by decide))
    · have h1 : abPo a2 i := hai
      have h2 : abPo i b2 := hib
      have h3 : abPo a2 j := haj
      have h4 : abPo j b2 := hjb
      clear hai hib haj hjb
      revert h1 h2 h3 h4
      cases i <;> cases j <;> first
        | (intro _ _ _ _; exact Or.inl rfl)
        | (intro x _ _ _; exact absurd x (by decide))
        | (intro _ x _ _; exact absurd x (by decide))
        | (intro _ _ x _; exact absurd x (by decide))
        | (intro _ _ _ x; exact absurd x (by decide))

end Atom

/-- **The premises of the lock-section statement hold jointly, and the conclusion bites**: two conflicting plain
    writes, each in a window of the lock, are ordered by happens-before. -/
theorem rennfreiAusLokal_erfuellbar :
    ∃ (G : Graph Atom.AbEv Bool Nat) (schloss : Bool → Option Bool),
      G.Abschnitte schloss (fun _ => True) ∧
        G.Konflikt Atom.AbEv.w1 Atom.AbEv.w2 ∧ G.na Atom.AbEv.w1 ∧
          (G.hb Atom.AbEv.w1 Atom.AbEv.w2 ∨ G.hb Atom.AbEv.w2 Atom.AbEv.w1) :=
  ⟨Atom.abGraph, Atom.abSchloss, Atom.abAbschnitte, ⟨by decide, rfl, Or.inl trivial⟩, rfl,
    Graph.rennfrei_aus_abschnitten Atom.abAbschnitte _ _ trivial trivial
      ⟨by decide, rfl, Or.inl trivial⟩ (Or.inl rfl)⟩

/-- **Without the lock the statement is false.** There is a consistent graph with two conflicting plain accesses
    that nothing orders; no guard map makes it satisfy the lock discipline. -/
theorem rennfreiAusLokal_nichtTrivial :
    ∃ (G : Graph Bool Bool Nat), G.Konsistent ∧
      (∀ schloss : Bool → Option Bool, ¬ G.Abschnitte schloss (fun _ => True)) ∧
        ¬ G.RennfreiAuf (fun _ => True) :=
  ⟨Atom.rennGraph, Atom.rennGraph_konsistent,
    fun _ d => Atom.rennGraph_nicht_rennfrei (Graph.rennfrei_aus_abschnitten d),
    Atom.rennGraph_nicht_rennfrei⟩

end Gabbro.Core.Speicher
