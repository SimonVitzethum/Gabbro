module

public import Core.Annahme.Annahme
public import Core.Verfeinerung.Simulation

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog
open Gabbro.Core.Annahme (Akzeptiert)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Remaining local work is counted at the ideal head, even when the
    implementation is executing a different instruction of that unit. -/
def RegelStotterSchranke (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (f : F) : Prop :=
  ∀ (h : Umgebung) (ρ : Maschine.Lauf E) (η : Lauf E),
    Maschine.Laeufe E h ρ → Laufabgleich ρ η → BelegungGeprueft η →
    ∀ c a n, Stotterintervall η c f a n →
      zaehle (fun t => decide (η.belegt t = some c)) a n ≤ E.stotterLaenge f

structure RegelSimulation (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (f : F) : Prop where
  schritt : RegelSimSchritt E f
  stottern : RegelStotterSchranke E f

/-- The form-independent conditions needed at load, idle and asynchronous
    transitions, including authority on each unprojected implementation tick. -/
structure SimBasisPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) : Prop where
  abgleich : AbgleichBasis E
  autoritaet : ∀ h ρ, Maschine.Laeufe E h ρ → ∀ t, BerechtigungAmTakt ρ t
  fortsetzung : ∀ s i, Zustandsbezug E s i → FortsetzungsBezug E s i

theorem SimBasisPflichten.mit_formen (basis : SimBasisPflichten E)
    (formen : ∀ f, RegelSimulation E f) : SimPflichten E :=
  ⟨⟨basis.abgleich, fun f => (formen f).schritt,
    fun h ρ η run matched checked c f a n interval => (formen f).stottern h ρ η run matched checked c a n interval⟩,
    basis.autoritaet, basis.fortsetzung⟩

/-- The checked form and unit obligations give one ideal run for each run of an
    accepted unit. The proof uses the original hardware history, including unfair ones. -/
theorem sim_akzeptierter_lauf
    (akzeptiert : Akzeptiert E) (basis : Akzeptiert E → SimBasisPflichten E)
    (formen : Akzeptiert E → ∀ f, RegelSimulation E f)
    {h : Umgebung} {ρ : Maschine.Lauf E} (lauf : Maschine.Laeufe E h ρ) :
    ∃ η : Lauf E, Laeufe E η ∧ Sim E ρ η := by
  exact sim_im_lauf ((basis akzeptiert).mit_formen (formen akzeptiert)) lauf

/-- A zero budget rules out every marked tick of this head in the interval. -/
theorem RegelStotterSchranke.null {f : F} (null : E.stotterLaenge f = 0) :
    RegelStotterSchranke E f := by
  intro h ρ η run matched checked c a n interval
  rw [null]
  suffices count : zaehle (fun t => decide (η.belegt t = some c)) a n = 0 by
    exact Nat.le_of_eq count
  induction n with
  | zero => rfl
  | succ n ih =>
    have before : Stotterintervall η c f a n := fun t lower upper =>
      interval t lower (Nat.lt_trans upper (Nat.add_lt_add_left (Nat.lt_succ_self n) a))
    have head := (interval (a + n) (Nat.le_add_right a n)
      (Nat.add_lt_add_left (Nat.lt_succ_self n) a)).1
    have empty : η.belegt (a + n) ≠ some c := fun mark =>
      Nat.not_lt_zero 0 (null ▸ checked _ _ _ mark head)
    simp only [zaehle, ih before, decide_eq_false empty, Bool.false_eq_true, if_false, Nat.add_zero]

omit [DecidableEq L] in
theorem Zustandsbezug.gleich
    (lokal : E.lokalerBezug = Eq) {s i : Zustand L Ort Wert Raum Lok Grund}
    (bezug : Zustandsbezug E s i) : s = i := by
  obtain ⟨shared, localEq⟩ := bezug
  change { s with lokal := i.lokal } = i at shared
  rw [lokal] at localEq
  rw [← localEq] at shared
  exact shared

/-- A one-step form with equal local states replays the same executed plan. -/
theorem RegelSimSchritt.aus_gleicher_regel {f : F} (lokal : E.lokalerBezug = Eq)
    (regel : ∀ c s w plans u, (E.system.regel f).impl c s w plans u →
      (E.system.regel f).ideal c s w plans u) :
    RegelSimSchritt E f := by
  intro hw t c w s u s' i plan spur related normal bereit kopf impl execute
  have state := related.gleich lokal
  subst i
  exact Or.inl ⟨s', .kontext normal bereit ⟨f, kopf, regel c s w [plan] u impl⟩ execute,
    ProtokollBezug.refl _, lokal.symm ▸ rfl⟩

/-- With equal states and rules, an ideal transition at an unoccupied tick
    would give a concrete transition at the very same tick. -/
theorem SimBasisPflichten.aus_gleichen_regeln (lokal : E.lokalerBezug = Eq)
    (laden : ∀ h s, Hardware E.katalog h → E.ZulStart h s →
      E.laden s (h.lade E.bild) = some (start E s).2)
    (regel : ∀ f c s w plans u, (E.system.regel f).ideal c s w plans u →
      (E.system.regel f).impl c s w plans u)
    (autoritaet : ∀ f c s w plan u, (E.system.regel f).impl c s w [plan] u →
      plan.Autorisiert E.einrichtung s c) :
    SimBasisPflichten E := by
  have refl l : E.lokalerBezug l l := lokal.symm ▸ rfl
  refine ⟨⟨refl, fun h s hw zul => ⟨_, laden h s hw zul, ProtokollBezug.refl _, refl _⟩, ?_⟩, ?_, ?_⟩
  · intro hw t s i rel stuck label next step
    have same := rel.gleich lokal
    subst i
    cases step with
    | kontext normal ready rule execute =>
      obtain ⟨f, kopf, form⟩ := rule
      exact stuck _ _ (.schritt (.kontext normal ready ⟨f, kopf, regel _ _ _ _ _ _ form⟩ execute))
    | antwort normal arrives => exact stuck _ _ (.schritt (.antwort normal arrives))
    | interrupt normal enters => exact stuck _ _ (.schritt (.interrupt normal enters))
    | absturz crash => exact stuck _ _ (.schritt (.absturz crash))
  · intro h ρ run t s s' c w spur u p load after label normal ready rule execute
    obtain ⟨f, _, step⟩ := rule
    exact autoritaet f c s w p u step
  · intro s i related
    cases related.gleich lokal
    exact fun _ => ⟨rfl, Iff.rfl, fun _ => Iff.rfl⟩

end Gabbro.Core.Maschine.I
