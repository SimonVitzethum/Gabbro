module

public import Core.Maschine.Einheit
public import Core.Maschine.Schritte

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Relation

variable {S Ev : Type}

/-- Private implementation steps leave the ordered source observations unchanged. -/
def Privat (step : S → S → Prop) (s s' : S × List Ev) : Prop :=
  step s.1 s'.1 ∧ s'.2 = s.2

/-- An observable step appends its actual event. Commutation on these states preserves the
    entire observation sequence, including observations contributed by intervening contexts. -/
def Beobachtet (step : S → Ev → S → Prop) (s s' : S × List Ev) : Prop :=
  ∃ event, step s.1 event s'.1 ∧ s'.2 = s.2 ++ [event]

theorem rechts_folge {vor andere : S → S → Prop} (h : RechtsBeweger vor andere) :
    RechtsBeweger (ReflTransGen vor) (ReflTransGen andere) := by
  intro s l r hv ha
  induction hv generalizing r with
  | refl => exact ⟨r, ha, .refl⟩
  | tail _ last ih =>
    obtain ⟨m, ha', last'⟩ := rechts_vorbei h last ha
    obtain ⟨s', ha'', hv'⟩ := ih _ ha'
    exact ⟨s', ha'', hv'.tail last'⟩

theorem links_folge {nach andere : S → S → Prop} (h : LinksBeweger nach andere) :
    LinksBeweger (ReflTransGen nach) (ReflTransGen andere) := by
  intro s l r ha hn
  induction hn generalizing s with
  | refl => exact ⟨s, .refl, ha⟩
  | tail _ last ih =>
    obtain ⟨m, hn', ha'⟩ := ih _ ha
    obtain ⟨r', last', ha''⟩ := links_vorbei h ha' last
    exact ⟨r', hn'.tail last', ha''⟩

/-- Gather the prefix of the unit after all the steps interleaved before the linearisation point. -/
theorem vor_sammeln {vor andere : S → S → Prop} (h : RechtsBeweger vor andere) {s t : S}
    (path : ReflTransGen (fun a b => vor a b ∨ andere a b) s t) :
    ∃ m, ReflTransGen andere s m ∧ ReflTransGen vor m t := by
  induction path with
  | refl => exact ⟨s, .refl, .refl⟩
  | tail _ last ih =>
    obtain ⟨m, ha, hv⟩ := ih
    rcases last with own | other
    · exact ⟨m, ha, hv.tail own⟩
    · obtain ⟨m', ha', hv'⟩ := rechts_folge h _ _ _ hv (.single other)
      exact ⟨m', ha.trans ha', hv'⟩

/-- Gather the suffix of the unit before all the steps interleaved after the linearisation point. -/
theorem nach_sammeln {nach andere : S → S → Prop} (h : LinksBeweger nach andere) {s t : S}
    (path : ReflTransGen (fun a b => nach a b ∨ andere a b) s t) :
    ∃ m, ReflTransGen nach s m ∧ ReflTransGen andere m t := by
  induction path with
  | refl => exact ⟨s, .refl, .refl⟩
  | tail _ last ih =>
    obtain ⟨m, hn, ha⟩ := ih
    rcases last with own | other
    · obtain ⟨m', own', ha'⟩ := links_vorbei h ha own
      exact ⟨m', hn.tail own', ha'⟩
    · exact ⟨m, hn, ha.tail other⟩

/-- A complete unit consists of its private prefix, its single linearisation step and its private suffix. -/
def EinheitSchritt (vor nach : S → S → Prop) (punkt : S → Ev → S → Prop) (s : S) (event : Ev) (s' : S) : Prop :=
  ∃ l r, ReflTransGen vor s l ∧ punkt l event r ∧ ReflTransGen nach r s'

/-- The form's accounting proof admits the gathered unit as one ideal step with the same
    observation. Every other step stays on its original side of the linearisation point. -/
theorem linearisiert {vor nach andere : S → S → Prop} {punkt ideal : S → Ev → S → Prop}
    (comm : Kommutation vor nach andere)
    (regel : ∀ s event s', EinheitSchritt vor nach punkt s event s' → ideal s event s')
    {s l r s' : S} {event : Ev}
    (vorlauf : ReflTransGen (fun a b => vor a b ∨ andere a b) s l)
    (mitte : punkt l event r)
    (nachlauf : ReflTransGen (fun a b => nach a b ∨ andere a b) r s') :
    ∃ a b, ReflTransGen andere s a ∧ ideal a event b ∧ ReflTransGen andere b s' := by
  obtain ⟨a, ha, hv⟩ := vor_sammeln comm.vor_rechts vorlauf
  obtain ⟨b, hn, hb⟩ := nach_sammeln comm.nach_links nachlauf
  exact ⟨a, b, ha, regel _ _ _ ⟨l, r, hv, mitte, hn⟩, hb⟩

/-- A unit with disjoint interfering state admits a linearisation with both movers present. -/
theorem linearisierung_erfuellbar (f g : Nat → Nat) (s : Nat × Nat) :
    let own := fun (a b : Nat × Nat) => b = (f a.1, a.2)
    let other := fun (a b : Nat × Nat) => b = (a.1, g a.2)
    let point := fun (a : Nat × Nat) (_ : Unit) (b : Nat × Nat) => b = a
    Kommutation own own other ∧
      EinheitSchritt own own point s () (f (f s.1), s.2) :=
  ⟨kommutation_erfuellbar f g, ⟨(f s.1, s.2), (f s.1, s.2), .single rfl, rfl, .single rfl⟩⟩

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The same gathering theorem at the concrete ideal transition interface. A form discharges
    the unit rule at the hardware cut where its linearisation step occurs. -/
theorem linearisiert_in_I [DecidableEq L] (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (k : Katalog.Katalog) (hw : Katalog.HwLauf) (t : Nat)
    {vor nach andere : Zustand L Ort Wert Raum Lok Grund → Zustand L Ort Wert Raum Lok Grund → Prop}
    {punkt : Zustand L Ort Wert Raum Lok Grund → SchrittSpur Ort Wert → Zustand L Ort Wert Raum Lok Grund → Prop}
    (comm : Kommutation vor nach andere)
    (regel : ∀ s spur s', EinheitSchritt vor nach punkt s spur s' → Schritt e Sy k hw t s spur s')
    {s l r s' : Zustand L Ort Wert Raum Lok Grund} {spur : SchrittSpur Ort Wert}
    (vorlauf : ReflTransGen (fun a b => vor a b ∨ andere a b) s l)
    (mitte : punkt l spur r) (nachlauf : ReflTransGen (fun a b => nach a b ∨ andere a b) r s') :
    ∃ a b, ReflTransGen andere s a ∧ Schritt e Sy k hw t a spur b ∧ ReflTransGen andere b s' :=
  linearisiert comm regel vorlauf mitte nachlauf

end Gabbro.Core.Maschine.I
