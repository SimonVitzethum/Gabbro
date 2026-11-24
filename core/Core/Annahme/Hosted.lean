module

public import Core.Annahme.AussenLauf
public import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Annahme.Hosted

open Katalog Maschine Beobachtung

abbrev Modell := Einheit Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit
abbrev Zustand := Maschine.Zustand Unit Unit Unit Unit (Option Handle) Unit
abbrev Plan := SchrittPlan Unit Unit Unit Unit
abbrev Spur := SchrittSpur Unit Unit

def kontext : Kontext := .faden 0
def griff : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
def frage : Frage := ⟨.hosted, griff, [], .read⟩

def bindePlan : Plan := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
def fragePlan : Plan := { bindePlan with aktion := .frage frage }

def binde (s : Zustand) : Zustand :=
  { s with
    lokal := fun _ => none
    buchung := { s.buchung with
      aussengriff := fun c h r => s.buchung.aussengriff c h r ∨ (c = kontext ∧ h = griff ∧ r = .read) } }

def warte (s : Zustand) : Zustand := { s with status := fun _ => .ruht }

def regel (c : Kontext) (s : Zustand) (_ : Unit) (plans : List Plan) (u : Zustand) : Prop :=
  c = kontext ∧
    ((plans = [bindePlan] ∧ s.lokal c = some griff ∧ u = binde s) ∨
     (plans = [fragePlan] ∧ AussengriffeEigen s c frage ∧ u = warte s))

def daten (g : Option Handle) : Startdaten Unit Unit (Option Handle) Unit :=
  ⟨fun _ => g, fun _ => .laeuft,
    fun _ => ⟨some kontext, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩

def startDaten (s : AussenStart) : Startdaten Unit Unit (Option Handle) Unit :=
  daten (s.outside.channels .hosted 0)

def einrichtung : Einrichtung Unit Unit Unit Unit (Option Handle) Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False, fun _ _ => True,
    ⟨0, 1⟩, ⟨kontext, 0, fun _ => daten none, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩

def startZustand (s : AussenStart) : Zustand :=
  let d := startDaten s
  Maschine.Zustand.start d.lokal d.status d.kerne d.rechte einrichtung.initial (.leer (fun _ => 0))

def hoch : Etikett := {0}

def einheit : Modell where
  katalog := Plattform.x86_64.katalog
  bild := Sicherheit.Laufkonstruktion.bild
  einrichtung := einrichtung
  system := ⟨fun _ => ⟨regel, regel⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩
  startdaten := startDaten
  startmedium := fun _ _ => 0
  laden := fun s _ => some (startZustand s)
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := .leer
  etiketten := { endpunkt := fun _ => hoch, objekt := fun _ => hoch }

theorem ausgewaehlt : einheit.katalog.enthaelt (.endpoint frage.endpoint) := by
  change Plattform.x86_64.katalog.enthaelt (.endpoint .hosted)
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map_of_mem
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem eigene_frage (s : Zustand) : AussengriffeEigen (binde s) kontext frage := by
  intro z mem
  change z ∈ [⟨griff, .read⟩] at mem
  cases List.mem_singleton.mp mem
  exact Or.inr ⟨rfl, rfl, rfl⟩

private theorem binden_offen {s : Zustand} {g} (offen : OffeneGriffeEigen s) :
    OffeneGriffeEigen { binde s with graph := g } := by
  intro ev mem epoche unbeantwortet
  obtain ⟨c, id, eig⟩ := offen ev mem epoche unbeantwortet
  exact ⟨c, id, fun z h => Or.inl (eig z h)⟩

private theorem fragen_offen {s : Zustand} {t c g} (rechte : AussengriffeEigen s c frage)
    (offen : OffeneGriffeEigen s) :
    OffeneGriffeEigen { (warte s).frage (s.stelleFrage t c frage) with graph := g } := by
  intro ev mem epoche unbeantwortet
  change ev ∈ s.fragen ++ [s.stelleFrage t c frage] at mem
  rw [List.mem_append, List.mem_singleton] at mem
  rcases mem with bisher | rfl
  · exact offen ev bisher epoche unbeantwortet
  · exact ⟨c, rfl, rechte⟩

theorem akzeptiert : Akzeptiert einheit := by
  refine ⟨⟨Plattform.katalog_wohlgeformt _, ?_, Aussen.zulassung_m2 _, ?_⟩, ?_, ?_⟩
  · intro i c s u w plan h
    change regel c s w [plan] u at h
    rcases h.2 with ⟨eq, _, _⟩ | ⟨eq, _, _⟩ <;>
      cases (List.cons.inj eq).1 <;>
      exact ⟨fun _ mem => (List.not_mem_nil mem).elim, fun _ mem => (List.not_mem_nil mem).elim⟩
  · apply aussen_gueltig_aus_kontext
    intro _ _ s c w spur s' h
    rcases spur with ⟨memory, events⟩
    cases h with
    | kontext _ _ form aus =>
      obtain ⟨i, _, h⟩ := form
      obtain ⟨_, _, _, _, aktion, _, ziel⟩ := aus
      change regel c s w [_] _ at h
      change FuehrtAus einrichtung _ c s _ _ _ events _ at aktion
      rcases h.2 with ⟨eq, _, rfl⟩ | ⟨eq, rechte, rfl⟩
      · cases (List.cons.inj eq).1
        cases aktion
        rw [ziel]
        exact ⟨fun _ mem => (List.not_mem_nil mem).elim, binden_offen,
          [], (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩
      · cases (List.cons.inj eq).1
        cases aktion
        rw [ziel]
        refine ⟨?_, fragen_offen rechte, [], (List.append_nil _).symm,
          fun _ mem => (List.not_mem_nil mem).elim⟩
        intro ev mem
        cases Ereignis.frage.inj (List.mem_singleton.mp mem)
        exact ⟨ausgewaehlt, rechte⟩
  · intro ρ _
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨fun _ _ _ _ _ need => False.elim need, fun _ _ _ h => ?_⟩
    obtain ⟨_, ⟨c, mem⟩, blockiert⟩ := h
    obtain ⟨_, nein, _⟩ := blockiert c mem
    exact nein

end Gabbro.Core.Annahme.Hosted
