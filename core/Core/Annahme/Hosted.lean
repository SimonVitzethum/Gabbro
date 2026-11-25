module

public import Core.Annahme.Annahme
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

theorem hoch_verborgen : oeffentlich hoch = false := by
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ hoch := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

/-- The hosted unit's declared table (MK-17d): contexts and memory objects live in
    domain `0`, the hosted device object in domain `1`, with the channel from `0` to
    `1` declared. The unit's question about the hosted object therefore travels over a
    declared channel. -/
def hostedTabelle : DomaenenTabelle where
  domaenen := 2
  kontexte := []
  objekte := []
  geraete := [(⟨.hosted, 0⟩, 1)]
  kanaele := [(0, 1)]

/-- The hosted table passes the line. -/
theorem hostedTabelle_akzeptiert : pruefeDomaenenTab hostedTabelle = true := rfl

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
  domaenen := hostedTabelle
  etiketten := { endpunkt := fun _ => hoch, objekt := fun _ => hoch, ende := fun _ => hoch }
  fluss := { lokal := fun _ => .ganz hoch, kontrolle := fun _ => hoch }

private theorem quellzustand_gleich (v u : Zustand) (initial : v.initial = u.initial)
    (rechte : v.rechte = u.rechte) (leihen : v.leihen = u.leihen)
    (antwort : ∀ c, AntwortSicht einheit v c = AntwortSicht einheit u c) :
    QuellzustandGleich einheit v u := by
  refine ⟨fun _ _ low => ?_, fun c => ?_, fun x => ?_, rechte, leihen, antwort⟩
  · exact (Bool.false_ne_true (hoch_verborgen.symm.trans low)).elim
  · have verdeckt (s : Status Unit Unit) : EndeSicht einheit c s = none := by
      cases s <;> simp only [EndeSicht, sichtbar, einheit, hoch_verborgen, Bool.false_eq_true, ite_false]
    exact (verdeckt _).trans (verdeckt _).symm
  · rw [initial]

theorem fluss_lokal : FlussLokal einheit := by
  refine ⟨fun s₁ s₂ _ => quellzustand_gleich (I.start einheit s₁).2 (I.start einheit s₂).2
      rfl rfl rfl (fun _ => rfl),
    fun _ => ⟨?_, fun low => (Bool.false_ne_true (hoch_verborgen.symm.trans low)).elim⟩⟩
  intro c v w p u step
  have ideal : regel c v w [p] u := step.2
  refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun _ => ?_⟩
  rcases ideal.2 with ⟨pEq, _, rfl⟩ | ⟨pEq, _, rfl⟩
  · cases (List.cons.inj pEq).1
    exact ⟨quellzustand_gleich _ _ rfl rfl rfl (fun _ => rfl), rfl, rfl⟩
  · cases (List.cons.inj pEq).1
    refine ⟨quellzustand_gleich _ _ rfl rfl rfl (fun _ => rfl), ?_, rfl⟩
    have union : hoch ∪ hoch = hoch := by
      ext n
      simp only [Finset.mem_union, or_self]
    change ([], [], sichtbar (hoch ∪ hoch) frage) = ([], [], none)
    simp only [union, sichtbar, hoch_verborgen, Bool.false_eq_true, ite_false]

theorem ausgewaehlt : einheit.katalog.enthaelt (.endpoint frage.endpoint) := by
  change Plattform.x86_64.katalog.enthaelt (.endpoint .hosted)
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map_of_mem
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem eigene_frage (s : Zustand) : AussengriffeEigen (binde s) kontext frage := by
  intro z mem
  change z ∈ [⟨griff, .read⟩] at mem
  cases List.mem_singleton.mp mem
  exact Or.inr ⟨rfl, rfl, rfl⟩

theorem binden_offen {s : Zustand} {g} (offen : OffeneGriffeEigen s) :
    OffeneGriffeEigen { binde s with graph := g } := by
  intro ev mem epoche unbeantwortet
  obtain ⟨c, id, eig⟩ := offen ev mem epoche unbeantwortet
  exact ⟨c, id, fun z h => Or.inl (eig z h)⟩

theorem fragen_offen {s : Zustand} {t c g} (rechte : AussengriffeEigen s c frage)
    (offen : OffeneGriffeEigen s) :
    OffeneGriffeEigen { (warte s).frage (s.stelleFrage t c frage) with graph := g } := by
  intro ev mem epoche unbeantwortet
  change ev ∈ s.fragen ++ [s.stelleFrage t c frage] at mem
  rw [List.mem_append, List.mem_singleton] at mem
  rcases mem with bisher | rfl
  · exact offen ev bisher epoche unbeantwortet
  · exact ⟨c, rfl, rechte⟩

/- Acceptance of the hosted unit is proved in `DomaeneBeweise/Kanal.lean`: its declared
   table (`hostedTabelle`) carries the channel its question uses, so the bound isolation
   row holds for it. The admitted runs with the owned request are carried by
   `HostedLauf.konkreter_lauf`. -/

end Gabbro.Core.Annahme.Hosted
