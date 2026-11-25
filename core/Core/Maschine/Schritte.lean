module

public import Core.Maschine.Absturz
public import Core.Maschine.Ereignisse
public import Core.Maschine.Regel
public import Core.Maschine.Unterbrechung

@[expose] public section

namespace Gabbro.Core.Maschine

open Speicher (Etikett Modus)
open Gabbro.Core.Katalog

inductive SperrAktion where
  | ticket
  | nehmen
  | geben

inductive SperrSchritt : SperrAktion → Kontext → SperrZustand → SperrZustand → Prop where
  | ticket {c z} (keinBesitz : z.besitzer ≠ some c) (keinTicket : c ∉ z.schlange) :
      SperrSchritt .ticket c z (z.anstellen c)
  | nehmen {c z z'} (h : z.Nimmt c z') : SperrSchritt .nehmen c z z'
  | geben {c z z'} (h : z.Gibt c z') : SperrSchritt .geben c z z'

theorem sperr_schritt_erfuellbar (c d : Kontext) :
    SperrSchritt .ticket c .frei ⟨none, [c]⟩ ∧
      SperrSchritt .nehmen c ⟨none, [c, d]⟩ ⟨some c, [d]⟩ ∧
      SperrSchritt .geben c ⟨some c, [d]⟩ ⟨some d, []⟩ :=
  ⟨.ticket (fun h => nomatch h) List.not_mem_nil, .nehmen (.frei c [d]), .geben (.besitzer c [d])⟩

/-- **The protocol actions of a step.** The first six are the lock, question and handler protocol. The four
    last ones are the thread lifecycle (MK-07):
    * `starte`: start the thread `faden naechsterFaden`, which rests, and advance the counter;
    * `verbinde kind`: join the context `kind`, which has ended and which the acting context started;
    * `beende`: end the acting thread (the form records its outcome in its own status);
    * `wechsle kern kind`: run the running context `kind` on the core `kern`, which the acting context
      holds or which is idle (a core start). -/
inductive Aktion (L Bedingung : Type) where
  | intern
  | warte (b : Bedingung)
  | sperre (l : L) (a : SperrAktion)
  | frage (q : Frage)
  | verbrauche (a : AntwortEreignis)
  | rueckkehr
  | starte
  | verbinde (kind : Kontext)
  | beende
  | wechsle (kern : Kern) (kind : Kontext)

/-- One form step supplies its memory reads and the writes of its footprint in source order. -/
structure SchrittPlan (L Ort Wert Bedingung : Type) where
  aktion : Aktion L Bedingung
  lesen : List (Etikett Ort Wert)
  fuss : List Ort
  schreibt : Ort → Bool
  modus : Ort → Modus
  wert : Ort → Wert

/-- Interpretation of memory locations and declared predicates by the unit. -/
structure Einrichtung (L Ort Wert Raum Lok Grund Bedingung : Type) where
  initial : Ort → Wert
  sperrOrt : L → Ort
  ereignisOrt : Ereignis → Ort
  ereignisWert : Ereignis → Wert
  bedingung : Zustand L Ort Wert Raum Lok Grund → Kontext → Bedingung → Prop
  invariant : Zustand L Ort Wert Raum Lok Grund → L → Prop
  persistenzRegion : Strecke
  wiederanlauf : Wiederanlauf Ort Wert Raum Lok Grund
  speicherObjekt : Ort → Nat
  speicherGriff : Zustand L Ort Wert Raum Lok Grund → Kontext → Ort → Option Griff

/-- A concrete access must use a handle held by its context, for the object of
    that location and its current generation, while the object is owned. -/
def Einrichtung.Zugriff (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (x : Ort) : Prop :=
  ∃ g, e.speicherGriff s c x = some g ∧ g.objekt = e.speicherObjekt x ∧
    s.rechte.Gueltig g ∧ (s.leihen g.objekt).Zugriff

/-- Check the accesses of the concrete plan before erasing any implementation
    work. Only actual writes in the declared footprint use write authority. -/
def SchrittPlan.Autorisiert (plan : SchrittPlan L Ort Wert Bedingung)
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) : Prop :=
  (∀ l ∈ plan.lesen, e.Zugriff s c l.ort) ∧
    (∀ x ∈ plan.fuss, plan.schreibt x = true → e.Zugriff s c x)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

abbrev MaschinenSystem (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) :=
  System (Zustand L Ort Wert Raum Lok Grund) (SchrittPlan L Ort Wert Bedingung) Wahl (Blockade L Bedingung) ι

/-- A form updates its local data, authority and statuses. The machine owns the shared protocol
    fields and the RC11 graph. -/
structure Zustandsrahmen (s s' : Zustand L Ort Wert Raum Lok Grund) : Prop where
  graph : s'.graph = s.graph
  kerne : s'.kerne = s.kerne
  sperren : s'.sperren = s.sperren
  fragen : s'.fragen = s.fragen
  antworten : s'.antworten = s.antworten
  verbraucht : s'.verbraucht = s.verbraucht
  verlauf : s'.verlauf = s.verlauf
  geliefert : s'.geliefert = s.geliefert

  initial : s'.initial = s.initial
  persistenz : s'.persistenz = s.persistenz
  epoche : s'.epoche = s.epoche
  verworfen : s'.verworfen = s.verworfen
  /-- The thread counter is the machine's: a form never moves it (`FuehrtAus.starte` does). -/
  naechsterFaden : s'.naechsterFaden = s.naechsterFaden
  /-- The creator map is the machine's: a form never moves it (`FuehrtAus.starte` sets it,
       `FuehrtAus.verbinde` clears the joined thread). -/
  erzeuger : s'.erzeuger = s.erzeuger
  /-- The software-interrupt queue is the machine's: a form never moves it (`FuehrtAus.sende`
      appends the raised vector). -/
  software : s'.software = s.software
  /-- The routing table is the machine's: a form never moves it (`FuehrtAus.leite` maps the line). -/
  leitung : s'.leitung = s.leitung

variable (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)

/-- Graph label of a catalogue event. The trace additionally records the complete typed event. -/
def aussenEtikett (event : Ereignis) : Etikett Ort Wert :=
  ⟨.aussen, e.ereignisOrt event, .na, e.ereignisWert event, e.ereignisWert event⟩

/-- Protocol actions shared by both machines. The underlying form contributes its interior update;
    lock ownership, waiting conditions and outside accounting are prescribed here. -/
inductive FuehrtAus [DecidableEq L] (t : Nat) (c : Kontext) (s u : Zustand L Ort Wert Raum Lok Grund) :
    Aktion L Bedingung → List (Etikett Ort Wert) → List Ereignis →
      Zustand L Ort Wert Raum Lok Grund → Prop
  | intern : FuehrtAus t c s u .intern [] [] u
  | warte {b} (bereit : e.bedingung s c b) : FuehrtAus t c s u (.warte b) [] [] u
  | sperre {l a next} (h : SperrSchritt a c (s.sperren l) next)
      (geschuetzt : (s.sperren l).Wechsel next → e.invariant u l) :
      FuehrtAus t c s u (.sperre l a)
        (sperrEreignisse (s.sperren l) next (e.sperrOrt l) (s.initial (e.sperrOrt l))) []
        { u with sperren := Function.update s.sperren l next }
  | frage (q : Frage) :
      FuehrtAus t c s u (.frage q) [] [.frage (s.stelleFrage t c q)] (u.frage (s.stelleFrage t c q))
  | verbrauche {a} (ready : s.naechsteAntwort c = some a) :
      FuehrtAus t c s u (.verbrauche a) [] [] (u.verbrauche c)
  | rueckkehr {k ausgang} (aktiv : KehrtZurueck s c k) (ende : u.status c = .beendet ausgang) :
      FuehrtAus t c s u .rueckkehr [] [] (Zustandsrueckkehr u k)
  /-- **A thread start.** The machine, not the form, picks the new thread: it is the resting context with the
      next number, which becomes running while the counter moves on. The machine records the acting context
      as the creator of the new thread. The form supplies the entry frame of
      the new thread and what it hands over. -/
  | starte (ruht : s.status (.faden s.naechsterFaden) = .ruht) :
      FuehrtAus t c s u .starte [] []
        { u with status := Function.update u.status (.faden s.naechsterFaden) .laeuft,
                 naechsterFaden := s.naechsterFaden + 1,
                 erzeuger := Function.update u.erzeuger (.faden s.naechsterFaden) (some c) }
  /-- **A join.** It takes place only when the joined context has ended AND the joiner is its creator;
      after the join the creator entry is cleared, so a second join has no step. Until the joined thread
      has ended, or for a joiner that did not start it, the joiner does not step. -/
  | verbinde {kind ausgang} (fertig : s.status kind = .beendet ausgang)
      (erz : s.erzeuger kind = some c) :
      FuehrtAus t c s u (.verbinde kind) [] []
        { u with erzeuger := Function.update u.erzeuger kind none }
  /-- **A thread end.** The form sets the outcome in the status of the acting thread. -/
  | beende {ausgang} (ende : u.status c = .beendet ausgang) : FuehrtAus t c s u .beende [] [] u
  /-- **A switch and a core start.** The acting context holds the core or the core is idle; the context
      switched to runs, rests on no core and is no other than the acting one. The core then runs it. -/
  | wechsle {kern kind} (frei : (s.kerne kern).laeuft = some c ∨ (s.kerne kern).laeuft = none)
      (laeuft : s.status kind = .laeuft) (nirgends : ∀ k, (s.kerne k).laeuft ≠ some kind)
      (anders : kind ≠ c) :
      FuehrtAus t c s u (.wechsle kern kind) [] []
        { u with kerne := Function.update u.kerne kern { u.kerne kern with laeuft := some kind } }

/-- Physical opportunity, dispatch and a live context are required for a context step. -/
def KannSchreiten (run : HwLauf) (t : Nat) (c : Kontext) (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∃ k, run.gelegenheit t k ∧ (s.kerne k).laeuft = some c ∧ s.status c = .laeuft

/-- Run one protocol action, then append all its memory events in order. The graph output can
    use any RC11-consistent resolution of the labels the form recorded. -/
def FuehrtSchrittAus [DecidableEq L] (t : Nat) (c : Kontext)
    (s u : Zustand L Ort Wert Raum Lok Grund) (plan : SchrittPlan L Ort Wert Bedingung)
    (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  Zustandsrahmen s u ∧ (∀ l ∈ plan.lesen, l.art.liest) ∧
    ∃ sperren v,
      FuehrtAus e t c s u plan.aktion sperren spur.aussen v ∧
      Speicherfolge s.initial (.kontext c) s.graph
        (sperren ++ plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert ++
          spur.aussen.map (aussenEtikett e)) spur.speicher s'.graph ∧
      s' = { v with graph := s'.graph }

/-- An environmental arrival is a separate transition, even while the receiving context is
    preempted or owns a lock. -/
def AntwortSchritt (k : Katalog.Katalog) (run : HwLauf) (t : Nat) (a : AntwortEreignis)
    (s : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert)
    (s' : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  s.AntwortAngeboten k run t a ∧ spur.aussen = [.antwort a] ∧
    Speicherfolge s.initial .aussen s.graph [aussenEtikett e (.antwort a)] spur.speicher s'.graph ∧
    s' = { s.antwort a with graph := s'.graph }

/-- Delivery runs on its own opportunity. A pending offer is consumed only when a handler enters. -/
def UnterbrechungsSchritt (run : HwLauf) (t : Nat) (id : Nat × Nat)
    (s : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∃ k irq c nmi,
    (run.angebot t).interrupt k = true ∧ UnterbrechungAusstehend s run t k id irq ∧
    NimmtUnterbrechung (s.kerne k) k (Nat.pair id.1 id.2) irq c nmi ∧ s.status c = .ruht ∧
    spur.aussen = [.interrupt k irq .handler] ∧
    Speicherfolge s.initial .aussen s.graph [aussenEtikett e (.interrupt k irq .handler)]
      spur.speicher s'.graph ∧ s' = { Zustandseintritt s k id c nmi with graph := s'.graph }

variable [DecidableEq L]
variable (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)

/-- The source of the step and its named choice at the shared machine boundary. -/
inductive SchrittWahl (Wahl : Type) where
  | kontext (c : Kontext) (wahl : Wahl)
  | antwort (a : AntwortEreignis)
  | interrupt (id : Nat × Nat)
  | absturz

/-- A concrete implementation step. Context steps interleave at core opportunities. -/
inductive ImplSchritt (k : Katalog.Katalog) (run : HwLauf) (t : Nat) :
    Zustand L Ort Wert Raum Lok Grund → (SchrittWahl Wahl × SchrittSpur Ort Wert) →
      Zustand L Ort Wert Raum Lok Grund → Prop
  | kontext {s s' u plan spur c w} (keinAbsturz : (run.angebot t).crash = false) (bereit : KannSchreiten run t c s)
      (regel : Sy.ImplSchritt c s w [plan] u) (aus : FuehrtSchrittAus e t c s u plan spur s') :
      ImplSchritt k run t s (.kontext c w, spur) s'
  | antwort {s s' spur a} (keinAbsturz : (run.angebot t).crash = false)
      (h : AntwortSchritt e k run t a s spur s') : ImplSchritt k run t s (.antwort a, spur) s'
  | interrupt {s s' spur id} (keinAbsturz : (run.angebot t).crash = false)
      (h : UnterbrechungsSchritt e run t id s spur s') : ImplSchritt k run t s (.interrupt id, spur) s'
  | absturz {s s' spur} (h : AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur s') :
      ImplSchritt k run t s (.absturz, spur) s'

namespace I

/-- An ideal step uses the whole unit rule at the same protocol or catalogue boundary. -/
inductive Schritt (k : Katalog.Katalog) (run : HwLauf) (t : Nat) :
    Zustand L Ort Wert Raum Lok Grund → (SchrittWahl Wahl × SchrittSpur Ort Wert) →
      Zustand L Ort Wert Raum Lok Grund → Prop
  | kontext {s s' u plan spur c w} (keinAbsturz : (run.angebot t).crash = false) (bereit : KannSchreiten run t c s)
      (regel : Sy.ISchritt c s w [plan] u) (aus : FuehrtSchrittAus e t c s u plan spur s') :
      Schritt k run t s (.kontext c w, spur) s'
  | antwort {s s' spur a} (keinAbsturz : (run.angebot t).crash = false)
      (h : AntwortSchritt e k run t a s spur s') :
      Schritt k run t s (.antwort a, spur) s'
  | interrupt {s s' spur id} (keinAbsturz : (run.angebot t).crash = false)
      (h : UnterbrechungsSchritt e run t id s spur s') :
      Schritt k run t s (.interrupt id, spur) s'
  | absturz {s s' spur} (h : AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur s') :
      Schritt k run t s (.absturz, spur) s'

end I

theorem FuehrtSchrittAus.viele {t c s u plan spur s'} (h : FuehrtSchrittAus e t c s u plan spur s') :
    s.graph.Viele spur.speicher s'.graph := by
  obtain ⟨_, _, _, _, _, append, _⟩ := h
  exact append.viele

theorem AntwortSchritt.viele {k run t a s spur s'} (h : AntwortSchritt e k run t a s spur s') :
    s.graph.Viele spur.speicher s'.graph := by
  obtain ⟨_, _, append, _⟩ := h
  exact append.viele

theorem AntwortSchritt.ankunft {k run t a s spur s'} (h : AntwortSchritt e k run t a s spur s') :
    spur.aussen = [.antwort a] ∧ s'.antworten = s.antworten ++ [a] ∧ s'.verbraucht = s.verbraucht := by
  obtain ⟨_, spurEq, _, stateEq⟩ := h
  rw [stateEq]
  exact ⟨spurEq, rfl, rfl⟩

theorem UnterbrechungsSchritt.viele {run t id s spur s'} (h : UnterbrechungsSchritt e run t id s spur s') :
    s.graph.Viele spur.speicher s'.graph := by
  obtain ⟨_, _, _, _, _, _, _, _, _, append, _⟩ := h
  exact append.viele

theorem impl_speicher_gut {k run t s spur s'} (h : ImplSchritt e Sy k run t s spur s')
    (gut : s.SpeicherGut) : s'.SpeicherGut := by
  cases h with
  | kontext _ _ _ aus => exact (aus.viele e).gut gut.1 gut.2
  | antwort _ h => exact (h.viele e).gut gut.1 gut.2
  | interrupt _ h => exact (h.viele e).gut gut.1 gut.2
  | absturz h => exact h.neustart.2.2.2.2.2.2.2

theorem ideal_speicher_gut {k run t s spur s'} (h : I.Schritt e Sy k run t s spur s')
    (gut : s.SpeicherGut) : s'.SpeicherGut := by
  cases h with
  | kontext _ _ _ aus => exact (aus.viele e).gut gut.1 gut.2
  | antwort _ h => exact (h.viele e).gut gut.1 gut.2
  | interrupt _ h => exact (h.viele e).gut gut.1 gut.2
  | absturz h => exact h.neustart.2.2.2.2.2.2.2

theorem ImplSchritt.absturzfall {k run t s spur s'} (h : ImplSchritt e Sy k run t s spur s')
    (offer : AbsturzAngeboten k run t) :
    spur.1 = .absturz ∧ AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur.2 s' := by
  cases h with
  | kontext normal _ _ _ | antwort normal _ | interrupt normal _ =>
    exact (Bool.false_ne_true (normal.symm.trans offer.2)).elim
  | absturz h => exact ⟨rfl, h⟩

theorem I.Schritt.absturzfall {k run t s spur s'} (h : I.Schritt e Sy k run t s spur s')
    (offer : AbsturzAngeboten k run t) :
    spur.1 = .absturz ∧ AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur.2 s' := by
  cases h with
  | kontext normal _ _ _ | antwort normal _ | interrupt normal _ =>
    exact (Bool.false_ne_true (normal.symm.trans offer.2)).elim
  | absturz h => exact ⟨rfl, h⟩

theorem warte_genau {t c s u b} :
    FuehrtAus e t c s u (.warte b) [] [] u ↔ e.bedingung s c b :=
  ⟨fun h => by cases h with | warte bereit => exact bereit, FuehrtAus.warte⟩

theorem warte_erfuellbar
    (s : Zustand L Ort Wert Raum Lok Grund) (t : Nat) (c : Kontext) :
    let enabled : Einrichtung L Ort Wert Raum Lok Grund Unit :=
      ⟨e.initial, e.sperrOrt, e.ereignisOrt, e.ereignisWert,
        fun _ _ _ => True, e.invariant, e.persistenzRegion, e.wiederanlauf, e.speicherObjekt, e.speicherGriff⟩
    FuehrtAus enabled t c s s (.warte ()) [] [] s :=
  .warte trivial

end Gabbro.Core.Maschine
