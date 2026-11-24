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

inductive Aktion (L Bedingung : Type) where
  | intern
  | warte (b : Bedingung)
  | sperre (l : L) (a : SperrAktion)
  | frage (q : Frage)
  | verbrauche (a : AntwortEreignis)
  | rueckkehr

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

/-- A concrete implementation step. Context steps interleave at core opportunities. -/
inductive ImplSchritt (k : Katalog.Katalog) (run : HwLauf) (t : Nat) :
    Zustand L Ort Wert Raum Lok Grund → SchrittSpur Ort Wert → Zustand L Ort Wert Raum Lok Grund → Prop
  | kontext {s s' u plan spur c} (keinAbsturz : (run.angebot t).crash = false) (bereit : KannSchreiten run t c s)
      (regel : Sy.ImplSchritt c s [plan] u) (aus : FuehrtSchrittAus e t c s u plan spur s') :
      ImplSchritt k run t s spur s'
  | antwort {s s' spur a} (keinAbsturz : (run.angebot t).crash = false)
      (h : AntwortSchritt e k run t a s spur s') : ImplSchritt k run t s spur s'
  | interrupt {s s' spur id} (keinAbsturz : (run.angebot t).crash = false)
      (h : UnterbrechungsSchritt e run t id s spur s') : ImplSchritt k run t s spur s'
  | absturz {s s' spur} (h : AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur s') :
      ImplSchritt k run t s spur s'

namespace I

/-- The source of the step and its named choice at the shared machine boundary. -/
inductive SchrittWahl (Wahl : Type) where
  | kontext (c : Kontext) (wahl : Wahl)
  | antwort (a : AntwortEreignis)
  | interrupt (id : Nat × Nat)
  | absturz

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
    (offer : AbsturzAngeboten k run t) : AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur s' := by
  cases h with
  | kontext normal _ _ _ | antwort normal _ | interrupt normal _ =>
    exact (Bool.false_ne_true (normal.symm.trans offer.2)).elim
  | absturz h => exact h

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
        fun _ _ _ => True, e.invariant, e.persistenzRegion, e.wiederanlauf⟩
    FuehrtAus enabled t c s s (.warte ()) [] [] s :=
  .warte trivial

end Gabbro.Core.Maschine
