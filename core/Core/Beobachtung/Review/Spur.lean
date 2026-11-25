module

public import Core.Beobachtung.Projektion
public import Core.Beobachtung.Schranken
public import Mathlib.Data.List.Forall2

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- Hardware tick indices are bookkeeping. Only a declared timed check exposes its duration. -/
inductive NiedrigesEreignis (Ort Wert Grund Form : Type) where
  | frage (kontext instanz : Nat) (frage : Frage)
  | antwort (kontext instanz : Nat) (frage : Frage) (antwort : Antwort)
  | katalog (ereignis : Ereignis)
  | register (endpoint : Endpunkt) (bus : GeratBus) (adresse : Nat)
  | dmaAdresse (endpoint : Endpunkt) (token offset laenge : Nat) (schreibt : Bool)
  | speicher (akteur : SpeicherAkteur Ort) (art : Speicher.Art) (ort : Ort) (modus : Speicher.Modus)
      (gelesen geschrieben : Option Wert)
  | ausgabe (kontext : Kontext) (kanal : Nat) (wert : Wert)
  | freigabe (kontext : Kontext) (stelle : Nat) (wert : Wert)
  | anfangsspeicher (inhalt : Ort → Option Wert)
  | ende (beendet : Kontext → Option (Ende Wert Grund))
  | ladefehler
  | zeit (kontext : Kontext) (block dauer : Nat) (late : Bool)
  | konstanteZeit (kontext : Kontext) (form : Form) (adressen : List Ort) (kosten : Nat)
  | spekulation (kontext : Kontext) (adresse : Ort)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

abbrev Beob (Ort Wert Grund Form : Type) := Praediktor → Nat → List (NiedrigesEreignis Ort Wert Grund Form)

def registerAdresse (p : Plattform) (q : Frage) : Option (GeratBus × Nat) := do
  let d ← p.geraet q.endpoint
  let offset ← match q.operation with
    | .registerRead offset | .registerWrite offset _ | .waitRegister offset _ => some offset
    | .read | .write _ | .resolve _ | .firmware _ _ | .exchange _ => none
  return (d.bus, d.window.von + offset)

def aussenBeob (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) :
    Ereignis → List (NiedrigesEreignis Ort Wert Grund Form)
  | .frage e => (sichtbar (E.etiketten.frage e.question) (.frage e.context e.questionInstance e.question)).toList
  | .antwort e =>
    let reply := sichtbar (E.etiketten.frage e.question) (.antwort e.context e.questionInstance e.question e.reply)
    let register := if e.reply.result.isOk then
      (registerAdresse E.katalog.plattform e.question).map fun (bus, adresse) =>
        NiedrigesEreignis.register e.question.endpoint bus adresse
      else none
    reply.toList ++ register.toList
  | .dma e access =>
    let address := match access with
      | .read token offset count => .dmaAdresse e token offset count false
      | .write token offset bytes => .dmaAdresse e token offset bytes.length true
    address :: (sichtbar (E.etiketten.endpunkt e) (.katalog (.dma e access))).toList
  | .geraet e a => [.katalog (.geraet e a)]
  | .interrupt c irq entry => [.katalog (.interrupt c irq entry)]
  | .seite e => [.katalog (.seite e)]
  | .persistenz e =>
    match e with
    | .write addr _ => (sichtbar (E.etiketten.persist addr) (.katalog (.persistenz e))).toList
    | .durable w | .discard w => (sichtbar (E.etiketten.persist w.addr) (.katalog (.persistenz e))).toList
    | .flush _ | .fence | .crash => [.katalog (.persistenz e)]

def speicherBeob (label : Etiketten Ort) (e : SpeicherAkteur Ort × Speicher.Etikett Ort Wert) :
    Option (NiedrigesEreignis Ort Wert Grund Form) :=
  let (actor, l) := e
  match l.art with
  | .lesen => sichtbar (label.ort l.ort) (.speicher actor l.art l.ort l.modus (some l.gelesen) none)
  | .schreiben => sichtbar (label.ort l.ort) (.speicher actor l.art l.ort l.modus none (some l.geschrieben))
  | .rmw => sichtbar (label.ort l.ort) (.speicher actor l.art l.ort l.modus (some l.gelesen) (some l.geschrieben))
  | .zaun => none
  | .aussen => none

def neuBeendet (v n : Zustand L Ort Wert Raum Lok Grund) (label : Etiketten Ort)
    (c : Kontext) : Option (Ende Wert Grund) :=
  match v.status c, n.status c with
  | .ruht, .beendet e | .laeuft, .beendet e => sichtbar (label.ende c) e
  | .ruht, .ruht | .ruht, .laeuft | .laeuft, .ruht | .laeuft, .laeuft
    | .beendet _, .ruht | .beendet _, .laeuft | .beendet _, .beendet _ => none

def zeitBeob (ρ : Lauf E) (c : Kontext) (v n : Lok) :
    List (NiedrigesEreignis Ort Wert Grund Form) :=
  let cycles t := (ρ.hw.angebot t).cycles
  let marken := (E.schranken.zeitstand n).filter fun m => decide (m ∉ E.schranken.zeitstand v)
  marken.filterMap fun m =>
    match m.phase with
    | .rumpf => none
    | .rechtzeitig t => some (.zeit c m.block (cycles t - cycles m.anfang) false)
    | .late t => some (.zeit c m.block (cycles t - cycles m.anfang) true)

def ausgabeBeob (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (c : Kontext) (v n : Lok) :
    List (NiedrigesEreignis Ort Wert Grund Form) :=
  ((E.fluss.ausgabeZuwachs v n).filter (Ausgabe.niedrig E.etiketten)).map fun
    | .wert kanal wert => .ausgabe c kanal wert
    | .freigabe id _ wert => .freigabe c id wert

def commitBeob (p : Plattform) (v n : Zustand L Ort Wert Raum Lok Grund) :
    List (NiedrigesEreignis Ort Wert Grund Form) :=
  (n.buchung.wirkungen.drop v.buchung.wirkungen.length).filterMap fun
    | .freigabe _ _ => none
    | .aussen effect =>
      (registerAdresse p effect.frage).map fun (bus, adresse) => .register effect.frage.endpoint bus adresse

def kontextBeob (ρ : Lauf E) (predictor : Praediktor) (t : Nat) (c : Kontext)
    (s : Zustand L Ort Wert Raum Lok Grund) (n : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) : List (NiedrigesEreignis Ort Wert Grund Form) :=
  let lok := s.lokal c
  let effekte := commitBeob E.katalog.plattform s n ++ ausgabeBeob E c lok (n.lokal c) ++ zeitBeob ρ c lok (n.lokal c)
  match E.system.kopf s c with
  | none => effekte
  | some form =>
    let konstant := if E.fluss.konstantzeit form then
      let adressen := spur.speicher.filterMap fun e =>
        match e.2.art with
        | .lesen | .schreiben | .rmw => some e.2.ort
        | .zaun | .aussen => none
      [.konstanteZeit c form adressen (Laufkosten ρ t 1)]
      else []
    let spekulation := E.katalog.plattform.spekulationshuelle.zugriffe (E.fluss.spekulativ form lok predictor)
    spekulation.map (.spekulation c) ++ konstant ++ effekte

/-- The observations at one occupied tick, retaining the recorded order within each event stream. -/
noncomputable def schrittBeob (ρ : Lauf E) (predictor : Praediktor) (t : Nat) :
    List (NiedrigesEreignis Ort Wert Grund Form) := by
  classical
  exact
    match ρ.zeit.spur t, ρ.zeit.zustand t, ρ.zeit.zustand (t + 1) with
    | some (wahl, spur), some s, some n =>
      let ende := neuBeendet s n E.etiketten
      let abschluesse := if ∃ c, (ende c).isSome = true then [.ende ende] else []
      let form := match wahl with
        | .kontext c _ => kontextBeob ρ predictor t c s n spur
        | .antwort _ | .interrupt _ | .absturz => []
      spur.speicher.filterMap (speicherBeob E.etiketten) ++ spur.aussen.flatMap (aussenBeob E) ++ form ++ abschluesse
    | none, _, _ | some _, none, _ | some _, some _, none => []

/-- Prefixes of one low trace per allowed predictor. Stuttering ticks append no observation. -/
noncomputable def NiedrigeBeob (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) : Beob Ort Wert Grund Form :=
  fun predictor =>
    let rec praefix : Nat → List (NiedrigesEreignis Ort Wert Grund Form)
      | 0 =>
        match ρ.zeit.zustand 0 with
        | none => [.ladefehler]
        | some s => [.anfangsspeicher (fun ort => sichtbar (E.etiketten.ort ort) (s.initial ort))]
      | t + 1 => praefix t ++ schrittBeob ρ predictor t
    praefix

/-- Only an occurrence of the same declared release can hide a difference in payload. -/
inductive EreignisAequiv (d : Nat → Option (Freigabe Wert)) :
    NiedrigesEreignis Ort Wert Grund Form → NiedrigesEreignis Ort Wert Grund Form → Prop
  | gleich (e) : EreignisAequiv d e e
  | freigabe (c : Kontext) (id : Nat) (links rechts : Wert) (g : Freigabe Wert)
      (deklaration : d id = some g) (autorisiert : g.projektion links = g.projektion rechts) :
      EreignisAequiv d (.freigabe c id links) (.freigabe c id rechts)

/-- Mutual coverage of finite prefixes compares order and termination without observing private
    delay. Taking prefixes of an infinite trace also detects any unmatched finite suffix. -/
def NiedrigAequiv (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (a b : Beob Ort Wert Grund Form) : Prop :=
  ∀ predictor, let rel := EreignisAequiv (Ort := Ort) (Grund := Grund) (Form := Form) E.fluss.freigabe
    (∀ t, ∃ u, List.Forall₂ rel (a predictor t) ((b predictor u).take (a predictor t).length)) ∧
    (∀ u, ∃ t, List.Forall₂ rel ((a predictor t).take (b predictor u).length) (b predictor u))

end Gabbro.Core.Beobachtung
