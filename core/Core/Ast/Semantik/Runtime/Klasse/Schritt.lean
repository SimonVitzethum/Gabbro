/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Schritt.lean
  Subject:   THE STEP OF A CLASS (MK-03). What a form of an effect class contributes to the machine is fixed
             by its class and by two frame-level facts it supplies:
             * the OPERAND: the cell, the value, the lock or the question its step names, read from the acting
               frame (`Schrittform.operand`) — so the plan of a step depends on the frame, not on a constant;
             * the TRANSFER: the update of the acting frame, given the value the memory model returned for a
               read (`Schrittform.uebertrag`).
             The class builds everything else: the plan (`Wirkungsklasse.plan`: the memory events, the lock
             action, the question), the authority the step needs (`Wirkungsklasse.befugt`), the refusal when
             that authority is missing (the frame halts and no access happens), and the one relation that is
             both the ideal and the implementation step (`Schrittform.ideal`): every class here has ONE
             linearisation point. The value of a read is the only thing the form does not decide; it is a
             free choice of the relation, and the memory model of the machine accepts or rejects it.
             `Befehl.form` gives each instruction its form; the instructions of the classes `lokal` and `ruf`
             have the operand `Operand.keiner` and the transfer `Befehl.auswerten`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.SchrittPlan

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus)
open Gabbro.Core.Sicherheit (Speicherrecht)

/-- **A step form**: a class, the operand its frame supplies and the frame transfer it applies. Everything
    else about the step is the class's. -/
structure Schrittform where
  klasse : Wirkungsklasse
  operand : Rahmen → Operand
  uebertrag : Rahmen → (Nat → Bool) → Int → Rahmen

/-- The plan of the step of the form at a frame, for the value `v` the memory returned. -/
def Schrittform.plan (F : Schrittform) (r : Rahmen) (v : Int) : Plan :=
  F.klasse.plan (F.operand r) v

/-- The state after the form's step: only the acting context's frame changes; the machine owns every
    shared field. -/
def Schrittform.nach (F : Schrittform) (c : Kontext) (s : Zustand) (v : Int) : Zustand :=
  { s with lokal := Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive v) }

/-- **The ledger after the step**: the concrete address of a load, store or update is booked at the event
    number of the access (`Zustand.zugriffsereignis`), so that the safety legs find the operand of every
    access the machine records (`ZugriffGebucht`). The other classes book nothing. -/
noncomputable def Schrittform.buchungNach (F : Schrittform) (c : Kontext) (s : Zustand) :
    Gabbro.Core.Sicherheit.Buchung Zelle :=
  match F.klasse with
  | .lesen .. | .schreiben .. | .rmw .. =>
    { s.buchung with
      adresse := fun e =>
        if e = s.zugriffsereignis (F.operand (s.lokal c)).ort then s.adresse c (F.operand (s.lokal c)).ort
        else s.buchung.adresse e }
  | .lokal | .ruf | .zaun .. | .sperre .. | .frage | .verbrauche | .starte | .beende | .verbinde
  | .wechsle | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung => s.buchung

/-- The state after the step of an access class: the frame transfer and the booked ledger. -/
noncomputable def Schrittform.zugriffNach (F : Schrittform) (c : Kontext) (s : Zustand) (v : Int) : Zustand :=
  { F.nach c s v with buchung := F.buchungNach c s }

/-- The state after a refused access: the acting frame halts, nothing else changes. -/
def Schrittform.verweigert (F : Schrittform) (c : Kontext) (s : Zustand) : Zustand :=
  { s with lokal := Function.update s.lokal c ((s.lokal c).halt .ungueltigerBereich) }

/-- **The step of an access class**: with the authority, the planned step with the chosen value; without
    it, the private plan and the refusal. -/
def Schrittform.zugriffsschritt (F : Schrittform) (c : Kontext) (s : Zustand) (plans : List Plan)
    (u : Zustand) : Prop :=
  (¬ F.klasse.befugt (F.operand (s.lokal c)) s c ∧ plans = [Semantik.plan] ∧ u = F.verweigert c s) ∨
  (F.klasse.befugt (F.operand (s.lokal c)) s c ∧
    ∃ v : Int, F.klasse.Lesewert v ∧ plans = [F.plan (s.lokal c) v] ∧ u = F.zugriffNach c s v)

/-- **The state after the step of a lifecycle class** (MK-07), before the machine adds its part
    (`FuehrtAus`: the status of the new thread and the counter of a start, the core of a switch).
    * `starte`: the starter's frame binds the number of the new thread, the new thread gets its entry frame, and
      the handles named are handed over (`Buchung.uebergeben`);
    * `beende`: the acting thread stops and its status records the outcome it names;
    * `verbinde`: the joiner's frame binds the outcome of the ended thread and the joiner takes back what the ended
      thread still held (`Buchung.zurueckgegeben`); a thread that ended with a reason exit halts the joiner; a
      thread that has not ended changes nothing (the machine does not run the join then);
    * `wechsle`: only the acting frame advances; the machine moves the core. -/
def Schrittform.faedenNach (F : Schrittform) (c : Kontext) (s : Zustand) : Zustand :=
  let o := (F.operand (s.lokal c)).faden
  match F.klasse with
  | .starte =>
    { s with
      lokal := Function.update
        (Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive (s.naechsterFaden : Int)))
        (.faden s.naechsterFaden) { o.anfang with fortsetzungen := [] },
      buchung := { s.buchung with
        haelt := s.buchung.uebergeben c (.faden s.naechsterFaden) o.griffe } }
  | .beende =>
    { s with
      lokal := Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive 0),
      status := Function.update s.status c (.beendet (.wert o.ergebnis)) }
  | .verbinde =>
    match s.status (.faden o.kind) with
    | .beendet (.wert w) =>
      { s with
        lokal := Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive w),
        buchung := { s.buchung with haelt := s.buchung.zurueckgegeben (.faden o.kind) c } }
    | .beendet (.grund _) =>
      { s with lokal := Function.update s.lokal c ((s.lokal c).halt .ungueltigerWert) }
    | .ruht | .laeuft => s
  | .lokal | .ruf | .lesen .. | .schreiben .. | .rmw .. | .zaun .. | .sperre .. | .frage | .verbrauche
  | .wechsle | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung => F.nach c s 0

/-- **The frame writes the translated value of an outside answer into its named slot.**
    The catalogue row of the question declares the return kind; an ok answer of that kind binds
    its translated value at `ziel`. An answer without a translated value (an error, or a value of
    another kind) halts the frame with a named reason; the context ends at the state level, see
    `verbraucheNach`. -/
def verbraucheSchreibe (ziel : Nat) (q : Frage) (r : Rahmen) (a : Antwort) : Rahmen :=
  match Antwort.uebersetzt q a with
  | some v => r.schreibe ziel (some v)
  | none => r.halt .ungueltigerWert

/-- The consume write keeps the continuation stack. -/
theorem verbraucheSchreibe_fortsetzungen (ziel : Nat) (q : Frage) (r : Rahmen) (a : Antwort) :
    (verbraucheSchreibe ziel q r a).fortsetzungen = r.fortsetzungen := by
  cases h : Antwort.uebersetzt q a with
  | none => simp only [verbraucheSchreibe, h, Rahmen.halt]
  | some v => simp only [verbraucheSchreibe, h, Rahmen.schreibe]

/-- **The state after a consume step** (MK-06, value binding and commit guard). The next arrived
    answer of the acting context is taken only when it still carries the revalidation evidence of
    its commit (`gueltigBeiCommit`): its translated value is bound at the operand slot and the
    consumption counter moves. An answer without that evidence is refused with a named halt and
    is not consumed. An answer that cannot be translated ends the context with a reason exit.
    Without an arrived answer the step is the private transfer (totality for progress). Only the
    acting context changes. -/
def Schrittform.verbraucheNach (F : Schrittform) (c : Kontext) (s : Zustand) : Zustand :=
  match s.naechsteAntwort c with
  | none => F.nach c s 0
  | some a =>
    if AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a then
      let s1 := s.verbrauche c
      let ziel := (F.operand (s.lokal c)).ziel
      match Antwort.uebersetzt a.question a.reply with
      | some _v =>
        { s1 with lokal := Function.update s1.lokal c (verbraucheSchreibe ziel a.question (s1.lokal c) a.reply) }
      | none =>
        { s1 with
          lokal := Function.update s1.lokal c (s1.lokal c).weiter,
          status := Function.update s1.status c (.beendet (.grund PUnit.unit)) }
    else
      { s with lokal := Function.update s.lokal c ((s.lokal c).halt .ungueltigerWert) }

/-- A refused consume keeps the consumption counters and halts only the acting frame. -/
def Schrittform.verbraucheVerweigert (F : Schrittform) (c : Kontext) (s : Zustand) : Zustand :=
  { s with lokal := Function.update s.lokal c ((s.lokal c).halt .ungueltigerWert) }

/-- A consume step leaves every other context's frame alone. -/
theorem Schrittform.verbraucheNach_andere (F : Schrittform) (c : Kontext) (s : Zustand)
    (d : Kontext) (hd : d ≠ c) : (F.verbraucheNach c s).lokal d = s.lokal d := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    simp only [h, Schrittform.nach, Function.update_of_ne hd]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche, Function.update_of_ne hd]
      | some _v => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche, Function.update_of_ne hd]
    · simp only [h, hg, if_true, if_false, Function.update_of_ne hd]

/-- A consume step keeps the authority ledger. -/
theorem Schrittform.verbraucheNach_rechte (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verbraucheNach c s).rechte = s.rechte := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    simp only [h, Schrittform.nach]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
      | some _v => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
    · simp only [h, hg, if_true, if_false]

/-- A consume step keeps the booking extents. -/
theorem Schrittform.verbraucheNach_umfang (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verbraucheNach c s).buchung.umfang = s.buchung.umfang := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    simp only [h, Schrittform.nach]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
      | some _v => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
    · simp only [h, hg, if_true, if_false]

/-- A consume step keeps the questions, the answers and the epoch. -/
theorem Schrittform.verbraucheNach_rahmen (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verbraucheNach c s).fragen = s.fragen ∧
      (F.verbraucheNach c s).antworten = s.antworten ∧
      (F.verbraucheNach c s).epoche = s.epoche := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    refine ⟨?_, ?_, ?_⟩ <;> simp only [h, Schrittform.nach]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => refine ⟨?_, ?_, ?_⟩ <;> simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
      | some _v => refine ⟨?_, ?_, ?_⟩ <;> simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
    · refine ⟨?_, ?_, ?_⟩ <;> simp only [h, hg, if_true, if_false]

/-- A consume step keeps the outside part of the ledger. -/
theorem Schrittform.verbraucheNach_aussen (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verbraucheNach c s).buchung.aussengriff = s.buchung.aussengriff ∧
      (F.verbraucheNach c s).buchung.geraet = s.buchung.geraet := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    refine ⟨?_, ?_⟩ <;> simp only [h, Schrittform.nach]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => refine ⟨?_, ?_⟩ <;> simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
      | some _v => refine ⟨?_, ?_⟩ <;> simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
    · refine ⟨?_, ?_⟩ <;> simp only [h, hg, if_true, if_false]

/-- A consume step keeps the whole booking (only the acting frame, status and counter move). -/
theorem Schrittform.verbraucheNach_buchung (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verbraucheNach c s).buchung = s.buchung := by
  simp only [Schrittform.verbraucheNach]
  cases h : s.naechsteAntwort c with
  | none =>
    simp only [h, Schrittform.nach]
  | some a =>
    by_cases hg : AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a
    · cases htr : Antwort.uebersetzt a.question a.reply with
      | none => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
      | some _v => simp only [h, hg, htr, if_true, if_false, Zustand.verbrauche]
    · simp only [h, hg, if_true, if_false]

/-- **The step of a lifecycle class**: with the operands it names, the planned step (the protocol action of
    its class, no memory event) and the state above; without them, the private plan and the refusal. The
    machine decides whether the action itself runs: a start of a thread that does not rest, a join of a
    thread that has not ended and a switch to a context that cannot be switched to do not execute. -/
def Schrittform.faedenschritt (F : Schrittform) (c : Kontext) (s : Zustand) (plans : List Plan)
    (u : Zustand) : Prop :=
  (¬ F.klasse.befugt (F.operand (s.lokal c)) s c ∧ plans = [Semantik.plan] ∧ u = F.verweigert c s) ∨
  (F.klasse.befugt (F.operand (s.lokal c)) s c ∧ plans = [F.plan (s.lokal c) 0] ∧ u = F.faedenNach c s)

/-- The ideal step follows the class. A consume step binds the answer with `verbraucheNach`.
    Interrupt control uses the protocol plan of the class and its frame transfer. -/
def Schrittform.ideal (F : Schrittform) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  match F.klasse with
  | .lokal => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .ruf => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .verbrauche => plans = [Semantik.plan] ∧ u = F.verbraucheNach c s
  | .maskiere => plans = [F.plan (s.lokal c) 0] ∧ u = F.nach c s 0
  | .prioritaet => plans = [F.plan (s.lokal c) 0] ∧ u = F.nach c s 0
  | .sendeUnterbrechung => plans = [F.plan (s.lokal c) 0] ∧ u = F.nach c s 0
  | .leiteLeitung => plans = [F.plan (s.lokal c) 0] ∧ u = F.nach c s 0
  | .lesen .. | .schreiben .. | .rmw .. | .zaun .. | .sperre .. | .frage => F.zugriffsschritt c s plans u
  | .starte | .beende | .verbinde | .wechsle => F.faedenschritt c s plans u

/-- **The implementation step of a form.** Every class of this package has ONE linearisation point: the
    implementation step is the ideal step, so a step of the implementation machine is a step of `I`. A class
    that needs private implementation steps (a store with a trailing fence, a multi-phase operation) is
    appended with its own implementation relation by the package that introduces it (MK-10). -/
def Schrittform.impl (F : Schrittform) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  F.ideal c s w plans u

/-- The rule of a form: its implementation step and its `I` step. -/
def Schrittform.regel (F : Schrittform) : Regel := ⟨F.impl, F.ideal⟩

/-- The operand of an access instruction whose operands the frame supplies: the cell, the value and the change.
    A missing operand (a slot that holds no integer) names the location of the outside events, to which no
    context holds a handle: the access is refused, nothing is read or written. -/
def Rahmen.zugriffOperand (r : Rahmen) (region index : Nat) (wert : Option Int) (a : Aenderung) : Operand :=
  match wert with
  | some w => ⟨r.zelle region index, w, 0, none, a, Fadenoperand.keiner, 0, Unterbrechungsoperand.keiner⟩
  | none => ⟨.aussen, 0, 0, none, a, Fadenoperand.keiner, 0, Unterbrechungsoperand.keiner⟩

/-- **The operand of an access instruction at a frame**, read from the frame it steps. A fence names
    nothing. -/
def Zugriffsform.operand (z : Zugriffsform) (r : Rahmen) : Operand :=
  match z with
  | .lade (region := region) (index := index) .. => r.zugriffOperand region index (some 0) .tausche
  | .erwarte (region := region) (index := index) .. => r.zugriffOperand region index (some 0) .tausche
  | .speichere (region := region) (index := index) (quelle := quelle) .. =>
    r.zugriffOperand region index (r.ganz quelle) .tausche
  | .veroeffentliche (region := region) (index := index) (quelle := quelle) .. =>
    r.zugriffOperand region index (r.ganz quelle) .tausche
  | .tausche (region := region) (index := index) (quelle := quelle) .. =>
    r.zugriffOperand region index (r.ganz quelle) .tausche
  | .holeUndAddiere (region := region) (index := index) (betrag := betrag) .. =>
    r.zugriffOperand region index (r.ganz betrag) .addiere
  | .vergleicheTausche (region := region) (index := index) (erwartet := erwartet) (neu := neu) .. =>
    match r.ganz erwartet with
    | some e => r.zugriffOperand region index (r.ganz neu) (.vergleiche e)
    | none => r.zugriffOperand region index none .tausche
  | .zaun .. => Operand.keiner

/-- The operand of an instruction at a frame. The instructions of the frame-only classes name nothing.
    A `verbrauche` names its answer slot `ziel`; a `frage` names nothing yet (its question wiring is
    follow-up work once the catalogue handle slots are bound). -/
def Befehl.operand (b : Befehl) (r : Rahmen) : Operand :=
  match b with
  | .zugriff form => form.operand r
  | .faden form => { Operand.keiner with faden := form.operand r }
  | .aussen (.verbrauche ziel) => { Operand.keiner with ziel := ziel }
  | .aussen (.frage ..) => Operand.keiner
  | .rufe .. | .starte .. => Operand.keiner
  | .literal .. | .binaer .. | .wahrheitswert .. | .lesen .. | .negativ ..
  | .negieren .. | .verneinen .. | .teilen .. | .vergleichen ..
  | .binden .. | .springeWenn .. | .zuweisen .. | .zurueck .. | .springe ..
  | .blockEnde .. | .bindeWert .. | .ende | .bindeRegion ..
  | .definiere .. | .rueckVoid | .pruefeMass .. | .setzePasszahl ..
  | .whileTest .. | .forAnfang .. | .forTest .. | .forNaechster .. | .zurueckSprung ..
  | .baueArray .. | .liesArray .. | .baueTupel .. | .liesTupelfeld .. | .bindeTupel ..
  | .definiereRecord .. | .baueRecord .. | .liesRecordFeld .. | .setzeRecordFeld ..
  | .definiereVariante .. | .baueVariante .. | .waehleVariante ..
  | .definiereTraeger .. | .optionIstBesetzt .. | .definiereEffektgruppe .. | .waehleUmgebung ..
  | .textLiteral .. | .textConcat .. | .textIndex .. | .substring .. | .textLength .. => Operand.keiner
  | .maskiere vektor aus =>
    { Operand.keiner with unterbrechung := ⟨vektor, aus, 0, 0, 0, 0⟩ }
  | .prioritaet grenze =>
    { Operand.keiner with unterbrechung := ⟨0, false, grenze, 0, 0, 0⟩ }
  | .sendeUnterbrechung vektor kern =>
    { Operand.keiner with unterbrechung := ⟨vektor, false, 0, kern, 0, 0⟩ }
  | .leiteLeitung ltg krn prio =>
    { Operand.keiner with unterbrechung := ⟨0, false, 0, krn, ltg, prio⟩ }

/-- The frame transfer of an instruction, given the value the memory returned: an access instruction binds or
    ignores that value; every other instruction ignores it and evaluates at the instruction boundary. -/
def Befehl.uebertrag (b : Befehl) (r : Rahmen) (live : Nat → Bool) (gelesen : Int) : Rahmen :=
  match b with
  | .zugriff form => form.uebertrag r gelesen
  | .faden form => form.uebertrag r gelesen
  | .rufe .. | .starte .. => b.auswerten r live
  | .literal .. | .binaer .. | .wahrheitswert .. | .lesen .. | .negativ ..
  | .negieren .. | .verneinen .. | .teilen .. | .vergleichen ..
  | .binden .. | .springeWenn .. | .zuweisen .. | .zurueck .. | .springe ..
  | .blockEnde .. | .bindeWert .. | .ende | .bindeRegion ..
  | .definiere .. | .rueckVoid | .pruefeMass .. | .setzePasszahl ..
  | .whileTest .. | .forAnfang .. | .forTest .. | .forNaechster .. | .zurueckSprung ..
  | .baueArray .. | .liesArray .. | .baueTupel .. | .liesTupelfeld .. | .bindeTupel ..
  | .definiereRecord .. | .baueRecord .. | .liesRecordFeld .. | .setzeRecordFeld ..
  | .definiereVariante .. | .baueVariante .. | .waehleVariante ..
  | .definiereTraeger .. | .optionIstBesetzt .. | .definiereEffektgruppe .. | .waehleUmgebung ..
  | .aussen .. | .textLiteral .. | .textConcat .. | .textIndex .. | .substring .. | .textLength .. => b.auswerten r live
  | .maskiere .. | .prioritaet .. | .sendeUnterbrechung .. | .leiteLeitung .. => b.auswerten r live

/-- **The step form of an instruction**: its class, operand and transfer. -/
def Befehl.form (b : Befehl) : Schrittform := ⟨b.klasse, b.operand, b.uebertrag⟩

end Gabbro.Core.Ast.Semantik
