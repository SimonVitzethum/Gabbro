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

public import Core.Ast.Semantik.Runtime.Klasse.Klasse
public import Core.Ast.Semantik.Runtime.Klasse.Zugriff
public import Core.Ast.Semantik.Runtime.Faden.Erhalt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus)
open Gabbro.Core.Sicherheit (Speicherrecht)

/-- **The plan of a private step**: no memory access, no lock, no question, no waiting. It is the plan of
    every step of the classes `lokal` and `ruf`, and of a refused access. -/
def plan : Plan := ⟨.intern, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

/-- A region is live while its object lives in its arrival generation and is not lent out. The
    acting context's own authority is its frame: only a frame that holds the owned-region value and
    lists the arrival extent can bind it, and a start gives the arrival regions to one context. -/
def Zustand.regionLive (s : Zustand) (slot : Nat) : Bool :=
  s.rechte.lebt slot && s.rechte.gen slot == 0 &&
    (match s.leihen slot with | .eigen => true | .verliehen _device => false)

/-- **What a step names, read from its frame**: the cell of an access, the value it writes, the lock of a
    lock action, the question it asks. A class reads the fields it needs and ignores the others. -/
structure Operand where
  ort : Zelle
  wert : Int
  sperre : Nat
  frage : Option Frage
  aenderung : Aenderung
  faden : Fadenoperand

/-- The operand of a step that names nothing (the frame-only classes). -/
def Operand.keiner : Operand := ⟨.aussen, 0, 0, none, .tausche, Fadenoperand.keiner⟩

/-- The plan of a step that records no memory event and no question and carries the given protocol action. -/
def planMit (a : Aktion Nat PUnit) : Plan := ⟨a, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

/-- The plan of a step that asks the question the operand names; an operand without a question has the
    private plan (the step is refused). -/
def Operand.fragePlan (o : Operand) : Plan :=
  match o.frage with
  | some q => ⟨.frage q, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | none => Semantik.plan

/-- **The plan of one step of class `k`** at the operand `o`, where `v` is the value the memory model
    returned for a read. A read records its label with the value read; a write names its cell in the
    footprint with the value and the mode; an update is ONE event that reads `v` and writes the operand's
    value; a lock action and a question name their lock and question; a private step, a fence, an
    interrupt-control step and a refused access have the private plan. -/
def Wirkungsklasse.plan : Wirkungsklasse → Operand → Int → Plan
  | .lokal, _o, _v => Semantik.plan
  | .ruf, _o, _v => Semantik.plan
  | .lesen m, o, v =>
    ⟨.intern, [⟨.lesen, o.ort, m, v, v⟩], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | .schreiben m, o, _v =>
    ⟨.intern, [], [o.ort], fun x => decide (x = o.ort), fun _ort => m, fun _ort => o.wert⟩
  | .rmw m, o, v =>
    ⟨.intern, [⟨o.aenderung.art v, o.ort, m, v, o.aenderung.schreibt v o.wert⟩], [], fun _ort => false,
      fun _ort => .na, fun _ort => 0⟩
  | .zaun _m, _o, _v => Semantik.plan
  | .sperre a, o, _v =>
    ⟨.sperre o.sperre a, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | .frage, o, _v => o.fragePlan
  | .verbrauche, _o, _v => Semantik.plan
  | .starte, _o, _v => planMit .starte
  | .beende, _o, _v => planMit .beende
  | .verbinde, o, _v => planMit (.verbinde (.faden o.faden.kind))
  | .wechsle, o, _v => planMit (.wechsle o.faden.kern (.faden o.faden.kind))
  | .maskiere, _o, _v => Semantik.plan
  | .prioritaet, _o, _v => Semantik.plan
  | .sendeUnterbrechung, _o, _v => Semantik.plan
  | .leiteLeitung, _o, _v => Semantik.plan

/-- **The shape of the plans of a class**: the only plans a step of the class may have. The footprint of the
    step on the shared state is read off the class alone: nothing for a private step, a fence, an
    interrupt-control step or a refused access, one read label for a load, one written cell for a store,
    one update label for an atomic update, one lock action, one question. -/
def Wirkungsklasse.Erlaubt : Wirkungsklasse → Plan → Prop
  | .lokal, p => p = Semantik.plan
  | .ruf, p => p = Semantik.plan
  | .lesen m, p =>
    p.aktion = .intern ∧ p.fuss = [] ∧ ∃ (z : Zelle) (v : Int), p.lesen = [⟨.lesen, z, m, v, v⟩]
  | .schreiben m, p =>
    p.aktion = .intern ∧ p.lesen = [] ∧
      ∃ z : Zelle, p.fuss = [z] ∧ p.schreibt z = true ∧ p.modus z = m
  | .rmw m, p =>
    p.aktion = .intern ∧ p.fuss = [] ∧
      ∃ (z : Zelle) (v w : Int), p.lesen = [⟨.rmw, z, m, v, w⟩] ∨ p.lesen = [⟨.lesen, z, m, v, v⟩]
  | .zaun _m, p => p = Semantik.plan
  | .sperre a, p => (∃ l : Nat, p.aktion = .sperre l a) ∧ p.lesen = [] ∧ p.fuss = []
  | .frage, p => (∃ q : Frage, p.aktion = .frage q) ∧ p.lesen = [] ∧ p.fuss = []
  | .verbrauche, p => p = Semantik.plan
  | .starte, p => p.aktion = .starte ∧ p.lesen = [] ∧ p.fuss = []
  | .beende, p => p.aktion = .beende ∧ p.lesen = [] ∧ p.fuss = []
  | .verbinde, p => (∃ k : Kontext, p.aktion = .verbinde k) ∧ p.lesen = [] ∧ p.fuss = []
  | .wechsle, p => (∃ (k : Kern) (d : Kontext), p.aktion = .wechsle k d) ∧ p.lesen = [] ∧ p.fuss = []
  | .maskiere, p => p = Semantik.plan
  | .prioritaet, p => p = Semantik.plan
  | .sendeUnterbrechung, p => p = Semantik.plan
  | .leiteLeitung, p => p = Semantik.plan

/-- Does a step of the class read a value from the memory model? Only a load and an atomic update do. -/
def Wirkungsklasse.liest : Wirkungsklasse → Bool
  | .lesen .. | .rmw .. => true
  | .lokal | .ruf | .schreiben .. | .zaun .. | .sperre .. | .frage | .starte | .beende | .verbinde
  | .wechsle | .verbrauche | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung => false

/-- The value a step of the class may take from the memory model: any value for a class that reads, and
    the fixed value `0` for every other class (it reads nothing, so nothing is chosen). -/
def Wirkungsklasse.Lesewert (k : Wirkungsklasse) (v : Int) : Prop :=
  k.liest = true ∨ v = 0

/-- **The authority a step of the class needs at the pre-state** (`Zustand.befugt`, `Zustand.fragenBefugt`): the right
    on the ledger for the cell of a load or store (both rights for an atomic update), and the handles of
    the question and the device authority of a register access for a question. The frame-only classes, the
    fence, the interrupt-control classes and the lock actions need none: a fence orders but accesses
    nothing, and a lock action that
    the protocol does not allow does not execute, it waits or never runs. -/
def Wirkungsklasse.befugt : Wirkungsklasse → Operand → Zustand → Kontext → Prop
  | .lokal, _o, _s, _c => True
  | .ruf, _o, _s, _c => True
  | .lesen _m, o, s, c => s.befugt c o.ort .lesen
  | .schreiben _m, o, s, c => s.befugt c o.ort .schreiben
  | .rmw _m, o, s, c => s.befugt c o.ort .lesen ∧ s.befugt c o.ort .schreiben
  | .zaun _m, _o, _s, _c => True
  | .sperre _a, _o, _s, _c => True
  | .frage, o, s, c => ∃ q : Frage, o.frage = some q ∧ s.fragenBefugt c q
  | .verbrauche, _o, _s, _c => True
  | .starte, o, s, c =>
    o.faden.gueltig = true ∧ ∀ g ∈ o.faden.griffe, s.rechte.Gueltig g ∧ ∃ r, s.buchung.haelt c g r
  | .beende, o, _s, _c => o.faden.gueltig = true
  | .verbinde, o, _s, _c => o.faden.gueltig = true
  | .wechsle, o, _s, _c => o.faden.gueltig = true
  | .maskiere, _o, _s, _c => True
  | .prioritaet, _o, _s, _c => True
  | .sendeUnterbrechung, _o, _s, _c => True
  | .leiteLeitung, _o, _s, _c => True

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

/-- **The step of a lifecycle class**: with the operands it names, the planned step (the protocol action of
    its class, no memory event) and the state above; without them, the private plan and the refusal. The
    machine decides whether the action itself runs: a start of a thread that does not rest, a join of a
    thread that has not ended and a switch to a context that cannot be switched to do not execute. -/
def Schrittform.faedenschritt (F : Schrittform) (c : Kontext) (s : Zustand) (plans : List Plan)
    (u : Zustand) : Prop :=
  (¬ F.klasse.befugt (F.operand (s.lokal c)) s c ∧ plans = [Semantik.plan] ∧ u = F.verweigert c s) ∨
  (F.klasse.befugt (F.operand (s.lokal c)) s c ∧ plans = [F.plan (s.lokal c) 0] ∧ u = F.faedenNach c s)

/-- **The ideal step of a form, from its class.** A private or interrupt-control class has one private
    plan and its frame transfer; an access class has the step above; a lifecycle class has the
    lifecycle step. -/
def Schrittform.ideal (F : Schrittform) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  match F.klasse with
  | .lokal => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .ruf => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .verbrauche => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .maskiere => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .prioritaet => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .sendeUnterbrechung => plans = [Semantik.plan] ∧ u = F.nach c s 0
  | .leiteLeitung => plans = [Semantik.plan] ∧ u = F.nach c s 0
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
  | some w => ⟨r.zelle region index, w, 0, none, a, Fadenoperand.keiner⟩
  | none => ⟨.aussen, 0, 0, none, a, Fadenoperand.keiner⟩

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

/-- The operand of an instruction at a frame. The instructions of the frame-only classes name nothing. -/
def Befehl.operand (b : Befehl) (r : Rahmen) : Operand :=
  match b with
  | .zugriff form => form.operand r
  | .faden form => { Operand.keiner with faden := form.operand r }
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
  | .aussen .. | .textLiteral .. | .textConcat .. | .textIndex .. | .substring .. | .textLength .. => Operand.keiner
  | .maskiere .. | .prioritaet .. | .sendeUnterbrechung .. | .leiteLeitung .. => Operand.keiner

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
