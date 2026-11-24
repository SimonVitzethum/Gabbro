/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Pflichten.lean
  Subject:   THE DUTIES OF A FORM, PROVED ONCE PER EFFECT CLASS (MK-03). A form of class `k` owes the machine
             six duties: simulation (with the authority of every planned access), locality (the step covers
             its memory footprint by authority), progress (the form always has its `I` step), information
             flow (the label rule of its operands and plan), bounds (stack and memory) and safety (the four
             legs of the access). Each duty is stated for EVERY unit that embeds a form of the class
             (`Schrittform.Eingebettet`: the unit's rule for the form is the class rule, and the unit reads
             memory through `Zustand.griff` and `Zelle.objekt`), with no free function parameter: the form is a
             bundled `Schrittform` whose plan, guard and refusal the class builds, so the duty is proved from
             the class definition, not assumed of an arbitrary decoder.
             PROVED here, for every class: simulation with the authority of the plan (`klassenSim`), locality
             (`klassenLokal`), progress (`klassenFortschritt`), determinacy up to the value a read returns
             (`klassenBestimmt`). OPEN for the provers, one pinned statement `KlassenAussagen` that holds
             every class: information flow, bounds, safety, and the non-triviality of each duty.
             The duties are informative because the classes carry real plans: a step that reads or writes
             covers its cell by authority only through the guard of its class, and a form without the guard
             violates locality (`KlassenNichtTrivialAussage`). Over the frame-only classes the same duties
             reduce to the old template (`Befehl.ideal_privat`).
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Speicherplan.Einrichtung
public import Core.Annahme.Lokal
public import Core.Annahme.Schranken
public import Core.Beobachtung.Fluss.Quellregel
public import Core.Beobachtung.Nichtinterferenz
public import Core.Ideal.Eigenschaften
public import Core.Sicherheit.Regel
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog

/-- The units that carry step forms: the interpretation of memory is the elaborated one. -/
abbrev Klasseneinheit (ι : Type) := Maschine.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι

/-- **A unit embeds a form**: the unit's rule for its form `f` is the rule of the step form `F`, and the
    unit reads memory through the handles and objects of the elaborated model. -/
structure Schrittform.Eingebettet {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform) : Prop where
  regel : E.system.regel f = F.regel
  griff : E.einrichtung.speicherGriff = Zustand.griff
  objekt : E.einrichtung.speicherObjekt = Zelle.objekt

/-- **The transfer of a form respects the declared stack bound of its unit**: a frame within the bound stays
    within it. A class that does not push a continuation (every class but `ruf`) has this from its stack
    effect; a class that pushes one refuses at the bound, as `Rahmen.ruf` does. -/
def Schrittform.Stapelschranke {ι : Type} (E : Klasseneinheit ι) (F : Schrittform) : Prop :=
  ∀ (r : Rahmen) (live : Nat → Bool) (v : Int) (n : Nat), E.schranken.stapel = some n →
    r.fortsetzungen.length ≤ n → (F.uebertrag r live v).fortsetzungen.length ≤ n

/-- **The operands of a form are visible to the observer**: from source states that agree on the public
    part, the form names the same operands (the same cell, value, lock and question). This is the label
    rule of an access: an address that depends on a secret is a leak through the memory trace. -/
def Schrittform.Operandensicht {ι : Type} (E : Klasseneinheit ι) (F : Schrittform) : Prop :=
  ∀ (c : Kontext) (v₁ v₂ : Zustand), Beobachtung.QuellzustandGleich E v₁ v₂ →
    F.operand (v₁.lokal c) = F.operand (v₂.lokal c)

/-! ### The six duties, per class -/

/-- **Simulation, once per class**, with the authority of the plan. A form of the class `k` in a unit that
    gives it one linearisation point (equal local states, stutter budget zero) satisfies the per-form
    simulation duty, and every plan its implementation step records is authorised at its pre-state: a
    planned read or write names a cell the context holds a valid handle for. -/
def KlassenSimAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse = k → F.Eingebettet E f →
    E.lokalerBezug = Eq → E.stotterLaenge f = 0 →
      I.RegelSimulation E f ∧
        ∀ (c : Kontext) (s u : Zustand) (w : PUnit) (plan : Plan),
          (E.system.regel f).impl c s w [plan] u → plan.Autorisiert E.einrichtung s c

/-- **Locality, once per class.** Every ideal step of a form of the class covers its footprint by live
    authority at the pre-state: a read has the read right, a write the write right, an update both. -/
def KlassenLokalAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse = k → F.Eingebettet E f →
    RegelLokal E f

/-- **Progress, once per class.** A context whose head is a form of the class has its `I` step: the class
    rule is total, because an access without authority is refused by the rule (the frame halts) instead of
    waiting. Whether the machine can schedule the step (a lock, a read the memory model permits) is
    the machine's progress, not the form's. -/
def KlassenFortschrittAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse = k → F.Eingebettet E f →
    Ideal.RegelFortschritt E.system f

/-- **Information flow, once per class.** In a unit that labels the form by the checker's flow rule, whose
    operands the observer sees equal from public-equal states, the form preserves the coupling of two runs
    (`RegelNIPflicht`). The value a read returns is a label of the cell it reads: the read value joins the
    label of the cell, a write checks that the value's label flows into the cell's label, an atomic update
    does both, a lock action and a question are visible events whose operands are public. Open: the
    label rule of the plan events (MK-13). Difficulty: schwer. Sketch: the plan of the step is
    `Wirkungsklasse.plan` of operands that `Operandensicht` makes equal, so the observed trace entries agree;
    the successor frame is `uebertrag` of frames that agree publicly, and the read value is related by the
    cell's label through the coupled graph step. -/
def KlassenNIAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse = k → F.Eingebettet E f →
    Beobachtung.RegelFluss E f → F.Operandensicht E → Beobachtung.RegelNIPflicht E f

/-- **Bounds, once per class.** A form whose transfer respects the declared stack bound, in a unit whose
    depth measure counts the continuation stack, preserves the stack and memory bounds of every ideal run
    (`RegelSchranken`). The step of an access class changes the acting frame and the ledger of addresses
    only: it allocates and frees nothing, so the live cells of the memory bound are those before the step.
    Open (MK-12). Difficulty: mittel. Sketch: split `RegelSchranken` into its stack and memory legs; the
    stack leg is `Stapelschranke` at the acting context and the identity at every other context
    (`Zustandsrahmen` and `Zustand.nach` leave their frames); the memory leg is
    `LebendeZellen nach = LebendeZellen vor`, because `rechte` and `buchung.umfang` are unchanged by
    `zugriffNach` and by every protocol action of `FuehrtAus`. -/
def KlassenSchrankenAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse = k → F.Eingebettet E f →
    F.Stapelschranke E → (∀ r : Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length) →
      RegelSchranken E f

/-- **Safety, once per class.** In an ACCEPTED safety unit whose machine embeds the form, an implementation
    step of the form keeps the four legs (booked and authorised accesses, invariants, race freedom, TOCTOU
    freedom) and the authority of pending questions (`Sicherheit.RegelPflichten`). The class books the
    concrete address of every access in the ledger at the event number of the access (`Schrittform.buchungNach`,
    `Zustand.zugriffsereignis`: the number depends on the lazily materialised initial write,
    `Initialisierung`), so `ZugriffGebucht` is a statement about the class rule. Open (MK-04, MK-05).
    Difficulty: schwer. Sketch: the booking leg is the position of the access in the memory record of
    `Speicherfolge` (case split on `Initialisierung`); the release leg is trivial (no class here releases);
    invariants and race freedom come from acceptance: `Lokal` must carry the lock sections that order the
    non-atomic accesses (`RennfreiAusLokalAussage`, MK-04) — until it does, the leg `rennen` is not provable
    for the non-atomic modes of `lesen`, `schreiben` and `rmw`. -/
def KlassenSicherheitAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι)
    (F : Schrittform), F.klasse = k → F.Eingebettet E.maschine f → Akzeptiert E.maschine →
      Sicherheit.RegelPflichten E f

/-- The class has a MEMORY authority guard: a step needs the right on the ledger for the cell it plans and is
    refused without it. The guard of a question (`aussenBefugt`) is a duty of the question rows of `Lokal`
    and of `RegelAntwortSicher`, not of `RegelLokal`: the plan of a question names no memory cell. -/
def Wirkungsklasse.gesichert : Wirkungsklasse → Bool
  | .lesen .. | .schreiben .. | .rmw .. => true
  | .lokal | .ruf | .sperre .. | .frage => false

/-- **The unit whose only form has the given rule**: the empty fragment's unit with its form replaced. Its
    one form is always at the head. -/
def Regeleinheit (platform : Plattform) (R : Regel) : Klasseneinheit _root_.Unit where
  katalog := platform.katalog
  bild := bild
  einrichtung := einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher
  system := ⟨fun _form => R, fun _s _c => some (), fun _s _c => False, fun _s _c _b => False⟩
  startdaten := fun start =>
    startdaten Fragment.leer.eingang Fragment.leer.eintritte (start.assignment 0) platform start.regions
  startmedium := startmedium
  laden := laden Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher platform
  lokalerBezug := Eq
  stotterLaenge := fun _form => 0
  quelltabellen := Fragment.leer.tabellen

/-- The rule of a form WITHOUT its authority guard and refusal: the planned step with any value, always.
    This is what a class would be if it dropped its guard; it is the falsifying counterpart of the class
    rule. -/
def Schrittform.ungeschuetzt (F : Schrittform) : Regel :=
  ⟨fun c s _ plans u => ∃ v : Int, F.klasse.Lesewert v ∧ plans = [F.plan (s.lokal c) v] ∧ u = F.zugriffNach c s v,
   fun c s _ plans u => ∃ v : Int, F.klasse.Lesewert v ∧ plans = [F.plan (s.lokal c) v] ∧ u = F.zugriffNach c s v⟩

/-- **The duties are informative for the class.** (1) The quantifier over units is not empty: a unit embeds a
    form of the class. (2) For a class with an authority guard, dropping the guard breaks locality: some
    unit with the unguarded rule of a form of the class has an ideal step that covers its footprint by no
    authority. Without (2) the locality duty could not tell a guarded class rule from one that always
    fires. Difficulty: mittel (a unit without regions and a cell it names). Sketch for (2): the empty
    fragment's start state grants no region, so `Zustand.griff` is `none` for the planned cell and
    `BefugtOrt` fails for the read, written or updated cell. Both parts are proved
    (`klassenNichtTrivial`). -/
def KlassenNichtTrivialAussage (k : Wirkungsklasse) : Prop :=
  (∃ (platform : Plattform) (F : Schrittform), F.klasse = k ∧
      F.Eingebettet (Regeleinheit platform F.regel) ()) ∧
  (k.gesichert = true → ∃ (platform : Plattform) (F : Schrittform), F.klasse = k ∧
      ¬ RegelLokal (Regeleinheit platform F.ungeschuetzt) ())

/-- **The six duties of every class, in one pinned statement.** The proved parts are `klassenSim`,
    `klassenLokal`, `klassenFortschritt`; the rest is open for the provers. -/
def KlassenAussagen : Prop :=
  ∀ k : Wirkungsklasse, KlassenSimAussage k ∧ KlassenNIAussage k ∧ KlassenSchrankenAussage k ∧
    KlassenSicherheitAussage k ∧ KlassenFortschrittAussage k ∧ KlassenLokalAussage k ∧
    KlassenNichtTrivialAussage k

/-! ### Proofs, once for every class -/

/-- Authority on the ledger of the elaborated model is authority for the unit that embeds the form. -/
theorem Schrittform.befugt_ort {ι : Type} {E : Klasseneinheit ι} {f : ι} {F : Schrittform}
    (emb : F.Eingebettet E f) {s : Zustand} {c : Kontext} {z : Zelle} {r : Sicherheit.Speicherrecht}
    (h : s.befugt c z r) : BefugtOrt E s c z r := by
  obtain ⟨g, offset, hg, ho, gueltig, zugriff, umfang, haelt⟩ := h
  refine ⟨g, offset, ?_, ?_, gueltig, zugriff, umfang, haelt⟩
  · rw [emb.griff]
    exact hg
  · rw [emb.objekt]
    exact ho

/-- A context that is authorised for a location may access it. -/
theorem BefugtOrt.zugriff {ι : Type} {E : Klasseneinheit ι} {s : Zustand} {c : Kontext} {z : Zelle}
    {r : Sicherheit.Speicherrecht} (h : BefugtOrt E s c z r) : E.einrichtung.Zugriff s c z := by
  obtain ⟨g, _, hg, ho, gueltig, zugriff, _, _⟩ := h
  exact ⟨g, hg, ho, gueltig, zugriff⟩

/-- A step that covers its footprint by authority is authorised in the sense of the simulation. -/
theorem Befugt.autorisiert {ι : Type} {E : Klasseneinheit ι} {s : Zustand} {c : Kontext} {p : Plan}
    (h : Befugt E s c p) : p.Autorisiert E.einrichtung s c :=
  ⟨fun l hl => BefugtOrt.zugriff (h.2 l hl).1, fun x hx _ => BefugtOrt.zugriff (h.1 x hx)⟩

/-- The step of an access class exists in every state: with the authority, the planned step; without
    it, the refusal. -/
theorem Schrittform.zugriffsschritt_total (F : Schrittform) (c : Kontext) (s : Zustand) :
    ∃ (plans : List Plan) (u : Zustand), F.zugriffsschritt c s plans u := by
  by_cases g : F.klasse.befugt (F.operand (s.lokal c)) s c
  · exact ⟨_, _, Or.inr ⟨g, 0, Or.inr rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, Or.inl ⟨g, rfl, rfl⟩⟩

/-- **The rule of every class is total**: every form has an ideal step in every state. -/
theorem Schrittform.ideal_total (F : Schrittform) (c : Kontext) (s : Zustand) (w : PUnit.{1}) :
    ∃ (plans : List Plan) (u : Zustand), F.ideal c s w plans u := by
  obtain ⟨k, o, t⟩ := F
  cases k with
  | lokal => exact ⟨[Semantik.plan], _, rfl, rfl⟩
  | ruf => exact ⟨[Semantik.plan], _, rfl, rfl⟩
  | lesen m => exact Schrittform.zugriffsschritt_total ⟨.lesen m, o, t⟩ c s
  | schreiben m => exact Schrittform.zugriffsschritt_total ⟨.schreiben m, o, t⟩ c s
  | rmw m => exact Schrittform.zugriffsschritt_total ⟨.rmw m, o, t⟩ c s
  | sperre a => exact Schrittform.zugriffsschritt_total ⟨.sperre a, o, t⟩ c s
  | frage => exact Schrittform.zugriffsschritt_total ⟨.frage, o, t⟩ c s

/-- The plan of a question reads nothing and writes nothing. -/
theorem Operand.fragePlan_leer (o : Operand) :
    o.fragePlan.lesen = [] ∧ o.fragePlan.fuss = [] := by
  unfold Operand.fragePlan
  cases o.frage <;> exact ⟨rfl, rfl⟩

/-- A private plan covers no footprint. -/
theorem Befugt.privat {ι : Type} {E : Klasseneinheit ι} {s : Zustand} {c : Kontext} {p : Plan}
    (h : p = Semantik.plan) : Befugt E s c p := by
  subst h
  exact ⟨fun _ hx => (List.not_mem_nil hx).elim, fun _ hl => (List.not_mem_nil hl).elim⟩

/-- **Every ideal step of every class covers its footprint by authority.** -/
theorem Schrittform.ideal_befugt {ι : Type} {E : Klasseneinheit ι} {f : ι} {F : Schrittform}
    (emb : F.Eingebettet E f) (c : Kontext) (s : Zustand) (w : PUnit.{1}) (p : Plan) (u : Zustand)
    (step : F.ideal c s w [p] u) : Befugt E s c p := by
  obtain ⟨k, o, t⟩ := F
  cases k with
  | lokal => exact Befugt.privat (List.cons.inj step.1).1
  | ruf => exact Befugt.privat (List.cons.inj step.1).1
  | lesen m =>
    rcases step with ⟨_, same, _⟩ | ⟨g, v, _, same, _⟩
    · exact Befugt.privat (List.cons.inj same).1
    · have hp : p = Wirkungsklasse.plan (.lesen m) (o (s.lokal c)) v := (List.cons.inj same).1
      subst hp
      refine ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => ?_⟩
      have hl' := List.mem_singleton.1 hl
      subst hl'
      exact ⟨Schrittform.befugt_ort emb g, fun h => False.elim h⟩
  | schreiben m =>
    rcases step with ⟨_, same, _⟩ | ⟨g, v, _, same, _⟩
    · exact Befugt.privat (List.cons.inj same).1
    · have hp : p = Wirkungsklasse.plan (.schreiben m) (o (s.lokal c)) v := (List.cons.inj same).1
      subst hp
      refine ⟨fun x hx => ?_, fun l hl => (List.not_mem_nil hl).elim⟩
      have hx' := List.mem_singleton.1 hx
      subst hx'
      exact Schrittform.befugt_ort emb g
  | rmw m =>
    rcases step with ⟨_, same, _⟩ | ⟨g, v, _, same, _⟩
    · exact Befugt.privat (List.cons.inj same).1
    · have hp : p = Wirkungsklasse.plan (.rmw m) (o (s.lokal c)) v := (List.cons.inj same).1
      subst hp
      refine ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => ?_⟩
      have hl' := List.mem_singleton.1 hl
      subst hl'
      exact ⟨Schrittform.befugt_ort emb g.1, fun _ => Schrittform.befugt_ort emb g.2⟩
  | sperre a =>
    rcases step with ⟨_, same, _⟩ | ⟨g, v, _, same, _⟩
    · exact Befugt.privat (List.cons.inj same).1
    · have hp : p = Wirkungsklasse.plan (.sperre a) (o (s.lokal c)) v := (List.cons.inj same).1
      subst hp
      exact ⟨fun _ hx => (List.not_mem_nil hx).elim, fun _ hl => (List.not_mem_nil hl).elim⟩
  | frage =>
    rcases step with ⟨_, same, _⟩ | ⟨g, v, _, same, _⟩
    · exact Befugt.privat (List.cons.inj same).1
    · have hp : p = Wirkungsklasse.plan .frage (o (s.lokal c)) v := (List.cons.inj same).1
      subst hp
      obtain ⟨hlesen, hfuss⟩ := Operand.fragePlan_leer (o (s.lokal c))
      refine ⟨fun x hx => ?_, fun l hl => ?_⟩
      · have hx' : x ∈ (o (s.lokal c)).fragePlan.fuss := hx
        rw [hfuss] at hx'
        exact (List.not_mem_nil hx').elim
      · have hl' : l ∈ (o (s.lokal c)).fragePlan.lesen := hl
        rw [hlesen] at hl'
        exact (List.not_mem_nil hl').elim

/-- **Simulation, once per class** (`KlassenSimAussage`): the one rule is its own implementation, so the
    simulation duty holds with zero stutter, and every recorded plan is authorised because the ideal step
    covers its footprint (`Schrittform.ideal_befugt`). -/
theorem klassenSim (k : Wirkungsklasse) : KlassenSimAussage k := by
  intro ι E f F _ emb lokal null
  refine ⟨⟨I.RegelSimSchritt.aus_gleicher_regel lokal ?_, I.RegelStotterSchranke.null null⟩, ?_⟩
  · intro c s w plans u step
    rw [emb.regel] at step ⊢
    exact step
  · intro c s u w p step
    rw [emb.regel] at step
    exact Befugt.autorisiert (Schrittform.ideal_befugt emb c s w p u step)

/-- **Locality, once per class** (`KlassenLokalAussage`). -/
theorem klassenLokal (k : Wirkungsklasse) : KlassenLokalAussage k := by
  intro ι E f F _ emb c s u w p step
  rw [emb.regel] at step
  exact Schrittform.ideal_befugt emb c s w p u step

/-- **Progress, once per class** (`KlassenFortschrittAussage`): the class rule is total. -/
theorem klassenFortschritt (k : Wirkungsklasse) : KlassenFortschrittAussage k := by
  intro ι E f F _ emb s c _
  obtain ⟨plans, u, step⟩ := F.ideal_total c s ()
  refine Or.inl ⟨(), plans, u, ?_⟩
  rw [emb.regel]
  exact step

/-! ### The duties are informative (`KlassenNichtTrivialAussage`) -/

/-- A state in which no context holds any region: the start state of the empty fragment with no grant. -/
def Leerzustand : Zustand :=
  let d := startdaten Fragment.leer.eingang Fragment.leer.eintritte (some 0) .x86_64 []
  Maschine.Zustand.start d.lokal d.status d.kerne d.rechte Fragment.leer.speicher.initial
    (.leer (fun _ => (0 : UInt8)))

/-- **No context holds a handle in the empty state.** -/
theorem leerzustand_griff (c : Kontext) (slot offset : Nat) :
    Zustand.griff Leerzustand c (.region slot offset) = none := by
  apply griff_ohne_region offset
  have arrival : (Leerzustand.lokal c).arrivalRegions = [] := by
    simp only [Leerzustand, startdaten, Maschine.Zustand.start, ite_self]
  rw [arrival]
  exact Nat.zero_le _

/-- **Dropping the guard of a memory class breaks locality.** The step of the unguarded rule of a form
    that names the cell `0` of region `0` plans an access at the empty state, where no context holds a
    handle, so the planned access is covered by no authority. -/
theorem ungeschuetzt_nicht_lokal (platform : Plattform) (k : Wirkungsklasse) (hk : k.gesichert = true)
    (o : Rahmen → Operand) (ho : ∀ r, o r = ⟨.region 0 0, 0, 0, none⟩)
    (t : Rahmen → (Nat → Bool) → Int → Rahmen) :
    ¬ RegelLokal (Regeleinheit platform (Schrittform.ungeschuetzt ⟨k, o, t⟩)) () := by
  intro h
  have step : (Schrittform.ungeschuetzt ⟨k, o, t⟩).ideal eintritt Leerzustand ()
      [Schrittform.plan ⟨k, o, t⟩ (Leerzustand.lokal eintritt) 0]
      (Schrittform.zugriffNach ⟨k, o, t⟩ eintritt Leerzustand 0) :=
    ⟨0, Or.inr rfl, rfl, rfl⟩
  have bef := h eintritt Leerzustand _ () _ step
  have keinGriff : ∀ r : Rahmen, Zustand.griff Leerzustand eintritt (o r).ort = none := by
    intro r
    rw [ho]
    exact leerzustand_griff _ _ _
  cases k with
  | lesen m =>
    obtain ⟨g, _, hg, _⟩ := (bef.2 ⟨.lesen, (o (Leerzustand.lokal eintritt)).ort, m, 0, 0⟩
      (List.mem_singleton.2 rfl)).1
    change Zustand.griff Leerzustand eintritt (o (Leerzustand.lokal eintritt)).ort = some g at hg
    rw [keinGriff] at hg
    cases hg
  | schreiben m =>
    obtain ⟨g, _, hg, _⟩ := bef.1 (o (Leerzustand.lokal eintritt)).ort (List.mem_singleton.2 rfl)
    change Zustand.griff Leerzustand eintritt (o (Leerzustand.lokal eintritt)).ort = some g at hg
    rw [keinGriff] at hg
    cases hg
  | rmw m =>
    obtain ⟨g, _, hg, _⟩ := (bef.2 ⟨.rmw, (o (Leerzustand.lokal eintritt)).ort, m, 0, (o (Leerzustand.lokal eintritt)).wert⟩
      (List.mem_singleton.2 rfl)).1
    change Zustand.griff Leerzustand eintritt (o (Leerzustand.lokal eintritt)).ort = some g at hg
    rw [keinGriff] at hg
    cases hg
  | lokal => cases hk
  | ruf => cases hk
  | sperre a => cases hk
  | frage => cases hk

/-- **The duties are informative, for every class** (`KlassenNichtTrivialAussage`). -/
theorem klassenNichtTrivial (k : Wirkungsklasse) : KlassenNichtTrivialAussage k := by
  refine ⟨⟨.x86_64, ⟨k, fun _ => Operand.keiner, fun r _ _ => r⟩, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro hk
  exact ⟨.x86_64, ⟨k, fun _ => ⟨.region 0 0, 0, 0, none⟩, fun r _ _ => r⟩, rfl,
    ungeschuetzt_nicht_lokal .x86_64 k hk _ (fun _ => rfl) _⟩

end Gabbro.Core.Ast.Semantik
