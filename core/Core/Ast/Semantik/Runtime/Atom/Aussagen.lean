/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Aussagen.lean
  Subject:   THE STATEMENTS OF THE MEMORY AND ATOMIC INSTRUCTIONS (MK-04), pinned under ONE statement
             `AtomAussagen`:
             * `AtomarSimAussage`: the implementation of a reading access instruction IS its ideal step under the
               same choice -- the value the memory model returns for the read (`Speicherwahl`: the reads-from
               source of the read event fixes it). Both machines run the one rule of the class
               (`Schrittform.impl := Schrittform.ideal`), and the value that the step binds into the frame is
               exactly the value of the label it records. PROVED (`atomarSim`).
             * `PayloadSichtbarAussage` (`Speicher/Atom/Nutzlast`): a publication's payload is visible to the
               observer that reads the publication. PROVED (`payloadSichtbar`).
             * `RennfreiAusLokalAussage` (`Sicherheit/Atom/RennfreiAusLokal`): lock sections order the plain
               accesses. PROVED (`rennfreiAusLokal`) from the graph-level discipline.
             Each has a satisfiability lemma and a non-triviality lemma that exhibits an instruction, a graph or a
             program the model represents and that violates the statement; only the checker's refusal excludes it
             (`atomarSim_erfuellbar` / `_nichtTrivial`, `payloadSichtbar_erfuellbar` / `_nichtTrivial`,
             `rennfreiAusLokal_erfuellbar` / `rennfreiAusLokal_nichtTrivial`).
             Open duties of the access instructions, pinned under `ZugriffBefehlAussage` for the registry entry of
             `Befehl.zugriff`: determinacy up to the value read (`ZugriffBestimmtAussage`, replacing
             `Ideal.RegelBestimmt`, which an instruction that CHOOSES a value cannot satisfy) and composability of the
             steps the memory model accepts (`ZugriffKomponierbarAussage`, replacing `I.RegelKomponierbar`, which
             quantifies over values no write produced).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Speicher.Atom.Nutzlast
public import Core.Speicher.Atom.NutzlastSchwach
public import Core.Speicher.Atom.AbschnitteBeispiele
public import Core.Sicherheit.Atom.RennfreiAusLokal

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog
open Gabbro.Core.Speicher (Modus)

/-! ### The mode of an access instruction -/

/-- The access mode an access instruction names. -/
def Zugriffsform.modus : Zugriffsform → Modus
  | .lade _ _ _ _ m => m
  | .speichere _ _ _ m => m
  | .tausche _ _ _ _ _ m => m
  | .vergleicheTausche _ _ _ _ _ _ m => m
  | .holeUndAddiere _ _ _ _ _ m => m
  | .erwarte _ _ _ _ _ m => m
  | .veroeffentliche _ _ _ m => m

/-- The class of an access instruction carries its mode. -/
theorem Zugriffsform.klasse_modus (z : Zugriffsform) :
    z.klasse = .lesen z.modus ∨ z.klasse = .schreiben z.modus ∨ z.klasse = .rmw z.modus := by
  cases z <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

/-- **The publication writes the flag cell in its mode**: the footprint of the step of `veroeffentliche` is the
    flag cell and the mode of the write is the mode of the instruction. This is the link between the instruction
    and the release event of `PayloadSichtbarAussage`. -/
theorem veroeffentliche_schreibt_im_modus (region index quelle : Nat) (m : Modus) (r : Rahmen) (v : Int) :
    ((Befehl.zugriff (.veroeffentliche region index quelle m)).plan r v).fuss =
        [((Befehl.zugriff (.veroeffentliche region index quelle m)).operand r).ort] ∧
      ∀ x, ((Befehl.zugriff (.veroeffentliche region index quelle m)).plan r v).modus x = m :=
  ⟨rfl, fun _ => rfl⟩

/-- **The confirming observation reads the flag cell in its mode**: the read label of the step of `erwarte` names
    the flag cell, the mode of the instruction and the value read. This is the link between the instruction and the
    acquire event of `PayloadSichtbarAussage`. -/
theorem erwarte_liest_im_modus (ziel region index : Nat) (erwartet : Int) (typ : Ty .value) (m : Modus)
    (r : Rahmen) (v : Int) :
    ((Befehl.zugriff (.erwarte ziel region index erwartet typ m)).plan r v).lesen =
      [⟨.lesen, ((Befehl.zugriff (.erwarte ziel region index erwartet typ m)).operand r).ort, m, v, v⟩] :=
  rfl

/-! ### `AtomarSimAussage`: the implementation read is the ideal read under the same choice -/

/-- **A rule is faithful to the class step of a reading form.** Its implementation step is its ideal step, and every
    step it takes is the refusal of an access without authority, or the planned step for a value `v` that is the
    value of the read label it records, with the frame transfer applied to exactly that value. -/
def AtomarTreu (F : Schrittform) (R : Regel) : Prop :=
  (∀ c s w plans u, R.impl c s w plans u ↔ R.ideal c s w plans u) ∧
    ∀ c s w p u, R.impl c s w [p] u →
      (p = Semantik.plan ∧ u = F.verweigert c s) ∨
        ∃ v : Int, F.klasse.befugt (F.operand (s.lokal c)) s c ∧ p = F.plan (s.lokal c) v ∧
          u = F.zugriffNach c s v ∧ ∃ l ∈ p.lesen, l.gelesen = v

/-- **Atomic simulation, for every unit that embeds a reading form.** The rule of the unit for the form is faithful to
    the class step: implementation and ideal read take the same value under the same choice, and the frame binds
    the value of the label. -/
def AtomarSimAussage : Prop :=
  ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse.liest = true →
    F.Eingebettet E f → AtomarTreu F (E.system.regel f)

/-- The step of a reading access class is faithful to the class step. -/
theorem Schrittform.zugriffsschritt_treu (F : Schrittform) (hl : F.klasse.liest = true) {c : Kontext} {s : Zustand}
    {p : Plan} {u : Zustand} (step : F.zugriffsschritt c s [p] u) :
    (p = Semantik.plan ∧ u = F.verweigert c s) ∨
      ∃ v : Int, F.klasse.befugt (F.operand (s.lokal c)) s c ∧ p = F.plan (s.lokal c) v ∧
        u = F.zugriffNach c s v ∧ ∃ l ∈ p.lesen, l.gelesen = v := by
  rcases step with ⟨_, same, ue⟩ | ⟨g, v, _, same, ue⟩
  · exact Or.inl ⟨(List.cons.inj same).1, ue⟩
  · have hp : p = F.plan (s.lokal c) v := (List.cons.inj same).1
    refine Or.inr ⟨v, g, hp, ue, ?_⟩
    subst hp
    obtain ⟨k, o, t⟩ := F
    cases k with
    | lesen m => exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
    | rmw m => exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
    | lokal => cases hl
    | ruf => cases hl
    | schreiben _ => cases hl
    | sperre _ => cases hl
    | frage => cases hl
    | starte => cases hl
    | beende => cases hl
    | verbinde => cases hl
    | wechsle => cases hl

/-- The class rule of a reading form is faithful to the class step. -/
theorem Schrittform.atomarTreu (F : Schrittform) (hl : F.klasse.liest = true) : AtomarTreu F F.regel := by
  refine ⟨fun _ _ _ _ _ => Iff.rfl, fun c s w p u step => F.zugriffsschritt_treu hl ?_⟩
  obtain ⟨k, o, t⟩ := F
  cases k with
  | lesen m => exact step
  | rmw m => exact step
  | lokal => cases hl
  | ruf => cases hl
  | schreiben _ => cases hl
  | sperre _ => cases hl
  | frage => cases hl
  | starte => cases hl
  | beende => cases hl
  | verbinde => cases hl
  | wechsle => cases hl

/-- **Atomic simulation** (the proof of `AtomarSimAussage`). -/
theorem atomarSim : AtomarSimAussage := by
  intro ι E f F hl emb
  rw [emb.regel]
  exact F.atomarTreu hl

/-- The instruction that implements an atomic update with a LOST value: its frame receives `0` whatever the memory
    returned (the classic bug of an update split into a load and a store). It is a form of the class `rmw`. -/
def atomarBeispiel : Schrittform := ⟨.rmw .sc, fun _ => Operand.keiner, fun r _ _ => r⟩

/-- The implementation of an update that loses the value it read: it plans the step for the value `v` and applies the
    frame transfer to `0`. -/
def Schrittform.verloren (F : Schrittform) : Regel :=
  ⟨fun c s _ plans u => ∃ v : Int, plans = [F.plan (s.lokal c) v] ∧ u = F.zugriffNach c s 0, F.ideal⟩

/-- **The premises of the atomic simulation hold jointly**: a unit embeds an atomic update form, and the form has a
    step (the refusal of an access the empty state grants no handle for; `klassenNichtTrivial` shows the guarded
    class is not trivial). -/
theorem atomarSim_erfuellbar :
    ∃ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform), F.klasse.liest = true ∧ F.Eingebettet E f ∧
      ∃ (c : Kontext) (s : Zustand) (plans : List Plan) (u : Zustand), (E.system.regel f).impl c s () plans u := by
  obtain ⟨plans, u, step⟩ := atomarBeispiel.ideal_total eintritt Leerzustand ()
  exact ⟨_, Regeleinheit .x86_64 atomarBeispiel.regel, (), atomarBeispiel, rfl, ⟨rfl, rfl, rfl⟩, eintritt,
    Leerzustand, plans, u, step⟩

/-- **The atomic simulation is not trivial.** An atomic update implemented so that it loses the value it read is a
    rule the model represents, and it is NOT faithful to the class step: its implementation step is not the ideal
    step. The class rule `F.regel` is faithful (`atomarSim`); only the checker's refusal of a non-embedded rule keeps
    the lost update out of a program. -/
theorem atomarSim_nichtTrivial :
    ∃ F : Schrittform, F.klasse.liest = true ∧ ¬ AtomarTreu F F.verloren := by
  refine ⟨atomarBeispiel, rfl, fun ⟨h1, _⟩ => ?_⟩
  have impl : atomarBeispiel.verloren.impl eintritt Leerzustand ()
      [atomarBeispiel.plan (Leerzustand.lokal eintritt) 1]
      (atomarBeispiel.zugriffNach eintritt Leerzustand 0) := ⟨1, rfl, rfl⟩
  rcases (h1 eintritt Leerzustand () _ _).1 impl with ⟨_, same, _⟩ | ⟨g, _, _, _, _⟩
  · have h : (atomarBeispiel.plan (Leerzustand.lokal eintritt) 1).lesen = Semantik.plan.lesen :=
      congrArg SchrittPlan.lesen (List.cons.inj same).1
    exact List.cons_ne_nil _ _ h
  · obtain ⟨⟨_, _, hg, _⟩, _⟩ := g
    cases hg

/-! ### The open duties of the access instructions -/

/-- **Determinacy of an access instruction up to the value it reads** (open, replaces `Ideal.RegelBestimmt` for
    `Befehl.zugriff`). Two ideal steps of the same instruction from the same state, context and choice are equal
    when their recorded reads return the same values: the value read is the one thing the instruction does not
    decide; the memory model fixes it (`Speicherwahl`). Difficulty: leicht. Sketch: `zugriffsschritt` is a
    disjunction on `befugt`, which is a function of the state; in the refusal both plans are
    `Semantik.plan`; in the granted case both plans are `F.plan (s.lokal c) v` and `F.plan (s.lokal c) v'`, and the
    equality of the read values gives `v = v'` for a reading class (`Wirkungsklasse.plan` records `v` in the label)
    and `v = v' = 0` for a non-reading class (`Wirkungsklasse.Lesewert`); then the plans and the states coincide. -/
def ZugriffBestimmtAussage : Prop :=
  ∀ (z : Zugriffsform) (c : Kontext) (s : Zustand) (w : PUnit.{1}) (plans plans' : List Plan) (u u' : Zustand),
    (Befehl.zugriff z).ideal c s w plans u → (Befehl.zugriff z).ideal c s w plans' u' →
      (∀ p p', plans = [p] → plans' = [p'] → p.lesen.map (fun l => l.gelesen) = p'.lesen.map (fun l => l.gelesen)) →
        plans = plans' ∧ u = u'

/-- **Composability of the steps of an access instruction that the memory model accepts** (open, replaces
    `I.RegelKomponierbar` for `Befehl.zugriff`). If the labels the step records can be appended to the graph of the
    state (`Speicherfolge`: some reads-from and modification-order choice is RC11-consistent), the protocol executes
    the step. Difficulty: mittel. Sketch: `FuehrtSchrittAus` needs `Zustandsrahmen s u` (the access step changes the
    frame and the ledger only), the read-label condition (`Wirkungsklasse.plan` records `lesen`, `rmw` or the failed
    update's `lesen` label), the internal action with no lock events, and the given `Speicherfolge`, with the
    state `{ u with graph := g }`. -/
def ZugriffKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Zugriffsform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand)
    (es : List (SpeicherAkteur Zelle × Gabbro.Core.Speicher.Etikett Zelle Int)) (g : SpeicherGraph Zelle Int),
    (p.einheit platform).system.kopf s c = some (Befehl.zugriff z) → (Befehl.zugriff z).ideal c s w [plan] u →
      Speicherfolge s.initial (.kontext c) s.graph
        (plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert) es g →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **The registry packet of `Befehl.zugriff`**: the two duties the classes do not carry. The other duties of the access
    classes are in `KlassenAussagen` (simulation, locality, progress, the four safety legs, bounds, information flow),
    the stack effect is `klassenStapel`, the information flow of the family is `ZugriffNIAussage`. -/
def ZugriffBefehlAussage : Prop :=
  ZugriffBestimmtAussage ∧ ZugriffKomponierbarAussage

/-- **The three kernel statements of the memory and atomic instructions**, pinned together. -/
def AtomAussagen : Prop :=
  AtomarSimAussage ∧ Speicher.PayloadSichtbarAussage ∧ Sicherheit.RennfreiAusLokalAussage

/-- The kernel statements hold. -/
theorem atomAussagen : AtomAussagen :=
  ⟨atomarSim, Speicher.payloadSichtbar, Sicherheit.rennfreiAusLokal⟩

end Gabbro.Core.Ast.Semantik
