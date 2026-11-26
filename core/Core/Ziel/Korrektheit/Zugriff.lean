/-
  File:      core/Core/Ziel/Korrektheit/Zugriff.lean
   Subject:   THE GOAL LEGS FOR FRAGMENTS WITH ACCESS INSTRUCTIONS (MK-04b). The proofs of the safety, noninterference
              and `I` legs of `Ziel/Korrektheit` for frame-only fragments rest on `fragment_rein`: every instruction
              of such a fragment is frame-only (`Befehl.Privat`), whose step is the template `impl ≡ ideal`. A source
              form that elaborates to an
             access instruction (`Zugriffsquelle`) makes a fragment that is not: its instruction reads a value the memory
             model chooses, so the template does not apply. The legs for such a fragment (`Fragment.MitZugriff`) rest on
             the duties of the access classes instead. What the classes carry is proved (`KlassenAussagen`,
             `ZugriffBefehlAussage`, `AtomAussagen`); what is left is pinned HERE, as four independent statements
             under ONE root, `ZugriffZielAussage`:
             * `Ast.Semantik.ZugriffSicherAussage` (in `UnitInvarianten`, where `InvariantenSicherheitAussage` needs it): the four
               safety legs of a run of the fragment of a source unit with an access;
             * `ZugriffIdealBestimmtAussage`: the composed `I` step of such a fragment is determined by the source choice
               and the resolution of the memory order (`I.Bestimmt`);
             * `ZugriffSchrittExistiertAussage`: the memory model offers a read to every access head (the liveness
               of the memory model); `I.Fortschritt` follows (`fortschritt_mitZugriff`);
             * `ZugriffNIFragmentAussage`: an accepted fragment with an access is noninterferent.
             Each is a statement about a NONEMPTY set of fragments (`mitZugriff_erfuellbar`) and each fails for the model if
             the corresponding duty of the access classes is dropped, so none is vacuous.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Klassenrein
public import Core.Ast.Semantik.Runtime.Atom.Quelle
public import Core.Sicherheit.RegelnErfuellbar
public import Core.Ast.Semantik.Runtime.UnitInvarianten
public import Core.Beobachtung.Satz
public import Core.Annahme.Annahme
public import Core.Ideal.Komposition

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine

/-- **The composed step of a fragment with an access instruction is determined** by the source choice and the
    resolution of the memory order. Difficulty: mittel. Sketch: two composed steps at one context have the same head
    (`kopf` of one state); a frame-only head is `Befehl.bestimmt`; for an access head, `ZugriffBestimmtAussage`
    makes the plans and the successors equal once the read values are equal, and the read value is fixed by the
    graph: `SpeicherWahlGleich` equates `po`, `rf`, `mo`, the new events have equal labels up to the value read
    (`Speicherfolge.ausgabe`), and the value of a read equals the value written by its `rf` source, which is an event
    of the common prefix. The step `FuehrtSchrittAus.bestimmt` then gives equal traces and states. -/
def ZugriffIdealBestimmtAussage : Prop :=
  ∀ (p : Ast.Semantik.Fragment) (platform : Katalog.Plattform), p.MitZugriff →
    Maschine.I.Bestimmt (p.einheit platform).einrichtung (p.einheit platform).system

/-- **The memory model offers a read to every access head.** In a consistent complete memory, an access instruction
    at the head of a context has an ideal step whose labels the memory model can append: some value is readable (the
    liveness of the memory model; the initial write of a location is materialised lazily and a read of a location with
    a coherent write exists). No well-formedness premise is needed: the step of a form the checker refuses (`na` update,
    whose `rmw` event no consistent memory accepts) takes its refusal branch and records no memory event. Difficulty:
    mittel. Sketch: for a load, an update or the confirming observation take the modification-order maximal write of
    the cell visible to the context (`Initialisierung` supplies the initial write if there is none) as the reads-from
    source, and extend `rf`, `mo` and the events accordingly (`Speicherfolge.cons`); a store extends `mo` at the end;
    a refused form keeps the graph. The plan is `Wirkungsklasse.plan` at that value, the authority decision is the
    state's. -/
def ZugriffSchrittExistiertAussage : Prop :=
  ∀ (p : Ast.Semantik.Fragment) (platform : Katalog.Plattform) (z : Ast.Semantik.Zugriffsform) (s : Ast.Semantik.Zustand) (c : Kontext),
    (p.einheit platform).system.kopf s c = some (Ast.Semantik.Befehl.zugriff z) → s.SpeicherGut →
      ∃ (w : PUnit.{1}) (plan : Ast.Semantik.Plan) (u : Ast.Semantik.Zustand)
        (es : List (SpeicherAkteur Ast.Semantik.Zelle × Gabbro.Core.Speicher.Etikett Ast.Semantik.Zelle Int))
        (g : SpeicherGraph Ast.Semantik.Zelle Int),
        (Ast.Semantik.Befehl.zugriff z).ideal c s w [plan] u ∧
          Speicherfolge s.initial (.kontext c) s.graph
            (plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert) es g

/-- **An accepted fragment with an access instruction is noninterferent.** Difficulty: schwer. Sketch: the coupling
    machinery of `FragmentNIBeweise` runs over the steps of two low-equal runs. The `zugriff` family case is
    `ZugriffNIAussage` (the flow rule of the labelled unit for an access: the label rule of a memory event, MK-13),
    the pause case `PauseNIAussage` is stated for frame-only code and is to be stated for the two classes, and the
    silence of a frame-only step (`fragment_kontext_schritt_still`) is replaced for an access by its plan: a store
    records its written cell (`PlanSicht` shows it for a public cell), a load puts the value of its `rf` source into
    the frame, which the coupled runs choose equal for a public cell (the graph-level coupling of MK-13). -/
def ZugriffNIFragmentAussage : Prop :=
  ∀ (p : Ast.Semantik.Fragment) (platform : Katalog.Plattform), p.MitZugriff →
    Annahme.Akzeptiert (p.einheit platform) → Beobachtung.Nichtinterferent (p.einheit platform)

/-- **The root of the goal legs for a fragment with an access instruction.** -/
def ZugriffZielAussage : Prop :=
  Ast.Semantik.ZugriffSicherAussage ∧ ZugriffIdealBestimmtAussage ∧ ZugriffSchrittExistiertAussage ∧ ZugriffNIFragmentAussage

/-- **The statements are about a nonempty set of fragments**: the unit of one load is a fragment with an access
    instruction (frame-only code is excluded, so no frame-only theorem applies to it). -/
theorem mitZugriff_erfuellbar : ∃ p : Ast.Semantik.Fragment, p.MitZugriff :=
  ⟨_, Ast.Semantik.Fragment.einzel_zugriff_mitZugriff
    (.lade 0 0 0 (Ast.Ty.int 0 0) Gabbro.Core.Speicher.Modus.na)⟩

/-- **Every head of a fragment of the two classes has a step that composes with the protocol**, from the liveness of the
    memory model. A frame-only head steps by its template (`Befehl.vollzug`); an access head steps by the step the memory
    model offers (`ZugriffSchrittExistiertAussage`), which composes with the protocol (`zugriffKomponierbar`). -/
theorem komponierbar_koepfe (existiert : ZugriffSchrittExistiertAussage) (p : Ast.Semantik.Fragment)
    (platform : Katalog.Plattform) (klassenrein : p.KlassenRein) :
    ∀ i t s c, (p.einheit platform).system.kopf s c = some i → s.SpeicherGut →
      ∃ w plan u spur s', ((p.einheit platform).system.regel i).ideal c s w [plan] u ∧
        FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s' := by
  intro i t s c head memory
  rcases klassenrein i (Ast.Semantik.kopf_mem (code := p.code) head) with privat | ⟨z, same⟩
  · exact ⟨(), Ast.Semantik.plan, i.nach c s, ⟨[], []⟩, i.nach c s,
      (i.ideal_privat privat c s () [Ast.Semantik.plan] (i.nach c s)).2 ⟨rfl, rfl⟩, i.vollzug _ t c s⟩
  · subst same
    obtain ⟨w, plan, u, es, g, step, folge⟩ := existiert p platform z s c head memory
    obtain ⟨spur, s', run⟩ := Ast.Semantik.zugriffKomponierbar p platform z t s c w plan u es g head step folge
    exact ⟨w, plan, u, spur, s', step, run⟩

/-- **`I.Fortschritt` for a fragment of the two classes, from the liveness of the memory model.** -/
theorem fortschritt_klassenrein (existiert : ZugriffSchrittExistiertAussage) (p : Ast.Semantik.Fragment)
    (platform : Katalog.Plattform) (klassenrein : p.KlassenRein) :
    Maschine.I.Fortschritt (p.einheit platform).einrichtung (p.einheit platform).system :=
  Maschine.I.fortschritt_aus_koepfen _ _ (Ast.Semantik.Fragment.fertig p platform)
    (fun b => b.regelFortschritt p platform) (komponierbar_koepfe existiert p platform klassenrein)

end Gabbro.Core.Ziel.Korrektheit
