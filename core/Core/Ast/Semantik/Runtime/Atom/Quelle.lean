/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Quelle.lean
  Subject:   THE ELABORATION FRAME OF THE ACCESS FORMS OF THE SOURCE (MK-04b). `Quellform` is the frame of a
             source form whose instruction is FRAME-ONLY (`Befehl.Privat`): its instruction is determined by the state,
             has the template step `impl ≡ ideal`, and is the single linearisation point of its unit. A source form
             that elaborates to an ACCESS instruction (`Befehl.zugriff`) is not that: the value a load or an update
             reads is chosen by the memory model, so the instruction is determined only up to the value read
             (`ZugriffBestimmtAussage`), and its composition with the protocol needs the step the memory model accepts
             (`ZugriffKomponierbarAussage`). `Zugriffsquelle` is the counterpart of `Quellform` for these forms. Its
             statements are the statements of `Quellform` with the access step in the place of the template step:
             * `Realisiert`: at its occurrence the instruction is the head of the running context and BOTH machines
               have a step (the class rule is total, `Schrittform.ideal_total`; the value it reads is the memory model's);
             * `AnnahmeAussage`: the step is covered by authority (`RegelLokal`), the instruction has no guard that
               needs a table fact, and every step it takes has the internal action, so it asks no question;
             * `IdealAussage`: the ideal step is the step of the class (`zugriffsschritt`: refuse without authority,
               else read any value), and it is determined up to the value read, which replaces
               `Ideal.RegelBestimmt`;
             * `ImplAussage`: the implementation step is the ideal step (one linearisation point);
             * `ErhaltungsAussage`: state match, progress, composability of the steps the memory model accepts, and
               the four class-determined safety legs. The race leg and the invariant legs are NOT class duties and
               are NOT claimed here: they belong to the fragment (`ZugriffSicherAussage`).
             A form of the source states only what is specific to its production: `ParseAussage`, `ElaboriertAussage`,
             `RegelAmOrt` and the joint satisfiability. Everything else is generic and proved once here
             (`Zugriffsquelle.aussage`). The registry entry of a surface constructor that elaborates to an access is the
             conjunction `Zugriffsquelle.Aussage` of the nine statements.
-/
module

public import Core.Ast.Semantik.Quellform
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Bestimmt
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Komponierbar
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Gesamt
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text (RawText Lexed canonicalTokens)

/-- **The registry packet of `Befehl.zugriff` is proved.** The two duties the classes do not carry: determinacy up to the
    value read and composability of the steps the memory model accepts. -/
theorem zugriffBefehl : ZugriffBefehlAussage := ⟨zugriffBestimmt, zugriffKomponierbar⟩

/-- **A source form that elaborates to an access instruction**: its production, the access it elaborates to and the
    position of that instruction in the compositional output. -/
structure Zugriffsquelle (category : Category) (Arguments : Type) where
  produktion : Surface.Rule category Arguments
  form : Arguments → Zugriffsform
  position : Arguments → Nat

variable {category : Category} {Arguments : Type} (quelle : Zugriffsquelle category Arguments)

/-- The instruction of the form. -/
def Zugriffsquelle.befehl (args : Arguments) : Befehl := .zugriff (quelle.form args)

def Zugriffsquelle.fragment (args : Arguments) : Fragment :=
  Semantik.fragment category (quelle.produktion.tree args)

def Zugriffsquelle.einheit (platform : Plattform) (args : Arguments) : Einheit :=
  (quelle.fragment args).einheit platform

def Zugriffsquelle.RegelAmOrt : Prop :=
  ∀ args, (quelle.fragment args).code[quelle.position args]? = some (quelle.befehl args)

/-- The actual access instruction is the head of the running context at its occurrence, and both machines have a step
    there: the class rule is total, the value a read returns is the memory model's choice. -/
def Zugriffsquelle.Realisiert (platform : Plattform) (args : Arguments) (s : Zustand) : Prop :=
  let b := quelle.befehl args
  let E := quelle.einheit platform args
  (s.lokal eintritt).pc = quelle.position args ∧
  E.system.kopf s eintritt = some b ∧
  (∃ plans u, E.system.ISchritt eintritt s () plans u) ∧
  (∃ plans u, E.system.ImplSchritt eintritt s () plans u)

theorem Zugriffsquelle.realisiert (position : quelle.RegelAmOrt) (platform : Plattform)
    (args : Arguments) (s : Zustand) (running : s.status eintritt = .laeuft)
    (active : (s.lokal eintritt).rueckgabe = none)
    (live : (s.lokal eintritt).stopp.isNone = true)
    (atPc : (s.lokal eintritt).pc = quelle.position args) :
    quelle.Realisiert platform args s := by
  have head : kopf (quelle.fragment args).code s eintritt = some (quelle.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc, position args]
  obtain ⟨plans, u, step⟩ := (quelle.befehl args).form.ideal_total eintritt s ()
  exact ⟨atPc, head, ⟨plans, u, _, head, step⟩, ⟨plans, u, _, head, step⟩⟩

/-- The raw grammar proof of the production. -/
def Zugriffsquelle.ParseAussage : Prop :=
  ∀ args text pieces, Lexed text pieces → quelle.produktion.production args (canonicalTokens pieces) →
    Ast.Parse text (quelle.produktion.tree args)

def Zugriffsquelle.ElaboriertAussage : Prop :=
  ∀ platform args, Elaboriert platform (quelle.produktion.tree args) (quelle.einheit platform args)

def Zugriffsquelle.RealisiertAussage : Prop :=
  ∀ platform args s, s.status eintritt = .laeuft →
    (s.lokal eintritt).rueckgabe = none → (s.lokal eintritt).stopp.isNone = true →
    (s.lokal eintritt).pc = quelle.position args → quelle.Realisiert platform args s

/-- Acceptance of the instruction's step: covered by authority, no guard that needs a table fact, and every step is the
    internal action (an access asks no question of the outside world). -/
def Zugriffsquelle.AnnahmeAussage : Prop :=
  ∀ platform args,
    let E := quelle.einheit platform args
    let b := quelle.befehl args
    RegelLokal E b ∧
    (∀ s c (g : Bedarf), E.system.kopf s c = some b →
      b.guard (s.lokal c) = some g → E.quelltabellen.guard s g.1 g.2) ∧
    ∀ c s w (stepPlan : Plan) u, (E.system.regel b).ideal c s w [stepPlan] u → stepPlan.aktion = .intern

/-- The ideal step is the step of the class, and it is determined up to the value it reads. -/
def Zugriffsquelle.IdealAussage : Prop :=
  quelle.RegelAmOrt ∧ ∀ args,
    (∀ c s w plans u, (quelle.befehl args).ideal c s w plans u ↔
      (quelle.befehl args).form.zugriffsschritt c s plans u) ∧
    ∀ c s w plans plans' u u', (quelle.befehl args).ideal c s w plans u →
      (quelle.befehl args).ideal c s w plans' u' →
      (∀ p p', plans = [p] → plans' = [p'] →
        p.lesen.map (fun l => l.gelesen) = p'.lesen.map (fun l => l.gelesen)) →
      plans = plans' ∧ u = u'

/-- One linearisation point, no stutter: the instruction is its unit's single linearisation point. -/
def Zugriffsquelle.EinheitAussage : Prop :=
  ∀ platform args,
    let b := quelle.befehl args
    (quelle.einheit platform args).stotterLaenge b = 0 ∧
    ∀ andere, Kommutation b.vor b.danach andere

/-- The implementation step is the ideal step. -/
def Zugriffsquelle.ImplAussage : Prop :=
  ∀ args c s w plans u,
    (quelle.befehl args).impl c s w plans u ↔ (quelle.befehl args).ideal c s w plans u

/-- State match, progress, composability of the accepted steps, and the four class-determined safety legs. The race
    leg and the invariant legs are the fragment's (`ZugriffSicherAussage`). -/
def Zugriffsquelle.ErhaltungsAussage : Prop :=
  ∀ platform args,
    let p := quelle.fragment args
    let E := p.einheit platform
    let b := quelle.befehl args
    I.RegelAbgleich E b ∧ Ideal.RegelFortschritt E.system b ∧
      (∀ t s c w plan u es g, E.system.kopf s c = some b → b.ideal c s w [plan] u →
        Speicherfolge s.initial (.kontext c) s.graph
          (plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert) es g →
        ∃ spur s', FuehrtSchrittAus E.einrichtung t c s u plan spur s') ∧
      KlassenSicherheitAussage b.klasse

/-- The common joint premise includes a real typed source, reachability of its occurrence from canonical
    initialisation and every guard at that occurrence. -/
def Zugriffsquelle.ErfuellbarAm (platform : Plattform) (start : AussenStart) (args : Arguments) : Prop :=
  let E := quelle.einheit platform args
  ∃ (text : RawText) (s : Zustand),
    Ast.Parse text (quelle.produktion.tree args) ∧ Elaboriert platform (quelle.produktion.tree args) E ∧
    E.system.IErreichbar (I.start E start).2 s ∧ quelle.Realisiert platform args s ∧
    ∀ (g : Bedarf), (quelle.befehl args).guard (s.lokal eintritt) = some g →
      waechterBedarf g.1 g.2

/-- **The nine statements of a source form that elaborates to an access**, with the joint satisfiability `joint` the
    production names. -/
def Zugriffsquelle.Aussage (joint : Prop) : Prop :=
  quelle.ParseAussage ∧ quelle.ElaboriertAussage ∧ quelle.RealisiertAussage ∧ quelle.AnnahmeAussage ∧
    quelle.IdealAussage ∧ quelle.EinheitAussage ∧ quelle.ImplAussage ∧ quelle.ErhaltungsAussage ∧ joint

/-! ### The generic proofs -/

/-- The ideal step of an access instruction is the step of its class. -/
theorem Zugriffsform.ideal_iff (z : Zugriffsform) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    (Befehl.zugriff z).ideal c s w plans u ↔ (Befehl.zugriff z).form.zugriffsschritt c s plans u := by
  cases z <;> exact Iff.rfl

/-- **Every step of an access instruction has the internal action**: it asks no question and starts no thread. -/
theorem Zugriffsform.ideal_aktion_intern (z : Zugriffsform) {c : Kontext} {s : Zustand} {w : PUnit.{1}}
    {plan : Plan} {u : Zustand} (step : (Befehl.zugriff z).ideal c s w [plan] u) : plan.aktion = .intern := by
  have step' := (z.ideal_iff c s w [plan] u).1 step
  rcases step' with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩
  · have e : plan = Semantik.plan := (List.cons.inj same).1
    subst e
    rfl
  · have e : plan = (Befehl.zugriff z).form.plan (s.lokal c) v := (List.cons.inj same).1
    subst e
    obtain h | h | h | h := z.klasse_modus
    · show (z.klasse.plan _ _).aktion = .intern
      rw [h]
      rfl
    · show (z.klasse.plan _ _).aktion = .intern
      rw [h]
      rfl
    · show (z.klasse.plan _ _).aktion = .intern
      rw [h]
      rfl
    · show (z.klasse.plan _ _).aktion = .intern
      rw [h]
      rfl

/-- The class-step instance of `AnnahmeAussage` holds for every access. -/
theorem Zugriffsquelle.annahme : quelle.AnnahmeAussage := by
  intro platform args
  dsimp only
  refine ⟨(quelle.befehl args).regelLokal (quelle.fragment args) platform, ?_, ?_⟩
  · intro s c g _ h
    have none : Befehl.guard (quelle.befehl args) (s.lokal c) = none := rfl
    rw [none] at h
    cases h
  · intro c s w plan u step
    exact (quelle.form args).ideal_aktion_intern (w := w) step

theorem Zugriffsquelle.ideal (position : quelle.RegelAmOrt) : quelle.IdealAussage := by
  refine ⟨position, fun args => ⟨fun c s w plans u => (quelle.form args).ideal_iff c s w plans u, ?_⟩⟩
  intro c s w plans plans' u u' h h' reads
  exact zugriffBestimmt (quelle.form args) c s w plans plans' u u' h h' reads

theorem Zugriffsquelle.einheitAussage : quelle.EinheitAussage := by
  intro platform args
  dsimp only
  exact ⟨rfl, (quelle.befehl args).kommutation⟩

theorem Zugriffsquelle.impl : quelle.ImplAussage :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem Zugriffsquelle.erhaltung : quelle.ErhaltungsAussage := by
  intro platform args
  dsimp only
  refine ⟨(quelle.befehl args).abgleich (quelle.fragment args) platform,
    (quelle.befehl args).regelFortschritt (quelle.fragment args) platform, ?_, klassenSicherheit _⟩
  intro t s c w plan u es g head step folge
  exact zugriffKomponierbar (quelle.fragment args) platform (quelle.form args) t s c w plan u es g head step folge

/-- **Everything but the production-specific part is generic**: a source form that elaborates to an access carries its
    nine statements as soon as its grammar proof, its elaboration, its occurrence and its joint satisfiability are
    proved. -/
theorem Zugriffsquelle.aussage (joint : Prop) (parse : quelle.ParseAussage)
    (elaboriert : quelle.ElaboriertAussage) (position : quelle.RegelAmOrt) (erfuellbar : joint) :
    quelle.Aussage joint :=
  ⟨parse, elaboriert, fun platform args s running active live atPc =>
    quelle.realisiert position platform args s running active live atPc, quelle.annahme,
    quelle.ideal position, quelle.einheitAussage, quelle.impl, quelle.erhaltung, erfuellbar⟩

end Gabbro.Core.Ast.Semantik
