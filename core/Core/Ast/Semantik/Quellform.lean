module

public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Surface
public import Core.Waechter.Registry

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text (RawText Lexed canonicalTokens)
open Lean (Name)

/-- The semantic occurrence of a surface production is its instruction at the
    constructor's linearisation point in the compositional output. -/
structure Quellform (category : Category) (Arguments : Type) where
  produktion : Surface.Rule category Arguments
  befehl : Arguments → Befehl
  position : Arguments → Nat

variable {category : Category} {Arguments : Type} (form : Quellform category Arguments)

def Quellform.fragment (args : Arguments) : Fragment :=
  Semantik.fragment category (form.produktion.tree args)

def Quellform.einheit (platform : Plattform) (args : Arguments) : Einheit :=
  (form.fragment args).einheit platform

def Quellform.RegelAmOrt : Prop :=
  ∀ args, (form.fragment args).code[form.position args]? = some (form.befehl args)

/-- The actual root instruction is present and can execute in both machines at this occurrence. -/
def Realisiert (platform : Plattform) (args : Arguments) (s : Zustand) : Prop :=
  let b := form.befehl args
  let E := form.einheit platform args
  (s.lokal eintritt).pc = form.position args ∧
  E.system.kopf s eintritt = some b ∧
  E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) ∧
  E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s)

theorem Quellform.realisiert (position : form.RegelAmOrt) (platform : Plattform)
    (args : Arguments) (s : Zustand) (running : s.status eintritt = .laeuft)
    (active : (s.lokal eintritt).rueckgabe = none)
    (live : (s.lokal eintritt).stopp.isNone = true)
    (atPc : (s.lokal eintritt).pc = form.position args) :
    Realisiert form platform args s := by
  have head : kopf (form.fragment args).code s eintritt = some (form.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc, position args]
  exact ⟨atPc, head, ⟨_, head, ((form.befehl args).ideal_privat eintritt s () [plan] _).2 ⟨rfl, rfl⟩⟩,
    ⟨_, head, ((form.befehl args).impl_privat eintritt s () [plan] _).2 ⟨rfl, rfl⟩⟩⟩

/-- Elaboration-independent part of the schema supplies the real raw grammar proof. -/
def Quellform.ParseAussage : Prop :=
  ∀ args text pieces, Lexed text pieces → form.produktion.production args (canonicalTokens pieces) →
    Ast.Parse text (form.produktion.tree args)

def Quellform.ElaboriertAussage : Prop :=
  ∀ platform args, Elaboriert platform (form.produktion.tree args) (form.einheit platform args)

def Quellform.RealisiertAussage : Prop :=
  ∀ platform args s, s.status eintritt = .laeuft →
    (s.lokal eintritt).rueckgabe = none → (s.lokal eintritt).stopp.isNone = true →
    (s.lokal eintritt).pc = form.position args → Realisiert form platform args s

def Quellform.AnnahmeAussage : Prop :=
  ∀ platform args,
    let E := form.einheit platform args
    let b := form.befehl args
    RegelLokal E b ∧
    (∀ s c (g : Bedarf), E.system.kopf s c = some b →
      b.guard (s.lokal c) = some g → E.quelltabellen.guard s g.1 g.2) ∧
    ∀ t c s w stepPlan u spur next, (E.system.regel b).ideal c s w [stepPlan] u →
      FuehrtSchrittAus E.einrichtung t c s u stepPlan spur next →
      ∀ ev : FrageEreignis, Ereignis.frage ev ∉ spur.aussen

def Quellform.IdealAussage : Prop :=
  form.RegelAmOrt ∧ ∀ args, Ideal.RegelBestimmt (form.befehl args).regel ∧
    ∀ c s w plans u, (form.befehl args).ideal c s w plans u ↔
      plans = [plan] ∧ u = (form.befehl args).nach c s

def Quellform.EinheitAussage : Prop :=
  ∀ platform args,
    let b := form.befehl args
    (form.einheit platform args).stotterLaenge b = 0 ∧
    ∀ andere, Kommutation b.vor b.danach andere

def Quellform.ImplAussage : Prop :=
  ∀ args c s w plans u, (form.befehl args).impl c s w plans u ↔
    plans = [plan] ∧ u = (form.befehl args).nach c s

/-- Both implementation safety obligations travel with each source form's preservation proof. -/
def Quellform.SicherheitsAussage : Prop :=
  ∀ platform args,
    Sicherheit.RegelPflichten ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def Quellform.ErhaltungsAussage : Prop :=
  ∀ platform args,
    let p := form.fragment args
    let E := p.einheit platform
    let b := form.befehl args
    I.RegelAbgleich E b ∧ Ideal.RegelFortschritt E.system b ∧
      I.RegelKomponierbar E.einrichtung E.system b ∧
      Sicherheit.RegelPflichten (p.sicherheitsEinheit platform) b

/-- Recover the safety statement from the typed registry preservation proof. -/
theorem Quellform.sicherheit_aus_erhaltung (erhaltung : form.ErhaltungsAussage) :
    form.SicherheitsAussage :=
  fun platform args => (erhaltung platform args).2.2.2

/-- The common joint premise includes a real typed source, reachability
    of its occurrence from canonical initialisation and every guard at that occurrence. -/
def Quellform.ErfuellbarAm (platform : Plattform) (start : AussenStart) (args : Arguments) : Prop :=
  let E := form.einheit platform args
  ∃ (text : RawText) (s : Zustand),
    Ast.Parse text (form.produktion.tree args) ∧ Elaboriert platform (form.produktion.tree args) E ∧
    E.system.IErreichbar (I.start E start).2 s ∧ Realisiert form platform args s ∧
    ∀ (g : Bedarf), (form.befehl args).guard (s.lokal eintritt) = some g →
      waechterBedarf g.1 g.2

def Quellform.statements {Context : Type} {cat : Context → Category} {args : Context → Type}
    (forms : (scope : Context) → Quellform (cat scope) (args scope))
    (joint : Prop) (constructor : Name) : RegistryStatements constructor .surface where
  realization := .surface (∀ scope, (forms scope).ParseAussage)
    (∀ scope, (forms scope).ElaboriertAussage) (∀ scope, (forms scope).RealisiertAussage)
  acceptanceRule := ∀ scope, (forms scope).AnnahmeAussage
  idealRule := ∀ scope, (forms scope).IdealAussage
  unitsAndCommutation := ∀ scope, (forms scope).EinheitAussage
  implementationRule := ∀ scope, (forms scope).ImplAussage
  preservation := ∀ scope, (forms scope).ErhaltungsAussage
  jointlySatisfiable := joint

end Gabbro.Core.Ast.Semantik
