module

public import Core.Ast.Semantik.BatchForms
public import Core.Ast.ProgramSurface
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Atom.Quelle

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

def returnVoidForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.ReturnVoidArgs scope result) where
  produktion := Surface.returnVoid scope result
  befehl := fun _ => .rueckVoid
  position := fun _ => 0

def returnVoidJoint : Prop :=
  ∀ platform start, ∃ a, (returnVoidForm [] none).ErfuellbarAm platform start a

def mutableLocalForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.MutableLocalArgs scope result) where
  produktion := Surface.mutableLocal scope result
  befehl := fun a => .bindeWert 0 a.written.type false
  position := fun a => (expr 0 a.value).code.length

def mutableLocalJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a, ((fun ctx => mutableLocalForm ctx.1 ctx.2) ctx).ErfuellbarAm platform start a

def directCallForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.DirectCallArgs scope result) where
  produktion := Surface.directCall scope result
  befehl := fun a => callInstruction a none
  position := fun a => (argsCode 0 a.args).code.length

/-- Joint call premises include a successful transfer inside a whole source unit. -/
def LaufenderRuf (platform : Plattform) (start : AussenStart) (b : Befehl) : Prop :=
  ∃ (unit : Ast.Unit) (text : Text.RawText) (s : Zustand),
    Ast.Parse (category := .unit) text unit ∧
    let E := elaborieren platform (category := .unit) unit
    let next := b.nach eintritt s
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s eintritt = some b ∧
      E.system.ISchritt eintritt s () [b.plan (s.lokal eintritt) 0] next ∧
      E.system.ImplSchritt eintritt s () [b.plan (s.lokal eintritt) 0] next ∧
      (next.lokal eintritt).stopp = none ∧
      (next.lokal eintritt).fortsetzungen.length = (s.lokal eintritt).fortsetzungen.length + 1

def directCallJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a,
    (directCallForm ctx.1 ctx.2).ErfuellbarAm platform start a ∧
      LaufenderRuf platform start ((directCallForm ctx.1 ctx.2).befehl a)

def bindDirectForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.BindDirectArgs scope result) where
  produktion := Surface.bindDirect scope result
  befehl := fun a => callInstruction a.call (some a.written.type)
  position := fun a => (argsCode 0 a.call.args).code.length

def bindDirectJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a,
    (bindDirectForm ctx.1 ctx.2).ErfuellbarAm platform start a ∧
      LaufenderRuf platform start ((bindDirectForm ctx.1 ctx.2).befehl a)

def boundedWhileForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.BoundedWhileArgs scope result) where
  produktion := Surface.boundedWhile scope result
  befehl := fun a => whileInstruction a.condition (bracedBlock a.body) a.overflow
  position := fun a => (expr 0 a.bound).code.length + 1 + (expr 0 a.condition).code.length

def boundedWhileJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a, ((fun ctx => boundedWhileForm ctx.1 ctx.2) ctx).ErfuellbarAm platform start a

def forRangeForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.ForRangeArgs scope result) where
  produktion := Surface.forRange scope result
  befehl := fun a => forInstruction (bracedBlock a.body) a.overflow
  position := fun a => (expr 0 a.lower).code.length + (expr 1 a.upper).code.length + 1

def forRangeJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a, ((fun ctx => forRangeForm ctx.1 ctx.2) ctx).ErfuellbarAm platform start a

def foreverForm (scope : Scope) (result : Option (Ty .value)) : Quellform (.statement scope result) (Surface.ForeverArgs scope result) where
  produktion := Surface.forever scope result
  befehl := fun a => .zurueckSprung (bracedBlock a.body).code.length
  position := fun a => (bracedBlock a.body).code.length

def foreverJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a, ((fun ctx => foreverForm ctx.1 ctx.2) ctx).ErfuellbarAm platform start a

/-- The descriptor of an access statement: the elaboration evaluates the index (and the value) into
    the temporaries `0` (and `1`), then ONE access instruction names the region by the position of its
    owner local (`accessCode`); the instruction is at the end of the evaluated operands. -/
def accessForm (scope : Scope) (result : Option (Ty .value)) :
    Zugriffsquelle (.statement scope result) (AccessStatement scope) where
  produktion := Surface.access scope result
  form := fun ⟨_, form⟩ => match form with
    | .load _ _ written _ region _ _ _ mode => .lade 0 region.index 0 written.type mode.modus
    | .store region _ _ _ _ mode => .speichere region.index 0 1 mode.modus
    | .swap _ _ written _ region _ _ _ _ mode => .tausche 0 region.index 0 1 written.type mode.modus
    | .vergleicheTausche _ _ written _ region _ _ _ _ _ mode =>
      .vergleicheTausche 0 region.index 0 1 2 written.type mode.modus
    | .holeUndAddiere _ _ written _ region _ _ _ _ mode =>
      .holeUndAddiere 0 region.index 0 1 written.type mode.modus
    | .erwarte _ _ written _ region _ _ _ marker mode =>
      .erwarte 0 region.index 0 marker written.type mode.modus
    | .veroeffentliche region _ _ _ _ mode => .veroeffentliche region.index 0 1 mode.modus
  position := fun ⟨_, form⟩ => match form with
    | .load _ _ _ _ _ _ _ index _ => (expr 0 index).code.length
    | .store _ _ _ index value _ => (expr 0 index).code.length + (expr 1 value).code.length
    | .swap _ _ _ _ _ _ _ index value _ => (expr 0 index).code.length + (expr 1 value).code.length
    | .vergleicheTausche _ _ _ _ _ _ _ index expected neu _ =>
      (expr 0 index).code.length + (expr 1 expected).code.length + (expr 2 neu).code.length
    | .holeUndAddiere _ _ _ _ _ _ _ index betrag _ =>
      (expr 0 index).code.length + (expr 1 betrag).code.length
    | .erwarte _ _ _ _ _ _ _ index _ _ => (expr 0 index).code.length
    | .veroeffentliche _ _ _ index value _ => (expr 0 index).code.length + (expr 1 value).code.length

def accessJoint : Prop :=
  ∀ platform start, ∃ (ctx : StatementContext), ∃ a, ((fun ctx => accessForm ctx.1 ctx.2) ctx).ErfuellbarAm platform start a

def constantForm (scope : Scope) : Quellform (.declaration scope) (Surface.ConstantArgs scope) where
  produktion := Surface.constant scope
  befehl := fun a => .bindeWert 0 a.written.type true
  position := fun a => (expr 0 a.value).code.length

def constantJoint : Prop :=
  ∀ platform start, ∃ (ctx : Scope), ∃ a, ((constantForm) ctx).ErfuellbarAm platform start a

def functionForm (scope : Scope) : Quellform (.declaration scope) (Surface.FunctionArgs scope) where
  produktion := Surface.function scope
  befehl := fun a => functionInstruction scope a.name a.parameters a.result a.measure.isSome
    (functionCode a.result a.measure a.body) (declaredEffects a.effects)
  position := fun _ => 0

def functionJoint : Prop :=
  ∀ platform start, ∃ (ctx : Scope), ∃ a, ((functionForm) ctx).ErfuellbarAm platform start a

def programForm  : Quellform (.unit) (Surface.ProgramArgs) where
  produktion := Surface.program
  befehl := fun _ => .starte mainName
  position := fun a => (unitBody a.unit.2).code.length

def programJoint : Prop :=
  ∀ platform start, ∃ a, programForm.ErfuellbarAm platform start a ∧
    LaufenderRuf platform start (programForm.befehl a)

end Gabbro.Core.Ast.Semantik
