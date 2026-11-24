module

public import Core.Ast.Semantik.ProgramForms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Annahme Maschine Katalog Gabbro.Core.Text

/-- A carrier type can occur in a signature even when its set of values is empty. -/
def carrierTypeForm (scope : Scope) (belongs : WrittenType → Prop) :
    Quellform (.declaration scope)
      {args : Surface.FunctionArgs scope // ∃ p ∈ args.parameters, belongs p.written} :=
  let fn := functionForm scope
  { produktion := ⟨fun args => fn.produktion.tree args.val,
                   fun args => fn.produktion.production args.val⟩
    befehl := fun args => fn.befehl args.val
    position := fun args => fn.position args.val }

def indexTypeUse : WrittenType → Prop
  | .index .. => True
  | _ => False

def indexOptionTypeUse : WrittenType → Prop
  | .indexOption .. => True
  | _ => False

/-- The registered signature contains exactly the resolved parameter types. -/
def CarrierParameterEffect (scope : Scope) (args : Surface.FunctionArgs scope)
    (frame : Rahmen) : Prop :=
  let after := ((functionForm scope).befehl args).auswerten frame
  ∃ signature, after.funktionen = signature :: frame.funktionen ∧
    signature.name = args.name ∧ signature.parameter = args.parameters.map (·.written.type)

/-- The registered signature is observed at the reachable source occurrence. -/
def CarrierParameterErfuellbar (scope : Scope) (belongs : WrittenType → Prop)
    (platform : Plattform) (start : AussenStart)
    (args : {args : Surface.FunctionArgs scope // ∃ p ∈ args.parameters, belongs p.written}) : Prop :=
  let form := carrierTypeForm scope belongs
  let E := form.einheit platform args
  ∃ (text : RawText) (s : Zustand),
    Ast.Parse text (form.produktion.tree args) ∧ Elaboriert platform (form.produktion.tree args) E ∧
    E.system.IErreichbar (I.start E start).2 s ∧ Realisiert form platform args s ∧
    (∀ g : Bedarf, (form.befehl args).guard (s.lokal eintritt) = some g → waechterBedarf g.1 g.2) ∧
    CarrierParameterEffect scope args.val (s.lokal eintritt)

end Gabbro.Core.Ast.Semantik
