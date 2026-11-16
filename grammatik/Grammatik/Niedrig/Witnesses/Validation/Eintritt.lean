module

public import Grammatik.Niedrig.Eingang.Rahmen

@[expose] public section

namespace Gabbro.Grammatik.Niedrig.Eingang

open Gabbro.Grammatik

/-! ## N5: an interrupt entry without a stack description is refused -/

/-- An IRQ entry record, otherwise valid, with an empty stack description. -/
def stapellosEingang : Parser.SEingang :=
  { name := "entry_j"
    vektor := some (Parser.SExpr.lit 21)
    via := none
    arch := "x86_64"
    regIn := [Parser.SRegBind.binds "x" "rdi"]
    regOut := [Parser.SRegBind.binds "y" "rax"]
    erhaelt := ["rbx"]
    kills := ["rcx"]
    stapel := ""
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

theorem n5_bad_stack_zeuge :
    frameOf stapellosEingang = Except.error einStapelFehlt := by
  rfl

/-! ## N6 (check 8): an output clobbered without an input is refused -/

/-- Checks 2 and 3 are already witnessed in `RahmenZeuge` (`zeigeAbgelehnt`,
    `zeigeEingabeAbgelehnt`); this is the remaining undeclared-clobber arm. -/
def ausgabeVerdeckt : Parser.SEingang :=
  { name := "entry_k"
    vektor := some (Parser.SExpr.lit 23)
    via := none
    arch := "x86_64"
    regIn := []
    regOut := [Parser.SRegBind.binds "y" "rax"]
    erhaelt := ["rbx"]
    kills := ["rax"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

theorem n6_ausgabe_verdeckt_zeuge :
    frameOf ausgabeVerdeckt = Except.error einAusVerdeckt := by
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Eingang.n5_bad_stack_zeuge
#print axioms Gabbro.Grammatik.Niedrig.Eingang.n6_ausgabe_verdeckt_zeuge

end Gabbro.Grammatik.Niedrig.Eingang
