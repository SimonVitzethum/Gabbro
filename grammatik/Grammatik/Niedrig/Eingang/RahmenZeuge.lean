/-
  File:      Grammatik/Niedrig/Eingang/RahmenZeuge.lean
  Subject:   WITNESS FOR THE ENTRY FRAME DESCRIPTORS (L5a): accepted
    declarations and one refused declaration per new refusal, each computed
    by `rfl`.

  The accepted declarations have the shape of the `t38` parser probe
  (`ElementTiefProben3.lean`): an interrupt vector, register maps, a
  preserved and a clobbered register, a stack, and a dispatch path. The
  second accepted declaration is an in-place update: its input is also its
  output and clobbered, which check 3 allows. The refused declarations
  are the preserved/clobbered overlap and one per new refusal: a vector
  with a `via` handler, an input clobbered without an output, and a
  duplicate in each of `erhaelt`, `kills`, `regIn` and `regOut`. All are
  structure literals, one field per line; no lexer or parser runs here.
-/
module

public import Grammatik.Niedrig.Eingang.Rahmen

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Eingang

open Gabbro.Grammatik

/-- An accepted declaration, shaped like the `t38` parser probe. -/
def zeigeEingang : Parser.SEingang :=
  { name := "entry_a"
    vektor := some (Parser.SExpr.lit 128)
    via := none
    arch := "x86_64"
    regIn := [Parser.SRegBind.binds "x" "rdi"]
    regOut := [Parser.SRegBind.binds "y" "rax"]
    erhaelt := ["rbx"]
    kills := ["rcx"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := some "never"
    dispatch := ["beispiel", "lockfree_entry_roots", "distribute_a"] }

/-- Its frame, computed by `frameOf`, with the carried context fields. -/
def zeigeRahmen : EntryFrame :=
  { art := FrameKind.irqEntry
    regIn := ["rdi"]
    regOut := ["rax"]
    erhaelt := ["rbx"]
    kills := ["rcx"]
    stapel := "ka"
    maskiertBeimEintritt := true
    privVor := Arch.Priv.nutzer
    privNach := Arch.Priv.kern
    arch := "x86_64"
    perCpu := true
    ist := none
    nest := some "never"
    dispatch := ["beispiel", "lockfree_entry_roots", "distribute_a"] }

/-- The accepted declaration computes its frame. -/
theorem zeigeRahmenOk : frameOf zeigeEingang = Except.ok zeigeRahmen := by
  rfl

/-- An accepted in-place update: the input is also the output, clobbered. -/
def zeigeInOut : Parser.SEingang :=
  { name := "entry_c"
    vektor := some (Parser.SExpr.lit 3)
    via := none
    arch := "x86_64"
    regIn := [Parser.SRegBind.binds "x" "rdi"]
    regOut := [Parser.SRegBind.binds "y" "rdi"]
    erhaelt := ["rbx"]
    kills := ["rdi"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- Its frame: the clobbered register is carried as input and output. -/
def zeigeRahmenInOut : EntryFrame :=
  { art := FrameKind.irqEntry
    regIn := ["rdi"]
    regOut := ["rdi"]
    erhaelt := ["rbx"]
    kills := ["rdi"]
    stapel := "ka"
    maskiertBeimEintritt := true
    privVor := Arch.Priv.nutzer
    privNach := Arch.Priv.kern
    arch := "x86_64"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The in-place update is accepted. -/
theorem zeigeInOutOk : frameOf zeigeInOut = Except.ok zeigeRahmenInOut := by
  rfl

/-- A refused declaration: `rbx` is both preserved and clobbered. -/
def zeigeSchlecht : Parser.SEingang :=
  { name := "entry_b"
    vektor := some (Parser.SExpr.lit 0)
    via := none
    arch := "x86_64"
    regIn := []
    regOut := []
    erhaelt := ["rbx"]
    kills := ["rbx"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The refused declaration is refused with its named message. -/
theorem zeigeAbgelehnt :
    frameOf zeigeSchlecht = Except.error einErhVerdeckt := by
  rfl

/-- A refused declaration: both a vector and a `via` handler. -/
def zeigeBeide : Parser.SEingang :=
  { name := "entry_d"
    vektor := some (Parser.SExpr.lit 7)
    via := some "handler"
    arch := "x86_64"
    regIn := []
    regOut := []
    erhaelt := ["rbx"]
    kills := ["rcx"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- Two ways to name the entry are refused with the first message. -/
theorem zeigeBeideAbgelehnt :
    frameOf zeigeBeide = Except.error einVektorVia := by
  rfl

/-- A refused declaration: the input `rdi` is clobbered, no output. -/
def zeigeEingabe : Parser.SEingang :=
  { name := "entry_e"
    vektor := some (Parser.SExpr.lit 9)
    via := none
    arch := "x86_64"
    regIn := [Parser.SRegBind.binds "x" "rdi"]
    regOut := []
    erhaelt := ["rbx"]
    kills := ["rdi"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- A clobbered pure input is refused with the third message. -/
theorem zeigeEingabeAbgelehnt :
    frameOf zeigeEingabe = Except.error einEinVerdeckt := by
  rfl

/-- A refused declaration: `rbx` is twice in the preserved set. -/
def zeigeDoppeltErhaelt : Parser.SEingang :=
  { name := "entry_f"
    vektor := some (Parser.SExpr.lit 11)
    via := none
    arch := "x86_64"
    regIn := []
    regOut := []
    erhaelt := ["rbx", "rbx"]
    kills := ["rcx"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The duplicated preserved set is refused as a duplicate. -/
theorem zeigeDoppeltErhaeltAbgelehnt :
    frameOf zeigeDoppeltErhaelt = Except.error einDoppelt := by
  rfl

/-- A refused declaration: `rcx` is twice in the clobbered set. -/
def zeigeDoppeltKills : Parser.SEingang :=
  { name := "entry_g"
    vektor := some (Parser.SExpr.lit 13)
    via := none
    arch := "x86_64"
    regIn := []
    regOut := []
    erhaelt := ["rbx"]
    kills := ["rcx", "rcx"]
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The duplicated clobbered set is refused as a duplicate. -/
theorem zeigeDoppeltKillsAbgelehnt :
    frameOf zeigeDoppeltKills = Except.error einDoppelt := by
  rfl

/-- A refused declaration: `rdi` is bound twice in the input map. -/
def zeigeDoppeltRegIn : Parser.SEingang :=
  { name := "entry_h"
    vektor := some (Parser.SExpr.lit 17)
    via := none
    arch := "x86_64"
    regIn := [Parser.SRegBind.binds "a" "rdi", Parser.SRegBind.binds "b" "rdi"]
    regOut := []
    erhaelt := ["rbx"]
    kills := []
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The twice-bound input is refused as a duplicate. -/
theorem zeigeDoppeltRegInAbgelehnt :
    frameOf zeigeDoppeltRegIn = Except.error einDoppelt := by
  rfl

/-- A refused declaration: `rax` is bound twice in the output map. -/
def zeigeDoppeltRegOut : Parser.SEingang :=
  { name := "entry_i"
    vektor := some (Parser.SExpr.lit 19)
    via := none
    arch := "x86_64"
    regIn := []
    regOut := [Parser.SRegBind.reg "rax", Parser.SRegBind.reg "rax"]
    erhaelt := ["rbx"]
    kills := []
    stapel := "ka"
    perCpu := true
    ist := none
    nest := none
    dispatch := [] }

/-- The twice-bound output is refused as a duplicate. -/
theorem zeigeDoppeltRegOutAbgelehnt :
    frameOf zeigeDoppeltRegOut = Except.error einDoppelt := by
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeRahmenOk
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeInOutOk
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeBeideAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeEingabeAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeDoppeltErhaeltAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeDoppeltKillsAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeDoppeltRegInAbgelehnt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.zeigeDoppeltRegOutAbgelehnt

end Gabbro.Grammatik.Niedrig.Eingang
