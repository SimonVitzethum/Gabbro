/-
  File:      Grammatik/Niedrig/Eingang/Rahmen.lean
  Subject:   ENTRY FRAME DESCRIPTORS FROM `entry` DECLARATIONS (L5a):
    `FrameKind`, `EntryFrame`, and the total descriptor function `frameOf`
    over the parser record `SEingang`, with named refusals in a fixed
    order, and carried context fields.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; theorems live in `RahmenSatz`, witnesses in
  `RahmenZeuge`).
  * `FrameKind` is the six L5 frame kinds: interrupt entry and return,
    system-call entry and return, thread switch, and the first entry of a
    thread. The privilege pair and the mask convention live beside them.
  * `EntryFrame` is the generated frame descriptor: the kind, the register
    maps as lists of names, the preserved set, the clobbered set, the stack
    description, whether interrupts are masked on entry, the privilege
    before and after as `Arch.Priv` from L4a, and the carried context
    fields `arch`, `perCpu`, `ist`, `nest` and `dispatch`, copied
    uninterpreted from the record. The frame carries the architecture name
    instead of dropping it, so that a later binding-specific check can
    refuse an unknown one.
  * `frameOf` is total: it refuses with a NAMED message when the declaration
    is inconsistent from its own fields, in this fixed order: (1) both a
    vector and a `via` handler (`eintritt-vektor-und-via`); (2) a register
    both preserved and clobbered (`eintritt-erhaelt-und-verdeckt`); (3) an
    input register clobbered without being declared as an output
    (`eintritt-eingabe-verdeckt-ohne-ausgabe`); (4) a duplicate in
    `erhaelt`, (5) in `kills`, (6) in `regIn`, (7) in `regOut`
    (`eintritt-doppelt`); (8) an output register clobbered without being
    listed as an input (`eintritt-ausgabe-verdeckt-ohne-eingabe`); (9) a
    missing stack for a kind that needs one (`eintritt-stapel-fehlt`).
  * The kind comes from the record's own fields: a vector means an interrupt
    entry, a `via` handler without a vector means a system-call entry, and
    neither means a thread switch. A record with both is refused (check 1)
    and never mapped. The record distinguishes no return kinds.
  * NOT delivered here: one generic theorem per frame kind (L5b proves a
    theorem for each of the six kinds, including the three return kinds no
    record reaches), and privileged operations as target-binding calls over
    `context<P>` with contracts (L4b, not this package).
-/
module

public import Grammatik.Niedrig.Arch.Zustand
public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Eingang

open Gabbro.Grammatik

/-- The six L5 frame kinds (PLAN-COMPILER-READY row L5). -/
inductive FrameKind
  | irqEntry : FrameKind
  | irqReturn : FrameKind
  | syscallEntry : FrameKind
  | syscallReturn : FrameKind
  | threadSwitch : FrameKind
  | threadFirst : FrameKind
  deriving DecidableEq

/-- The generated entry frame descriptor: the kind, the register maps, the
    preserved and clobbered sets, the stack, the mask and privilege pair,
    and the carried context fields `arch`, `perCpu`, `ist`, `nest` and
    `dispatch`, copied uninterpreted from the declaration. -/
structure EntryFrame where
  art : FrameKind
  regIn : List String
  regOut : List String
  erhaelt : List String
  kills : List String
  stapel : String
  maskiertBeimEintritt : Bool
  privVor : Arch.Priv
  privNach : Arch.Priv
  arch : String
  perCpu : Bool
  ist : Option Parser.SExpr
  nest : Option String
  dispatch : List String

/-- The hardware register of one `regs` binding: the target of `binds`, the
    name of `reg`. -/
def regName : Parser.SRegBind → String
  | Parser.SRegBind.binds _ r => r
  | Parser.SRegBind.reg r => r

/-- The register maps as lists of names. -/
def regNamen (xs : List Parser.SRegBind) : List String :=
  xs.map regName

/-- The overlap of two register lists, in order. -/
def ueberschneidung : List String → List String → List String
  | [], _ => []
  | x :: xs, ys =>
    match ys.contains x with
    | true => x :: ueberschneidung xs ys
    | false => ueberschneidung xs ys

/-- Two register lists are disjoint, as a proposition over `contains`. -/
def getrennt : List String → List String → Prop
  | [], _ => True
  | x :: xs, ys => ys.contains x = false ∧ getrennt xs ys

/-- The elements of the first list not contained in the second, in order. -/
def ohneAus : List String → List String → List String
  | [], _ => []
  | x :: xs, ys =>
    match ys.contains x with
    | true => ohneAus xs ys
    | false => x :: ohneAus xs ys

/-- The output registers that are clobbered without being listed as inputs. -/
def ausVerdeckt : List String → List String → List String → List String
  | [], _, _ => []
  | r :: rs, ins, kills =>
    match kills.contains r, ins.contains r with
    | true, false => r :: ausVerdeckt rs ins kills
    | _, _ => ausVerdeckt rs ins kills

/-- Whether the record names both a vector and a `via` handler. -/
def hatBeide (d : Parser.SEingang) : Bool :=
  match d.vektor, d.via with
  | some _, some _ => true
  | _, _ => false

/-- Whether a register list names some register twice. -/
def hatDoppelt : List String → Bool
  | [] => false
  | x :: xs => xs.contains x || hatDoppelt xs

/-- The frame kind from the record's own fields. -/
def artAus (d : Parser.SEingang) : FrameKind :=
  match d.vektor, d.via with
  | some _, _ => FrameKind.irqEntry
  | none, some _ => FrameKind.syscallEntry
  | none, none => FrameKind.threadSwitch

/-- Which kinds need a stack description. -/
def brauchtStapel : FrameKind → Bool
  | FrameKind.irqEntry => true
  | FrameKind.irqReturn => false
  | FrameKind.syscallEntry => true
  | FrameKind.syscallReturn => false
  | FrameKind.threadSwitch => true
  | FrameKind.threadFirst => true

/-- The stack check: a kind that needs one gets a nonempty description. -/
def stapelOk (k : FrameKind) (s : String) : Bool :=
  (!brauchtStapel k) || (s != "")

/-- Whether interrupts are masked on entry, by kind. -/
def maskiertBeimEintritt : FrameKind → Bool
  | FrameKind.irqEntry => true
  | FrameKind.irqReturn => false
  | FrameKind.syscallEntry => true
  | FrameKind.syscallReturn => false
  | FrameKind.threadSwitch => true
  | FrameKind.threadFirst => false

/-- The privilege pair, by kind: the frame's kind determines it. -/
def privPaar : FrameKind → Arch.Priv × Arch.Priv
  | FrameKind.irqEntry => (Arch.Priv.nutzer, Arch.Priv.kern)
  | FrameKind.irqReturn => (Arch.Priv.kern, Arch.Priv.nutzer)
  | FrameKind.syscallEntry => (Arch.Priv.nutzer, Arch.Priv.kern)
  | FrameKind.syscallReturn => (Arch.Priv.kern, Arch.Priv.nutzer)
  | FrameKind.threadSwitch => (Arch.Priv.kern, Arch.Priv.kern)
  | FrameKind.threadFirst => (Arch.Priv.kern, Arch.Priv.nutzer)

/-- A record with both a vector and a `via` handler: two ways to name the
    entry. -/
def einVektorVia : String :=
  "eintritt-vektor-und-via"

/-- A register is both preserved and clobbered. -/
def einErhVerdeckt : String :=
  "eintritt-erhaelt-und-verdeckt"

/-- An input register is clobbered without being declared as an output.

    The low-level plan fixes which combinations are meaningful
    ("Obligations"): "preservation of everything not declared. A clobber
    declaration is not permission to overwrite arbitrary memory." A pure
    input carries a value the handler reads, so clobbering it destroys the
    declared input; an input that is also an output is the declared
    in-place update and stays allowed. A preserved input in the clobbered
    set is already refused as overlap (check 2). -/
def einEinVerdeckt : String :=
  "eintritt-eingabe-verdeckt-ohne-ausgabe"

/-- A duplicate register: twice in `erhaelt`, in `kills`, or bound twice in
    `regIn` or `regOut`. -/
def einDoppelt : String :=
  "eintritt-doppelt"

/-- An output register is clobbered without being listed as an input. -/
def einAusVerdeckt : String :=
  "eintritt-ausgabe-verdeckt-ohne-eingabe"

/-- A kind that needs a stack has no stack description. -/
def einStapelFehlt : String :=
  "eintritt-stapel-fehlt"

/-- The descriptor without checks; context fields are copied uninterpreted. -/
def rahmenAus (d : Parser.SEingang) : EntryFrame :=
  { art := artAus d
    regIn := regNamen d.regIn
    regOut := regNamen d.regOut
    erhaelt := d.erhaelt
    kills := d.kills
    stapel := d.stapel
    maskiertBeimEintritt := maskiertBeimEintritt (artAus d)
    privVor := (privPaar (artAus d)).1
    privNach := (privPaar (artAus d)).2
    arch := d.arch
    perCpu := d.perCpu
    ist := d.ist
    nest := d.nest
    dispatch := d.dispatch }

/-! ## The checks in their fixed, documented order -/

/-- All nine checks as one conjunction, in the documented order. -/
def alleOk (d : Parser.SEingang) : Prop :=
  hatBeide d = false ∧
    ueberschneidung d.erhaelt d.kills = [] ∧
    ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [] ∧
    hatDoppelt d.erhaelt = false ∧
    hatDoppelt d.kills = false ∧
    hatDoppelt (regNamen d.regIn) = false ∧
    hatDoppelt (regNamen d.regOut) = false ∧
    ausVerdeckt (regNamen d.regOut) (regNamen d.regIn) d.kills = [] ∧
    stapelOk (artAus d) d.stapel = true

/-- Decidability of the nine checks: every conjunct is a decidable equality
    over `Bool` or `List String`, so the total descriptor computes. -/
instance (d : Parser.SEingang) : Decidable (alleOk d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The first failing check, by name: (1) vector and `via`, (2) the
    preserved/clobbered overlap, (3) an input clobbered without an output,
    (4)-(7) a duplicate in `erhaelt`, `kills`, `regIn`, `regOut`, (8) an
    output clobbered without an input, (9) the missing stack. When the
    first eight checks pass, the only remaining failure is the stack. -/
def ersteFehler (d : Parser.SEingang) : String :=
  match hatBeide d with
  | true => einVektorVia
  | false =>
    match ueberschneidung d.erhaelt d.kills with
    | _ :: _ => einErhVerdeckt
    | [] =>
      match ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills with
      | _ :: _ => einEinVerdeckt
      | [] =>
        match hatDoppelt d.erhaelt with
        | true => einDoppelt
        | false =>
          match hatDoppelt d.kills with
          | true => einDoppelt
          | false =>
            match hatDoppelt (regNamen d.regIn) with
            | true => einDoppelt
            | false =>
              match hatDoppelt (regNamen d.regOut) with
              | true => einDoppelt
              | false =>
                match ausVerdeckt (regNamen d.regOut) (regNamen d.regIn) d.kills with
                | _ :: _ => einAusVerdeckt
                | [] => einStapelFehlt

/-- The total descriptor: accept with the frame, or refuse with the named
    message of the first failing check in the documented order. -/
def frameOf (d : Parser.SEingang) : Except String EntryFrame :=
  if alleOk d then
    Except.ok (rahmenAus d)
  else
    Except.error (ersteFehler d)

/-! ## Only the name is not part of a frame -/

/-- The name is unrelated: renaming changes nothing. It is the only listed
    field `frameOf` ignores: `arch`, `perCpu`, `ist`, `nest` and `dispatch`
    are carried fields of `EntryFrame`, so no independence lemma holds for
    them; a later binding-specific check refuses an unknown architecture by
    reading the carried `arch`. -/
theorem frameOf_name (d : Parser.SEingang) (n : String) :
    frameOf { d with name := n } = frameOf d := by
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_name

end Gabbro.Grammatik.Niedrig.Eingang
