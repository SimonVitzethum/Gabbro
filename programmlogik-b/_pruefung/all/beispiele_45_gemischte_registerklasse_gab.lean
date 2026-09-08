/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/45-gemischte-registerklasse.gab  total 2  goals 0  refused 2
        @assumed 2  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

    The meaning of a body is `Gabbro.Body`, written by hand and read by a
    person. What stands here is a DATUM of it -- this file defines nothing.

    WHAT A PERSON OWES: the `_statement` of every `_meets` and every `_keeps`
    theorem below. Each is proved by `gabbro_auto`, which closes what the
    model closes by computation and leaves a `sorry` on the rest -- and the
    rest is, by construction, the program's own logic: every hypothesis the
    proof can need stands in front of the turnstile. A person proves the
    statement in a file of their own and hands it to `unit_closed`.

    WHAT THE GENERATOR OWES, AND PAYS: the composition over every call
    (`Contract`, `Frame`), the rule of every loop (`LoopRule`), the
    precondition at every call site (the call gets stuck without it), and
    the wiring from the duties to the contracts (`unit_closed`).

    ASSUMED, and visible because it is written down: two different carrier
    names are two different objects (the alias passes carry it), and two
    objects of one record type are ONE object of the model (a record's
    places are named by its type, as a table's are); the
    declared `effects` list is complete (`E008`/`E010`, `Frame` in `Program`);
    the initial world satisfies every invariant (a statement about `boot`,
    booked by no register); and everything `Assumed` names.
-/

import Gabbro.Body

set_option autoImplicit false
set_option maxHeartbeats 11300000

open Gabbro.Body

namespace GabbroDuty.Duty45GemischteRegisterklasse

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  device-promise (2): ASSUMED -- a promise at hardware Gabbro does not see: an ASSUMPTION
    duty_1  D  Vtd :: transition scharf_te requires
    duty_2  D  Vtd :: transition scharf_te

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  D  Vtd :: transition scharf_te requires  --  ASSUMED (device-promise)
  duty_2  D  Vtd :: transition scharf_te  --  ASSUMED (device-promise)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `fehler_quittieren` -/

-- REFUSED  fehler_quittieren  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def fehler_quittieren_pre : Expr :=
  (.lit (.bool true))

def fehler_quittieren_writes : List String := ["v"]

/-- What a caller of `fehler_quittieren` has to bring: a well-typed world and the precondition. -/
def fehler_quittieren_requires (t : State) : Prop := wellFormed t ∧ eval t fehler_quittieren_pre = some (.bool true)

/-- What `fehler_quittieren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fehler_quittieren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `fehlerindex` -/

-- REFUSED  fehlerindex  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def fehlerindex_pre : Expr :=
  (.lit (.bool true))

def fehlerindex_writes : List String := []

/-- What a caller of `fehlerindex` has to bring: a well-typed world and the precondition. -/
def fehlerindex_requires (t : State) : Prop := wellFormed t ∧ eval t fehlerindex_pre = some (.bool true)

/-- What `fehlerindex` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fehlerindex_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `uebersetzung_steht` -/

-- REFUSED  uebersetzung_steht  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def uebersetzung_steht_pre : Expr :=
  (.lit (.bool true))

def uebersetzung_steht_writes : List String := []

/-- What a caller of `uebersetzung_steht` has to bring: a well-typed world and the precondition. -/
def uebersetzung_steht_requires (t : State) : Prop := wellFormed t ∧ eval t uebersetzung_steht_pre = some (.bool true)

/-- What `uebersetzung_steht` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def uebersetzung_steht_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  True

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ) :
    True := by
  trivial

end GabbroDuty.Duty45GemischteRegisterklasse
