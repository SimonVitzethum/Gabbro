/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/21-verbundwert.gab  total 1  goals 0  refused 1
        @assumed 0  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 1 are refused forms

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

namespace GabbroDuty.Duty21Verbundwert

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  carrier-not-a-table (1): refused -- the carrier of a place is not a declared `table`, record or `format`
    duty_1  V  laenge_von :: fertig requires #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  laenge_von :: fertig requires #1  --  refused (carrier-not-a-table)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Completion" "id" => some (.intIn 0 4294967295)
  | .field "Completion" "len" => some (.intIn 0 4294967295)
  | .field "Marke" "wer" => some (.intIn 0 63)
  | .field "Marke" "fertig" => some .bool
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

/-! ### `fertig` -/

-- REFUSED  fertig  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def fertig_pre : Expr :=
  (.bin .and (.hasShape "k" (.intIn 0 4294967295)) (.bin .and (.hasShape "n" (.intIn 0 4294967295)) (.bin .and (.bin .lt (.name "k") (.lit (.int 64))) (.bin .lt (.name "n") (.lit (.int 4096))))))

def fertig_writes : List String := []

/-- What a caller of `fertig` has to bring: a well-typed world and the precondition. -/
def fertig_requires (t : State) : Prop := wellFormed t ∧ eval t fertig_pre = some (.bool true)

/-- What `fertig` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fertig_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `laenge_von` -/

-- REFUSED  laenge_von  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def laenge_von_pre : Expr :=
  (.bin .and (.hasShape "k" (.intIn 0 4294967295)) (.bin .lt (.name "k") (.lit (.int 64))))

def laenge_von_writes : List String := []

/-- What a caller of `laenge_von` has to bring: a well-typed world and the precondition. -/
def laenge_von_requires (t : State) : Prop := wellFormed t ∧ eval t laenge_von_pre = some (.bool true)

/-- What `laenge_von` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def laenge_von_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `markiere` -/

-- REFUSED  markiere  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def markiere_pre : Expr :=
  (.hasShape "w" (.intIn 0 63))

def markiere_writes : List String := []

/-- What a caller of `markiere` has to bring: a well-typed world and the precondition. -/
def markiere_requires (t : State) : Prop := wellFormed t ∧ eval t markiere_pre = some (.bool true)

/-- What `markiere` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def markiere_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

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

end GabbroDuty.Duty21Verbundwert
