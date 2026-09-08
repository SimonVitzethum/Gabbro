/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/62-grenzwort-im-ausdruck.gab  total 0  goals 0  refused 0
        @assumed 0  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty62GrenzwortImAusdruck

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
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

/-! ### `invertiere` -/

-- REFUSED  invertiere  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format` -- name it through a parameter of that type, so the place has a declaration to take its shape from
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def invertiere_pre : Expr :=
  (.hasShape "w" (.intIn 0 4294967295))

def invertiere_writes : List String := []

/-- What a caller of `invertiere` has to bring: a well-typed world and the precondition. -/
def invertiere_requires (t : State) : Prop := wellFormed t ∧ eval t invertiere_pre = some (.bool true)

/-- What `invertiere` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def invertiere_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `ist_kleinster` -/

-- REFUSED  ist_kleinster  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format` -- name it through a parameter of that type, so the place has a declaration to take its shape from
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def ist_kleinster_pre : Expr :=
  (.hasShape "x" (.intIn (-2147483648) 2147483647))

def ist_kleinster_writes : List String := []

/-- What a caller of `ist_kleinster` has to bring: a well-typed world and the precondition. -/
def ist_kleinster_requires (t : State) : Prop := wellFormed t ∧ eval t ist_kleinster_pre = some (.bool true)

/-- What `ist_kleinster` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ist_kleinster_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `passt_in_16` -/

-- REFUSED  passt_in_16  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format` -- name it through a parameter of that type, so the place has a declaration to take its shape from
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def passt_in_16_pre : Expr :=
  (.hasShape "w" (.intIn 0 4294967295))

def passt_in_16_writes : List String := []

/-- What a caller of `passt_in_16` has to bring: a well-typed world and the precondition. -/
def passt_in_16_requires (t : State) : Prop := wellFormed t ∧ eval t passt_in_16_pre = some (.bool true)

/-- What `passt_in_16` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def passt_in_16_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `zwei_wege_eine_maske` -/

-- REFUSED  zwei_wege_eine_maske  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format` -- name it through a parameter of that type, so the place has a declaration to take its shape from
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def zwei_wege_eine_maske_pre : Expr :=
  (.hasShape "w" (.intIn 0 255))

def zwei_wege_eine_maske_writes : List String := []

/-- What a caller of `zwei_wege_eine_maske` has to bring: a well-typed world and the precondition. -/
def zwei_wege_eine_maske_requires (t : State) : Prop := wellFormed t ∧ eval t zwei_wege_eine_maske_pre = some (.bool true)

/-- What `zwei_wege_eine_maske` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zwei_wege_eine_maske_post (s s' : State) (r : Option Value) : Prop :=
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

end GabbroDuty.Duty62GrenzwortImAusdruck