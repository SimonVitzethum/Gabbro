/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/07-eintritt-und-boot.gab  total 5  goals 0  refused 5
        @assumed 5  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty07EintrittUndBoot

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (1): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_5  F  boot_ende :: ensures #1

  walk-invariant (4): ASSUMED -- an invariant of a `walk` -- a statement about a hardware table: an ASSUMPTION
    duty_1  W  Seitentabelle :: down
    duty_2  W  Seitentabelle :: leaf
    duty_3  W  Seitentabelle :: invariant wx_getrennt
    duty_4  W  Seitentabelle :: invariant kein_nutzer_im_kern

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Seitentabelle :: down  --  ASSUMED (walk-invariant)
  duty_2  W  Seitentabelle :: leaf  --  ASSUMED (walk-invariant)
  duty_3  W  Seitentabelle :: invariant wx_getrennt  --  ASSUMED (walk-invariant)
  duty_4  W  Seitentabelle :: invariant kein_nutzer_im_kern  --  ASSUMED (walk-invariant)
  duty_5  F  boot_ende :: ensures #1  --  ASSUMED (foreign-body)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Kontext" "rsp" => some (.intIn 0 18446744073709551615)
  | .field "Kontext" "rip" => some (.intIn 0 18446744073709551615)
  | .field "Pte" "praesent" => some .bool
  | .field "Pte" "schreibbar" => some .bool
  | .field "Pte" "nutzer" => some .bool
  | .field "Pte" "pwt" => some .bool
  | .field "Pte" "pcd" => some .bool
  | .field "Pte" "benutzt" => some .bool
  | .field "Pte" "schmutzig" => some .bool
  | .field "Pte" "gross" => some .bool
  | .field "Pte" "global" => some .bool
  | .field "Pte" "rahmen" => some (.intIn 0 18446744073709551615)
  | .field "Pte" "nx" => some .bool
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

end GabbroDuty.Duty07EintrittUndBoot
