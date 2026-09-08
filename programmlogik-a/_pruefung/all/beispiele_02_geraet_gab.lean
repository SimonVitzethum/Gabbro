/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/02-geraet.gab  total 8  goals 0  refused 8
        @assumed 8  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty02Geraet

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  device-promise (8): ASSUMED -- a promise at hardware Gabbro does not see: an ASSUMPTION
    duty_1  D  Vtd :: transition wurzel_setzen
    duty_2  D  Vtd :: transition uebersetzung_an requires
    duty_3  D  Vtd :: transition uebersetzung_an
    duty_4  D  Vtd :: transition uebersetzung_aus requires
    duty_5  D  Vtd :: transition uebersetzung_aus
    duty_6  D  Vtd :: transition irq_umlenken requires
    duty_7  D  Vtd :: transition irq_umlenken
    duty_8  N  scharfschalten :: ensures #1
      (inherited: this clause HAS a term; the body or the `requires` of `scharfschalten` has none)

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  D  Vtd :: transition wurzel_setzen  --  ASSUMED (device-promise)
  duty_2  D  Vtd :: transition uebersetzung_an requires  --  ASSUMED (device-promise)
  duty_3  D  Vtd :: transition uebersetzung_an  --  ASSUMED (device-promise)
  duty_4  D  Vtd :: transition uebersetzung_aus requires  --  ASSUMED (device-promise)
  duty_5  D  Vtd :: transition uebersetzung_aus  --  ASSUMED (device-promise)
  duty_6  D  Vtd :: transition irq_umlenken requires  --  ASSUMED (device-promise)
  duty_7  D  Vtd :: transition irq_umlenken  --  ASSUMED (device-promise)
  duty_8  N  scharfschalten :: ensures #1  --  ASSUMED (device-promise)
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

/-! ### `scharfschalten` -/

-- REFUSED  scharfschalten  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def scharfschalten_pre : Expr :=
  (.bin .and (.hasShape "wurzel" (.intIn 0 18446744073709551615)) (.bin .eq (.bin .rem (.name "wurzel") (.lit (.int 4096))) (.lit (.int 0))))

def scharfschalten_writes : List String := ["v"]

/-- What a caller of `scharfschalten` has to bring: a well-typed world and the precondition. -/
def scharfschalten_requires (t : State) : Prop := wellFormed t ∧ eval t scharfschalten_pre = some (.bool true)

/-- What `scharfschalten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def scharfschalten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1: NOT SAID (device-promise) -- a promise fewer makes a caller's goal harder, never wrong
  True

/-! ### `used_lesen` -/

-- REFUSED  used_lesen  (record-value): a field of a record VALUE bound in the body (`let c = f(x); c.len`) -- this model's places are named by a record TYPE; pass the record through a `ptr` parameter
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def used_lesen_pre : Expr :=
  (.lit (.bool true))

def used_lesen_writes : List String := []

/-- What a caller of `used_lesen` has to bring: a well-typed world and the precondition. -/
def used_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t used_lesen_pre = some (.bool true)

/-- What `used_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def used_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `warteschlange_scharf` -/

-- REFUSED  warteschlange_scharf  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def warteschlange_scharf_pre : Expr :=
  (.lit (.bool true))

def warteschlange_scharf_writes : List String := ["q", "p"]

/-- What a caller of `warteschlange_scharf` has to bring: a well-typed world and the precondition. -/
def warteschlange_scharf_requires (t : State) : Prop := wellFormed t ∧ eval t warteschlange_scharf_pre = some (.bool true)

/-- What `warteschlange_scharf` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def warteschlange_scharf_post (s s' : State) (r : Option Value) : Prop :=
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

end GabbroDuty.Duty02Geraet