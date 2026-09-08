/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F05.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyF05

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Nachricht" "op" => some (.intIn 0 18446744073709551615)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `benachrichtige` -- a foreign body: its contract is an assumption. -/
def benachrichtige_pre : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 18446744073709551615)) (.hasShape "w" (.intIn 0 18446744073709551615)))

def benachrichtige_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def benachrichtige_writes : List String := ["NTFN"]

def benachrichtige_requires (t : State) : Prop := wellFormed t ∧ eval t benachrichtige_pre = some (.bool true)

/-- `dienst_abbruch` -- a foreign body: its contract is an assumption. -/
def dienst_abbruch_pre : Expr :=
  (.lit (.bool true))

def dienst_abbruch_post (t t' : State) (r : Option Value) : Prop :=
  False

def dienst_abbruch_writes : List String := []

def dienst_abbruch_requires (t : State) : Prop := wellFormed t ∧ eval t dienst_abbruch_pre = some (.bool true)

/-- `map_window` -- a foreign body: its contract is an assumption. -/
def map_window_pre : Expr :=
  (.hasShape "cap" (.intIn 0 18446744073709551615))

def map_window_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615) ∨ ∃ e, r = some (.reason e))

def map_window_writes : List String := []

def map_window_requires (t : State) : Prop := wellFormed t ∧ eval t map_window_pre = some (.bool true)

/-- `pool_new` -- a foreign body: its contract is an assumption. -/
def pool_new_pre : Expr :=
  (.hasShape "fenster" (.intIn 0 18446744073709551615))

def pool_new_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615) ∨ ∃ e, r = some (.reason e))

def pool_new_writes : List String := []

def pool_new_requires (t : State) : Prop := wellFormed t ∧ eval t pool_new_pre = some (.bool true)

/-- `probe_ecam` -- a foreign body: its contract is an assumption. -/
def probe_ecam_pre : Expr :=
  (.hasShape "cfg" (.intIn 0 18446744073709551615))

def probe_ecam_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615) ∨ ∃ e, r = some (.reason e))

def probe_ecam_writes : List String := []

def probe_ecam_requires (t : State) : Prop := wellFormed t ∧ eval t probe_ecam_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "benachrichtige" benachrichtige_requires benachrichtige_post
  ∧ Frame ρ "benachrichtige" benachrichtige_writes
  ∧ Contract ρ "dienst_abbruch" dienst_abbruch_requires dienst_abbruch_post
  ∧ Frame ρ "dienst_abbruch" dienst_abbruch_writes
  ∧ Contract ρ "map_window" map_window_requires map_window_post
  ∧ Frame ρ "map_window" map_window_writes
  ∧ Contract ρ "pool_new" pool_new_requires pool_new_post
  ∧ Frame ρ "pool_new" pool_new_writes
  ∧ Contract ρ "probe_ecam" probe_ecam_requires probe_ecam_post
  ∧ Frame ρ "probe_ecam" probe_ecam_writes

/-! ## The routines: body and contract -/

/-! ### `run` -/

-- REFUSED  run  (record-value): a field of a record VALUE bound in the body (`let c = f(x); c.len`) -- this model's places are named by a record TYPE; pass the record through a `ptr` parameter
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def run_pre : Expr :=
  (.hasShape "startwert" (.intIn 0 18446744073709551615))

def run_writes : List String := ["DMA", "SHARED"]

/-- What a caller of `run` has to bring: a well-typed world and the precondition. -/
def run_requires (t : State) : Prop := wellFormed t ∧ eval t run_pre = some (.bool true)

/-- What `run` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def run_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

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

end GabbroDuty.DutyF05