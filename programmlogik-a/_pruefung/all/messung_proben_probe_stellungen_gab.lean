/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-stellungen.gab  total 8  goals 0  refused 8
        @assumed 3  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 5 are refused forms

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

namespace GabbroDuty.DutyProbeStellungen

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  quantified-threads (5): refused -- `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
    duty_1  W  Knoten :: invariant s1_slots
      (inherited: this invariant HAS a term; `r1_slots` writes its carrier and `s8_threads` -- the invariant `r1_slots` must keep because it writes `Knoten` has none)
    duty_2  W  Knoten :: invariant s2_chain
      (inherited: this invariant HAS a term; `r1_slots` writes its carrier and `s8_threads` -- the invariant `r1_slots` must keep because it writes `Knoten` has none)
    duty_3  W  Knoten :: invariant s3_descendants
      (inherited: this invariant HAS a term; `r1_slots` writes its carrier and `s8_threads` -- the invariant `r1_slots` must keep because it writes `Knoten` has none)
    duty_4  W  Knoten :: invariant s4_ancestors
      (inherited: this invariant HAS a term; `r1_slots` writes its carrier and `s8_threads` -- the invariant `r1_slots` must keep because it writes `Knoten` has none)
    duty_5  W  Knoten :: invariant s8_threads

  walk-invariant (3): ASSUMED -- an invariant of a `walk` -- a statement about a hardware table: an ASSUMPTION
    duty_6  W  Baum :: down
    duty_7  W  Baum :: leaf
    duty_8  W  Baum :: invariant s9_mappings

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Knoten :: invariant s1_slots  --  refused (quantified-threads)
  duty_2  W  Knoten :: invariant s2_chain  --  refused (quantified-threads)
  duty_3  W  Knoten :: invariant s3_descendants  --  refused (quantified-threads)
  duty_4  W  Knoten :: invariant s4_ancestors  --  refused (quantified-threads)
  duty_5  W  Knoten :: invariant s8_threads  --  refused (quantified-threads)
  duty_6  W  Baum :: down  --  ASSUMED (walk-invariant)
  duty_7  W  Baum :: leaf  --  ASSUMED (walk-invariant)
  duty_8  W  Baum :: invariant s9_mappings  --  ASSUMED (walk-invariant)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Knoten" _ "belegt" => some .bool
  | .slot "Knoten" _ "marke" => some (.intIn 0 4294967295)
  | .slot "Knoten" _ "elter" => some .opt
  | .slot "Knoten" _ "erstes_kind" => some .opt
  | .slot "Knoten" _ "naechstes_geschwister" => some .opt
  | .slot "Ring.plaetze" _ "elem" => some (.intIn 0 31)
  | .field "Ring" "kopf" => some (.intIn 0 4294967295)
  | .field "Ring" "zahl" => some (.intIn 0 4294967295)
  | .field "Wort" "gueltigkeit" => some .bool
  | .field "Wort" "schreibbar" => some .bool
  | .field "Wort" "rahmen" => some (.intIn 0 18446744073709551615)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `s1_slots` over `Knoten`. -/
def inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain` over `Knoten`. -/
def inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants` over `Knoten`. -/
def inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors` over `Knoten`. -/
def inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_s1_slots = some (.bool true)
  ∧ eval s0 inv_s2_chain = some (.bool true)
  ∧ eval s0 inv_s3_descendants = some (.bool true)
  ∧ eval s0 inv_s4_ancestors = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `r1_slots` -/

-- REFUSED  r1_slots  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r1_slots_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r1_slots` keeps it. -/
def r1_slots_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r1_slots` keeps it. -/
def r1_slots_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r1_slots` keeps it. -/
def r1_slots_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r1_slots` keeps it. -/
def r1_slots_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r1_slots_writes : List String := ["Knoten"]

/-- What a caller of `r1_slots` has to bring: a well-typed world and the precondition. -/
def r1_slots_requires (t : State) : Prop := wellFormed t ∧ eval t r1_slots_pre = some (.bool true)

/-- What `r1_slots` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r1_slots_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r1_slots_inv_s1_slots = some (.bool true)
  ∧ eval s' r1_slots_inv_s2_chain = some (.bool true)
  ∧ eval s' r1_slots_inv_s3_descendants = some (.bool true)
  ∧ eval s' r1_slots_inv_s4_ancestors = some (.bool true)

/-! ### `r2_chain` -/

-- REFUSED  r2_chain  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r2_chain_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r2_chain` keeps it. -/
def r2_chain_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r2_chain` keeps it. -/
def r2_chain_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r2_chain` keeps it. -/
def r2_chain_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r2_chain` keeps it. -/
def r2_chain_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r2_chain_writes : List String := ["Knoten"]

/-- What a caller of `r2_chain` has to bring: a well-typed world and the precondition. -/
def r2_chain_requires (t : State) : Prop := wellFormed t ∧ eval t r2_chain_pre = some (.bool true)

/-- What `r2_chain` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r2_chain_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r2_chain_inv_s1_slots = some (.bool true)
  ∧ eval s' r2_chain_inv_s2_chain = some (.bool true)
  ∧ eval s' r2_chain_inv_s3_descendants = some (.bool true)
  ∧ eval s' r2_chain_inv_s4_ancestors = some (.bool true)

/-! ### `r3_descendants` -/

-- REFUSED  r3_descendants  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r3_descendants_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r3_descendants` keeps it. -/
def r3_descendants_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r3_descendants` keeps it. -/
def r3_descendants_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r3_descendants` keeps it. -/
def r3_descendants_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r3_descendants` keeps it. -/
def r3_descendants_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r3_descendants_writes : List String := ["Knoten"]

/-- What a caller of `r3_descendants` has to bring: a well-typed world and the precondition. -/
def r3_descendants_requires (t : State) : Prop := wellFormed t ∧ eval t r3_descendants_pre = some (.bool true)

/-- What `r3_descendants` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r3_descendants_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r3_descendants_inv_s1_slots = some (.bool true)
  ∧ eval s' r3_descendants_inv_s2_chain = some (.bool true)
  ∧ eval s' r3_descendants_inv_s3_descendants = some (.bool true)
  ∧ eval s' r3_descendants_inv_s4_ancestors = some (.bool true)

/-! ### `r4_ancestors` -/

-- REFUSED  r4_ancestors  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r4_ancestors_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r4_ancestors` keeps it. -/
def r4_ancestors_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r4_ancestors` keeps it. -/
def r4_ancestors_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r4_ancestors` keeps it. -/
def r4_ancestors_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r4_ancestors` keeps it. -/
def r4_ancestors_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r4_ancestors_writes : List String := ["Knoten"]

/-- What a caller of `r4_ancestors` has to bring: a well-typed world and the precondition. -/
def r4_ancestors_requires (t : State) : Prop := wellFormed t ∧ eval t r4_ancestors_pre = some (.bool true)

/-- What `r4_ancestors` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r4_ancestors_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r4_ancestors_inv_s1_slots = some (.bool true)
  ∧ eval s' r4_ancestors_inv_s2_chain = some (.bool true)
  ∧ eval s' r4_ancestors_inv_s3_descendants = some (.bool true)
  ∧ eval s' r4_ancestors_inv_s4_ancestors = some (.bool true)

/-! ### `r5_queue` -/

def r5_queue_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def r5_queue_pre : Expr :=
  (.forallSlots "j" 32 (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64))))

def r5_queue_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `r5_queue` has to bring: a well-typed world and the precondition. -/
def r5_queue_requires (t : State) : Prop := wellFormed t ∧ eval t r5_queue_pre = some (.bool true)

/-- What `r5_queue` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r5_queue_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `r6_fields` -/

-- REFUSED  r6_fields  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r6_fields_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r6_fields` keeps it. -/
def r6_fields_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r6_fields` keeps it. -/
def r6_fields_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r6_fields` keeps it. -/
def r6_fields_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r6_fields` keeps it. -/
def r6_fields_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r6_fields_writes : List String := ["Knoten"]

/-- What a caller of `r6_fields` has to bring: a well-typed world and the precondition. -/
def r6_fields_requires (t : State) : Prop := wellFormed t ∧ eval t r6_fields_pre = some (.bool true)

/-- What `r6_fields` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r6_fields_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r6_fields_inv_s1_slots = some (.bool true)
  ∧ eval s' r6_fields_inv_s2_chain = some (.bool true)
  ∧ eval s' r6_fields_inv_s3_descendants = some (.bool true)
  ∧ eval s' r6_fields_inv_s4_ancestors = some (.bool true)

/-! ### `r7_elems` -/

def r7_elems_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def r7_elems_pre : Expr :=
  (.forallSlots "j" 32 (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64))))

def r7_elems_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `r7_elems` has to bring: a well-typed world and the precondition. -/
def r7_elems_requires (t : State) : Prop := wellFormed t ∧ eval t r7_elems_pre = some (.bool true)

/-- What `r7_elems` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r7_elems_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `r8_threads` -/

-- REFUSED  r8_threads  (quantified-threads): `threads` -- no declaration names the thread set (every other domain hangs on one); write `slots of <the thread table>`, or the language needs a `threads over T`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r8_threads_pre : Expr :=
  (.lit (.bool true))

/-- `s1_slots`, as `r8_threads` keeps it. -/
def r8_threads_inv_s1_slots : Expr :=
  (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0))))

/-- `s2_chain`, as `r8_threads` keeps it. -/
def r8_threads_inv_s2_chain : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "s") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.place "Knoten" (.name "x") "belegt"))))

/-- `s3_descendants`, as `r8_threads` keeps it. -/
def r8_threads_inv_s3_descendants : Expr :=
  (.forallSlots "s" 64 (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.un .not (.place "Knoten" (.name "x") "belegt"))))))

/-- `s4_ancestors`, as `r8_threads` keeps it. -/
def r8_threads_inv_s4_ancestors : Expr :=
  (.forallSlots "s" 64 (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))))

def r8_threads_writes : List String := ["Knoten"]

/-- What a caller of `r8_threads` has to bring: a well-typed world and the precondition. -/
def r8_threads_requires (t : State) : Prop := wellFormed t ∧ eval t r8_threads_pre = some (.bool true)

/-- What `r8_threads` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r8_threads_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' r8_threads_inv_s1_slots = some (.bool true)
  ∧ eval s' r8_threads_inv_s2_chain = some (.bool true)
  ∧ eval s' r8_threads_inv_s3_descendants = some (.bool true)
  ∧ eval s' r8_threads_inv_s4_ancestors = some (.bool true)

/-! ### `r9_mappings` -/

-- REFUSED  r9_mappings  (quantified-mappings): `mappings of <walk>` -- the mappings of a page-table walk are hardware; state it as an `invariant` OF the `walk`, which is ASSUMED by name
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def r9_mappings_pre : Expr :=
  (.lit (.bool true))

def r9_mappings_writes : List String := ["w"]

/-- What a caller of `r9_mappings` has to bring: a well-typed world and the precondition. -/
def r9_mappings_requires (t : State) : Prop := wellFormed t ∧ eval t r9_mappings_pre = some (.bool true)

/-- What `r9_mappings` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def r9_mappings_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `r5_queue` -/

/-- **The duty of `r5_queue`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def r5_queue_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s r5_queue_pre = some (.bool true)),
    ∃ s', finalState (exec ρ r5_queue_body s) = some s'
        ∧ r5_queue_post s s' (finalValue (exec ρ r5_queue_body s))

theorem r5_queue_meets : r5_queue_meets_statement := by
  unfold r5_queue_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [r5_queue_pre]
  gabbro_auto [r5_queue_body, r5_queue_pre, r5_queue_post, wellFormed, hall] using shapeOf

/-! ### `r7_elems` -/

/-- **The duty of `r7_elems`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def r7_elems_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s r7_elems_pre = some (.bool true)),
    ∃ s', finalState (exec ρ r7_elems_body s) = some s'
        ∧ r7_elems_post s s' (finalValue (exec ρ r7_elems_body s))

theorem r7_elems_meets : r7_elems_meets_statement := by
  unfold r7_elems_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [r7_elems_pre]
  gabbro_auto [r7_elems_body, r7_elems_pre, r7_elems_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "r5_queue" r5_queue_body
  ∧ Frame ρ "r5_queue" r5_queue_writes
  ∧ Runs ρ "r7_elems" r7_elems_body
  ∧ Frame ρ "r7_elems" r7_elems_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_r5_queue : r5_queue_meets_statement)
    (d_r7_elems : r7_elems_meets_statement) :
    Contract ρ "r5_queue" r5_queue_requires r5_queue_post
    ∧ Contract ρ "r7_elems" r7_elems_requires r7_elems_post := by
  obtain ⟨r_r5_queue, fr_r5_queue, r_r7_elems, fr_r7_elems⟩ := hp
  have c_r5_queue : Contract ρ "r5_queue" r5_queue_requires r5_queue_post :=
    contract_of_duty ρ "r5_queue" r5_queue_body r5_queue_requires r5_queue_post r_r5_queue
      (fun t ht => d_r5_queue ρ t ht.1 ht.2)
  have c_r7_elems : Contract ρ "r7_elems" r7_elems_requires r7_elems_post :=
    contract_of_duty ρ "r7_elems" r7_elems_body r7_elems_requires r7_elems_post r_r7_elems
      (fun t ht => d_r7_elems ρ t ht.1 ht.2)
  exact ⟨c_r5_queue, c_r7_elems⟩

end GabbroDuty.DutyProbeStellungen