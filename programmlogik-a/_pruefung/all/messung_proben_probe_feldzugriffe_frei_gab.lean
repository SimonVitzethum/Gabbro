/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-feldzugriffe-frei.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeFeldzugriffeFrei

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

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `aus_geraeteparameter` -/

-- REFUSED  aus_geraeteparameter  (record-value): a field of a record VALUE bound in the body (`let c = f(x); c.len`) -- this model's places are named by a record TYPE; pass the record through a `ptr` parameter
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def aus_geraeteparameter_pre : Expr :=
  (.lit (.bool true))

def aus_geraeteparameter_writes : List String := []

/-- What a caller of `aus_geraeteparameter` has to bring: a well-typed world and the precondition. -/
def aus_geraeteparameter_requires (t : State) : Prop := wellFormed t ∧ eval t aus_geraeteparameter_pre = some (.bool true)

/-- What `aus_geraeteparameter` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aus_geraeteparameter_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `aus_register` -/

-- REFUSED  aus_register  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def aus_register_pre : Expr :=
  (.lit (.bool true))

def aus_register_writes : List String := []

/-- What a caller of `aus_register` has to bring: a well-typed world and the precondition. -/
def aus_register_requires (t : State) : Prop := wellFormed t ∧ eval t aus_register_pre = some (.bool true)

/-- What `aus_register` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aus_register_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `aus_verbund` -/

def aus_verbund_body : List Stmt :=
  [(.ret (some (.fieldOf "Nachricht" "op")))]

/-- The precondition: the declared shapes and the `requires`. -/
def aus_verbund_pre : Expr :=
  (.lit (.bool true))

def aus_verbund_writes : List String := []

/-- What a caller of `aus_verbund` has to bring: a well-typed world and the precondition. -/
def aus_verbund_requires (t : State) : Prop := wellFormed t ∧ eval t aus_verbund_pre = some (.bool true)

/-- What `aus_verbund` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aus_verbund_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `aus_verbund` -/

/-- **The duty of `aus_verbund`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aus_verbund_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aus_verbund_pre = some (.bool true)),
    ∃ s', finalState (exec ρ aus_verbund_body s) = some s'
        ∧ aus_verbund_post s s' (finalValue (exec ρ aus_verbund_body s))

theorem aus_verbund_meets : aus_verbund_meets_statement := by
  unfold aus_verbund_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Nachricht_op, h_Nachricht_op, lo_Nachricht_op, hi_Nachricht_op⟩ := WF_intIn shapeOf s.world (.field "Nachricht" "op") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [aus_verbund_pre, h_Nachricht_op]
  gabbro_auto [aus_verbund_body, aus_verbund_pre, aus_verbund_post, wellFormed, h_Nachricht_op, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aus_verbund" aus_verbund_body
  ∧ Frame ρ "aus_verbund" aus_verbund_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_aus_verbund : aus_verbund_meets_statement) :
    Contract ρ "aus_verbund" aus_verbund_requires aus_verbund_post := by
  obtain ⟨r_aus_verbund, fr_aus_verbund⟩ := hp
  have c_aus_verbund : Contract ρ "aus_verbund" aus_verbund_requires aus_verbund_post :=
    contract_of_duty ρ "aus_verbund" aus_verbund_body aus_verbund_requires aus_verbund_post r_aus_verbund
      (fun t ht => d_aus_verbund ρ t ht.1 ht.2)
  exact c_aus_verbund

end GabbroDuty.DutyProbeFeldzugriffeFrei