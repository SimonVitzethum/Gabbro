/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/49-dispatch-tabelle.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty49DispatchTabelle

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "ZUSTAND" => some (.intIn 0 4294967295)
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

/-! ### `ausgeben` -/

-- REFUSED  ausgeben  (call-not-compositional): a call to a routine this unit does not declare
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def ausgeben_pre : Expr :=
  (.hasShape "b" (.intIn 0 255))

def ausgeben_writes : List String := ["ZUSTAND"]

/-- What a caller of `ausgeben` has to bring: a well-typed world and the precondition. -/
def ausgeben_requires (t : State) : Prop := wellFormed t ∧ eval t ausgeben_pre = some (.bool true)

/-- What `ausgeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ausgeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `baue` -/

-- REFUSED  baue  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def baue_pre : Expr :=
  (.lit (.bool true))

def baue_writes : List String := []

/-- What a caller of `baue` has to bring: a well-typed world and the precondition. -/
def baue_requires (t : State) : Prop := wellFormed t ∧ eval t baue_pre = some (.bool true)

/-- What `baue` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def baue_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `hart_bereit` -/

def hart_bereit_body : List Stmt :=
  [(.ret (some (.bin .eq (.global "ZUSTAND") (.lit (.int 1)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def hart_bereit_pre : Expr :=
  (.lit (.bool true))

def hart_bereit_writes : List String := []

/-- What a caller of `hart_bereit` has to bring: a well-typed world and the precondition. -/
def hart_bereit_requires (t : State) : Prop := wellFormed t ∧ eval t hart_bereit_pre = some (.bool true)

/-- What `hart_bereit` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hart_bereit_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `hart_senden` -/

def hart_senden_body : List Stmt :=
  [(.assignGlobal "ZUSTAND" (.name "b"))]

/-- The precondition: the declared shapes and the `requires`. -/
def hart_senden_pre : Expr :=
  (.hasShape "b" (.intIn 0 255))

def hart_senden_writes : List String := ["ZUSTAND"]

/-- What a caller of `hart_senden` has to bring: a well-typed world and the precondition. -/
def hart_senden_requires (t : State) : Prop := wellFormed t ∧ eval t hart_senden_pre = some (.bool true)

/-- What `hart_senden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hart_senden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `hart_bereit` -/

/-- **The duty of `hart_bereit`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def hart_bereit_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s hart_bereit_pre = some (.bool true)),
    ∃ s', finalState (exec ρ hart_bereit_body s) = some s'
        ∧ hart_bereit_post s s' (finalValue (exec ρ hart_bereit_body s))

theorem hart_bereit_meets : hart_bereit_meets_statement := by
  unfold hart_bereit_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [hart_bereit_pre]
  gabbro_auto [hart_bereit_body, hart_bereit_pre, hart_bereit_post, wellFormed, hall] using shapeOf

/-! ### `hart_senden` -/

/-- **The duty of `hart_senden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def hart_senden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s hart_senden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ hart_senden_body s) = some s'
        ∧ hart_senden_post s s' (finalValue (exec ρ hart_senden_body s))

theorem hart_senden_meets : hart_senden_meets_statement := by
  unfold hart_senden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [hart_senden_pre, e_b]
  gabbro_auto [hart_senden_body, hart_senden_pre, hart_senden_post, wellFormed, e_b, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "hart_bereit" hart_bereit_body
  ∧ Frame ρ "hart_bereit" hart_bereit_writes
  ∧ Runs ρ "hart_senden" hart_senden_body
  ∧ Frame ρ "hart_senden" hart_senden_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_hart_bereit : hart_bereit_meets_statement)
    (d_hart_senden : hart_senden_meets_statement) :
    Contract ρ "hart_bereit" hart_bereit_requires hart_bereit_post
    ∧ Contract ρ "hart_senden" hart_senden_requires hart_senden_post := by
  obtain ⟨r_hart_bereit, fr_hart_bereit, r_hart_senden, fr_hart_senden⟩ := hp
  have c_hart_bereit : Contract ρ "hart_bereit" hart_bereit_requires hart_bereit_post :=
    contract_of_duty ρ "hart_bereit" hart_bereit_body hart_bereit_requires hart_bereit_post r_hart_bereit
      (fun t ht => d_hart_bereit ρ t ht.1 ht.2)
  have c_hart_senden : Contract ρ "hart_senden" hart_senden_requires hart_senden_post :=
    contract_of_duty ρ "hart_senden" hart_senden_body hart_senden_requires hart_senden_post r_hart_senden
      (fun t ht => d_hart_senden ρ t ht.1 ht.2)
  exact ⟨c_hart_bereit, c_hart_senden⟩

end GabbroDuty.Duty49DispatchTabelle