/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/gift/286-maintains-ohne-schreiben.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty286MaintainsOhneSchreiben

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  E  nur_lesen :: klein  --  carried by `nur_lesen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "T" _ "a" => some (.intIn 0 10)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `klein` over `T`. -/
def inv_klein : Expr :=
  (.forallSlots "i" 16 (.bin .lt (.place "T" (.name "i") "a") (.lit (.int 10))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_klein = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `nur_lesen` -/

def nur_lesen_body : List Stmt :=
  [(.ret (some (.place "T" (.lit (.int 0)) "a")))]

/-- The precondition: the declared shapes and the `requires`. -/
def nur_lesen_pre : Expr :=
  (.forallSlots "i" 16 (.bin .lt (.place "T" (.name "i") "a") (.lit (.int 10))))

/-- `klein`, as `nur_lesen` keeps it. -/
def nur_lesen_inv_klein : Expr :=
  (.forallSlots "i" 16 (.bin .lt (.place "T" (.name "i") "a") (.lit (.int 10))))

def nur_lesen_writes : List String := []

/-- What a caller of `nur_lesen` has to bring: a well-typed world and the precondition. -/
def nur_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t nur_lesen_pre = some (.bool true)

/-- What `nur_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def nur_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)
  ∧ eval s' nur_lesen_inv_klein = some (.bool true)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `nur_lesen` -/

/-- **The duty of `nur_lesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def nur_lesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s nur_lesen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ nur_lesen_body s) = some s'
        ∧ nur_lesen_post s s' (finalValue (exec ρ nur_lesen_body s))

theorem nur_lesen_meets : nur_lesen_meets_statement := by
  unfold nur_lesen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_klein := hpre
  gabbro_simp_at hi_klein [nur_lesen_inv_klein, nur_lesen_pre]
  have hall := hpre
  gabbro_simp_at hall [nur_lesen_pre]
  gabbro_auto [nur_lesen_body, nur_lesen_pre, nur_lesen_post, wellFormed, nur_lesen_inv_klein, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "nur_lesen" nur_lesen_body
  ∧ Frame ρ "nur_lesen" nur_lesen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_nur_lesen : nur_lesen_meets_statement) :
    Contract ρ "nur_lesen" nur_lesen_requires nur_lesen_post := by
  obtain ⟨r_nur_lesen, fr_nur_lesen⟩ := hp
  have c_nur_lesen : Contract ρ "nur_lesen" nur_lesen_requires nur_lesen_post :=
    contract_of_duty ρ "nur_lesen" nur_lesen_body nur_lesen_requires nur_lesen_post r_nur_lesen
      (fun t ht => d_nur_lesen ρ t ht.1 ht.2)
  exact c_nur_lesen

end GabbroDuty.Duty286MaintainsOhneSchreiben