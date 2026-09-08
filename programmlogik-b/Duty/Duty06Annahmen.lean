/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/06-annahmen.gab  total 1  goals 0  refused 1
        @assumed 1  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty06Annahmen

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (1): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_1  F  groesse_gemessen :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  F  groesse_gemessen :: ensures #1  --  ASSUMED (foreign-body)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "tiefe_max" => some (.intIn 0 1048576)
  | .global "tiefe_lebend" => some (.intIn 0 1048576)
  | .global "kerne_gemessen" => some (.intIn 0 4294967295)
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

/-! ### `abnahme` -/

def abnahme_body : List Stmt :=
  [(.ret none)]

/-- The precondition: the declared shapes and the `requires`. -/
def abnahme_pre : Expr :=
  (.lit (.bool true))

def abnahme_writes : List String := []

/-- What a caller of `abnahme` has to bring: a well-typed world and the precondition. -/
def abnahme_requires (t : State) : Prop := wellFormed t ∧ eval t abnahme_pre = some (.bool true)

/-- What `abnahme` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abnahme_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `freigabe` -/

def freigabe_body : List Stmt :=
  [(.ret none)]

/-- The precondition: the declared shapes and the `requires`. -/
def freigabe_pre : Expr :=
  (.lit (.bool true))

def freigabe_writes : List String := []

/-- What a caller of `freigabe` has to bring: a well-typed world and the precondition. -/
def freigabe_requires (t : State) : Prop := wellFormed t ∧ eval t freigabe_pre = some (.bool true)

/-- What `freigabe` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigabe_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abnahme` -/

/-- **The duty of `abnahme`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abnahme_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abnahme_pre = some (.bool true)),
    ∃ s', finalState (exec ρ abnahme_body s) = some s'
        ∧ abnahme_post s s' (finalValue (exec ρ abnahme_body s))

theorem abnahme_meets : abnahme_meets_statement := by
  unfold abnahme_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [abnahme_pre]
  gabbro_auto [abnahme_body, abnahme_pre, abnahme_post, wellFormed, hall] using shapeOf

/-! ### `freigabe` -/

/-- **The duty of `freigabe`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def freigabe_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s freigabe_pre = some (.bool true)),
    ∃ s', finalState (exec ρ freigabe_body s) = some s'
        ∧ freigabe_post s s' (finalValue (exec ρ freigabe_body s))

theorem freigabe_meets : freigabe_meets_statement := by
  unfold freigabe_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [freigabe_pre]
  gabbro_auto [freigabe_body, freigabe_pre, freigabe_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abnahme" abnahme_body
  ∧ Frame ρ "abnahme" abnahme_writes
  ∧ Runs ρ "freigabe" freigabe_body
  ∧ Frame ρ "freigabe" freigabe_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abnahme : abnahme_meets_statement)
    (d_freigabe : freigabe_meets_statement) :
    Contract ρ "abnahme" abnahme_requires abnahme_post
    ∧ Contract ρ "freigabe" freigabe_requires freigabe_post := by
  obtain ⟨r_abnahme, fr_abnahme, r_freigabe, fr_freigabe⟩ := hp
  have c_abnahme : Contract ρ "abnahme" abnahme_requires abnahme_post :=
    contract_of_duty ρ "abnahme" abnahme_body abnahme_requires abnahme_post r_abnahme
      (fun t ht => d_abnahme ρ t ht.1 ht.2)
  have c_freigabe : Contract ρ "freigabe" freigabe_requires freigabe_post :=
    contract_of_duty ρ "freigabe" freigabe_body freigabe_requires freigabe_post r_freigabe
      (fun t ht => d_freigabe ρ t ht.1 ht.2)
  exact ⟨c_abnahme, c_freigabe⟩

end GabbroDuty.Duty06Annahmen
