/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-let-ohne-leser.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeLetOhneLeser

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

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `spuelen` -- a foreign body: its contract is an assumption. -/
def spuelen_pre : Expr :=
  (.hasShape "a" (.intIn 0 18446744073709551615))

def spuelen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

def spuelen_writes : List String := ["a"]

def spuelen_requires (t : State) : Prop := wellFormed t ∧ eval t spuelen_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "spuelen" spuelen_requires spuelen_post
  ∧ Frame ρ "spuelen" spuelen_writes

/-! ## The routines: body and contract -/

/-! ### `dienst` -/

def dienst_body : List Stmt :=
  [(.bindCall "r2" "spuelen" ["a"] [(.name "a")] (.hasShape "a" (.intIn 0 18446744073709551615))), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def dienst_pre : Expr :=
  (.hasShape "a" (.intIn 0 18446744073709551615))

def dienst_writes : List String := ["a"]

/-- What a caller of `dienst` has to bring: a well-typed world and the precondition. -/
def dienst_requires (t : State) : Prop := wellFormed t ∧ eval t dienst_pre = some (.bool true)

/-- What `dienst` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def dienst_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `dienst` -/

/-- **The duty of `dienst`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def dienst_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s dienst_pre = some (.bool true))
    -- the contract of `spuelen`
    (c_spuelen : Contract ρ "spuelen" spuelen_requires spuelen_post)
    -- the frame of `spuelen`
    (fr_spuelen : Frame ρ "spuelen" spuelen_writes),
    ∃ s', finalState (exec ρ dienst_body s) = some s'
        ∧ dienst_post s s' (finalValue (exec ρ dienst_body s))

theorem dienst_meets : dienst_meets_statement := by
  unfold dienst_meets_statement
  intro ρ s hwf hpre c_spuelen fr_spuelen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [dienst_pre, e_a]
  gabbro_auto [dienst_body, dienst_pre, dienst_post, wellFormed, spuelen_pre, spuelen_requires, spuelen_post, spuelen_writes, Frame_read _ _ _ fr_spuelen, e_a, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "dienst" dienst_body
  ∧ Frame ρ "dienst" dienst_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_dienst : dienst_meets_statement) :
    Contract ρ "dienst" dienst_requires dienst_post := by
  obtain ⟨r_dienst, fr_dienst⟩ := hp
  obtain ⟨c_spuelen, fr_spuelen⟩ := ha
  have c_dienst : Contract ρ "dienst" dienst_requires dienst_post :=
    contract_of_duty ρ "dienst" dienst_body dienst_requires dienst_post r_dienst
      (fun t ht => d_dienst ρ t ht.1 ht.2 c_spuelen fr_spuelen)
  exact c_dienst

end GabbroDuty.DutyProbeLetOhneLeser
