/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-extern-bindet-c.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeExternBindetC

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

/-- `putchar` -- a foreign body: its contract is an assumption. -/
def putchar_pre : Expr :=
  (.hasShape "c" (.intIn (-2147483648) 2147483647))

def putchar_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ (-2147483648) ≤ x ∧ x ≤ 2147483647)

def putchar_writes : List String := ["ausgabe"]

def putchar_requires (t : State) : Prop := wellFormed t ∧ eval t putchar_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "putchar" putchar_requires putchar_post
  ∧ Frame ρ "putchar" putchar_writes

/-! ## The routines: body and contract -/

/-! ### `haupt` -/

def haupt_body : List Stmt :=
  [(.call "putchar" ["c"] [(.name "z")] (.hasShape "c" (.intIn (-2147483648) 2147483647))), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def haupt_pre : Expr :=
  (.hasShape "z" (.intIn 0 100))

def haupt_writes : List String := ["ausgabe"]

/-- What a caller of `haupt` has to bring: a well-typed world and the precondition. -/
def haupt_requires (t : State) : Prop := wellFormed t ∧ eval t haupt_pre = some (.bool true)

/-- What `haupt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def haupt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 1)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `haupt` -/

/-- **The duty of `haupt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def haupt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s haupt_pre = some (.bool true))
    -- the contract of `putchar`
    (c_putchar : Contract ρ "putchar" putchar_requires putchar_post)
    -- the frame of `putchar`
    (fr_putchar : Frame ρ "putchar" putchar_writes),
    ∃ s', finalState (exec ρ haupt_body s) = some s'
        ∧ haupt_post s s' (finalValue (exec ρ haupt_body s))

theorem haupt_meets : haupt_meets_statement := by
  unfold haupt_meets_statement
  intro ρ s hwf hpre c_putchar fr_putchar
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_z, e_z, lo_z, hi_z⟩ := shape_intIn s "z" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [haupt_pre, e_z]
  gabbro_auto [haupt_body, haupt_pre, haupt_post, wellFormed, putchar_pre, putchar_requires, putchar_post, putchar_writes, Frame_read _ _ _ fr_putchar, e_z, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "haupt" haupt_body
  ∧ Frame ρ "haupt" haupt_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_haupt : haupt_meets_statement) :
    Contract ρ "haupt" haupt_requires haupt_post := by
  obtain ⟨r_haupt, fr_haupt⟩ := hp
  obtain ⟨c_putchar, fr_putchar⟩ := ha
  have c_haupt : Contract ρ "haupt" haupt_requires haupt_post :=
    contract_of_duty ρ "haupt" haupt_body haupt_requires haupt_post r_haupt
      (fun t ht => d_haupt ρ t ht.1 ht.2 c_putchar fr_putchar)
  exact c_haupt

end GabbroDuty.DutyProbeExternBindetC
