/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-zeugenpflicht.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeZeugenpflicht

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Arena" _ "belegt" => some .bool
  | .global "hinterlegt" => some (.intIn 4 16)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `griff_fuer` -- a foreign body: its contract is an assumption. -/
def griff_fuer_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def griff_fuer_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)

def griff_fuer_writes : List String := []

def griff_fuer_requires (t : State) : Prop := wellFormed t ∧ eval t griff_fuer_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "griff_fuer" griff_fuer_requires griff_fuer_post
  ∧ Frame ρ "griff_fuer" griff_fuer_writes

/-! ## The routines: body and contract -/

/-! ### `freigeben` -/

-- REFUSED  freigeben  (match-not-option): a `match` over something other than an `option`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def freigeben_pre : Expr :=
  (.lit (.bool true))

def freigeben_writes : List String := ["Arena", "g"]

/-- What a caller of `freigeben` has to bring: a well-typed world and the precondition. -/
def freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t freigeben_pre = some (.bool true)

/-- What `freigeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `vergeben` -/

def vergeben_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "i") (.lit (.int 0))) (.bin .lt (.name "i") (.global "hinterlegt"))) [] [(.retCall "griff_fuer" ["i"] [(.name "i")] (.hasShape "i" (.intIn 0 15)))]), (.assign "Arena" (.name "i") "belegt" (.lit (.bool true))), (.retCall "griff_fuer" ["i"] [(.name "i")] (.hasShape "i" (.intIn 0 15)))]

/-- The precondition: the declared shapes and the `requires`. -/
def vergeben_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def vergeben_writes : List String := ["Arena"]

/-- What a caller of `vergeben` has to bring: a well-typed world and the precondition. -/
def vergeben_requires (t : State) : Prop := wellFormed t ∧ eval t vergeben_pre = some (.bool true)

/-- What `vergeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def vergeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `vergeben` -/

/-- **The duty of `vergeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def vergeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s vergeben_pre = some (.bool true))
    -- the contract of `griff_fuer`
    (c_griff_fuer : Contract ρ "griff_fuer" griff_fuer_requires griff_fuer_post)
    -- the frame of `griff_fuer`
    (fr_griff_fuer : Frame ρ "griff_fuer" griff_fuer_writes),
    ∃ s', finalState (exec ρ vergeben_body s) = some s'
        ∧ vergeben_post s s' (finalValue (exec ρ vergeben_body s))

theorem vergeben_meets : vergeben_meets_statement := by
  unfold vergeben_meets_statement
  intro ρ s hwf hpre c_griff_fuer fr_griff_fuer
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [vergeben_pre, e_i]
  gabbro_auto [vergeben_body, vergeben_pre, vergeben_post, wellFormed, griff_fuer_pre, griff_fuer_requires, griff_fuer_post, griff_fuer_writes, Frame_read _ _ _ fr_griff_fuer, e_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "vergeben" vergeben_body
  ∧ Frame ρ "vergeben" vergeben_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_vergeben : vergeben_meets_statement) :
    Contract ρ "vergeben" vergeben_requires vergeben_post := by
  obtain ⟨r_vergeben, fr_vergeben⟩ := hp
  obtain ⟨c_griff_fuer, fr_griff_fuer⟩ := ha
  have c_vergeben : Contract ρ "vergeben" vergeben_requires vergeben_post :=
    contract_of_duty ρ "vergeben" vergeben_body vergeben_requires vergeben_post r_vergeben
      (fun t ht => d_vergeben ρ t ht.1 ht.2 c_griff_fuer fr_griff_fuer)
  exact c_vergeben

end GabbroDuty.DutyProbeZeugenpflicht