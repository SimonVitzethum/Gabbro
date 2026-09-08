/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/gift/414-tabellenspeicher-heisst-so.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty414TabellenspeicherHeisstSo

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kappe" _ "benutzt" => some .bool
  | .global "Kappe_speicher" => some (.intIn 0 4294967295)
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

/-! ### `beruehren` -/

def beruehren_body : List Stmt :=
  [(.ret (some (.place "Kappe" (.name "s") "benutzt")))]

/-- The precondition: the declared shapes and the `requires`. -/
def beruehren_pre : Expr :=
  (.hasShape "s" (.intIn 0 7))

def beruehren_writes : List String := []

/-- What a caller of `beruehren` has to bring: a well-typed world and the precondition. -/
def beruehren_requires (t : State) : Prop := wellFormed t ∧ eval t beruehren_pre = some (.bool true)

/-- What `beruehren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def beruehren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `beruehren` -/

/-- **The duty of `beruehren`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def beruehren_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s beruehren_pre = some (.bool true)),
    ∃ s', finalState (exec ρ beruehren_body s) = some s'
        ∧ beruehren_post s s' (finalValue (exec ρ beruehren_body s))

theorem beruehren_meets : beruehren_meets_statement := by
  unfold beruehren_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ hpre
  obtain ⟨n_Kappe_benutzt_s, h_Kappe_benutzt_s⟩ := WF_bool shapeOf s.world (.slot "Kappe" w_s "benutzt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [beruehren_pre, e_s, h_Kappe_benutzt_s]
  gabbro_auto [beruehren_body, beruehren_pre, beruehren_post, wellFormed, e_s, h_Kappe_benutzt_s, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "beruehren" beruehren_body
  ∧ Frame ρ "beruehren" beruehren_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_beruehren : beruehren_meets_statement) :
    Contract ρ "beruehren" beruehren_requires beruehren_post := by
  obtain ⟨r_beruehren, fr_beruehren⟩ := hp
  have c_beruehren : Contract ρ "beruehren" beruehren_requires beruehren_post :=
    contract_of_duty ρ "beruehren" beruehren_body beruehren_requires beruehren_post r_beruehren
      (fun t ht => d_beruehren ρ t ht.1 ht.2)
  exact c_beruehren

end GabbroDuty.Duty414TabellenspeicherHeisstSo