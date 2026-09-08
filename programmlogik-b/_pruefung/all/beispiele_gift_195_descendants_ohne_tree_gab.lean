/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/gift/195-descendants-ohne-tree.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty195DescendantsOhneTree

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "T" _ "elter" => some .opt
  | .slot "T" _ "kind" => some .opt
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

/-! ### `raeume` -/

def raeume_body : List Stmt :=
  [(.loop "raeume#1" (.hasShape "s" (.intIn 0 7)) [])]

/-- The precondition: the declared shapes and the `requires`. -/
def raeume_pre : Expr :=
  (.hasShape "s" (.intIn 0 7))

def raeume_writes : List String := ["T"]

/-- What a caller of `raeume` has to bring: a well-typed world and the precondition. -/
def raeume_requires (t : State) : Prop := wellFormed t ∧ eval t raeume_pre = some (.bool true)

/-- What `raeume` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def raeume_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `raeume` -/

/-- Loop `raeume#1` of `raeume`: its body and its invariant (with the shapes of the locals in scope). -/
def raeume_loop_1_inv : Expr :=
  (.hasShape "s" (.intIn 0 7))

def raeume_loop_1_body : List Stmt :=
  []

/-- **The loop rule of `raeume#1`, as a statement over one pass.** -/
def raeume_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t raeume_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ raeume_loop_1_body { t with local' := bindLocal t.local' "v" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' raeume_loop_1_inv = some (.bool true)

theorem raeume_loop_1_keeps : raeume_loop_1_keeps_statement := by
  unfold raeume_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn t "s" _ _ hinv
  have hall := hinv
  gabbro_simp_at hall [raeume_loop_1_inv, e_s]
  gabbro_auto [raeume_loop_1_body, raeume_loop_1_inv, wellFormed, e_s, hall] using shapeOf

/-- **The duty of `raeume`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def raeume_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s raeume_pre = some (.bool true))
    -- the rule of loop `raeume#1`
    (l_raeume_loop_1 : LoopRule ρ "raeume#1" wellFormed raeume_loop_1_inv),
    ∃ s', finalState (exec ρ raeume_body s) = some s'
        ∧ raeume_post s s' (finalValue (exec ρ raeume_body s))

theorem raeume_meets : raeume_meets_statement := by
  unfold raeume_meets_statement
  intro ρ s hwf hpre l_raeume_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [raeume_pre, e_s]
  gabbro_auto [raeume_body, raeume_pre, raeume_post, wellFormed, raeume_loop_1_inv, e_s, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "raeume" raeume_body
  ∧ Frame ρ "raeume" raeume_writes
  ∧ RunsLoop ρ "raeume#1" raeume_loop_1_body "v"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_raeume_loop_1 : raeume_loop_1_keeps_statement)
    (d_raeume : raeume_meets_statement) :
    LoopRule ρ "raeume#1" wellFormed raeume_loop_1_inv
    ∧ Contract ρ "raeume" raeume_requires raeume_post := by
  obtain ⟨r_raeume, fr_raeume, rl_raeume_loop_1⟩ := hp
  have l_raeume_loop_1 : LoopRule ρ "raeume#1" wellFormed raeume_loop_1_inv :=
    looprule_of_body ρ "raeume#1" wellFormed raeume_loop_1_inv raeume_loop_1_body "v" rl_raeume_loop_1
      (fun t k hw hi => d_raeume_loop_1 ρ t k hw hi)
  have c_raeume : Contract ρ "raeume" raeume_requires raeume_post :=
    contract_of_duty ρ "raeume" raeume_body raeume_requires raeume_post r_raeume
      (fun t ht => d_raeume ρ t ht.1 ht.2 l_raeume_loop_1)
  exact ⟨l_raeume_loop_1, c_raeume⟩

end GabbroDuty.Duty195DescendantsOhneTree
