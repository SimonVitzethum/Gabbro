/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/gift/642-a-forever-loop-in-a-function-that-answers.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty642AForeverLoopInAFunctionThatAnswers

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "erledigt" => some (.intIn 0 18446744073709551615)
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

/-! ### `g` -/

def g_body : List Stmt :=
  [(.loop "g#1" (.lit (.bool true)) [(.assignGlobal "erledigt" (.lit (.int 1)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def g_pre : Expr :=
  (.lit (.bool true))

def g_writes : List String := ["erledigt"]

/-- What a caller of `g` has to bring: a well-typed world and the precondition. -/
def g_requires (t : State) : Prop := wellFormed t ∧ eval t g_pre = some (.bool true)

/-- What `g` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def g_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `g` -/

/-- Loop `g#1` of `g`: its body and its invariant (with the shapes of the locals in scope). -/
def g_loop_1_inv : Expr :=
  (.lit (.bool true))

def g_loop_1_body : List Stmt :=
  [(.assignGlobal "erledigt" (.lit (.int 1)))]

/-- **The loop rule of `g#1`, as a statement over one pass.** -/
def g_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t g_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ g_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' g_loop_1_inv = some (.bool true)

theorem g_loop_1_keeps : g_loop_1_keeps_statement := by
  unfold g_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [g_loop_1_inv]
  gabbro_auto [g_loop_1_body, g_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `g`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def g_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s g_pre = some (.bool true))
    -- the rule of loop `g#1`
    (l_g_loop_1 : LoopRule ρ "g#1" wellFormed g_loop_1_inv),
    ∃ s', finalState (exec ρ g_body s) = some s'
        ∧ g_post s s' (finalValue (exec ρ g_body s))

theorem g_meets : g_meets_statement := by
  unfold g_meets_statement
  intro ρ s hwf hpre l_g_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [g_pre]
  gabbro_auto [g_body, g_pre, g_post, wellFormed, g_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "g" g_body
  ∧ Frame ρ "g" g_writes
  ∧ RunsLoop ρ "g#1" g_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_g_loop_1 : g_loop_1_keeps_statement)
    (d_g : g_meets_statement) :
    LoopRule ρ "g#1" wellFormed g_loop_1_inv
    ∧ Contract ρ "g" g_requires g_post := by
  obtain ⟨r_g, fr_g, rl_g_loop_1⟩ := hp
  have l_g_loop_1 : LoopRule ρ "g#1" wellFormed g_loop_1_inv :=
    looprule_of_body ρ "g#1" wellFormed g_loop_1_inv g_loop_1_body "#pass" rl_g_loop_1
      (fun t k hw hi => d_g_loop_1 ρ t k hw hi)
  have c_g : Contract ρ "g" g_requires g_post :=
    contract_of_duty ρ "g" g_body g_requires g_post r_g
      (fun t ht => d_g ρ t ht.1 ht.2 l_g_loop_1)
  exact ⟨l_g_loop_1, c_g⟩

end GabbroDuty.Duty642AForeverLoopInAFunctionThatAnswers
