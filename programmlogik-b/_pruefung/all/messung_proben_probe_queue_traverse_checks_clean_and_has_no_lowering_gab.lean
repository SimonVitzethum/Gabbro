/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-queue-traverse-checks-clean-and-has-no-lowering.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeQueueTraverseChecksCleanAndHasNoLowering

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "TidQueue.buf" _ "elem" => some (.intIn 0 4294967295)
  | .field "TidQueue" "head" => some (.intIn 0 31)
  | .field "TidQueue" "tail" => some (.intIn 0 31)
  | .field "TidQueue" "count" => some (.intIn 0 32)
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

/-! ### `leeren` -/

def leeren_body : List Stmt :=
  [(.bindName "n" (.lit (.int 0))), (.loop "leeren#1" (.bin .and (.hasShape "k" (.intIn 0 3)) (.hasShape "n" (.intIn 0 4294967295))) [(.bindName "n" (.name "cand"))]), (.ret (some (.name "n")))]

/-- The precondition: the declared shapes and the `requires`. -/
def leeren_pre : Expr :=
  (.hasShape "k" (.intIn 0 3))

def leeren_writes : List String := ["Halter"]

/-- What a caller of `leeren` has to bring: a well-typed world and the precondition. -/
def leeren_requires (t : State) : Prop := wellFormed t ∧ eval t leeren_pre = some (.bool true)

/-- What `leeren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def leeren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `leeren` -/

/-- Loop `leeren#1` of `leeren`: its body and its invariant (with the shapes of the locals in scope). -/
def leeren_loop_1_inv : Expr :=
  (.bin .and (.hasShape "k" (.intIn 0 3)) (.hasShape "n" (.intIn 0 4294967295)))

def leeren_loop_1_body : List Stmt :=
  [(.bindName "n" (.name "cand"))]

/-- **The loop rule of `leeren#1`, as a statement over one pass.** -/
def leeren_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 4294967296)
    (hwf : wellFormed t)
    (hinv : eval t leeren_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ leeren_loop_1_body { t with local' := bindLocal t.local' "cand" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' leeren_loop_1_inv = some (.bool true)

theorem leeren_loop_1_keeps : leeren_loop_1_keeps_statement := by
  unfold leeren_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn t "k" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_right _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [leeren_loop_1_inv, e_k, e_n]
  gabbro_auto [leeren_loop_1_body, leeren_loop_1_inv, wellFormed, e_k, e_n, hall] using shapeOf

/-- **The duty of `leeren`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def leeren_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s leeren_pre = some (.bool true))
    -- the rule of loop `leeren#1`
    (l_leeren_loop_1 : LoopRule ρ "leeren#1" wellFormed leeren_loop_1_inv),
    ∃ s', finalState (exec ρ leeren_body s) = some s'
        ∧ leeren_post s s' (finalValue (exec ρ leeren_body s))

theorem leeren_meets : leeren_meets_statement := by
  unfold leeren_meets_statement
  intro ρ s hwf hpre l_leeren_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn s "k" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [leeren_pre, e_k]
  gabbro_auto [leeren_body, leeren_pre, leeren_post, wellFormed, leeren_loop_1_inv, e_k, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "leeren" leeren_body
  ∧ Frame ρ "leeren" leeren_writes
  ∧ RunsLoopIn ρ "leeren#1" leeren_loop_1_body "cand" 0 4294967296

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_leeren_loop_1 : leeren_loop_1_keeps_statement)
    (d_leeren : leeren_meets_statement) :
    LoopRule ρ "leeren#1" wellFormed leeren_loop_1_inv
    ∧ Contract ρ "leeren" leeren_requires leeren_post := by
  obtain ⟨r_leeren, fr_leeren, rl_leeren_loop_1⟩ := hp
  have l_leeren_loop_1 : LoopRule ρ "leeren#1" wellFormed leeren_loop_1_inv :=
    looprule_of_body_in ρ "leeren#1" wellFormed leeren_loop_1_inv leeren_loop_1_body "cand" 0 4294967296 rl_leeren_loop_1
      (fun t k hlo hhi hw hi => d_leeren_loop_1 ρ t k hlo hhi hw hi)
  have c_leeren : Contract ρ "leeren" leeren_requires leeren_post :=
    contract_of_duty ρ "leeren" leeren_body leeren_requires leeren_post r_leeren
      (fun t ht => d_leeren ρ t ht.1 ht.2 l_leeren_loop_1)
  exact ⟨l_leeren_loop_1, c_leeren⟩

end GabbroDuty.DutyProbeQueueTraverseChecksCleanAndHasNoLowering
