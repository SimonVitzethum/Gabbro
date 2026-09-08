/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-marke-an-retry-und-traverse.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeMarkeAnRetryUndTraverse

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "zaehler" => some (.intIn 0 4294967295)
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

/-! ### `an_forever` -/

def an_forever_body : List Stmt :=
  [(.loop "an_forever#1" (.lit (.bool true)) [(.ite (.bin .eq (.global "zaehler") (.lit (.int 0))) [.exit] []), (.assignGlobal "zaehler" (.lit (.int 0)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def an_forever_pre : Expr :=
  (.lit (.bool true))

def an_forever_writes : List String := ["zaehler"]

/-- What a caller of `an_forever` has to bring: a well-typed world and the precondition. -/
def an_forever_requires (t : State) : Prop := wellFormed t ∧ eval t an_forever_pre = some (.bool true)

/-- What `an_forever` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def an_forever_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `an_retry` -/

def an_retry_body : List Stmt :=
  [(.loop "an_retry#1" (.lit (.bool true)) [(.ite (.bin .eq (.global "zaehler") (.lit (.int 0))) [.exit] []), (.assignGlobal "zaehler" (.lit (.int 3)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def an_retry_pre : Expr :=
  (.lit (.bool true))

def an_retry_writes : List String := ["zaehler"]

/-- What a caller of `an_retry` has to bring: a well-typed world and the precondition. -/
def an_retry_requires (t : State) : Prop := wellFormed t ∧ eval t an_retry_pre = some (.bool true)

/-- What `an_retry` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def an_retry_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `an_forever` -/

/-- Loop `an_forever#1` of `an_forever`: its body and its invariant (with the shapes of the locals in scope). -/
def an_forever_loop_1_inv : Expr :=
  (.lit (.bool true))

def an_forever_loop_1_body : List Stmt :=
  [(.ite (.bin .eq (.global "zaehler") (.lit (.int 0))) [.exit] []), (.assignGlobal "zaehler" (.lit (.int 0)))]

/-- **The loop rule of `an_forever#1`, as a statement over one pass.** -/
def an_forever_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t an_forever_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ an_forever_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' an_forever_loop_1_inv = some (.bool true)

theorem an_forever_loop_1_keeps : an_forever_loop_1_keeps_statement := by
  unfold an_forever_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [an_forever_loop_1_inv]
  gabbro_auto [an_forever_loop_1_body, an_forever_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `an_forever`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def an_forever_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s an_forever_pre = some (.bool true))
    -- the rule of loop `an_forever#1`
    (l_an_forever_loop_1 : LoopRule ρ "an_forever#1" wellFormed an_forever_loop_1_inv),
    ∃ s', finalState (exec ρ an_forever_body s) = some s'
        ∧ an_forever_post s s' (finalValue (exec ρ an_forever_body s))

theorem an_forever_meets : an_forever_meets_statement := by
  unfold an_forever_meets_statement
  intro ρ s hwf hpre l_an_forever_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [an_forever_pre]
  gabbro_auto [an_forever_body, an_forever_pre, an_forever_post, wellFormed, an_forever_loop_1_inv, hall] using shapeOf

/-! ### `an_retry` -/

/-- Loop `an_retry#1` of `an_retry`: its body and its invariant (with the shapes of the locals in scope). -/
def an_retry_loop_1_inv : Expr :=
  (.lit (.bool true))

def an_retry_loop_1_body : List Stmt :=
  [(.ite (.bin .eq (.global "zaehler") (.lit (.int 0))) [.exit] []), (.assignGlobal "zaehler" (.lit (.int 3)))]

/-- **The loop rule of `an_retry#1`, as a statement over one pass.** -/
def an_retry_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t an_retry_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ an_retry_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' an_retry_loop_1_inv = some (.bool true)

theorem an_retry_loop_1_keeps : an_retry_loop_1_keeps_statement := by
  unfold an_retry_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [an_retry_loop_1_inv]
  gabbro_auto [an_retry_loop_1_body, an_retry_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `an_retry`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def an_retry_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s an_retry_pre = some (.bool true))
    -- the rule of loop `an_retry#1`
    (l_an_retry_loop_1 : LoopRule ρ "an_retry#1" wellFormed an_retry_loop_1_inv),
    ∃ s', finalState (exec ρ an_retry_body s) = some s'
        ∧ an_retry_post s s' (finalValue (exec ρ an_retry_body s))

theorem an_retry_meets : an_retry_meets_statement := by
  unfold an_retry_meets_statement
  intro ρ s hwf hpre l_an_retry_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [an_retry_pre]
  gabbro_auto [an_retry_body, an_retry_pre, an_retry_post, wellFormed, an_retry_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "an_forever" an_forever_body
  ∧ Frame ρ "an_forever" an_forever_writes
  ∧ RunsLoop ρ "an_forever#1" an_forever_loop_1_body "#pass"
  ∧ Runs ρ "an_retry" an_retry_body
  ∧ Frame ρ "an_retry" an_retry_writes
  ∧ RunsLoop ρ "an_retry#1" an_retry_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_an_forever_loop_1 : an_forever_loop_1_keeps_statement)
    (d_an_forever : an_forever_meets_statement)
    (d_an_retry_loop_1 : an_retry_loop_1_keeps_statement)
    (d_an_retry : an_retry_meets_statement) :
    LoopRule ρ "an_forever#1" wellFormed an_forever_loop_1_inv
    ∧ Contract ρ "an_forever" an_forever_requires an_forever_post
    ∧ LoopRule ρ "an_retry#1" wellFormed an_retry_loop_1_inv
    ∧ Contract ρ "an_retry" an_retry_requires an_retry_post := by
  obtain ⟨r_an_forever, fr_an_forever, rl_an_forever_loop_1, r_an_retry, fr_an_retry, rl_an_retry_loop_1⟩ := hp
  have l_an_forever_loop_1 : LoopRule ρ "an_forever#1" wellFormed an_forever_loop_1_inv :=
    looprule_of_body ρ "an_forever#1" wellFormed an_forever_loop_1_inv an_forever_loop_1_body "#pass" rl_an_forever_loop_1
      (fun t k hw hi => d_an_forever_loop_1 ρ t k hw hi)
  have c_an_forever : Contract ρ "an_forever" an_forever_requires an_forever_post :=
    contract_of_duty ρ "an_forever" an_forever_body an_forever_requires an_forever_post r_an_forever
      (fun t ht => d_an_forever ρ t ht.1 ht.2 l_an_forever_loop_1)
  have l_an_retry_loop_1 : LoopRule ρ "an_retry#1" wellFormed an_retry_loop_1_inv :=
    looprule_of_body ρ "an_retry#1" wellFormed an_retry_loop_1_inv an_retry_loop_1_body "#pass" rl_an_retry_loop_1
      (fun t k hw hi => d_an_retry_loop_1 ρ t k hw hi)
  have c_an_retry : Contract ρ "an_retry" an_retry_requires an_retry_post :=
    contract_of_duty ρ "an_retry" an_retry_body an_retry_requires an_retry_post r_an_retry
      (fun t ht => d_an_retry ρ t ht.1 ht.2 l_an_retry_loop_1)
  exact ⟨l_an_forever_loop_1, c_an_forever, l_an_retry_loop_1, c_an_retry⟩

end GabbroDuty.DutyProbeMarkeAnRetryUndTraverse