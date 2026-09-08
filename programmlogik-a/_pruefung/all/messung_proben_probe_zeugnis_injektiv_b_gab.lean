/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-zeugnis-injektiv-b.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeZeugnisInjektivB

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Ring.plaetze" _ "elem" => some (.intIn 0 4294967295)
  | .slot "Warteschlange" _ "a" => some (.intIn 0 4294967295)
  | .slot "Warteschlange" _ "naechst" => some .opt
  | .field "Ring" "kopf" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `nie` -- a foreign body: its contract is an assumption. -/
def nie_pre : Expr :=
  (.lit (.bool true))

def nie_post (t t' : State) (r : Option Value) : Prop :=
  False

def nie_writes : List String := []

def nie_requires (t : State) : Prop := wellFormed t ∧ eval t nie_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "nie" nie_requires nie_post
  ∧ Frame ρ "nie" nie_writes

/-! ## The routines: body and contract -/

/-! ### `eine` -/

def eine_body : List Stmt :=
  [(.loop "eine#1" (.lit (.bool true)) [(.assign "Warteschlange" (.lit (.int 0)) "a" (.lit (.int 1)))]), (.call "nie" [] [] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def eine_pre : Expr :=
  (.lit (.bool true))

def eine_writes : List String := ["Warteschlange"]

/-- What a caller of `eine` has to bring: a well-typed world and the precondition. -/
def eine_requires (t : State) : Prop := wellFormed t ∧ eval t eine_pre = some (.bool true)

/-- What `eine` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def eine_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `eine` -/

/-- Loop `eine#1` of `eine`: its body and its invariant (with the shapes of the locals in scope). -/
def eine_loop_1_inv : Expr :=
  (.lit (.bool true))

def eine_loop_1_body : List Stmt :=
  [(.assign "Warteschlange" (.lit (.int 0)) "a" (.lit (.int 1)))]

/-- **The loop rule of `eine#1`, as a statement over one pass.** -/
def eine_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 4294967296)
    (hwf : wellFormed t)
    (hinv : eval t eine_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ eine_loop_1_body { t with local' := bindLocal t.local' "t" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' eine_loop_1_inv = some (.bool true)

theorem eine_loop_1_keeps : eine_loop_1_keeps_statement := by
  unfold eine_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [eine_loop_1_inv]
  gabbro_auto [eine_loop_1_body, eine_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `eine`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def eine_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s eine_pre = some (.bool true))
    -- the contract of `nie`
    (c_nie : Contract ρ "nie" nie_requires nie_post)
    -- the frame of `nie`
    (fr_nie : Frame ρ "nie" nie_writes)
    -- the rule of loop `eine#1`
    (l_eine_loop_1 : LoopRule ρ "eine#1" wellFormed eine_loop_1_inv),
    ∃ s', finalState (exec ρ eine_body s) = some s'
        ∧ eine_post s s' (finalValue (exec ρ eine_body s))

theorem eine_meets : eine_meets_statement := by
  unfold eine_meets_statement
  intro ρ s hwf hpre c_nie fr_nie l_eine_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [eine_pre]
  gabbro_auto [eine_body, eine_pre, eine_post, wellFormed, nie_pre, nie_requires, nie_post, nie_writes, Frame_read _ _ _ fr_nie, eine_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "eine" eine_body
  ∧ Frame ρ "eine" eine_writes
  ∧ RunsLoopIn ρ "eine#1" eine_loop_1_body "t" 0 4294967296

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_eine_loop_1 : eine_loop_1_keeps_statement)
    (d_eine : eine_meets_statement) :
    LoopRule ρ "eine#1" wellFormed eine_loop_1_inv
    ∧ Contract ρ "eine" eine_requires eine_post := by
  obtain ⟨r_eine, fr_eine, rl_eine_loop_1⟩ := hp
  obtain ⟨c_nie, fr_nie⟩ := ha
  have l_eine_loop_1 : LoopRule ρ "eine#1" wellFormed eine_loop_1_inv :=
    looprule_of_body_in ρ "eine#1" wellFormed eine_loop_1_inv eine_loop_1_body "t" 0 4294967296 rl_eine_loop_1
      (fun t k hlo hhi hw hi => d_eine_loop_1 ρ t k hlo hhi hw hi)
  have c_eine : Contract ρ "eine" eine_requires eine_post :=
    contract_of_duty ρ "eine" eine_body eine_requires eine_post r_eine
      (fun t ht => d_eine ρ t ht.1 ht.2 c_nie fr_nie l_eine_loop_1)
  exact ⟨l_eine_loop_1, c_eine⟩

end GabbroDuty.DutyProbeZeugnisInjektivB