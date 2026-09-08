/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/57-faedenhalt.gab  total 2  goals 1  refused 1
        @assumed 0  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 1 are refused forms

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

namespace GabbroDuty.Duty57Faedenhalt

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  quantified (1): refused -- a quantifier over a domain other than `slots of`, or a membership
    duty_1  N  alle_anhalten :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  alle_anhalten :: ensures #1  --  refused (quantified)
  duty_2  V  halt_verteiler :: alle_anhalten requires #1  --  carried by `halt_verteiler_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Faden" _ "zustand" => some (.intIn 0 255)
  | .slot "Faden" _ "kern" => some (.intIn 0 4294967295)
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

/-! ### `alle_anhalten` -/

def alle_anhalten_body : List Stmt :=
  [(.loop "alle_anhalten#1" (.lit (.bool true)) [(.ite (.bin .eq (.place "Faden" (.name "t") "zustand") (.lit (.int 0))) [(.assign "Faden" (.name "t") "zustand" (.lit (.int 1)))] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def alle_anhalten_pre : Expr :=
  (.lit (.bool true))

def alle_anhalten_writes : List String := ["Faden"]

/-- What a caller of `alle_anhalten` has to bring: a well-typed world and the precondition. -/
def alle_anhalten_requires (t : State) : Prop := wellFormed t ∧ eval t alle_anhalten_pre = some (.bool true)

/-- What `alle_anhalten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def alle_anhalten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1: NOT SAID (quantified) -- a promise fewer makes a caller's goal harder, never wrong
  True

/-! ### `halt_verteiler` -/

def halt_verteiler_body : List Stmt :=
  [(.locked "FAEDEN" [(.call "alle_anhalten" [] [] (.lit (.bool true)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def halt_verteiler_pre : Expr :=
  (.lit (.bool true))

def halt_verteiler_writes : List String := ["Faden"]

/-- What a caller of `halt_verteiler` has to bring: a well-typed world and the precondition. -/
def halt_verteiler_requires (t : State) : Prop := wellFormed t ∧ eval t halt_verteiler_pre = some (.bool true)

/-- What `halt_verteiler` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def halt_verteiler_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `alle_anhalten` -/

/-- Loop `alle_anhalten#1` of `alle_anhalten`: its body and its invariant (with the shapes of the locals in scope). -/
def alle_anhalten_loop_1_inv : Expr :=
  (.lit (.bool true))

def alle_anhalten_loop_1_body : List Stmt :=
  [(.ite (.bin .eq (.place "Faden" (.name "t") "zustand") (.lit (.int 0))) [(.assign "Faden" (.name "t") "zustand" (.lit (.int 1)))] [])]

/-- **The loop rule of `alle_anhalten#1`, as a statement over one pass.** -/
def alle_anhalten_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 128)
    (hwf : wellFormed t)
    (hinv : eval t alle_anhalten_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ alle_anhalten_loop_1_body { t with local' := bindLocal t.local' "t" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' alle_anhalten_loop_1_inv = some (.bool true)

theorem alle_anhalten_loop_1_keeps : alle_anhalten_loop_1_keeps_statement := by
  unfold alle_anhalten_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Faden_zustand_t, h_Faden_zustand_t, lo_Faden_zustand_t, hi_Faden_zustand_t⟩ := WF_intIn shapeOf t.world (.slot "Faden" k "zustand") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [alle_anhalten_loop_1_inv, h_Faden_zustand_t]
  gabbro_auto [alle_anhalten_loop_1_body, alle_anhalten_loop_1_inv, wellFormed, h_Faden_zustand_t, hall] using shapeOf

/-- **The duty of `alle_anhalten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def alle_anhalten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s alle_anhalten_pre = some (.bool true))
    -- the rule of loop `alle_anhalten#1`
    (l_alle_anhalten_loop_1 : LoopRule ρ "alle_anhalten#1" wellFormed alle_anhalten_loop_1_inv),
    ∃ s', finalState (exec ρ alle_anhalten_body s) = some s'
        ∧ alle_anhalten_post s s' (finalValue (exec ρ alle_anhalten_body s))

theorem alle_anhalten_meets : alle_anhalten_meets_statement := by
  unfold alle_anhalten_meets_statement
  intro ρ s hwf hpre l_alle_anhalten_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [alle_anhalten_pre]
  gabbro_auto [alle_anhalten_body, alle_anhalten_pre, alle_anhalten_post, wellFormed, alle_anhalten_loop_1_inv, hall] using shapeOf

/-! ### `halt_verteiler` -/

/-- **The duty of `halt_verteiler`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def halt_verteiler_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s halt_verteiler_pre = some (.bool true))
    -- the contract of `alle_anhalten`
    (c_alle_anhalten : Contract ρ "alle_anhalten" alle_anhalten_requires alle_anhalten_post)
    -- the frame of `alle_anhalten`
    (fr_alle_anhalten : Frame ρ "alle_anhalten" alle_anhalten_writes),
    ∃ s', finalState (exec ρ halt_verteiler_body s) = some s'
        ∧ halt_verteiler_post s s' (finalValue (exec ρ halt_verteiler_body s))

theorem halt_verteiler_meets : halt_verteiler_meets_statement := by
  unfold halt_verteiler_meets_statement
  intro ρ s hwf hpre c_alle_anhalten fr_alle_anhalten
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [halt_verteiler_pre]
  gabbro_auto [halt_verteiler_body, halt_verteiler_pre, halt_verteiler_post, wellFormed, alle_anhalten_pre, alle_anhalten_requires, alle_anhalten_post, alle_anhalten_writes, Frame_read _ _ _ fr_alle_anhalten, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "alle_anhalten" alle_anhalten_body
  ∧ Frame ρ "alle_anhalten" alle_anhalten_writes
  ∧ RunsLoopIn ρ "alle_anhalten#1" alle_anhalten_loop_1_body "t" 0 128
  ∧ Runs ρ "halt_verteiler" halt_verteiler_body
  ∧ Frame ρ "halt_verteiler" halt_verteiler_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_alle_anhalten_loop_1 : alle_anhalten_loop_1_keeps_statement)
    (d_alle_anhalten : alle_anhalten_meets_statement)
    (d_halt_verteiler : halt_verteiler_meets_statement) :
    LoopRule ρ "alle_anhalten#1" wellFormed alle_anhalten_loop_1_inv
    ∧ Contract ρ "alle_anhalten" alle_anhalten_requires alle_anhalten_post
    ∧ Contract ρ "halt_verteiler" halt_verteiler_requires halt_verteiler_post := by
  obtain ⟨r_alle_anhalten, fr_alle_anhalten, rl_alle_anhalten_loop_1, r_halt_verteiler, fr_halt_verteiler⟩ := hp
  have l_alle_anhalten_loop_1 : LoopRule ρ "alle_anhalten#1" wellFormed alle_anhalten_loop_1_inv :=
    looprule_of_body_in ρ "alle_anhalten#1" wellFormed alle_anhalten_loop_1_inv alle_anhalten_loop_1_body "t" 0 128 rl_alle_anhalten_loop_1
      (fun t k hlo hhi hw hi => d_alle_anhalten_loop_1 ρ t k hlo hhi hw hi)
  have c_alle_anhalten : Contract ρ "alle_anhalten" alle_anhalten_requires alle_anhalten_post :=
    contract_of_duty ρ "alle_anhalten" alle_anhalten_body alle_anhalten_requires alle_anhalten_post r_alle_anhalten
      (fun t ht => d_alle_anhalten ρ t ht.1 ht.2 l_alle_anhalten_loop_1)
  have c_halt_verteiler : Contract ρ "halt_verteiler" halt_verteiler_requires halt_verteiler_post :=
    contract_of_duty ρ "halt_verteiler" halt_verteiler_body halt_verteiler_requires halt_verteiler_post r_halt_verteiler
      (fun t ht => d_halt_verteiler ρ t ht.1 ht.2 c_alle_anhalten fr_alle_anhalten)
  exact ⟨l_alle_anhalten_loop_1, c_alle_anhalten, c_halt_verteiler⟩

end GabbroDuty.Duty57Faedenhalt
