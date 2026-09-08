/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/11a-divergenz-endet.gab  total 0  goals 0  refused 0
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
set_option maxHeartbeats 6000000

open Gabbro.Body

namespace GabbroDuty.Duty11aDivergenzEndet

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

/-- `abbruch` -- a foreign body: its contract is an assumption. -/
def abbruch_pre : Expr :=
  (.lit (.bool true))

def abbruch_post (t t' : State) (r : Option Value) : Prop :=
  False

def abbruch_writes : List String := []

def abbruch_requires (t : State) : Prop := wellFormed t ∧ eval t abbruch_pre = some (.bool true)

/-- `hol` -- a foreign body: its contract is an assumption. -/
def hol_pre : Expr :=
  (.lit (.bool true))

def hol_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x)) ∨ ∃ e, r = some (.reason e))

def hol_writes : List String := []

def hol_requires (t : State) : Prop := wellFormed t ∧ eval t hol_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "abbruch" abbruch_requires abbruch_post
  ∧ Frame ρ "abbruch" abbruch_writes
  ∧ Contract ρ "hol" hol_requires hol_post
  ∧ Frame ρ "hol" hol_writes

/-! ## The routines: body and contract -/

/-! ### `f` -/

def f_body : List Stmt :=
  [(.bindCallElse "x" "hol" [] [] (.lit (.bool true)) "e" [(.call "abbruch" [] [] (.lit (.bool true)))]), (.ret (some (.name "x")))]

/-- The precondition: the declared shapes and the `requires`. -/
def f_pre : Expr :=
  (.lit (.bool true))

def f_writes : List String := []

/-- What a caller of `f` has to bring: a well-typed world and the precondition. -/
def f_requires (t : State) : Prop := wellFormed t ∧ eval t f_pre = some (.bool true)

/-- What `f` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def f_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `f` -/

/-- **The duty of `f`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def f_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s f_pre = some (.bool true))
    -- the contract of `abbruch`
    (c_abbruch : Contract ρ "abbruch" abbruch_requires abbruch_post)
    -- the frame of `abbruch`
    (fr_abbruch : Frame ρ "abbruch" abbruch_writes)
    -- the contract of `hol`
    (c_hol : Contract ρ "hol" hol_requires hol_post)
    -- the frame of `hol`
    (fr_hol : Frame ρ "hol" hol_writes),
    ∃ s', finalState (exec ρ f_body s) = some s'
        ∧ f_post s s' (finalValue (exec ρ f_body s))

theorem f_meets : f_meets_statement := by
  unfold f_meets_statement
  intro ρ s hwf hpre c_abbruch fr_abbruch c_hol fr_hol
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [f_pre]
  gabbro_try 300 (gabbro_simp [f_body, f_pre, f_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, hol_pre, hol_requires, hol_post, hol_writes, Frame_read _ _ _ fr_hol, hall])
  gabbro_try 300 (all_goals (try gabbro_cases 4 [f_body, f_pre, f_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, hol_pre, hol_requires, hol_post, hol_writes, Frame_read _ _ _ fr_hol, hall]))
  gabbro_try 300 (all_goals (try gabbro_calls shapeOf [f_body, f_pre, f_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, hol_pre, hol_requires, hol_post, hol_writes, Frame_read _ _ _ fr_hol, hall]))
  gabbro_try 300 (all_goals (try gabbro_simp_hyps [f_body, f_pre, f_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, hol_pre, hol_requires, hol_post, hol_writes, Frame_read _ _ _ fr_hol, hall]))
  trace_state
  gabbro_calls shapeOf [f_body, f_pre, f_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, hol_pre, hol_requires, hol_post, hol_writes, Frame_read _ _ _ fr_hol, hall]
  trace_state
  all_goals sorry

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "f" f_body
  ∧ Frame ρ "f" f_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_f : f_meets_statement) :
    Contract ρ "f" f_requires f_post := by
  obtain ⟨r_f, fr_f⟩ := hp
  obtain ⟨c_abbruch, fr_abbruch, c_hol, fr_hol⟩ := ha
  have c_f : Contract ρ "f" f_requires f_post :=
    contract_of_duty ρ "f" f_body f_requires f_post r_f
      (fun t ht => d_f ρ t ht.1 ht.2 c_abbruch fr_abbruch c_hol fr_hol)
  exact c_f

end GabbroDuty.Duty11aDivergenzEndet
