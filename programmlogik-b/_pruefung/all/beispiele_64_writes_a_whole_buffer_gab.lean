/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/64-writes-a-whole-buffer.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty64WritesAWholeBuffer

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  main :: write requires #1  --  carried by `main_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "PUFFER" _ "elem" => some (.intIn 0 255)
  | .global "LAENGE" => some (.intIn 0 64)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `write` -- a foreign body: its contract is an assumption. -/
def write_pre : Expr :=
  (.bin .and (.hasShape "fd" (.intIn (-2147483648) 2147483647)) (.bin .and (.hasShape "n" (.intIn 0 18446744073709551615)) (.bin .le (.name "n") (.lit (.int 64)))))

def write_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ (-9223372036854775808) ≤ x ∧ x ≤ 9223372036854775807)

def write_writes : List String := ["ausgabe"]

def write_requires (t : State) : Prop := wellFormed t ∧ eval t write_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "write" write_requires write_post
  ∧ Frame ρ "write" write_writes

/-! ## The routines: body and contract -/

/-! ### `main` -/

def main_body : List Stmt :=
  [(.assign "PUFFER" (.lit (.int 0)) "elem" (.lit (.int 80))), (.assign "PUFFER" (.lit (.int 1)) "elem" (.lit (.int 117))), (.assign "PUFFER" (.lit (.int 2)) "elem" (.lit (.int 102))), (.assign "PUFFER" (.lit (.int 3)) "elem" (.lit (.int 102))), (.assign "PUFFER" (.lit (.int 4)) "elem" (.lit (.int 101))), (.assign "PUFFER" (.lit (.int 5)) "elem" (.lit (.int 114))), (.assign "PUFFER" (.lit (.int 6)) "elem" (.lit (.int 10))), (.assignGlobal "LAENGE" (.lit (.int 7))), (.call "write" ["fd", "p", "n"] [(.lit (.int 1)), (.global "PUFFER"), (.global "LAENGE")] (.bin .and (.hasShape "fd" (.intIn (-2147483648) 2147483647)) (.bin .and (.hasShape "n" (.intIn 0 18446744073709551615)) (.bin .le (.name "n") (.lit (.int 64)))))), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def main_pre : Expr :=
  (.lit (.bool true))

def main_writes : List String := ["PUFFER", "LAENGE", "ausgabe"]

/-- What a caller of `main` has to bring: a well-typed world and the precondition. -/
def main_requires (t : State) : Prop := wellFormed t ∧ eval t main_pre = some (.bool true)

/-- What `main` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def main_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 1)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `main` -/

/-- **The duty of `main`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def main_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s main_pre = some (.bool true))
    -- the contract of `write`
    (c_write : Contract ρ "write" write_requires write_post)
    -- the frame of `write`
    (fr_write : Frame ρ "write" write_writes),
    ∃ s', finalState (exec ρ main_body s) = some s'
        ∧ main_post s s' (finalValue (exec ρ main_body s))

theorem main_meets : main_meets_statement := by
  unfold main_meets_statement
  intro ρ s hwf hpre c_write fr_write
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [main_pre]
  gabbro_auto [main_body, main_pre, main_post, wellFormed, write_pre, write_requires, write_post, write_writes, Frame_read _ _ _ fr_write, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "main" main_body
  ∧ Frame ρ "main" main_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_main : main_meets_statement) :
    Contract ρ "main" main_requires main_post := by
  obtain ⟨r_main, fr_main⟩ := hp
  obtain ⟨c_write, fr_write⟩ := ha
  have c_main : Contract ρ "main" main_requires main_post :=
    contract_of_duty ρ "main" main_body main_requires main_post r_main
      (fun t ht => d_main ρ t ht.1 ht.2 c_write fr_write)
  exact c_main

end GabbroDuty.Duty64WritesAWholeBuffer
