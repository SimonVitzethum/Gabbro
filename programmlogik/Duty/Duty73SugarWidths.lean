/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/73-sugar-widths.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty73SugarWidths

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

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `dreizehn` -/

def dreizehn_body : List Stmt :=
  [(.ret (some (.name "x")))]

/-- The precondition: the declared shapes and the `requires`. -/
def dreizehn_pre : Expr :=
  (.hasShape "x" (.intIn 0 8191))

def dreizehn_writes : List String := []

/-- What a caller of `dreizehn` has to bring: a well-typed world and the precondition. -/
def dreizehn_requires (t : State) : Prop := wellFormed t ∧ eval t dreizehn_pre = some (.bool true)

/-- What `dreizehn` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def dreizehn_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `eins` -/

def eins_body : List Stmt :=
  [(.ret (some (.name "x")))]

/-- The precondition: the declared shapes and the `requires`. -/
def eins_pre : Expr :=
  (.hasShape "x" (.intIn 0 1))

def eins_writes : List String := []

/-- What a caller of `eins` has to bring: a well-typed world and the precondition. -/
def eins_requires (t : State) : Prop := wellFormed t ∧ eval t eins_pre = some (.bool true)

/-- What `eins` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def eins_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 255)

/-! ### `grenze` -/

-- REFUSED  grenze  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format` -- name it through a parameter of that type, so the place has a declaration to take its shape from
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def grenze_pre : Expr :=
  (.lit (.bool true))

def grenze_writes : List String := []

/-- What a caller of `grenze` has to bring: a well-typed world and the precondition. -/
def grenze_requires (t : State) : Prop := wellFormed t ∧ eval t grenze_pre = some (.bool true)

/-- What `grenze` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def grenze_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `minus` -/

def minus_body : List Stmt :=
  [(.ret (some (.name "x")))]

/-- The precondition: the declared shapes and the `requires`. -/
def minus_pre : Expr :=
  (.hasShape "x" (.intIn (-68719476736) 68719476735))

def minus_writes : List String := []

/-- What a caller of `minus` has to bring: a well-typed world and the precondition. -/
def minus_requires (t : State) : Prop := wellFormed t ∧ eval t minus_pre = some (.bool true)

/-- What `minus` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def minus_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ (-9223372036854775808) ≤ x ∧ x ≤ 9223372036854775807)

/-! ### `voll` -/

def voll_body : List Stmt :=
  [(.ret (some (.name "x")))]

/-- The precondition: the declared shapes and the `requires`. -/
def voll_pre : Expr :=
  (.hasShape "x" (.intIn 0 18446744073709551615))

def voll_writes : List String := []

/-- What a caller of `voll` has to bring: a well-typed world and the precondition. -/
def voll_requires (t : State) : Prop := wellFormed t ∧ eval t voll_pre = some (.bool true)

/-- What `voll` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def voll_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `wandle` -/

-- REFUSED  wandle  (call-not-compositional): a call to a routine this unit does not declare
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def wandle_pre : Expr :=
  (.hasShape "a" (.intIn 0 100))

def wandle_writes : List String := []

/-- What a caller of `wandle` has to bring: a well-typed world and the precondition. -/
def wandle_requires (t : State) : Prop := wellFormed t ∧ eval t wandle_pre = some (.bool true)

/-- What `wandle` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def wandle_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 8191)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `dreizehn` -/

/-- **The duty of `dreizehn`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def dreizehn_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s dreizehn_pre = some (.bool true)),
    ∃ s', finalState (exec ρ dreizehn_body s) = some s'
        ∧ dreizehn_post s s' (finalValue (exec ρ dreizehn_body s))

theorem dreizehn_meets : dreizehn_meets_statement := by
  unfold dreizehn_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [dreizehn_pre, e_x]
  gabbro_auto2 [dreizehn_body, dreizehn_pre, dreizehn_post, wellFormed, e_x, hall] [dreizehn_body, dreizehn_pre, dreizehn_post, wellFormed, e_x] using shapeOf

/-! ### `eins` -/

/-- **The duty of `eins`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def eins_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s eins_pre = some (.bool true)),
    ∃ s', finalState (exec ρ eins_body s) = some s'
        ∧ eins_post s s' (finalValue (exec ρ eins_body s))

theorem eins_meets : eins_meets_statement := by
  unfold eins_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [eins_pre, e_x]
  gabbro_auto2 [eins_body, eins_pre, eins_post, wellFormed, e_x, hall] [eins_body, eins_pre, eins_post, wellFormed, e_x] using shapeOf

/-! ### `minus` -/

/-- **The duty of `minus`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def minus_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s minus_pre = some (.bool true)),
    ∃ s', finalState (exec ρ minus_body s) = some s'
        ∧ minus_post s s' (finalValue (exec ρ minus_body s))

theorem minus_meets : minus_meets_statement := by
  unfold minus_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [minus_pre, e_x]
  gabbro_auto2 [minus_body, minus_pre, minus_post, wellFormed, e_x, hall] [minus_body, minus_pre, minus_post, wellFormed, e_x] using shapeOf

/-! ### `voll` -/

/-- **The duty of `voll`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def voll_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s voll_pre = some (.bool true)),
    ∃ s', finalState (exec ρ voll_body s) = some s'
        ∧ voll_post s s' (finalValue (exec ρ voll_body s))

theorem voll_meets : voll_meets_statement := by
  unfold voll_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [voll_pre, e_x]
  gabbro_auto2 [voll_body, voll_pre, voll_post, wellFormed, e_x, hall] [voll_body, voll_pre, voll_post, wellFormed, e_x] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "dreizehn" dreizehn_body
  ∧ Frame ρ "dreizehn" dreizehn_writes
  ∧ Runs ρ "eins" eins_body
  ∧ Frame ρ "eins" eins_writes
  ∧ Runs ρ "minus" minus_body
  ∧ Frame ρ "minus" minus_writes
  ∧ Runs ρ "voll" voll_body
  ∧ Frame ρ "voll" voll_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_dreizehn : dreizehn_meets_statement)
    (d_eins : eins_meets_statement)
    (d_minus : minus_meets_statement)
    (d_voll : voll_meets_statement) :
    Contract ρ "dreizehn" dreizehn_requires dreizehn_post
    ∧ Contract ρ "eins" eins_requires eins_post
    ∧ Contract ρ "minus" minus_requires minus_post
    ∧ Contract ρ "voll" voll_requires voll_post := by
  obtain ⟨r_dreizehn, fr_dreizehn, r_eins, fr_eins, r_minus, fr_minus, r_voll, fr_voll⟩ := hp
  have c_dreizehn : Contract ρ "dreizehn" dreizehn_requires dreizehn_post :=
    contract_of_duty ρ "dreizehn" dreizehn_body dreizehn_requires dreizehn_post r_dreizehn
      (fun t ht => d_dreizehn ρ t ht.1 ht.2)
  have c_eins : Contract ρ "eins" eins_requires eins_post :=
    contract_of_duty ρ "eins" eins_body eins_requires eins_post r_eins
      (fun t ht => d_eins ρ t ht.1 ht.2)
  have c_minus : Contract ρ "minus" minus_requires minus_post :=
    contract_of_duty ρ "minus" minus_body minus_requires minus_post r_minus
      (fun t ht => d_minus ρ t ht.1 ht.2)
  have c_voll : Contract ρ "voll" voll_requires voll_post :=
    contract_of_duty ρ "voll" voll_body voll_requires voll_post r_voll
      (fun t ht => d_voll ρ t ht.1 ht.2)
  exact ⟨c_dreizehn, c_eins, c_minus, c_voll⟩

end GabbroDuty.Duty73SugarWidths
