/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F08.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.DutyF08

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  toeten :: aufloesen requires #1  --  carried by `toeten_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Laufliste" _ "belegt" => some .bool
  | .slot "Laufliste" _ "kern" => some (.intIn 0 63)
  | .slot "Laufliste" _ "prio" => some (.intIn 0 255)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `aufloesen` -- a foreign body: its contract is an assumption. -/
def aufloesen_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))

def aufloesen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (r = some .absent ∨ ∃ x, r = some (.present x))

def aufloesen_writes : List String := []

def aufloesen_requires (t : State) : Prop := wellFormed t ∧ eval t aufloesen_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "aufloesen" aufloesen_requires aufloesen_post
  ∧ Frame ρ "aufloesen" aufloesen_writes

/-! ## The routines: body and contract -/

/-! ### `beenden` -/

def beenden_body : List Stmt :=
  [(.assign "Laufliste" (.name "k") "belegt" (.lit (.bool false))), (.ret (some (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def beenden_pre : Expr :=
  (.bin .and (.hasShape "k" (.intIn 0 1023)) (.lit (.bool true)))

def beenden_writes : List String := ["Laufliste"]

/-- What a caller of `beenden` has to bring: a well-typed world and the precondition. -/
def beenden_requires (t : State) : Prop := wellFormed t ∧ eval t beenden_pre = some (.bool true)

/-- What `beenden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def beenden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `toeten` -/

def toeten_body : List Stmt :=
  [(.locked "SCHEDS" [(.bindCall "#m1" "aufloesen" ["l", "t"] [(.name "l"), (.name "t")] (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))), (.onOption (.name "#m1") "i" [(.assign "Laufliste" (.name "i") "belegt" (.lit (.bool false))), (.ret (some (.lit (.bool true))))] [(.ret (some (.lit (.bool false))))])]), (.ret (some (.lit (.bool false))))]

/-- The precondition: the declared shapes and the `requires`. -/
def toeten_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.hasShape "k" (.intIn 0 1023)))

def toeten_writes : List String := ["Laufliste"]

/-- What a caller of `toeten` has to bring: a well-typed world and the precondition. -/
def toeten_requires (t : State) : Prop := wellFormed t ∧ eval t toeten_pre = some (.bool true)

/-- What `toeten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def toeten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `beenden` -/

/-- **The duty of `beenden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def beenden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s beenden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ beenden_body s) = some s'
        ∧ beenden_post s s' (finalValue (exec ρ beenden_body s))

theorem beenden_meets : beenden_meets_statement := by
  unfold beenden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn s "k" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [beenden_pre, e_k]
  gabbro_auto [beenden_body, beenden_pre, beenden_post, wellFormed, e_k, hall] using shapeOf

/-! ### `toeten` -/

/-- **The duty of `toeten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def toeten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s toeten_pre = some (.bool true))
    -- the contract of `aufloesen`
    (c_aufloesen : Contract ρ "aufloesen" aufloesen_requires aufloesen_post)
    -- the frame of `aufloesen`
    (fr_aufloesen : Frame ρ "aufloesen" aufloesen_writes),
    ∃ s', finalState (exec ρ toeten_body s) = some s'
        ∧ toeten_post s s' (finalValue (exec ρ toeten_body s))

theorem toeten_meets : toeten_meets_statement := by
  unfold toeten_meets_statement
  intro ρ s hwf hpre c_aufloesen fr_aufloesen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn s "k" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [toeten_pre, e_t, e_k]
  gabbro_auto [toeten_body, toeten_pre, toeten_post, wellFormed, aufloesen_pre, aufloesen_requires, aufloesen_post, aufloesen_writes, Frame_read _ _ _ fr_aufloesen, e_t, e_k, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "beenden" beenden_body
  ∧ Frame ρ "beenden" beenden_writes
  ∧ Runs ρ "toeten" toeten_body
  ∧ Frame ρ "toeten" toeten_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_beenden : beenden_meets_statement)
    (d_toeten : toeten_meets_statement) :
    Contract ρ "beenden" beenden_requires beenden_post
    ∧ Contract ρ "toeten" toeten_requires toeten_post := by
  obtain ⟨r_beenden, fr_beenden, r_toeten, fr_toeten⟩ := hp
  obtain ⟨c_aufloesen, fr_aufloesen⟩ := ha
  have c_beenden : Contract ρ "beenden" beenden_requires beenden_post :=
    contract_of_duty ρ "beenden" beenden_body beenden_requires beenden_post r_beenden
      (fun t ht => d_beenden ρ t ht.1 ht.2)
  have c_toeten : Contract ρ "toeten" toeten_requires toeten_post :=
    contract_of_duty ρ "toeten" toeten_body toeten_requires toeten_post r_toeten
      (fun t ht => d_toeten ρ t ht.1 ht.2 c_aufloesen fr_aufloesen)
  exact ⟨c_beenden, c_toeten⟩

end GabbroDuty.DutyF08
