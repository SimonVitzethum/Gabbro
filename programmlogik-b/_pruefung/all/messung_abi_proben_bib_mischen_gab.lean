/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/abi-proben/bib-mischen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyBibMischen

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

/-! ### `mische` -/

def mische_body : List Stmt :=
  [(.bindCall "d" "verdopple" ["x"] [(.name "a")] (.hasShape "x" (.intIn 0 65535))), (.ret (some (.bin .add (.name "d") (.name "b"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def mische_pre : Expr :=
  (.bin .and (.hasShape "a" (.intIn 0 65535)) (.hasShape "b" (.intIn 0 65535)))

def mische_writes : List String := []

/-- What a caller of `mische` has to bring: a well-typed world and the precondition. -/
def mische_requires (t : State) : Prop := wellFormed t ∧ eval t mische_pre = some (.bool true)

/-- What `mische` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def mische_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 196605)

/-! ### `verdopple` -/

def verdopple_body : List Stmt :=
  [(.ret (some (.bin .add (.name "x") (.name "x"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def verdopple_pre : Expr :=
  (.hasShape "x" (.intIn 0 65535))

def verdopple_writes : List String := []

/-- What a caller of `verdopple` has to bring: a well-typed world and the precondition. -/
def verdopple_requires (t : State) : Prop := wellFormed t ∧ eval t verdopple_pre = some (.bool true)

/-- What `verdopple` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def verdopple_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 131070)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `mische` -/

/-- **The duty of `mische`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def mische_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s mische_pre = some (.bool true))
    -- the contract of `verdopple`
    (c_verdopple : Contract ρ "verdopple" verdopple_requires verdopple_post)
    -- the frame of `verdopple`
    (fr_verdopple : Frame ρ "verdopple" verdopple_writes),
    ∃ s', finalState (exec ρ mische_body s) = some s'
        ∧ mische_post s s' (finalValue (exec ρ mische_body s))

theorem mische_meets : mische_meets_statement := by
  unfold mische_meets_statement
  intro ρ s hwf hpre c_verdopple fr_verdopple
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [mische_pre, e_a, e_b]
  gabbro_auto [mische_body, mische_pre, mische_post, wellFormed, verdopple_pre, verdopple_requires, verdopple_post, verdopple_writes, Frame_read _ _ _ fr_verdopple, e_a, e_b, hall] using shapeOf

/-! ### `verdopple` -/

/-- **The duty of `verdopple`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def verdopple_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s verdopple_pre = some (.bool true)),
    ∃ s', finalState (exec ρ verdopple_body s) = some s'
        ∧ verdopple_post s s' (finalValue (exec ρ verdopple_body s))

theorem verdopple_meets : verdopple_meets_statement := by
  unfold verdopple_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [verdopple_pre, e_x]
  gabbro_auto [verdopple_body, verdopple_pre, verdopple_post, wellFormed, e_x, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "mische" mische_body
  ∧ Frame ρ "mische" mische_writes
  ∧ Runs ρ "verdopple" verdopple_body
  ∧ Frame ρ "verdopple" verdopple_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_verdopple : verdopple_meets_statement)
    (d_mische : mische_meets_statement) :
    Contract ρ "verdopple" verdopple_requires verdopple_post
    ∧ Contract ρ "mische" mische_requires mische_post := by
  obtain ⟨r_mische, fr_mische, r_verdopple, fr_verdopple⟩ := hp
  have c_verdopple : Contract ρ "verdopple" verdopple_requires verdopple_post :=
    contract_of_duty ρ "verdopple" verdopple_body verdopple_requires verdopple_post r_verdopple
      (fun t ht => d_verdopple ρ t ht.1 ht.2)
  have c_mische : Contract ρ "mische" mische_requires mische_post :=
    contract_of_duty ρ "mische" mische_body mische_requires mische_post r_mische
      (fun t ht => d_mische ρ t ht.1 ht.2 c_verdopple fr_verdopple)
  exact ⟨c_verdopple, c_mische⟩

end GabbroDuty.DutyBibMischen
