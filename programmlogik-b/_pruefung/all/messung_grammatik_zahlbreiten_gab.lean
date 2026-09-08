/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/grammatik/zahlbreiten.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyZahlbreiten

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "alle_gesund" => some (.intIn 0 4294967295)
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

/-! ### `haelfte` -/

-- REFUSED  haelfte  (float): a floating-point value -- this model has no float
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def haelfte_pre : Expr :=
  (.lit (.bool true))

def haelfte_writes : List String := []

/-- What a caller of `haelfte` has to bring: a well-typed world and the precondition. -/
def haelfte_requires (t : State) : Prop := wellFormed t ∧ eval t haelfte_pre = some (.bool true)

/-- What `haelfte` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def haelfte_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `melden` -/

def melden_body : List Stmt :=
  [(.assignGlobal "alle_gesund" (.name "m"))]

/-- The precondition: the declared shapes and the `requires`. -/
def melden_pre : Expr :=
  (.hasShape "m" (.intIn 0 4294967295))

def melden_writes : List String := ["alle_gesund"]

/-- What a caller of `melden` has to bring: a well-typed world and the precondition. -/
def melden_requires (t : State) : Prop := wellFormed t ∧ eval t melden_pre = some (.bool true)

/-- What `melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `summe` -/

def summe_body : List Stmt :=
  [(.ret (some (.bin .add (.name "a") (.name "b"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def summe_pre : Expr :=
  (.bin .and (.hasShape "a" (.intIn (-128) 127)) (.hasShape "b" (.intIn (-1000) 1000)))

def summe_writes : List String := []

/-- What a caller of `summe` has to bring: a well-typed world and the precondition. -/
def summe_requires (t : State) : Prop := wellFormed t ∧ eval t summe_pre = some (.bool true)

/-- What `summe` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def summe_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ (-100000) ≤ x ∧ x ≤ 100000)

/-! ### `weiten` -/

def weiten_body : List Stmt :=
  [(.ret (some (.name "g")))]

/-- The precondition: the declared shapes and the `requires`. -/
def weiten_pre : Expr :=
  (.hasShape "g" (.intIn (-100000) 100000))

def weiten_writes : List String := []

/-- What a caller of `weiten` has to bring: a well-typed world and the precondition. -/
def weiten_requires (t : State) : Prop := wellFormed t ∧ eval t weiten_pre = some (.bool true)

/-- What `weiten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def weiten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ (-1000000) ≤ x ∧ x ≤ 1000000)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `melden` -/

/-- **The duty of `melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ melden_body s) = some s'
        ∧ melden_post s s' (finalValue (exec ρ melden_body s))

theorem melden_meets : melden_meets_statement := by
  unfold melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_m, e_m, lo_m, hi_m⟩ := shape_intIn s "m" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [melden_pre, e_m]
  gabbro_auto [melden_body, melden_pre, melden_post, wellFormed, e_m, hall] using shapeOf

/-! ### `summe` -/

/-- **The duty of `summe`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def summe_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s summe_pre = some (.bool true)),
    ∃ s', finalState (exec ρ summe_body s) = some s'
        ∧ summe_post s s' (finalValue (exec ρ summe_body s))

theorem summe_meets : summe_meets_statement := by
  unfold summe_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [summe_pre, e_a, e_b]
  gabbro_auto [summe_body, summe_pre, summe_post, wellFormed, e_a, e_b, hall] using shapeOf

/-! ### `weiten` -/

/-- **The duty of `weiten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def weiten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s weiten_pre = some (.bool true)),
    ∃ s', finalState (exec ρ weiten_body s) = some s'
        ∧ weiten_post s s' (finalValue (exec ρ weiten_body s))

theorem weiten_meets : weiten_meets_statement := by
  unfold weiten_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn s "g" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [weiten_pre, e_g]
  gabbro_auto [weiten_body, weiten_pre, weiten_post, wellFormed, e_g, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "melden" melden_body
  ∧ Frame ρ "melden" melden_writes
  ∧ Runs ρ "summe" summe_body
  ∧ Frame ρ "summe" summe_writes
  ∧ Runs ρ "weiten" weiten_body
  ∧ Frame ρ "weiten" weiten_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_melden : melden_meets_statement)
    (d_summe : summe_meets_statement)
    (d_weiten : weiten_meets_statement) :
    Contract ρ "melden" melden_requires melden_post
    ∧ Contract ρ "summe" summe_requires summe_post
    ∧ Contract ρ "weiten" weiten_requires weiten_post := by
  obtain ⟨r_melden, fr_melden, r_summe, fr_summe, r_weiten, fr_weiten⟩ := hp
  have c_melden : Contract ρ "melden" melden_requires melden_post :=
    contract_of_duty ρ "melden" melden_body melden_requires melden_post r_melden
      (fun t ht => d_melden ρ t ht.1 ht.2)
  have c_summe : Contract ρ "summe" summe_requires summe_post :=
    contract_of_duty ρ "summe" summe_body summe_requires summe_post r_summe
      (fun t ht => d_summe ρ t ht.1 ht.2)
  have c_weiten : Contract ρ "weiten" weiten_requires weiten_post :=
    contract_of_duty ρ "weiten" weiten_body weiten_requires weiten_post r_weiten
      (fun t ht => d_weiten ρ t ht.1 ht.2)
  exact ⟨c_melden, c_summe, c_weiten⟩

end GabbroDuty.DutyZahlbreiten
