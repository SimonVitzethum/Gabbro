/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-erzeugernamen-frei.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeErzeugernamenFrei

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Baum_knoten" "fuellung" => some (.intIn 0 4294967295)
  | .field "Rahmen" "setz_b" => some .bool
  | .field "Rahmen" "marke" => some .bool
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

/-! ### `gueltig` -/

def gueltig_body : List Stmt :=
  [(.ret (some (.bin .gt (.name "x") (.lit (.int 0)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def gueltig_pre : Expr :=
  (.hasShape "x" (.intIn 0 4294967295))

def gueltig_writes : List String := []

/-- What a caller of `gueltig` has to bring: a well-typed world and the precondition. -/
def gueltig_requires (t : State) : Prop := wellFormed t ∧ eval t gueltig_pre = some (.bool true)

/-- What `gueltig` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gueltig_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `lies` -/

def lies_body : List Stmt :=
  [(.ret (some (.fieldOf "Rahmen" "setz_b")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lies_pre : Expr :=
  (.lit (.bool true))

def lies_writes : List String := []

/-- What a caller of `lies` has to bring: a well-typed world and the precondition. -/
def lies_requires (t : State) : Prop := wellFormed t ∧ eval t lies_pre = some (.bool true)

/-- What `lies` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lies_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `gueltig` -/

/-- **The duty of `gueltig`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def gueltig_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s gueltig_pre = some (.bool true)),
    ∃ s', finalState (exec ρ gueltig_body s) = some s'
        ∧ gueltig_post s s' (finalValue (exec ρ gueltig_body s))

theorem gueltig_meets : gueltig_meets_statement := by
  unfold gueltig_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [gueltig_pre, e_x]
  gabbro_auto [gueltig_body, gueltig_pre, gueltig_post, wellFormed, e_x, hall] using shapeOf

/-! ### `lies` -/

/-- **The duty of `lies`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def lies_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s lies_pre = some (.bool true)),
    ∃ s', finalState (exec ρ lies_body s) = some s'
        ∧ lies_post s s' (finalValue (exec ρ lies_body s))

theorem lies_meets : lies_meets_statement := by
  unfold lies_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Rahmen_setz_b, h_Rahmen_setz_b⟩ := WF_bool shapeOf s.world (.field "Rahmen" "setz_b") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lies_pre, h_Rahmen_setz_b]
  gabbro_auto [lies_body, lies_pre, lies_post, wellFormed, h_Rahmen_setz_b, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "gueltig" gueltig_body
  ∧ Frame ρ "gueltig" gueltig_writes
  ∧ Runs ρ "lies" lies_body
  ∧ Frame ρ "lies" lies_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_gueltig : gueltig_meets_statement)
    (d_lies : lies_meets_statement) :
    Contract ρ "gueltig" gueltig_requires gueltig_post
    ∧ Contract ρ "lies" lies_requires lies_post := by
  obtain ⟨r_gueltig, fr_gueltig, r_lies, fr_lies⟩ := hp
  have c_gueltig : Contract ρ "gueltig" gueltig_requires gueltig_post :=
    contract_of_duty ρ "gueltig" gueltig_body gueltig_requires gueltig_post r_gueltig
      (fun t ht => d_gueltig ρ t ht.1 ht.2)
  have c_lies : Contract ρ "lies" lies_requires lies_post :=
    contract_of_duty ρ "lies" lies_body lies_requires lies_post r_lies
      (fun t ht => d_lies ρ t ht.1 ht.2)
  exact ⟨c_gueltig, c_lies⟩

end GabbroDuty.DutyProbeErzeugernamenFrei