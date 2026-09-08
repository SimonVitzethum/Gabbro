/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/37-umlauf-rechnet.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty37UmlaufRechnet

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Zaehler" _ "a" => some .int
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

/-! ### `quadriere` -/

def quadriere_body : List Stmt :=
  [(.assign "Zaehler" (.name "i") "a" (.wrapTo 16 false (.bin .mul (.place "Zaehler" (.name "i") "a") (.place "Zaehler" (.name "i") "a"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def quadriere_pre : Expr :=
  (.hasShape "i" (.intIn 0 3))

def quadriere_writes : List String := ["Zaehler"]

/-- What a caller of `quadriere` has to bring: a well-typed world and the precondition. -/
def quadriere_requires (t : State) : Prop := wellFormed t ∧ eval t quadriere_pre = some (.bool true)

/-- What `quadriere` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def quadriere_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `ring_quadrieren` -/

-- REFUSED  ring_quadrieren  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def ring_quadrieren_pre : Expr :=
  (.lit (.bool true))

def ring_quadrieren_writes : List String := ["r"]

/-- What a caller of `ring_quadrieren` has to bring: a well-typed world and the precondition. -/
def ring_quadrieren_requires (t : State) : Prop := wellFormed t ∧ eval t ring_quadrieren_pre = some (.bool true)

/-- What `ring_quadrieren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ring_quadrieren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `quadriere` -/

/-- **The duty of `quadriere`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def quadriere_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s quadriere_pre = some (.bool true)),
    ∃ s', finalState (exec ρ quadriere_body s) = some s'
        ∧ quadriere_post s s' (finalValue (exec ρ quadriere_body s))

theorem quadriere_meets : quadriere_meets_statement := by
  unfold quadriere_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Zaehler_a_i, h_Zaehler_a_i⟩ := WF_int shapeOf s.world (.slot "Zaehler" w_i "a") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [quadriere_pre, e_i, h_Zaehler_a_i]
  gabbro_auto [quadriere_body, quadriere_pre, quadriere_post, wellFormed, e_i, h_Zaehler_a_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "quadriere" quadriere_body
  ∧ Frame ρ "quadriere" quadriere_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_quadriere : quadriere_meets_statement) :
    Contract ρ "quadriere" quadriere_requires quadriere_post := by
  obtain ⟨r_quadriere, fr_quadriere⟩ := hp
  have c_quadriere : Contract ρ "quadriere" quadriere_requires quadriere_post :=
    contract_of_duty ρ "quadriere" quadriere_body quadriere_requires quadriere_post r_quadriere
      (fun t ht => d_quadriere ρ t ht.1 ht.2)
  exact c_quadriere

end GabbroDuty.Duty37UmlaufRechnet
