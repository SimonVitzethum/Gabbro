/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/44-register-einmal-lesen.gab  total 1  goals 0  refused 1
        @assumed 1  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty44RegisterEinmalLesen

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  device-promise (1): ASSUMED -- a promise at hardware Gabbro does not see: an ASSUMPTION
    duty_1  D  Tiefengeraet :: reg TIEFE requires

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  D  Tiefengeraet :: reg TIEFE requires  --  ASSUMED (device-promise)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Auftrag" _ "gewicht" => some (.intIn 0 4294967295)
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

/-! ### `gewicht_bei` -/

def gewicht_bei_body : List Stmt :=
  [(.ret (some (.place "Auftrag" (.name "n") "gewicht")))]

/-- The precondition: the declared shapes and the `requires`. -/
def gewicht_bei_pre : Expr :=
  (.hasShape "n" (.intIn 0 7))

def gewicht_bei_writes : List String := []

/-- What a caller of `gewicht_bei` has to bring: a well-typed world and the precondition. -/
def gewicht_bei_requires (t : State) : Prop := wellFormed t ∧ eval t gewicht_bei_pre = some (.bool true)

/-- What `gewicht_bei` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gewicht_bei_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `gewicht_des_stands` -/

-- REFUSED  gewicht_des_stands  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def gewicht_des_stands_pre : Expr :=
  (.lit (.bool true))

def gewicht_des_stands_writes : List String := []

/-- What a caller of `gewicht_des_stands` has to bring: a well-typed world and the precondition. -/
def gewicht_des_stands_requires (t : State) : Prop := wellFormed t ∧ eval t gewicht_des_stands_pre = some (.bool true)

/-- What `gewicht_des_stands` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gewicht_des_stands_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `quittieren` -/

-- REFUSED  quittieren  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def quittieren_pre : Expr :=
  (.lit (.bool true))

def quittieren_writes : List String := ["d"]

/-- What a caller of `quittieren` has to bring: a well-typed world and the precondition. -/
def quittieren_requires (t : State) : Prop := wellFormed t ∧ eval t quittieren_pre = some (.bool true)

/-- What `quittieren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def quittieren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `tiefe_lesen` -/

-- REFUSED  tiefe_lesen  (let-else): `let … else` -- two exits out of a call
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def tiefe_lesen_pre : Expr :=
  (.lit (.bool true))

def tiefe_lesen_writes : List String := []

/-- What a caller of `tiefe_lesen` has to bring: a well-typed world and the precondition. -/
def tiefe_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t tiefe_lesen_pre = some (.bool true)

/-- What `tiefe_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tiefe_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295) ∨ ∃ e, r = some (.reason e))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `gewicht_bei` -/

/-- **The duty of `gewicht_bei`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def gewicht_bei_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s gewicht_bei_pre = some (.bool true)),
    ∃ s', finalState (exec ρ gewicht_bei_body s) = some s'
        ∧ gewicht_bei_post s s' (finalValue (exec ρ gewicht_bei_body s))

theorem gewicht_bei_meets : gewicht_bei_meets_statement := by
  unfold gewicht_bei_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn s "n" _ _ hpre
  obtain ⟨n_Auftrag_gewicht_n, h_Auftrag_gewicht_n, lo_Auftrag_gewicht_n, hi_Auftrag_gewicht_n⟩ := WF_intIn shapeOf s.world (.slot "Auftrag" w_n "gewicht") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [gewicht_bei_pre, e_n, h_Auftrag_gewicht_n]
  gabbro_auto [gewicht_bei_body, gewicht_bei_pre, gewicht_bei_post, wellFormed, e_n, h_Auftrag_gewicht_n, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "gewicht_bei" gewicht_bei_body
  ∧ Frame ρ "gewicht_bei" gewicht_bei_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_gewicht_bei : gewicht_bei_meets_statement) :
    Contract ρ "gewicht_bei" gewicht_bei_requires gewicht_bei_post := by
  obtain ⟨r_gewicht_bei, fr_gewicht_bei⟩ := hp
  have c_gewicht_bei : Contract ρ "gewicht_bei" gewicht_bei_requires gewicht_bei_post :=
    contract_of_duty ρ "gewicht_bei" gewicht_bei_body gewicht_bei_requires gewicht_bei_post r_gewicht_bei
      (fun t ht => d_gewicht_bei ρ t ht.1 ht.2)
  exact c_gewicht_bei

end GabbroDuty.Duty44RegisterEinmalLesen