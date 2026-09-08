/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/31-rcu.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty31Rcu

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Konten" _ "zaehler" => some (.intIn 0 65535)
  | .slot "Konten" _ "naechst" => some .opt
  | .global "frei" => some .opt
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

/-! ### `lesen` -/

-- REFUSED  lesen  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def lesen_pre : Expr :=
  (.hasShape "i" (.intIn 0 255))

def lesen_writes : List String := []

/-- What a caller of `lesen` has to bring: a well-typed world and the precondition. -/
def lesen_requires (t : State) : Prop := wellFormed t ∧ eval t lesen_pre = some (.bool true)

/-- What `lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `setzen` -/

def setzen_body : List Stmt :=
  [(.locked "SCHREIBER" [(.assign "Konten" (.name "i") "zaehler" (.name "w"))])]

/-- The precondition: the declared shapes and the `requires`. -/
def setzen_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 255)) (.hasShape "w" (.intIn 0 65535)))

def setzen_writes : List String := ["Konten"]

/-- What a caller of `setzen` has to bring: a well-typed world and the precondition. -/
def setzen_requires (t : State) : Prop := wellFormed t ∧ eval t setzen_pre = some (.bool true)

/-- What `setzen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def setzen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `zurueckgeben` -/

def zurueckgeben_body : List Stmt :=
  [(.locked "SCHREIBER" [(.assignGlobal "frei" (.someOf (.name "i")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def zurueckgeben_pre : Expr :=
  (.hasShape "i" (.intIn 0 255))

def zurueckgeben_writes : List String := ["frei"]

/-- What a caller of `zurueckgeben` has to bring: a well-typed world and the precondition. -/
def zurueckgeben_requires (t : State) : Prop := wellFormed t ∧ eval t zurueckgeben_pre = some (.bool true)

/-- What `zurueckgeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zurueckgeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `setzen` -/

/-- **The duty of `setzen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def setzen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s setzen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ setzen_body s) = some s'
        ∧ setzen_post s s' (finalValue (exec ρ setzen_body s))

theorem setzen_meets : setzen_meets_statement := by
  unfold setzen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [setzen_pre, e_i, e_w]
  gabbro_auto [setzen_body, setzen_pre, setzen_post, wellFormed, e_i, e_w, hall] using shapeOf

/-! ### `zurueckgeben` -/

/-- **The duty of `zurueckgeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def zurueckgeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s zurueckgeben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ zurueckgeben_body s) = some s'
        ∧ zurueckgeben_post s s' (finalValue (exec ρ zurueckgeben_body s))

theorem zurueckgeben_meets : zurueckgeben_meets_statement := by
  unfold zurueckgeben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [zurueckgeben_pre, e_i]
  gabbro_auto [zurueckgeben_body, zurueckgeben_pre, zurueckgeben_post, wellFormed, e_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "setzen" setzen_body
  ∧ Frame ρ "setzen" setzen_writes
  ∧ Runs ρ "zurueckgeben" zurueckgeben_body
  ∧ Frame ρ "zurueckgeben" zurueckgeben_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_setzen : setzen_meets_statement)
    (d_zurueckgeben : zurueckgeben_meets_statement) :
    Contract ρ "setzen" setzen_requires setzen_post
    ∧ Contract ρ "zurueckgeben" zurueckgeben_requires zurueckgeben_post := by
  obtain ⟨r_setzen, fr_setzen, r_zurueckgeben, fr_zurueckgeben⟩ := hp
  have c_setzen : Contract ρ "setzen" setzen_requires setzen_post :=
    contract_of_duty ρ "setzen" setzen_body setzen_requires setzen_post r_setzen
      (fun t ht => d_setzen ρ t ht.1 ht.2)
  have c_zurueckgeben : Contract ρ "zurueckgeben" zurueckgeben_requires zurueckgeben_post :=
    contract_of_duty ρ "zurueckgeben" zurueckgeben_body zurueckgeben_requires zurueckgeben_post r_zurueckgeben
      (fun t ht => d_zurueckgeben ρ t ht.1 ht.2)
  exact ⟨c_setzen, c_zurueckgeben⟩

end GabbroDuty.Duty31Rcu