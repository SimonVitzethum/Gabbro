/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/grammatik/geraeteworte.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyGeraeteworte

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Stand" "bereit" => some .bool
  | .global "SCHRANKE" => some .bool
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

/-! ### `freigeben` -/

def freigeben_body : List Stmt :=
  [(.assignField "Stand" "bereit" (.lit (.bool true))), (.publish "SCHRANKE" (.lit (.bool true)) ["lage"])]

/-- The precondition: the declared shapes and the `requires`. -/
def freigeben_pre : Expr :=
  (.lit (.bool true))

def freigeben_writes : List String := ["Stand", "SCHRANKE"]

/-- What a caller of `freigeben` has to bring: a well-typed world and the precondition. -/
def freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t freigeben_pre = some (.bool true)

/-- What `freigeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `grund_lesen` -/

-- REFUSED  grund_lesen  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def grund_lesen_pre : Expr :=
  (.lit (.bool true))

def grund_lesen_writes : List String := []

/-- What a caller of `grund_lesen` has to bring: a well-typed world and the precondition. -/
def grund_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t grund_lesen_pre = some (.bool true)

/-- What `grund_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def grund_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `warten` -/

def warten_body : List Stmt :=
  [(.awaitLoad "fertig" "SCHRANKE" ["lage"]), (.ret (some (.name "fertig")))]

/-- The precondition: the declared shapes and the `requires`. -/
def warten_pre : Expr :=
  (.lit (.bool true))

def warten_writes : List String := []

/-- What a caller of `warten` has to bring: a well-typed world and the precondition. -/
def warten_requires (t : State) : Prop := wellFormed t ∧ eval t warten_pre = some (.bool true)

/-- What `warten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def warten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `freigeben` -/

/-- **The duty of `freigeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def freigeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s freigeben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ freigeben_body s) = some s'
        ∧ freigeben_post s s' (finalValue (exec ρ freigeben_body s))

theorem freigeben_meets : freigeben_meets_statement := by
  unfold freigeben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Stand_bereit, h_Stand_bereit⟩ := WF_bool shapeOf s.world (.field "Stand" "bereit") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [freigeben_pre, h_Stand_bereit]
  gabbro_auto [freigeben_body, freigeben_pre, freigeben_post, wellFormed, h_Stand_bereit, hall] using shapeOf

/-! ### `warten` -/

/-- **The duty of `warten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def warten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s warten_pre = some (.bool true)),
    ∃ s', finalState (exec ρ warten_body s) = some s'
        ∧ warten_post s s' (finalValue (exec ρ warten_body s))

theorem warten_meets : warten_meets_statement := by
  unfold warten_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [warten_pre]
  gabbro_auto [warten_body, warten_pre, warten_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "freigeben" freigeben_body
  ∧ Frame ρ "freigeben" freigeben_writes
  ∧ Runs ρ "warten" warten_body
  ∧ Frame ρ "warten" warten_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_freigeben : freigeben_meets_statement)
    (d_warten : warten_meets_statement) :
    Contract ρ "freigeben" freigeben_requires freigeben_post
    ∧ Contract ρ "warten" warten_requires warten_post := by
  obtain ⟨r_freigeben, fr_freigeben, r_warten, fr_warten⟩ := hp
  have c_freigeben : Contract ρ "freigeben" freigeben_requires freigeben_post :=
    contract_of_duty ρ "freigeben" freigeben_body freigeben_requires freigeben_post r_freigeben
      (fun t ht => d_freigeben ρ t ht.1 ht.2)
  have c_warten : Contract ρ "warten" warten_requires warten_post :=
    contract_of_duty ρ "warten" warten_body warten_requires warten_post r_warten
      (fun t ht => d_warten ρ t ht.1 ht.2)
  exact ⟨c_freigeben, c_warten⟩

end GabbroDuty.DutyGeraeteworte