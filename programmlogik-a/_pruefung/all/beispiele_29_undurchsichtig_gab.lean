/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/29-undurchsichtig.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty29Undurchsichtig

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

/-! ### `erste_seite` -/

def erste_seite_body : List Stmt :=
  [(.retCall "pa_aus_zahl" ["z"] [(.lit (.int 4096))] (.hasShape "z" (.intIn 0 18446744073709551615)))]

/-- The precondition: the declared shapes and the `requires`. -/
def erste_seite_pre : Expr :=
  (.lit (.bool true))

def erste_seite_writes : List String := []

/-- What a caller of `erste_seite` has to bring: a well-typed world and the precondition. -/
def erste_seite_requires (t : State) : Prop := wellFormed t ∧ eval t erste_seite_pre = some (.bool true)

/-- What `erste_seite` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def erste_seite_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `pa_als_zahl` -/

def pa_als_zahl_body : List Stmt :=
  [(.ret (some (.name "p")))]

/-- The precondition: the declared shapes and the `requires`. -/
def pa_als_zahl_pre : Expr :=
  (.hasShape "p" (.intIn 0 18446744073709551615))

def pa_als_zahl_writes : List String := []

/-- What a caller of `pa_als_zahl` has to bring: a well-typed world and the precondition. -/
def pa_als_zahl_requires (t : State) : Prop := wellFormed t ∧ eval t pa_als_zahl_pre = some (.bool true)

/-- What `pa_als_zahl` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def pa_als_zahl_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `pa_aus_zahl` -/

def pa_aus_zahl_body : List Stmt :=
  [(.ret (some (.name "z")))]

/-- The precondition: the declared shapes and the `requires`. -/
def pa_aus_zahl_pre : Expr :=
  (.hasShape "z" (.intIn 0 18446744073709551615))

def pa_aus_zahl_writes : List String := []

/-- What a caller of `pa_aus_zahl` has to bring: a well-typed world and the precondition. -/
def pa_aus_zahl_requires (t : State) : Prop := wellFormed t ∧ eval t pa_aus_zahl_pre = some (.bool true)

/-- What `pa_aus_zahl` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def pa_aus_zahl_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `erste_seite` -/

/-- **The duty of `erste_seite`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def erste_seite_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s erste_seite_pre = some (.bool true))
    -- the contract of `pa_aus_zahl`
    (c_pa_aus_zahl : Contract ρ "pa_aus_zahl" pa_aus_zahl_requires pa_aus_zahl_post)
    -- the frame of `pa_aus_zahl`
    (fr_pa_aus_zahl : Frame ρ "pa_aus_zahl" pa_aus_zahl_writes),
    ∃ s', finalState (exec ρ erste_seite_body s) = some s'
        ∧ erste_seite_post s s' (finalValue (exec ρ erste_seite_body s))

theorem erste_seite_meets : erste_seite_meets_statement := by
  unfold erste_seite_meets_statement
  intro ρ s hwf hpre c_pa_aus_zahl fr_pa_aus_zahl
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [erste_seite_pre]
  gabbro_auto [erste_seite_body, erste_seite_pre, erste_seite_post, wellFormed, pa_aus_zahl_pre, pa_aus_zahl_requires, pa_aus_zahl_post, pa_aus_zahl_writes, Frame_read _ _ _ fr_pa_aus_zahl, hall] using shapeOf

/-! ### `pa_als_zahl` -/

/-- **The duty of `pa_als_zahl`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def pa_als_zahl_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s pa_als_zahl_pre = some (.bool true)),
    ∃ s', finalState (exec ρ pa_als_zahl_body s) = some s'
        ∧ pa_als_zahl_post s s' (finalValue (exec ρ pa_als_zahl_body s))

theorem pa_als_zahl_meets : pa_als_zahl_meets_statement := by
  unfold pa_als_zahl_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_p, e_p, lo_p, hi_p⟩ := shape_intIn s "p" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [pa_als_zahl_pre, e_p]
  gabbro_auto [pa_als_zahl_body, pa_als_zahl_pre, pa_als_zahl_post, wellFormed, e_p, hall] using shapeOf

/-! ### `pa_aus_zahl` -/

/-- **The duty of `pa_aus_zahl`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def pa_aus_zahl_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s pa_aus_zahl_pre = some (.bool true)),
    ∃ s', finalState (exec ρ pa_aus_zahl_body s) = some s'
        ∧ pa_aus_zahl_post s s' (finalValue (exec ρ pa_aus_zahl_body s))

theorem pa_aus_zahl_meets : pa_aus_zahl_meets_statement := by
  unfold pa_aus_zahl_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_z, e_z, lo_z, hi_z⟩ := shape_intIn s "z" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [pa_aus_zahl_pre, e_z]
  gabbro_auto [pa_aus_zahl_body, pa_aus_zahl_pre, pa_aus_zahl_post, wellFormed, e_z, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "erste_seite" erste_seite_body
  ∧ Frame ρ "erste_seite" erste_seite_writes
  ∧ Runs ρ "pa_als_zahl" pa_als_zahl_body
  ∧ Frame ρ "pa_als_zahl" pa_als_zahl_writes
  ∧ Runs ρ "pa_aus_zahl" pa_aus_zahl_body
  ∧ Frame ρ "pa_aus_zahl" pa_aus_zahl_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_pa_als_zahl : pa_als_zahl_meets_statement)
    (d_pa_aus_zahl : pa_aus_zahl_meets_statement)
    (d_erste_seite : erste_seite_meets_statement) :
    Contract ρ "pa_als_zahl" pa_als_zahl_requires pa_als_zahl_post
    ∧ Contract ρ "pa_aus_zahl" pa_aus_zahl_requires pa_aus_zahl_post
    ∧ Contract ρ "erste_seite" erste_seite_requires erste_seite_post := by
  obtain ⟨r_erste_seite, fr_erste_seite, r_pa_als_zahl, fr_pa_als_zahl, r_pa_aus_zahl, fr_pa_aus_zahl⟩ := hp
  have c_pa_als_zahl : Contract ρ "pa_als_zahl" pa_als_zahl_requires pa_als_zahl_post :=
    contract_of_duty ρ "pa_als_zahl" pa_als_zahl_body pa_als_zahl_requires pa_als_zahl_post r_pa_als_zahl
      (fun t ht => d_pa_als_zahl ρ t ht.1 ht.2)
  have c_pa_aus_zahl : Contract ρ "pa_aus_zahl" pa_aus_zahl_requires pa_aus_zahl_post :=
    contract_of_duty ρ "pa_aus_zahl" pa_aus_zahl_body pa_aus_zahl_requires pa_aus_zahl_post r_pa_aus_zahl
      (fun t ht => d_pa_aus_zahl ρ t ht.1 ht.2)
  have c_erste_seite : Contract ρ "erste_seite" erste_seite_requires erste_seite_post :=
    contract_of_duty ρ "erste_seite" erste_seite_body erste_seite_requires erste_seite_post r_erste_seite
      (fun t ht => d_erste_seite ρ t ht.1 ht.2 c_pa_aus_zahl fr_pa_aus_zahl)
  exact ⟨c_pa_als_zahl, c_pa_aus_zahl, c_erste_seite⟩

end GabbroDuty.Duty29Undurchsichtig