/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-zwei-gibibyte.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeZweiGibibyte

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Gross" _ "wert" => some (.intIn 0 18446744073709551615)
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

def lesen_body : List Stmt :=
  [(.ret (some (.place "Gross" (.name "i") "wert")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lesen_pre : Expr :=
  (.hasShape "i" (.intIn 0 399999999))

def lesen_writes : List String := []

/-- What a caller of `lesen` has to bring: a well-typed world and the precondition. -/
def lesen_requires (t : State) : Prop := wellFormed t ∧ eval t lesen_pre = some (.bool true)

/-- What `lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `schreiben` -/

def schreiben_body : List Stmt :=
  [(.assign "Gross" (.name "i") "wert" (.name "w"))]

/-- The precondition: the declared shapes and the `requires`. -/
def schreiben_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 399999999)) (.hasShape "w" (.intIn 0 18446744073709551615)))

def schreiben_writes : List String := ["Gross"]

/-- What a caller of `schreiben` has to bring: a well-typed world and the precondition. -/
def schreiben_requires (t : State) : Prop := wellFormed t ∧ eval t schreiben_pre = some (.bool true)

/-- What `schreiben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def schreiben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `lesen` -/

/-- **The duty of `lesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def lesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s lesen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ lesen_body s) = some s'
        ∧ lesen_post s s' (finalValue (exec ρ lesen_body s))

theorem lesen_meets : lesen_meets_statement := by
  unfold lesen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Gross_wert_i, h_Gross_wert_i, lo_Gross_wert_i, hi_Gross_wert_i⟩ := WF_intIn shapeOf s.world (.slot "Gross" w_i "wert") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lesen_pre, e_i, h_Gross_wert_i]
  gabbro_auto [lesen_body, lesen_pre, lesen_post, wellFormed, e_i, h_Gross_wert_i, hall] using shapeOf

/-! ### `schreiben` -/

/-- **The duty of `schreiben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def schreiben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s schreiben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ schreiben_body s) = some s'
        ∧ schreiben_post s s' (finalValue (exec ρ schreiben_body s))

theorem schreiben_meets : schreiben_meets_statement := by
  unfold schreiben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [schreiben_pre, e_i, e_w]
  gabbro_auto [schreiben_body, schreiben_pre, schreiben_post, wellFormed, e_i, e_w, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "lesen" lesen_body
  ∧ Frame ρ "lesen" lesen_writes
  ∧ Runs ρ "schreiben" schreiben_body
  ∧ Frame ρ "schreiben" schreiben_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_lesen : lesen_meets_statement)
    (d_schreiben : schreiben_meets_statement) :
    Contract ρ "lesen" lesen_requires lesen_post
    ∧ Contract ρ "schreiben" schreiben_requires schreiben_post := by
  obtain ⟨r_lesen, fr_lesen, r_schreiben, fr_schreiben⟩ := hp
  have c_lesen : Contract ρ "lesen" lesen_requires lesen_post :=
    contract_of_duty ρ "lesen" lesen_body lesen_requires lesen_post r_lesen
      (fun t ht => d_lesen ρ t ht.1 ht.2)
  have c_schreiben : Contract ρ "schreiben" schreiben_requires schreiben_post :=
    contract_of_duty ρ "schreiben" schreiben_body schreiben_requires schreiben_post r_schreiben
      (fun t ht => d_schreiben ρ t ht.1 ht.2)
  exact ⟨c_lesen, c_schreiben⟩

end GabbroDuty.DutyProbeZweiGibibyte
