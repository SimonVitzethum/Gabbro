/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/28-reserve-und-hinterlegung.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty28ReserveUndHinterlegung

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Halde" _ "kopf" => some (.intIn 0 18446744073709551615)
  | .slot "Halde" _ "naechst" => some .opt
  | .global "hinterlegt" => some (.intIn 0 1048576)
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

/-! ### `einhaengen` -/

def einhaengen_body : List Stmt :=
  [(.assignGlobal "hinterlegt" (.name "neu"))]

/-- The precondition: the declared shapes and the `requires`. -/
def einhaengen_pre : Expr :=
  (.hasShape "neu" (.intIn 0 1048576))

def einhaengen_writes : List String := ["hinterlegt"]

/-- What a caller of `einhaengen` has to bring: a well-typed world and the precondition. -/
def einhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t einhaengen_pre = some (.bool true)

/-- What `einhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `lesen` -/

def lesen_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "i") (.lit (.int 0))) (.bin .lt (.name "i") (.global "hinterlegt"))) [] [(.ret (some (.lit (.int 0))))]), (.ret (some (.place "Halde" (.name "i") "kopf")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lesen_pre : Expr :=
  (.hasShape "i" (.intIn 0 1048575))

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

/-! ### `lesen_mit_wenn` -/

def lesen_mit_wenn_body : List Stmt :=
  [(.ite (.bin .lt (.name "i") (.global "hinterlegt")) [(.ret (some (.place "Halde" (.name "i") "kopf")))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def lesen_mit_wenn_pre : Expr :=
  (.hasShape "i" (.intIn 0 1048575))

def lesen_mit_wenn_writes : List String := []

/-- What a caller of `lesen_mit_wenn` has to bring: a well-typed world and the precondition. -/
def lesen_mit_wenn_requires (t : State) : Prop := wellFormed t ∧ eval t lesen_mit_wenn_pre = some (.bool true)

/-- What `lesen_mit_wenn` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lesen_mit_wenn_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `einhaengen` -/

/-- **The duty of `einhaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einhaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einhaengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ einhaengen_body s) = some s'
        ∧ einhaengen_post s s' (finalValue (exec ρ einhaengen_body s))

theorem einhaengen_meets : einhaengen_meets_statement := by
  unfold einhaengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_neu, e_neu, lo_neu, hi_neu⟩ := shape_intIn s "neu" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [einhaengen_pre, e_neu]
  gabbro_auto [einhaengen_body, einhaengen_pre, einhaengen_post, wellFormed, e_neu, hall] using shapeOf

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
  obtain ⟨n_Halde_kopf_i, h_Halde_kopf_i, lo_Halde_kopf_i, hi_Halde_kopf_i⟩ := WF_intIn shapeOf s.world (.slot "Halde" w_i "kopf") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lesen_pre, e_i, h_Halde_kopf_i]
  gabbro_auto [lesen_body, lesen_pre, lesen_post, wellFormed, e_i, h_Halde_kopf_i, hall] using shapeOf

/-! ### `lesen_mit_wenn` -/

/-- **The duty of `lesen_mit_wenn`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def lesen_mit_wenn_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s lesen_mit_wenn_pre = some (.bool true)),
    ∃ s', finalState (exec ρ lesen_mit_wenn_body s) = some s'
        ∧ lesen_mit_wenn_post s s' (finalValue (exec ρ lesen_mit_wenn_body s))

theorem lesen_mit_wenn_meets : lesen_mit_wenn_meets_statement := by
  unfold lesen_mit_wenn_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Halde_kopf_i, h_Halde_kopf_i, lo_Halde_kopf_i, hi_Halde_kopf_i⟩ := WF_intIn shapeOf s.world (.slot "Halde" w_i "kopf") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lesen_mit_wenn_pre, e_i, h_Halde_kopf_i]
  gabbro_auto [lesen_mit_wenn_body, lesen_mit_wenn_pre, lesen_mit_wenn_post, wellFormed, e_i, h_Halde_kopf_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "einhaengen" einhaengen_body
  ∧ Frame ρ "einhaengen" einhaengen_writes
  ∧ Runs ρ "lesen" lesen_body
  ∧ Frame ρ "lesen" lesen_writes
  ∧ Runs ρ "lesen_mit_wenn" lesen_mit_wenn_body
  ∧ Frame ρ "lesen_mit_wenn" lesen_mit_wenn_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_einhaengen : einhaengen_meets_statement)
    (d_lesen : lesen_meets_statement)
    (d_lesen_mit_wenn : lesen_mit_wenn_meets_statement) :
    Contract ρ "einhaengen" einhaengen_requires einhaengen_post
    ∧ Contract ρ "lesen" lesen_requires lesen_post
    ∧ Contract ρ "lesen_mit_wenn" lesen_mit_wenn_requires lesen_mit_wenn_post := by
  obtain ⟨r_einhaengen, fr_einhaengen, r_lesen, fr_lesen, r_lesen_mit_wenn, fr_lesen_mit_wenn⟩ := hp
  have c_einhaengen : Contract ρ "einhaengen" einhaengen_requires einhaengen_post :=
    contract_of_duty ρ "einhaengen" einhaengen_body einhaengen_requires einhaengen_post r_einhaengen
      (fun t ht => d_einhaengen ρ t ht.1 ht.2)
  have c_lesen : Contract ρ "lesen" lesen_requires lesen_post :=
    contract_of_duty ρ "lesen" lesen_body lesen_requires lesen_post r_lesen
      (fun t ht => d_lesen ρ t ht.1 ht.2)
  have c_lesen_mit_wenn : Contract ρ "lesen_mit_wenn" lesen_mit_wenn_requires lesen_mit_wenn_post :=
    contract_of_duty ρ "lesen_mit_wenn" lesen_mit_wenn_body lesen_mit_wenn_requires lesen_mit_wenn_post r_lesen_mit_wenn
      (fun t ht => d_lesen_mit_wenn ρ t ht.1 ht.2)
  exact ⟨c_einhaengen, c_lesen, c_lesen_mit_wenn⟩

end GabbroDuty.Duty28ReserveUndHinterlegung