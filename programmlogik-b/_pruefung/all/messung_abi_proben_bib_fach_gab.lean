/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/abi-proben/bib-fach.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyBibFach

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kaesten" _ "wert" => some (.intIn 0 4294967295)
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

/-! ### `begrenze` -/

def begrenze_body : List Stmt :=
  [(.ite (.bin .gt (.name "w") (.lit (.int 65535))) [(.ret (some (.lit (.int 65535))))] []), (.ret (some (.name "w")))]

/-- The precondition: the declared shapes and the `requires`. -/
def begrenze_pre : Expr :=
  (.hasShape "w" (.intIn 0 4294967295))

def begrenze_writes : List String := []

/-- What a caller of `begrenze` has to bring: a well-typed world and the precondition. -/
def begrenze_requires (t : State) : Prop := wellFormed t ∧ eval t begrenze_pre = some (.bool true)

/-- What `begrenze` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def begrenze_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `lege_ab` -/

def lege_ab_body : List Stmt :=
  [(.bindCall "#m1" "begrenze" ["w"] [(.name "w")] (.hasShape "w" (.intIn 0 4294967295))), (.assign "Kaesten" (.name "i") "wert" (.name "#m1")), (.ret (some (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def lege_ab_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 7)) (.hasShape "w" (.intIn 0 4294967295)))

def lege_ab_writes : List String := ["Kaesten"]

/-- What a caller of `lege_ab` has to bring: a well-typed world and the precondition. -/
def lege_ab_requires (t : State) : Prop := wellFormed t ∧ eval t lege_ab_pre = some (.bool true)

/-- What `lege_ab` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lege_ab_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `lies` -/

def lies_body : List Stmt :=
  [(.ret (some (.place "Kaesten" (.name "i") "wert")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lies_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def lies_writes : List String := []

/-- What a caller of `lies` has to bring: a well-typed world and the precondition. -/
def lies_requires (t : State) : Prop := wellFormed t ∧ eval t lies_pre = some (.bool true)

/-- What `lies` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lies_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `begrenze` -/

/-- **The duty of `begrenze`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def begrenze_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s begrenze_pre = some (.bool true)),
    ∃ s', finalState (exec ρ begrenze_body s) = some s'
        ∧ begrenze_post s s' (finalValue (exec ρ begrenze_body s))

theorem begrenze_meets : begrenze_meets_statement := by
  unfold begrenze_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [begrenze_pre, e_w]
  gabbro_auto [begrenze_body, begrenze_pre, begrenze_post, wellFormed, e_w, hall] using shapeOf

/-! ### `lege_ab` -/

/-- **The duty of `lege_ab`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def lege_ab_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s lege_ab_pre = some (.bool true))
    -- the contract of `begrenze`
    (c_begrenze : Contract ρ "begrenze" begrenze_requires begrenze_post)
    -- the frame of `begrenze`
    (fr_begrenze : Frame ρ "begrenze" begrenze_writes),
    ∃ s', finalState (exec ρ lege_ab_body s) = some s'
        ∧ lege_ab_post s s' (finalValue (exec ρ lege_ab_body s))

theorem lege_ab_meets : lege_ab_meets_statement := by
  unfold lege_ab_meets_statement
  intro ρ s hwf hpre c_begrenze fr_begrenze
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [lege_ab_pre, e_i, e_w]
  gabbro_auto [lege_ab_body, lege_ab_pre, lege_ab_post, wellFormed, begrenze_pre, begrenze_requires, begrenze_post, begrenze_writes, Frame_read _ _ _ fr_begrenze, e_i, e_w, hall] using shapeOf

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
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Kaesten_wert_i, h_Kaesten_wert_i, lo_Kaesten_wert_i, hi_Kaesten_wert_i⟩ := WF_intIn shapeOf s.world (.slot "Kaesten" w_i "wert") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lies_pre, e_i, h_Kaesten_wert_i]
  gabbro_auto [lies_body, lies_pre, lies_post, wellFormed, e_i, h_Kaesten_wert_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "begrenze" begrenze_body
  ∧ Frame ρ "begrenze" begrenze_writes
  ∧ Runs ρ "lege_ab" lege_ab_body
  ∧ Frame ρ "lege_ab" lege_ab_writes
  ∧ Runs ρ "lies" lies_body
  ∧ Frame ρ "lies" lies_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_begrenze : begrenze_meets_statement)
    (d_lege_ab : lege_ab_meets_statement)
    (d_lies : lies_meets_statement) :
    Contract ρ "begrenze" begrenze_requires begrenze_post
    ∧ Contract ρ "lege_ab" lege_ab_requires lege_ab_post
    ∧ Contract ρ "lies" lies_requires lies_post := by
  obtain ⟨r_begrenze, fr_begrenze, r_lege_ab, fr_lege_ab, r_lies, fr_lies⟩ := hp
  have c_begrenze : Contract ρ "begrenze" begrenze_requires begrenze_post :=
    contract_of_duty ρ "begrenze" begrenze_body begrenze_requires begrenze_post r_begrenze
      (fun t ht => d_begrenze ρ t ht.1 ht.2)
  have c_lege_ab : Contract ρ "lege_ab" lege_ab_requires lege_ab_post :=
    contract_of_duty ρ "lege_ab" lege_ab_body lege_ab_requires lege_ab_post r_lege_ab
      (fun t ht => d_lege_ab ρ t ht.1 ht.2 c_begrenze fr_begrenze)
  have c_lies : Contract ρ "lies" lies_requires lies_post :=
    contract_of_duty ρ "lies" lies_body lies_requires lies_post r_lies
      (fun t ht => d_lies ρ t ht.1 ht.2)
  exact ⟨c_begrenze, c_lege_ab, c_lies⟩

end GabbroDuty.DutyBibFach
