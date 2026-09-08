/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/34-markierter-wert.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty34MarkierterWert

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Anfragen" _ "benutzt" => some .bool
  | .slot "Anfragen" _ "was" => some (.sum [("Leer", none), ("Kurz", (some (some (0, 4294967295)))), ("Lang", (some (some (0, 18446744073709551615)))), ("Antwort", (some (some (0, 65535))))])
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

/-! ### `art_von` -/

def art_von_body : List Stmt :=
  [(.onTag (.name "m") [("Leer", none, [(.ret (some (.lit (.int 0))))]), ("Kurz", some "k", [(.ret (some (.lit (.int 1))))]), ("Lang", some "p", [(.ret (some (.lit (.int 2))))]), ("Antwort", some "z", [(.ret (some (.lit (.int 3))))])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def art_von_pre : Expr :=
  (.hasShape "m" (.sum [("Leer", none), ("Kurz", (some (some (0, 4294967295)))), ("Lang", (some (some (0, 18446744073709551615)))), ("Antwort", (some (some (0, 65535))))]))

def art_von_writes : List String := []

/-- What a caller of `art_von` has to bring: a well-typed world and the precondition. -/
def art_von_requires (t : State) : Prop := wellFormed t ∧ eval t art_von_pre = some (.bool true)

/-- What `art_von` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def art_von_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `gewicht` -/

def gewicht_body : List Stmt :=
  [(.onTag (.name "m") [("Leer", none, [(.ret (some (.lit (.int 0))))]), ("Kurz", some "k", [(.ret (some (.name "k")))]), ("Lang", some "p", [(.ret (some (.name "p")))]), ("Antwort", some "z", [(.ret (some (.name "z")))])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def gewicht_pre : Expr :=
  (.hasShape "m" (.sum [("Leer", none), ("Kurz", (some (some (0, 4294967295)))), ("Lang", (some (some (0, 18446744073709551615)))), ("Antwort", (some (some (0, 65535))))]))

def gewicht_writes : List String := []

/-- What a caller of `gewicht` has to bring: a well-typed world and the precondition. -/
def gewicht_requires (t : State) : Prop := wellFormed t ∧ eval t gewicht_pre = some (.bool true)

/-- What `gewicht` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gewicht_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `gewicht_im_slot` -/

def gewicht_im_slot_body : List Stmt :=
  [(.onTag (.place "Anfragen" (.name "i") "was") [("Leer", none, [(.ret (some (.lit (.int 0))))]), ("Kurz", some "k", [(.ret (some (.name "k")))]), ("Lang", some "p", [(.ret (some (.name "p")))]), ("Antwort", some "z", [(.ret (some (.name "z")))])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def gewicht_im_slot_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def gewicht_im_slot_writes : List String := []

/-- What a caller of `gewicht_im_slot` has to bring: a well-typed world and the precondition. -/
def gewicht_im_slot_requires (t : State) : Prop := wellFormed t ∧ eval t gewicht_im_slot_pre = some (.bool true)

/-- What `gewicht_im_slot` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gewicht_im_slot_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `art_von` -/

/-- **The duty of `art_von`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def art_von_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s art_von_pre = some (.bool true)),
    ∃ s', finalState (exec ρ art_von_body s) = some s'
        ∧ art_von_post s s' (finalValue (exec ρ art_von_body s))

theorem art_von_meets : art_von_meets_statement := by
  unfold art_von_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_m, p_m, e_m, c_m⟩ := shape_sum s "m" _ hpre
  have hall := hpre
  gabbro_simp_at hall [art_von_pre, e_m]
  gabbro_auto [art_von_body, art_von_pre, art_von_post, wellFormed, e_m, c_m, hall] using shapeOf

/-! ### `gewicht` -/

/-- **The duty of `gewicht`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def gewicht_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s gewicht_pre = some (.bool true)),
    ∃ s', finalState (exec ρ gewicht_body s) = some s'
        ∧ gewicht_post s s' (finalValue (exec ρ gewicht_body s))

theorem gewicht_meets : gewicht_meets_statement := by
  unfold gewicht_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_m, p_m, e_m, c_m⟩ := shape_sum s "m" _ hpre
  have hall := hpre
  gabbro_simp_at hall [gewicht_pre, e_m]
  gabbro_auto [gewicht_body, gewicht_pre, gewicht_post, wellFormed, e_m, c_m, hall] using shapeOf

/-! ### `gewicht_im_slot` -/

/-- **The duty of `gewicht_im_slot`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def gewicht_im_slot_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s gewicht_im_slot_pre = some (.bool true)),
    ∃ s', finalState (exec ρ gewicht_im_slot_body s) = some s'
        ∧ gewicht_im_slot_post s s' (finalValue (exec ρ gewicht_im_slot_body s))

theorem gewicht_im_slot_meets : gewicht_im_slot_meets_statement := by
  unfold gewicht_im_slot_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Anfragen_was_i, q_Anfragen_was_i, h_Anfragen_was_i, c_Anfragen_was_i⟩ := WF_sum shapeOf s.world (.slot "Anfragen" w_i "was") _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [gewicht_im_slot_pre, e_i, h_Anfragen_was_i]
  gabbro_auto [gewicht_im_slot_body, gewicht_im_slot_pre, gewicht_im_slot_post, wellFormed, e_i, h_Anfragen_was_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "art_von" art_von_body
  ∧ Frame ρ "art_von" art_von_writes
  ∧ Runs ρ "gewicht" gewicht_body
  ∧ Frame ρ "gewicht" gewicht_writes
  ∧ Runs ρ "gewicht_im_slot" gewicht_im_slot_body
  ∧ Frame ρ "gewicht_im_slot" gewicht_im_slot_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_art_von : art_von_meets_statement)
    (d_gewicht : gewicht_meets_statement)
    (d_gewicht_im_slot : gewicht_im_slot_meets_statement) :
    Contract ρ "art_von" art_von_requires art_von_post
    ∧ Contract ρ "gewicht" gewicht_requires gewicht_post
    ∧ Contract ρ "gewicht_im_slot" gewicht_im_slot_requires gewicht_im_slot_post := by
  obtain ⟨r_art_von, fr_art_von, r_gewicht, fr_gewicht, r_gewicht_im_slot, fr_gewicht_im_slot⟩ := hp
  have c_art_von : Contract ρ "art_von" art_von_requires art_von_post :=
    contract_of_duty ρ "art_von" art_von_body art_von_requires art_von_post r_art_von
      (fun t ht => d_art_von ρ t ht.1 ht.2)
  have c_gewicht : Contract ρ "gewicht" gewicht_requires gewicht_post :=
    contract_of_duty ρ "gewicht" gewicht_body gewicht_requires gewicht_post r_gewicht
      (fun t ht => d_gewicht ρ t ht.1 ht.2)
  have c_gewicht_im_slot : Contract ρ "gewicht_im_slot" gewicht_im_slot_requires gewicht_im_slot_post :=
    contract_of_duty ρ "gewicht_im_slot" gewicht_im_slot_body gewicht_im_slot_requires gewicht_im_slot_post r_gewicht_im_slot
      (fun t ht => d_gewicht_im_slot ρ t ht.1 ht.2)
  exact ⟨c_art_von, c_gewicht, c_gewicht_im_slot⟩

end GabbroDuty.Duty34MarkierterWert