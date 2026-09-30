/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/104-referenz.gab  total 3  goals 3  refused 0
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

namespace GabbroDuty.Duty104Referenz

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  einzahlen :: ensures #1  --  carried by `einzahlen_meets`
  duty_2  N  lies :: ensures #1  --  carried by `lies_meets`
  duty_3  V  einzahlen :: lies requires #1  --  carried by `einzahlen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Konto" _ "stand" => some (.intIn 0 100)
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

/-! ### `einzahlen` -/

def einzahlen_body : List Stmt :=
  [(.assign "Konto" (.name "i") "stand" (.lit (.int 100))), (.call "lies" ["k", "i"] [(.name "k"), (.name "i")] (.bin .and (.hasShape "i" (.intIn 0 1)) (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def einzahlen_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 1)) (.bin .and (.hasShape "b" (.intIn 0 10)) (.lit (.bool true))))

def einzahlen_writes : List String := ["Konto"]

/-- What a caller of `einzahlen` has to bring: a well-typed world and the precondition. -/
def einzahlen_requires (t : State) : Prop := wellFormed t ∧ eval t einzahlen_pre = some (.bool true)

/-- What `einzahlen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einzahlen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (∀ o1, eval s (.place "Konto" (.name "i") "stand") = some o1 → eval { world := s'.world, local' := (bindLocal s.local' "old#1" o1) } (.bin .le (.name "old#1") (.place "Konto" (.name "i") "stand")) = some (.bool true))

/-! ### `lies` -/

def lies_body : List Stmt :=
  [(.ret (some (.place "Konto" (.name "i") "stand")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lies_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 1)) (.lit (.bool true)))

def lies_writes : List String := []

/-- What a caller of `lies` has to bring: a well-typed world and the precondition. -/
def lies_requires (t : State) : Prop := wellFormed t ∧ eval t lies_pre = some (.bool true)

/-- What `lies` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lies_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 100)
  ∧ -- ensures #1
  (∃ v, r = some v ∧ eval { world := s'.world, local' := (bindLocal s.local' "result" v) } (.bin .eq (.name "result") (.place "Konto" (.name "i") "stand")) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `einzahlen` -/

/-- **The duty of `einzahlen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einzahlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einzahlen_pre = some (.bool true))
    -- the contract of `lies`
    (c_lies : Contract ρ "lies" lies_requires lies_post)
    -- the frame of `lies`
    (fr_lies : Frame ρ "lies" lies_writes),
    ∃ s', finalState (exec ρ einzahlen_body s) = some s'
        ∧ einzahlen_post s s' (finalValue (exec ρ einzahlen_body s))

theorem einzahlen_meets : einzahlen_meets_statement := by
  unfold einzahlen_meets_statement
  intro ρ s hwf hpre c_lies fr_lies
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨n_Konto_stand_i, h_Konto_stand_i, lo_Konto_stand_i, hi_Konto_stand_i⟩ := WF_intIn shapeOf s.world (.slot "Konto" w_i "stand") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [einzahlen_pre, e_i, e_b, h_Konto_stand_i]
  gabbro_auto2 [einzahlen_body, einzahlen_pre, einzahlen_post, wellFormed, lies_pre, lies_requires, lies_post, lies_writes, Frame_read _ _ _ fr_lies, e_i, e_b, h_Konto_stand_i, hall] [einzahlen_body, einzahlen_pre, einzahlen_post, wellFormed, lies_pre, lies_requires, lies_post, lies_writes, Frame_read _ _ _ fr_lies, e_i, e_b, h_Konto_stand_i] using shapeOf

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
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Konto_stand_i, h_Konto_stand_i, lo_Konto_stand_i, hi_Konto_stand_i⟩ := WF_intIn shapeOf s.world (.slot "Konto" w_i "stand") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lies_pre, e_i, h_Konto_stand_i]
  gabbro_auto2 [lies_body, lies_pre, lies_post, wellFormed, e_i, h_Konto_stand_i, hall] [lies_body, lies_pre, lies_post, wellFormed, e_i, h_Konto_stand_i] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "einzahlen" einzahlen_body
  ∧ Frame ρ "einzahlen" einzahlen_writes
  ∧ Runs ρ "lies" lies_body
  ∧ Frame ρ "lies" lies_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_lies : lies_meets_statement)
    (d_einzahlen : einzahlen_meets_statement) :
    Contract ρ "lies" lies_requires lies_post
    ∧ Contract ρ "einzahlen" einzahlen_requires einzahlen_post := by
  obtain ⟨r_einzahlen, fr_einzahlen, r_lies, fr_lies⟩ := hp
  have c_lies : Contract ρ "lies" lies_requires lies_post :=
    contract_of_duty ρ "lies" lies_body lies_requires lies_post r_lies
      (fun t ht => d_lies ρ t ht.1 ht.2)
  have c_einzahlen : Contract ρ "einzahlen" einzahlen_requires einzahlen_post :=
    contract_of_duty ρ "einzahlen" einzahlen_body einzahlen_requires einzahlen_post r_einzahlen
      (fun t ht => d_einzahlen ρ t ht.1 ht.2 c_lies fr_lies)
  exact ⟨c_lies, c_einzahlen⟩

end GabbroDuty.Duty104Referenz
