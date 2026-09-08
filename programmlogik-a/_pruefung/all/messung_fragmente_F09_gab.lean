/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F09.gab  total 3  goals 0  refused 3
        @assumed 3  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.DutyF09

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  walk-invariant (3): ASSUMED -- an invariant of a `walk` -- a statement about a hardware table: an ASSUMPTION
    duty_1  W  Seitenabstieg :: down
    duty_2  W  Seitenabstieg :: leaf
    duty_3  W  Seitenabstieg :: invariant wx_getrennt

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Seitenabstieg :: down  --  ASSUMED (walk-invariant)
  duty_2  W  Seitenabstieg :: leaf  --  ASSUMED (walk-invariant)
  duty_3  W  Seitenabstieg :: invariant wx_getrennt  --  ASSUMED (walk-invariant)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Pte" "P" => some .bool
  | .field "Pte" "RW" => some .bool
  | .field "Pte" "US" => some .bool
  | .field "Pte" "PWT" => some .bool
  | .field "Pte" "PCD" => some .bool
  | .field "Pte" "PS" => some .bool
  | .field "Pte" "roh" => some (.intIn 0 18446744073709551615)
  | .field "Pte" "NX" => some .bool
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

/-! ### `rechte_pruefen` -/

def rechte_pruefen_body : List Stmt :=
  [(.ret (some (.un .not (.bin .and (.fieldOf "Pte" "RW") (.un .not (.fieldOf "Pte" "NX"))))))]

/-- The precondition: the declared shapes and the `requires`. -/
def rechte_pruefen_pre : Expr :=
  (.lit (.bool true))

def rechte_pruefen_writes : List String := []

/-- What a caller of `rechte_pruefen` has to bring: a well-typed world and the precondition. -/
def rechte_pruefen_requires (t : State) : Prop := wellFormed t ∧ eval t rechte_pruefen_pre = some (.bool true)

/-- What `rechte_pruefen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def rechte_pruefen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `rechte_pruefen` -/

/-- **The duty of `rechte_pruefen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def rechte_pruefen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s rechte_pruefen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ rechte_pruefen_body s) = some s'
        ∧ rechte_pruefen_post s s' (finalValue (exec ρ rechte_pruefen_body s))

theorem rechte_pruefen_meets : rechte_pruefen_meets_statement := by
  unfold rechte_pruefen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Pte_RW, h_Pte_RW⟩ := WF_bool shapeOf s.world (.field "Pte" "RW") hwf rfl
  obtain ⟨n_Pte_NX, h_Pte_NX⟩ := WF_bool shapeOf s.world (.field "Pte" "NX") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [rechte_pruefen_pre, h_Pte_RW, h_Pte_NX]
  gabbro_auto [rechte_pruefen_body, rechte_pruefen_pre, rechte_pruefen_post, wellFormed, h_Pte_RW, h_Pte_NX, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "rechte_pruefen" rechte_pruefen_body
  ∧ Frame ρ "rechte_pruefen" rechte_pruefen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_rechte_pruefen : rechte_pruefen_meets_statement) :
    Contract ρ "rechte_pruefen" rechte_pruefen_requires rechte_pruefen_post := by
  obtain ⟨r_rechte_pruefen, fr_rechte_pruefen⟩ := hp
  have c_rechte_pruefen : Contract ρ "rechte_pruefen" rechte_pruefen_requires rechte_pruefen_post :=
    contract_of_duty ρ "rechte_pruefen" rechte_pruefen_body rechte_pruefen_requires rechte_pruefen_post r_rechte_pruefen
      (fun t ht => d_rechte_pruefen ρ t ht.1 ht.2)
  exact c_rechte_pruefen

end GabbroDuty.DutyF09