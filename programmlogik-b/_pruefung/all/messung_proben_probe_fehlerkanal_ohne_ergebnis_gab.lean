/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-fehlerkanal-ohne-ergebnis.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeFehlerkanalOhneErgebnis

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Zelle" "n" => some (.intIn 0 4294967295)
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

/-! ### `rufer` -/

def rufer_body : List Stmt :=
  [(.bindCallElse "ok" "tut_was" ["z"] [(.name "z")] (.lit (.bool true)) "e" [(.ret (some (.name "e")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def rufer_pre : Expr :=
  (.lit (.bool true))

def rufer_writes : List String := ["Zelle"]

/-- What a caller of `rufer` has to bring: a well-typed world and the precondition. -/
def rufer_requires (t : State) : Prop := wellFormed t ∧ eval t rufer_pre = some (.bool true)

/-- What `rufer` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def rufer_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = none ∨ ∃ e, r = some (.reason e))

/-! ### `tut_was` -/

def tut_was_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.fieldOf "Zelle" "n") (.lit (.int 0))) (.bin .le (.fieldOf "Zelle" "n") (.lit (.int 100)))) [] [(.ret (some (.lit (.reason "Boese"))))]), (.assignField "Zelle" "n" (.bin .add (.fieldOf "Zelle" "n") (.lit (.int 1))))]

/-- The precondition: the declared shapes and the `requires`. -/
def tut_was_pre : Expr :=
  (.lit (.bool true))

def tut_was_writes : List String := ["Zelle"]

/-- What a caller of `tut_was` has to bring: a well-typed world and the precondition. -/
def tut_was_requires (t : State) : Prop := wellFormed t ∧ eval t tut_was_pre = some (.bool true)

/-- What `tut_was` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tut_was_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = none ∨ ∃ e, r = some (.reason e))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `rufer` -/

/-- **The duty of `rufer`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def rufer_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s rufer_pre = some (.bool true))
    -- the contract of `tut_was`
    (c_tut_was : Contract ρ "tut_was" tut_was_requires tut_was_post)
    -- the frame of `tut_was`
    (fr_tut_was : Frame ρ "tut_was" tut_was_writes),
    ∃ s', finalState (exec ρ rufer_body s) = some s'
        ∧ rufer_post s s' (finalValue (exec ρ rufer_body s))

theorem rufer_meets : rufer_meets_statement := by
  unfold rufer_meets_statement
  intro ρ s hwf hpre c_tut_was fr_tut_was
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [rufer_pre]
  gabbro_auto [rufer_body, rufer_pre, rufer_post, wellFormed, tut_was_pre, tut_was_requires, tut_was_post, tut_was_writes, Frame_read _ _ _ fr_tut_was, hall] using shapeOf

/-! ### `tut_was` -/

/-- **The duty of `tut_was`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def tut_was_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s tut_was_pre = some (.bool true)),
    ∃ s', finalState (exec ρ tut_was_body s) = some s'
        ∧ tut_was_post s s' (finalValue (exec ρ tut_was_body s))

theorem tut_was_meets : tut_was_meets_statement := by
  unfold tut_was_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Zelle_n, h_Zelle_n, lo_Zelle_n, hi_Zelle_n⟩ := WF_intIn shapeOf s.world (.field "Zelle" "n") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [tut_was_pre, h_Zelle_n]
  gabbro_auto [tut_was_body, tut_was_pre, tut_was_post, wellFormed, h_Zelle_n, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "rufer" rufer_body
  ∧ Frame ρ "rufer" rufer_writes
  ∧ Runs ρ "tut_was" tut_was_body
  ∧ Frame ρ "tut_was" tut_was_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_tut_was : tut_was_meets_statement)
    (d_rufer : rufer_meets_statement) :
    Contract ρ "tut_was" tut_was_requires tut_was_post
    ∧ Contract ρ "rufer" rufer_requires rufer_post := by
  obtain ⟨r_rufer, fr_rufer, r_tut_was, fr_tut_was⟩ := hp
  have c_tut_was : Contract ρ "tut_was" tut_was_requires tut_was_post :=
    contract_of_duty ρ "tut_was" tut_was_body tut_was_requires tut_was_post r_tut_was
      (fun t ht => d_tut_was ρ t ht.1 ht.2)
  have c_rufer : Contract ρ "rufer" rufer_requires rufer_post :=
    contract_of_duty ρ "rufer" rufer_body rufer_requires rufer_post r_rufer
      (fun t ht => d_rufer ρ t ht.1 ht.2 c_tut_was fr_tut_was)
  exact ⟨c_tut_was, c_rufer⟩

end GabbroDuty.DutyProbeFehlerkanalOhneErgebnis
