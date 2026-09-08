/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-match-ruf.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeMatchRuf

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

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `entschluessle` -- a foreign body: its contract is an assumption. -/
def entschluessle_pre : Expr :=
  (.hasShape "w" (.intIn 0 18446744073709551615))

def entschluessle_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ t p, r = some (.tagged t p) ∧ Shape.caseOk [("Info", none), ("Read", none), ("Stop", none)] t p = true)

def entschluessle_writes : List String := []

def entschluessle_requires (t : State) : Prop := wellFormed t ∧ eval t entschluessle_pre = some (.bool true)

/-- `melde` -- a foreign body: its contract is an assumption. -/
def melde_pre : Expr :=
  (.hasShape "w" (.intIn 0 18446744073709551615))

def melde_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def melde_writes : List String := []

def melde_requires (t : State) : Prop := wellFormed t ∧ eval t melde_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "entschluessle" entschluessle_requires entschluessle_post
  ∧ Frame ρ "entschluessle" entschluessle_writes
  ∧ Contract ρ "melde" melde_requires melde_post
  ∧ Frame ρ "melde" melde_writes

/-! ## The routines: body and contract -/

/-! ### `bediene` -/

def bediene_body : List Stmt :=
  [(.bindCall "#m1" "entschluessle" ["w"] [(.name "w")] (.hasShape "w" (.intIn 0 18446744073709551615))), (.onTag (.name "#m1") [("Info", none, [(.call "melde" ["w"] [(.lit (.int 1))] (.hasShape "w" (.intIn 0 18446744073709551615)))]), ("Read", none, [(.call "melde" ["w"] [(.lit (.int 2))] (.hasShape "w" (.intIn 0 18446744073709551615)))]), ("Stop", none, [(.call "melde" ["w"] [(.lit (.int 3))] (.hasShape "w" (.intIn 0 18446744073709551615)))])])]

/-- The precondition: the declared shapes and the `requires`. -/
def bediene_pre : Expr :=
  (.hasShape "w" (.intIn 0 18446744073709551615))

def bediene_writes : List String := []

/-- What a caller of `bediene` has to bring: a well-typed world and the precondition. -/
def bediene_requires (t : State) : Prop := wellFormed t ∧ eval t bediene_pre = some (.bool true)

/-- What `bediene` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bediene_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `bediene` -/

/-- **The duty of `bediene`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def bediene_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s bediene_pre = some (.bool true))
    -- the contract of `entschluessle`
    (c_entschluessle : Contract ρ "entschluessle" entschluessle_requires entschluessle_post)
    -- the frame of `entschluessle`
    (fr_entschluessle : Frame ρ "entschluessle" entschluessle_writes)
    -- the contract of `melde`
    (c_melde : Contract ρ "melde" melde_requires melde_post)
    -- the frame of `melde`
    (fr_melde : Frame ρ "melde" melde_writes),
    ∃ s', finalState (exec ρ bediene_body s) = some s'
        ∧ bediene_post s s' (finalValue (exec ρ bediene_body s))

theorem bediene_meets : bediene_meets_statement := by
  unfold bediene_meets_statement
  intro ρ s hwf hpre c_entschluessle fr_entschluessle c_melde fr_melde
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [bediene_pre, e_w]
  gabbro_auto [bediene_body, bediene_pre, bediene_post, wellFormed, entschluessle_pre, entschluessle_requires, entschluessle_post, entschluessle_writes, Frame_read _ _ _ fr_entschluessle, melde_pre, melde_requires, melde_post, melde_writes, Frame_read _ _ _ fr_melde, e_w, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "bediene" bediene_body
  ∧ Frame ρ "bediene" bediene_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_bediene : bediene_meets_statement) :
    Contract ρ "bediene" bediene_requires bediene_post := by
  obtain ⟨r_bediene, fr_bediene⟩ := hp
  obtain ⟨c_entschluessle, fr_entschluessle, c_melde, fr_melde⟩ := ha
  have c_bediene : Contract ρ "bediene" bediene_requires bediene_post :=
    contract_of_duty ρ "bediene" bediene_body bediene_requires bediene_post r_bediene
      (fun t ht => d_bediene ρ t ht.1 ht.2 c_entschluessle fr_entschluessle c_melde fr_melde)
  exact c_bediene

end GabbroDuty.DutyProbeMatchRuf