/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/36-asm.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty36Asm

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "GERAET" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `ausgeben` -- a foreign body: its contract is an assumption. -/
def ausgeben_pre : Expr :=
  (.bin .and (.hasShape "tor" (.intIn 0 65535)) (.hasShape "wert" (.intIn 0 255)))

def ausgeben_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def ausgeben_writes : List String := ["GERAET"]

def ausgeben_requires (t : State) : Prop := wellFormed t ∧ eval t ausgeben_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "ausgeben" ausgeben_requires ausgeben_post
  ∧ Frame ρ "ausgeben" ausgeben_writes

/-! ## The routines: body and contract -/

/-! ### `melden` -/

def melden_body : List Stmt :=
  [(.call "ausgeben" ["tor", "wert"] [(.lit (.int 112)), (.name "w")] (.bin .and (.hasShape "tor" (.intIn 0 65535)) (.hasShape "wert" (.intIn 0 255))))]

/-- The precondition: the declared shapes and the `requires`. -/
def melden_pre : Expr :=
  (.hasShape "w" (.intIn 0 255))

def melden_writes : List String := ["GERAET"]

/-- What a caller of `melden` has to bring: a well-typed world and the precondition. -/
def melden_requires (t : State) : Prop := wellFormed t ∧ eval t melden_pre = some (.bool true)

/-- What `melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `melden` -/

/-- **The duty of `melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s melden_pre = some (.bool true))
    -- the contract of `ausgeben`
    (c_ausgeben : Contract ρ "ausgeben" ausgeben_requires ausgeben_post)
    -- the frame of `ausgeben`
    (fr_ausgeben : Frame ρ "ausgeben" ausgeben_writes),
    ∃ s', finalState (exec ρ melden_body s) = some s'
        ∧ melden_post s s' (finalValue (exec ρ melden_body s))

theorem melden_meets : melden_meets_statement := by
  unfold melden_meets_statement
  intro ρ s hwf hpre c_ausgeben fr_ausgeben
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [melden_pre, e_w]
  gabbro_auto [melden_body, melden_pre, melden_post, wellFormed, ausgeben_pre, ausgeben_requires, ausgeben_post, ausgeben_writes, Frame_read _ _ _ fr_ausgeben, e_w, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "melden" melden_body
  ∧ Frame ρ "melden" melden_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_melden : melden_meets_statement) :
    Contract ρ "melden" melden_requires melden_post := by
  obtain ⟨r_melden, fr_melden⟩ := hp
  obtain ⟨c_ausgeben, fr_ausgeben⟩ := ha
  have c_melden : Contract ρ "melden" melden_requires melden_post :=
    contract_of_duty ρ "melden" melden_body melden_requires melden_post r_melden
      (fun t ht => d_melden ρ t ht.1 ht.2 c_ausgeben fr_ausgeben)
  exact c_melden

end GabbroDuty.Duty36Asm