/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-besitz-zwei-typen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeBesitzZweiTypen

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

/-- `arm` -- a foreign body: its contract is an assumption. -/
def arm_pre : Expr :=
  (.lit (.bool true))

def arm_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)

def arm_writes : List String := ["b"]

def arm_requires (t : State) : Prop := wellFormed t ∧ eval t arm_pre = some (.bool true)

/-- `fertig` -- a foreign body: its contract is an assumption. -/
def fertig_pre : Expr :=
  (.lit (.bool true))

def fertig_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def fertig_writes : List String := ["b"]

def fertig_requires (t : State) : Prop := wellFormed t ∧ eval t fertig_pre = some (.bool true)

/-- `hole` -- a foreign body: its contract is an assumption. -/
def hole_pre : Expr :=
  (.hasShape "q" (.intIn 0 18446744073709551615))

def hole_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)

def hole_writes : List String := ["b"]

def hole_requires (t : State) : Prop := wellFormed t ∧ eval t hole_pre = some (.bool true)

/-- `hole_unbelegt` -- a foreign body: its contract is an assumption. -/
def hole_unbelegt_pre : Expr :=
  (.lit (.bool true))

def hole_unbelegt_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)

def hole_unbelegt_writes : List String := ["b"]

def hole_unbelegt_requires (t : State) : Prop := wellFormed t ∧ eval t hole_unbelegt_pre = some (.bool true)

/-- `schreibe` -- a foreign body: its contract is an assumption. -/
def schreibe_pre : Expr :=
  (.hasShape "v" (.intIn 0 255))

def schreibe_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)

def schreibe_writes : List String := ["b"]

def schreibe_requires (t : State) : Prop := wellFormed t ∧ eval t schreibe_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "arm" arm_requires arm_post
  ∧ Frame ρ "arm" arm_writes
  ∧ Contract ρ "fertig" fertig_requires fertig_post
  ∧ Frame ρ "fertig" fertig_writes
  ∧ Contract ρ "hole" hole_requires hole_post
  ∧ Frame ρ "hole" hole_writes
  ∧ Contract ρ "hole_unbelegt" hole_unbelegt_requires hole_unbelegt_post
  ∧ Frame ρ "hole_unbelegt" hole_unbelegt_writes
  ∧ Contract ρ "schreibe" schreibe_requires schreibe_post
  ∧ Frame ρ "schreibe" schreibe_writes

/-! ## The routines: body and contract -/

/-! ### `runde` -/

def runde_body : List Stmt :=
  [(.bindCall "b1" "schreibe" ["b", "v"] [(.name "b"), (.lit (.int 7))] (.hasShape "v" (.intIn 0 255))), (.bindCall "b2" "arm" ["b"] [(.name "b1")] (.lit (.bool true))), (.bindCall "q" "used_eintrag" ["roh"] [(.name "roh")] (.hasShape "roh" (.intIn 0 18446744073709551615))), (.bindCall "b3" "hole" ["b", "q"] [(.name "b2"), (.name "q")] (.hasShape "q" (.intIn 0 18446744073709551615))), (.bindCall "b4" "schreibe" ["b", "v"] [(.name "b3"), (.lit (.int 9))] (.hasShape "v" (.intIn 0 255))), (.call "fertig" ["b"] [(.name "b4")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def runde_pre : Expr :=
  (.hasShape "roh" (.intIn 0 18446744073709551615))

def runde_writes : List String := ["b"]

/-- What a caller of `runde` has to bring: a well-typed world and the precondition. -/
def runde_requires (t : State) : Prop := wellFormed t ∧ eval t runde_pre = some (.bool true)

/-- What `runde` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def runde_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `runde_unbelegt` -/

def runde_unbelegt_body : List Stmt :=
  [(.bindCall "b1" "arm" ["b"] [(.name "b")] (.lit (.bool true))), (.bindCall "b2" "hole_unbelegt" ["b"] [(.name "b1")] (.lit (.bool true))), (.call "fertig" ["b"] [(.name "b2")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def runde_unbelegt_pre : Expr :=
  (.lit (.bool true))

def runde_unbelegt_writes : List String := ["b"]

/-- What a caller of `runde_unbelegt` has to bring: a well-typed world and the precondition. -/
def runde_unbelegt_requires (t : State) : Prop := wellFormed t ∧ eval t runde_unbelegt_pre = some (.bool true)

/-- What `runde_unbelegt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def runde_unbelegt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `used_eintrag` -/

def used_eintrag_body : List Stmt :=
  [(.ret (some (.name "roh")))]

/-- The precondition: the declared shapes and the `requires`. -/
def used_eintrag_pre : Expr :=
  (.hasShape "roh" (.intIn 0 18446744073709551615))

def used_eintrag_writes : List String := []

/-- What a caller of `used_eintrag` has to bring: a well-typed world and the precondition. -/
def used_eintrag_requires (t : State) : Prop := wellFormed t ∧ eval t used_eintrag_pre = some (.bool true)

/-- What `used_eintrag` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def used_eintrag_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `runde` -/

/-- **The duty of `runde`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def runde_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s runde_pre = some (.bool true))
    -- the contract of `arm`
    (c_arm : Contract ρ "arm" arm_requires arm_post)
    -- the frame of `arm`
    (fr_arm : Frame ρ "arm" arm_writes)
    -- the contract of `fertig`
    (c_fertig : Contract ρ "fertig" fertig_requires fertig_post)
    -- the frame of `fertig`
    (fr_fertig : Frame ρ "fertig" fertig_writes)
    -- the contract of `hole`
    (c_hole : Contract ρ "hole" hole_requires hole_post)
    -- the frame of `hole`
    (fr_hole : Frame ρ "hole" hole_writes)
    -- the contract of `schreibe`
    (c_schreibe : Contract ρ "schreibe" schreibe_requires schreibe_post)
    -- the frame of `schreibe`
    (fr_schreibe : Frame ρ "schreibe" schreibe_writes)
    -- the contract of `used_eintrag`
    (c_used_eintrag : Contract ρ "used_eintrag" used_eintrag_requires used_eintrag_post)
    -- the frame of `used_eintrag`
    (fr_used_eintrag : Frame ρ "used_eintrag" used_eintrag_writes),
    ∃ s', finalState (exec ρ runde_body s) = some s'
        ∧ runde_post s s' (finalValue (exec ρ runde_body s))

theorem runde_meets : runde_meets_statement := by
  unfold runde_meets_statement
  intro ρ s hwf hpre c_arm fr_arm c_fertig fr_fertig c_hole fr_hole c_schreibe fr_schreibe c_used_eintrag fr_used_eintrag
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_roh, e_roh, lo_roh, hi_roh⟩ := shape_intIn s "roh" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [runde_pre, e_roh]
  gabbro_auto [runde_body, runde_pre, runde_post, wellFormed, arm_pre, arm_requires, arm_post, arm_writes, Frame_read _ _ _ fr_arm, fertig_pre, fertig_requires, fertig_post, fertig_writes, Frame_read _ _ _ fr_fertig, hole_pre, hole_requires, hole_post, hole_writes, Frame_read _ _ _ fr_hole, schreibe_pre, schreibe_requires, schreibe_post, schreibe_writes, Frame_read _ _ _ fr_schreibe, used_eintrag_pre, used_eintrag_requires, used_eintrag_post, used_eintrag_writes, Frame_read _ _ _ fr_used_eintrag, e_roh, hall] using shapeOf

/-! ### `runde_unbelegt` -/

/-- **The duty of `runde_unbelegt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def runde_unbelegt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s runde_unbelegt_pre = some (.bool true))
    -- the contract of `arm`
    (c_arm : Contract ρ "arm" arm_requires arm_post)
    -- the frame of `arm`
    (fr_arm : Frame ρ "arm" arm_writes)
    -- the contract of `fertig`
    (c_fertig : Contract ρ "fertig" fertig_requires fertig_post)
    -- the frame of `fertig`
    (fr_fertig : Frame ρ "fertig" fertig_writes)
    -- the contract of `hole_unbelegt`
    (c_hole_unbelegt : Contract ρ "hole_unbelegt" hole_unbelegt_requires hole_unbelegt_post)
    -- the frame of `hole_unbelegt`
    (fr_hole_unbelegt : Frame ρ "hole_unbelegt" hole_unbelegt_writes),
    ∃ s', finalState (exec ρ runde_unbelegt_body s) = some s'
        ∧ runde_unbelegt_post s s' (finalValue (exec ρ runde_unbelegt_body s))

theorem runde_unbelegt_meets : runde_unbelegt_meets_statement := by
  unfold runde_unbelegt_meets_statement
  intro ρ s hwf hpre c_arm fr_arm c_fertig fr_fertig c_hole_unbelegt fr_hole_unbelegt
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [runde_unbelegt_pre]
  gabbro_auto [runde_unbelegt_body, runde_unbelegt_pre, runde_unbelegt_post, wellFormed, arm_pre, arm_requires, arm_post, arm_writes, Frame_read _ _ _ fr_arm, fertig_pre, fertig_requires, fertig_post, fertig_writes, Frame_read _ _ _ fr_fertig, hole_unbelegt_pre, hole_unbelegt_requires, hole_unbelegt_post, hole_unbelegt_writes, Frame_read _ _ _ fr_hole_unbelegt, hall] using shapeOf

/-! ### `used_eintrag` -/

/-- **The duty of `used_eintrag`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def used_eintrag_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s used_eintrag_pre = some (.bool true)),
    ∃ s', finalState (exec ρ used_eintrag_body s) = some s'
        ∧ used_eintrag_post s s' (finalValue (exec ρ used_eintrag_body s))

theorem used_eintrag_meets : used_eintrag_meets_statement := by
  unfold used_eintrag_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_roh, e_roh, lo_roh, hi_roh⟩ := shape_intIn s "roh" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [used_eintrag_pre, e_roh]
  gabbro_auto [used_eintrag_body, used_eintrag_pre, used_eintrag_post, wellFormed, e_roh, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "runde" runde_body
  ∧ Frame ρ "runde" runde_writes
  ∧ Runs ρ "runde_unbelegt" runde_unbelegt_body
  ∧ Frame ρ "runde_unbelegt" runde_unbelegt_writes
  ∧ Runs ρ "used_eintrag" used_eintrag_body
  ∧ Frame ρ "used_eintrag" used_eintrag_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_runde_unbelegt : runde_unbelegt_meets_statement)
    (d_used_eintrag : used_eintrag_meets_statement)
    (d_runde : runde_meets_statement) :
    Contract ρ "runde_unbelegt" runde_unbelegt_requires runde_unbelegt_post
    ∧ Contract ρ "used_eintrag" used_eintrag_requires used_eintrag_post
    ∧ Contract ρ "runde" runde_requires runde_post := by
  obtain ⟨r_runde, fr_runde, r_runde_unbelegt, fr_runde_unbelegt, r_used_eintrag, fr_used_eintrag⟩ := hp
  obtain ⟨c_arm, fr_arm, c_fertig, fr_fertig, c_hole, fr_hole, c_hole_unbelegt, fr_hole_unbelegt, c_schreibe, fr_schreibe⟩ := ha
  have c_runde_unbelegt : Contract ρ "runde_unbelegt" runde_unbelegt_requires runde_unbelegt_post :=
    contract_of_duty ρ "runde_unbelegt" runde_unbelegt_body runde_unbelegt_requires runde_unbelegt_post r_runde_unbelegt
      (fun t ht => d_runde_unbelegt ρ t ht.1 ht.2 c_arm fr_arm c_fertig fr_fertig c_hole_unbelegt fr_hole_unbelegt)
  have c_used_eintrag : Contract ρ "used_eintrag" used_eintrag_requires used_eintrag_post :=
    contract_of_duty ρ "used_eintrag" used_eintrag_body used_eintrag_requires used_eintrag_post r_used_eintrag
      (fun t ht => d_used_eintrag ρ t ht.1 ht.2)
  have c_runde : Contract ρ "runde" runde_requires runde_post :=
    contract_of_duty ρ "runde" runde_body runde_requires runde_post r_runde
      (fun t ht => d_runde ρ t ht.1 ht.2 c_arm fr_arm c_fertig fr_fertig c_hole fr_hole c_schreibe fr_schreibe c_used_eintrag fr_used_eintrag)
  exact ⟨c_runde_unbelegt, c_used_eintrag, c_runde⟩

end GabbroDuty.DutyProbeBesitzZweiTypen
