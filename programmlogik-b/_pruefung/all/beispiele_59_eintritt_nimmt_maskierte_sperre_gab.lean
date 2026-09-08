/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/59-eintritt-nimmt-maskierte-sperre.gab  total 2  goals 2  refused 0
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

namespace GabbroDuty.Duty59EintrittNimmtMaskierteSperre

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  takt_verteiler :: zaehle requires #1  --  carried by `takt_verteiler_meets`
  duty_2  V  ruf_verteiler :: bearbeite requires #1  --  carried by `ruf_verteiler_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Auftraege" _ "stand" => some (.intIn 0 18446744073709551615)
  | .slot "Takte" _ "stand" => some (.intIn 0 18446744073709551615)
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

/-! ### `bearbeite` -/

def bearbeite_body : List Stmt :=
  [(.assign "Auftraege" (.name "i") "stand" (.lit (.int 1)))]

/-- The precondition: the declared shapes and the `requires`. -/
def bearbeite_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 15)) (.lit (.bool true)))

def bearbeite_writes : List String := ["Auftraege"]

/-- What a caller of `bearbeite` has to bring: a well-typed world and the precondition. -/
def bearbeite_requires (t : State) : Prop := wellFormed t ∧ eval t bearbeite_pre = some (.bool true)

/-- What `bearbeite` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bearbeite_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `ruf_verteiler` -/

def ruf_verteiler_body : List Stmt :=
  [(.locked "RING" [(.call "bearbeite" ["i"] [(.lit (.int 0))] (.bin .and (.hasShape "i" (.intIn 0 15)) (.lit (.bool true))))])]

/-- The precondition: the declared shapes and the `requires`. -/
def ruf_verteiler_pre : Expr :=
  (.lit (.bool true))

def ruf_verteiler_writes : List String := ["Auftraege"]

/-- What a caller of `ruf_verteiler` has to bring: a well-typed world and the precondition. -/
def ruf_verteiler_requires (t : State) : Prop := wellFormed t ∧ eval t ruf_verteiler_pre = some (.bool true)

/-- What `ruf_verteiler` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ruf_verteiler_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `takt_verteiler` -/

def takt_verteiler_body : List Stmt :=
  [(.locked "TAKT" [(.call "zaehle" ["i"] [(.lit (.int 0))] (.bin .and (.hasShape "i" (.intIn 0 63)) (.lit (.bool true))))])]

/-- The precondition: the declared shapes and the `requires`. -/
def takt_verteiler_pre : Expr :=
  (.lit (.bool true))

def takt_verteiler_writes : List String := ["Takte"]

/-- What a caller of `takt_verteiler` has to bring: a well-typed world and the precondition. -/
def takt_verteiler_requires (t : State) : Prop := wellFormed t ∧ eval t takt_verteiler_pre = some (.bool true)

/-- What `takt_verteiler` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def takt_verteiler_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `zaehle` -/

def zaehle_body : List Stmt :=
  [(.assign "Takte" (.name "i") "stand" (.lit (.int 1)))]

/-- The precondition: the declared shapes and the `requires`. -/
def zaehle_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 63)) (.lit (.bool true)))

def zaehle_writes : List String := ["Takte"]

/-- What a caller of `zaehle` has to bring: a well-typed world and the precondition. -/
def zaehle_requires (t : State) : Prop := wellFormed t ∧ eval t zaehle_pre = some (.bool true)

/-- What `zaehle` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zaehle_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `bearbeite` -/

/-- **The duty of `bearbeite`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def bearbeite_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s bearbeite_pre = some (.bool true)),
    ∃ s', finalState (exec ρ bearbeite_body s) = some s'
        ∧ bearbeite_post s s' (finalValue (exec ρ bearbeite_body s))

theorem bearbeite_meets : bearbeite_meets_statement := by
  unfold bearbeite_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [bearbeite_pre, e_i]
  gabbro_auto [bearbeite_body, bearbeite_pre, bearbeite_post, wellFormed, e_i, hall] using shapeOf

/-! ### `ruf_verteiler` -/

/-- **The duty of `ruf_verteiler`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def ruf_verteiler_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s ruf_verteiler_pre = some (.bool true))
    -- the contract of `bearbeite`
    (c_bearbeite : Contract ρ "bearbeite" bearbeite_requires bearbeite_post)
    -- the frame of `bearbeite`
    (fr_bearbeite : Frame ρ "bearbeite" bearbeite_writes),
    ∃ s', finalState (exec ρ ruf_verteiler_body s) = some s'
        ∧ ruf_verteiler_post s s' (finalValue (exec ρ ruf_verteiler_body s))

theorem ruf_verteiler_meets : ruf_verteiler_meets_statement := by
  unfold ruf_verteiler_meets_statement
  intro ρ s hwf hpre c_bearbeite fr_bearbeite
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [ruf_verteiler_pre]
  gabbro_auto [ruf_verteiler_body, ruf_verteiler_pre, ruf_verteiler_post, wellFormed, bearbeite_pre, bearbeite_requires, bearbeite_post, bearbeite_writes, Frame_read _ _ _ fr_bearbeite, hall] using shapeOf

/-! ### `takt_verteiler` -/

/-- **The duty of `takt_verteiler`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def takt_verteiler_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s takt_verteiler_pre = some (.bool true))
    -- the contract of `zaehle`
    (c_zaehle : Contract ρ "zaehle" zaehle_requires zaehle_post)
    -- the frame of `zaehle`
    (fr_zaehle : Frame ρ "zaehle" zaehle_writes),
    ∃ s', finalState (exec ρ takt_verteiler_body s) = some s'
        ∧ takt_verteiler_post s s' (finalValue (exec ρ takt_verteiler_body s))

theorem takt_verteiler_meets : takt_verteiler_meets_statement := by
  unfold takt_verteiler_meets_statement
  intro ρ s hwf hpre c_zaehle fr_zaehle
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [takt_verteiler_pre]
  gabbro_auto [takt_verteiler_body, takt_verteiler_pre, takt_verteiler_post, wellFormed, zaehle_pre, zaehle_requires, zaehle_post, zaehle_writes, Frame_read _ _ _ fr_zaehle, hall] using shapeOf

/-! ### `zaehle` -/

/-- **The duty of `zaehle`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def zaehle_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s zaehle_pre = some (.bool true)),
    ∃ s', finalState (exec ρ zaehle_body s) = some s'
        ∧ zaehle_post s s' (finalValue (exec ρ zaehle_body s))

theorem zaehle_meets : zaehle_meets_statement := by
  unfold zaehle_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [zaehle_pre, e_i]
  gabbro_auto [zaehle_body, zaehle_pre, zaehle_post, wellFormed, e_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "bearbeite" bearbeite_body
  ∧ Frame ρ "bearbeite" bearbeite_writes
  ∧ Runs ρ "ruf_verteiler" ruf_verteiler_body
  ∧ Frame ρ "ruf_verteiler" ruf_verteiler_writes
  ∧ Runs ρ "takt_verteiler" takt_verteiler_body
  ∧ Frame ρ "takt_verteiler" takt_verteiler_writes
  ∧ Runs ρ "zaehle" zaehle_body
  ∧ Frame ρ "zaehle" zaehle_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_bearbeite : bearbeite_meets_statement)
    (d_ruf_verteiler : ruf_verteiler_meets_statement)
    (d_zaehle : zaehle_meets_statement)
    (d_takt_verteiler : takt_verteiler_meets_statement) :
    Contract ρ "bearbeite" bearbeite_requires bearbeite_post
    ∧ Contract ρ "ruf_verteiler" ruf_verteiler_requires ruf_verteiler_post
    ∧ Contract ρ "zaehle" zaehle_requires zaehle_post
    ∧ Contract ρ "takt_verteiler" takt_verteiler_requires takt_verteiler_post := by
  obtain ⟨r_bearbeite, fr_bearbeite, r_ruf_verteiler, fr_ruf_verteiler, r_takt_verteiler, fr_takt_verteiler, r_zaehle, fr_zaehle⟩ := hp
  have c_bearbeite : Contract ρ "bearbeite" bearbeite_requires bearbeite_post :=
    contract_of_duty ρ "bearbeite" bearbeite_body bearbeite_requires bearbeite_post r_bearbeite
      (fun t ht => d_bearbeite ρ t ht.1 ht.2)
  have c_ruf_verteiler : Contract ρ "ruf_verteiler" ruf_verteiler_requires ruf_verteiler_post :=
    contract_of_duty ρ "ruf_verteiler" ruf_verteiler_body ruf_verteiler_requires ruf_verteiler_post r_ruf_verteiler
      (fun t ht => d_ruf_verteiler ρ t ht.1 ht.2 c_bearbeite fr_bearbeite)
  have c_zaehle : Contract ρ "zaehle" zaehle_requires zaehle_post :=
    contract_of_duty ρ "zaehle" zaehle_body zaehle_requires zaehle_post r_zaehle
      (fun t ht => d_zaehle ρ t ht.1 ht.2)
  have c_takt_verteiler : Contract ρ "takt_verteiler" takt_verteiler_requires takt_verteiler_post :=
    contract_of_duty ρ "takt_verteiler" takt_verteiler_body takt_verteiler_requires takt_verteiler_post r_takt_verteiler
      (fun t ht => d_takt_verteiler ρ t ht.1 ht.2 c_zaehle fr_zaehle)
  exact ⟨c_bearbeite, c_ruf_verteiler, c_zaehle, c_takt_verteiler⟩

end GabbroDuty.Duty59EintrittNimmtMaskierteSperre
