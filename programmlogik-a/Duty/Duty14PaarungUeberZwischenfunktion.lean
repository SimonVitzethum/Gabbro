/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/14-paarung-ueber-zwischenfunktion.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty14PaarungUeberZwischenfunktion

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Bericht" "daten" => some (.intIn 0 4294967295)
  | .global "FERTIG" => some .bool
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

/-! ### `abholen` -/

def abholen_body : List Stmt :=
  [(.awaitLoad "f" "FERTIG" ["b.daten"]), (.ret (some (.name "f")))]

/-- The precondition: the declared shapes and the `requires`. -/
def abholen_pre : Expr :=
  (.lit (.bool true))

def abholen_writes : List String := []

/-- What a caller of `abholen` has to bring: a well-typed world and the precondition. -/
def abholen_requires (t : State) : Prop := wellFormed t ∧ eval t abholen_pre = some (.bool true)

/-- What `abholen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abholen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `anstossen` -/

def anstossen_body : List Stmt :=
  [(.call "melden" ["b"] [(.name "b")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def anstossen_pre : Expr :=
  (.lit (.bool true))

def anstossen_writes : List String := ["Bericht", "FERTIG"]

/-- What a caller of `anstossen` has to bring: a well-typed world and the precondition. -/
def anstossen_requires (t : State) : Prop := wellFormed t ∧ eval t anstossen_pre = some (.bool true)

/-- What `anstossen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def anstossen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `melden` -/

def melden_body : List Stmt :=
  [(.publish "FERTIG" (.lit (.bool true)) ["b.daten"])]

/-- The precondition: the declared shapes and the `requires`. -/
def melden_pre : Expr :=
  (.lit (.bool true))

def melden_writes : List String := ["Bericht", "FERTIG"]

/-- What a caller of `melden` has to bring: a well-typed world and the precondition. -/
def melden_requires (t : State) : Prop := wellFormed t ∧ eval t melden_pre = some (.bool true)

/-- What `melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abholen` -/

/-- **The duty of `abholen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abholen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abholen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ abholen_body s) = some s'
        ∧ abholen_post s s' (finalValue (exec ρ abholen_body s))

theorem abholen_meets : abholen_meets_statement := by
  unfold abholen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [abholen_pre]
  gabbro_auto [abholen_body, abholen_pre, abholen_post, wellFormed, hall] using shapeOf

/-! ### `anstossen` -/

/-- **The duty of `anstossen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def anstossen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s anstossen_pre = some (.bool true))
    -- the contract of `melden`
    (c_melden : Contract ρ "melden" melden_requires melden_post)
    -- the frame of `melden`
    (fr_melden : Frame ρ "melden" melden_writes),
    ∃ s', finalState (exec ρ anstossen_body s) = some s'
        ∧ anstossen_post s s' (finalValue (exec ρ anstossen_body s))

theorem anstossen_meets : anstossen_meets_statement := by
  unfold anstossen_meets_statement
  intro ρ s hwf hpre c_melden fr_melden
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [anstossen_pre]
  gabbro_auto [anstossen_body, anstossen_pre, anstossen_post, wellFormed, melden_pre, melden_requires, melden_post, melden_writes, Frame_read _ _ _ fr_melden, hall] using shapeOf

/-! ### `melden` -/

/-- **The duty of `melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ melden_body s) = some s'
        ∧ melden_post s s' (finalValue (exec ρ melden_body s))

theorem melden_meets : melden_meets_statement := by
  unfold melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [melden_pre]
  gabbro_auto [melden_body, melden_pre, melden_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abholen" abholen_body
  ∧ Frame ρ "abholen" abholen_writes
  ∧ Runs ρ "anstossen" anstossen_body
  ∧ Frame ρ "anstossen" anstossen_writes
  ∧ Runs ρ "melden" melden_body
  ∧ Frame ρ "melden" melden_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abholen : abholen_meets_statement)
    (d_melden : melden_meets_statement)
    (d_anstossen : anstossen_meets_statement) :
    Contract ρ "abholen" abholen_requires abholen_post
    ∧ Contract ρ "melden" melden_requires melden_post
    ∧ Contract ρ "anstossen" anstossen_requires anstossen_post := by
  obtain ⟨r_abholen, fr_abholen, r_anstossen, fr_anstossen, r_melden, fr_melden⟩ := hp
  have c_abholen : Contract ρ "abholen" abholen_requires abholen_post :=
    contract_of_duty ρ "abholen" abholen_body abholen_requires abholen_post r_abholen
      (fun t ht => d_abholen ρ t ht.1 ht.2)
  have c_melden : Contract ρ "melden" melden_requires melden_post :=
    contract_of_duty ρ "melden" melden_body melden_requires melden_post r_melden
      (fun t ht => d_melden ρ t ht.1 ht.2)
  have c_anstossen : Contract ρ "anstossen" anstossen_requires anstossen_post :=
    contract_of_duty ρ "anstossen" anstossen_body anstossen_requires anstossen_post r_anstossen
      (fun t ht => d_anstossen ρ t ht.1 ht.2 c_melden fr_melden)
  exact ⟨c_abholen, c_melden, c_anstossen⟩

end GabbroDuty.Duty14PaarungUeberZwischenfunktion
