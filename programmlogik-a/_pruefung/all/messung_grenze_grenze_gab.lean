/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/grenze/grenze.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyGrenze

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Fach" _ "marke" => some (.intIn 0 4294967295)
  | .slot "Fach" _ "gueltig" => some .bool
  | .slot "Fach" _ "breit" => some (.intIn 0 18446744073709551615)
  | .slot "Fach" _ "schmal" => some (.intIn 0 255)
  | .slot "Plan" _ "wert" => some (.intIn 0 4294967295)
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

/-! ### `fremd_schreiben` -/

def fremd_schreiben_body : List Stmt :=
  [(.assign "Fach" (.name "i") "marke" (.name "w")), (.ret (some (.place "Fach" (.name "i") "marke")))]

/-- The precondition: the declared shapes and the `requires`. -/
def fremd_schreiben_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 7)) (.hasShape "w" (.intIn 0 4294967295)))

def fremd_schreiben_writes : List String := ["Fach"]

/-- What a caller of `fremd_schreiben` has to bring: a well-typed world and the precondition. -/
def fremd_schreiben_requires (t : State) : Prop := wellFormed t ∧ eval t fremd_schreiben_pre = some (.bool true)

/-- What `fremd_schreiben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fremd_schreiben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `lies_marke` -/

def lies_marke_body : List Stmt :=
  [(.ret (some (.place "Fach" (.name "i") "marke")))]

/-- The precondition: the declared shapes and the `requires`. -/
def lies_marke_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def lies_marke_writes : List String := []

/-- What a caller of `lies_marke` has to bring: a well-typed world and the precondition. -/
def lies_marke_requires (t : State) : Prop := wellFormed t ∧ eval t lies_marke_pre = some (.bool true)

/-- What `lies_marke` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def lies_marke_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `misch` -/

def misch_body : List Stmt :=
  [(.assign "Fach" (.name "i") "marke" (.lit (.int 1))), (.assign "Fach" (.name "i") "marke" (.lit (.int 2))), (.ret (some (.place "Fach" (.name "i") "marke")))]

/-- The precondition: the declared shapes and the `requires`. -/
def misch_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def misch_writes : List String := ["Fach"]

/-- What a caller of `misch` has to bring: a well-typed world and the precondition. -/
def misch_requires (t : State) : Prop := wellFormed t ∧ eval t misch_pre = some (.bool true)

/-- What `misch` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def misch_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `rangtreu` -/

def rangtreu_body : List Stmt :=
  [(.locked "A" [(.locked "B" [(.assign "Fach" (.name "i") "marke" (.name "w")), (.assign "Plan" (.name "i") "wert" (.name "w"))])])]

/-- The precondition: the declared shapes and the `requires`. -/
def rangtreu_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 7)) (.hasShape "w" (.intIn 0 4294967295)))

def rangtreu_writes : List String := ["Fach", "Plan"]

/-- What a caller of `rangtreu` has to bring: a well-typed world and the precondition. -/
def rangtreu_requires (t : State) : Prop := wellFormed t ∧ eval t rangtreu_pre = some (.bool true)

/-- What `rangtreu` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def rangtreu_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `fremd_schreiben` -/

/-- **The duty of `fremd_schreiben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def fremd_schreiben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s fremd_schreiben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ fremd_schreiben_body s) = some s'
        ∧ fremd_schreiben_post s s' (finalValue (exec ρ fremd_schreiben_body s))

theorem fremd_schreiben_meets : fremd_schreiben_meets_statement := by
  unfold fremd_schreiben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  obtain ⟨n_Fach_marke_i, h_Fach_marke_i, lo_Fach_marke_i, hi_Fach_marke_i⟩ := WF_intIn shapeOf s.world (.slot "Fach" w_i "marke") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [fremd_schreiben_pre, e_i, e_w, h_Fach_marke_i]
  gabbro_auto [fremd_schreiben_body, fremd_schreiben_pre, fremd_schreiben_post, wellFormed, e_i, e_w, h_Fach_marke_i, hall] using shapeOf

/-! ### `lies_marke` -/

/-- **The duty of `lies_marke`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def lies_marke_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s lies_marke_pre = some (.bool true)),
    ∃ s', finalState (exec ρ lies_marke_body s) = some s'
        ∧ lies_marke_post s s' (finalValue (exec ρ lies_marke_body s))

theorem lies_marke_meets : lies_marke_meets_statement := by
  unfold lies_marke_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Fach_marke_i, h_Fach_marke_i, lo_Fach_marke_i, hi_Fach_marke_i⟩ := WF_intIn shapeOf s.world (.slot "Fach" w_i "marke") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lies_marke_pre, e_i, h_Fach_marke_i]
  gabbro_auto [lies_marke_body, lies_marke_pre, lies_marke_post, wellFormed, e_i, h_Fach_marke_i, hall] using shapeOf

/-! ### `misch` -/

/-- **The duty of `misch`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def misch_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s misch_pre = some (.bool true)),
    ∃ s', finalState (exec ρ misch_body s) = some s'
        ∧ misch_post s s' (finalValue (exec ρ misch_body s))

theorem misch_meets : misch_meets_statement := by
  unfold misch_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Fach_marke_i, h_Fach_marke_i, lo_Fach_marke_i, hi_Fach_marke_i⟩ := WF_intIn shapeOf s.world (.slot "Fach" w_i "marke") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [misch_pre, e_i, h_Fach_marke_i]
  gabbro_auto [misch_body, misch_pre, misch_post, wellFormed, e_i, h_Fach_marke_i, hall] using shapeOf

/-! ### `rangtreu` -/

/-- **The duty of `rangtreu`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def rangtreu_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s rangtreu_pre = some (.bool true)),
    ∃ s', finalState (exec ρ rangtreu_body s) = some s'
        ∧ rangtreu_post s s' (finalValue (exec ρ rangtreu_body s))

theorem rangtreu_meets : rangtreu_meets_statement := by
  unfold rangtreu_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [rangtreu_pre, e_i, e_w]
  gabbro_auto [rangtreu_body, rangtreu_pre, rangtreu_post, wellFormed, e_i, e_w, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "fremd_schreiben" fremd_schreiben_body
  ∧ Frame ρ "fremd_schreiben" fremd_schreiben_writes
  ∧ Runs ρ "lies_marke" lies_marke_body
  ∧ Frame ρ "lies_marke" lies_marke_writes
  ∧ Runs ρ "misch" misch_body
  ∧ Frame ρ "misch" misch_writes
  ∧ Runs ρ "rangtreu" rangtreu_body
  ∧ Frame ρ "rangtreu" rangtreu_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_fremd_schreiben : fremd_schreiben_meets_statement)
    (d_lies_marke : lies_marke_meets_statement)
    (d_misch : misch_meets_statement)
    (d_rangtreu : rangtreu_meets_statement) :
    Contract ρ "fremd_schreiben" fremd_schreiben_requires fremd_schreiben_post
    ∧ Contract ρ "lies_marke" lies_marke_requires lies_marke_post
    ∧ Contract ρ "misch" misch_requires misch_post
    ∧ Contract ρ "rangtreu" rangtreu_requires rangtreu_post := by
  obtain ⟨r_fremd_schreiben, fr_fremd_schreiben, r_lies_marke, fr_lies_marke, r_misch, fr_misch, r_rangtreu, fr_rangtreu⟩ := hp
  have c_fremd_schreiben : Contract ρ "fremd_schreiben" fremd_schreiben_requires fremd_schreiben_post :=
    contract_of_duty ρ "fremd_schreiben" fremd_schreiben_body fremd_schreiben_requires fremd_schreiben_post r_fremd_schreiben
      (fun t ht => d_fremd_schreiben ρ t ht.1 ht.2)
  have c_lies_marke : Contract ρ "lies_marke" lies_marke_requires lies_marke_post :=
    contract_of_duty ρ "lies_marke" lies_marke_body lies_marke_requires lies_marke_post r_lies_marke
      (fun t ht => d_lies_marke ρ t ht.1 ht.2)
  have c_misch : Contract ρ "misch" misch_requires misch_post :=
    contract_of_duty ρ "misch" misch_body misch_requires misch_post r_misch
      (fun t ht => d_misch ρ t ht.1 ht.2)
  have c_rangtreu : Contract ρ "rangtreu" rangtreu_requires rangtreu_post :=
    contract_of_duty ρ "rangtreu" rangtreu_body rangtreu_requires rangtreu_post r_rangtreu
      (fun t ht => d_rangtreu ρ t ht.1 ht.2)
  exact ⟨c_fremd_schreiben, c_lies_marke, c_misch, c_rangtreu⟩

end GabbroDuty.DutyGrenze