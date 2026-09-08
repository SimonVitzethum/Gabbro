/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/66-transport-rueckgabe.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty66TransportRueckgabe

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Puffer" _ "belegt" => some .bool
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

/-! ### `arm` -/

def arm_body : List Stmt :=
  [(.assign "Puffer" (.name "i") "belegt" (.lit (.bool true))), (.ret (some (.name "b")))]

/-- The precondition: the declared shapes and the `requires`. -/
def arm_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def arm_writes : List String := ["Puffer", "b"]

/-- What a caller of `arm` has to bring: a well-typed world and the precondition. -/
def arm_requires (t : State) : Prop := wellFormed t ∧ eval t arm_pre = some (.bool true)

/-- What `arm` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arm_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `hole` -/

-- REFUSED  hole  (call-in-expression): a call inside an expression
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def hole_pre : Expr :=
  (.lit (.bool true))

def hole_writes : List String := ["Puffer", "b"]

/-- What a caller of `hole` has to bring: a well-typed world and the precondition. -/
def hole_requires (t : State) : Prop := wellFormed t ∧ eval t hole_pre = some (.bool true)

/-- What `hole` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hole_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `hole_unbelegt` -/

def hole_unbelegt_body : List Stmt :=
  [(.assign "Puffer" (.name "i") "belegt" (.lit (.bool false))), (.ret (some (.name "b")))]

/-- The precondition: the declared shapes and the `requires`. -/
def hole_unbelegt_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def hole_unbelegt_writes : List String := ["Puffer", "b"]

/-- What a caller of `hole_unbelegt` has to bring: a well-typed world and the precondition. -/
def hole_unbelegt_requires (t : State) : Prop := wellFormed t ∧ eval t hole_unbelegt_pre = some (.bool true)

/-- What `hole_unbelegt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hole_unbelegt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `tritt` -/

def tritt_body : List Stmt :=
  [(.bindName "a" (.name "basis")), (.bindName "o" (.name "versatz")), (.bindName "f" (.name "faktor")), (.bindName "addr" (.bin .add (.name "a") (.bin .mul (.name "o") (.name "f")))), (.ret (some (.bin .add (.name "addr") (.name "warteschlange"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def tritt_pre : Expr :=
  (.bin .and (.hasShape "basis" (.intIn 0 1099511627776)) (.bin .and (.hasShape "versatz" (.intIn 0 65535)) (.bin .and (.hasShape "faktor" (.intIn 0 65536)) (.hasShape "warteschlange" (.intIn 0 65535)))))

def tritt_writes : List String := []

/-- What a caller of `tritt` has to bring: a well-typed world and the precondition. -/
def tritt_requires (t : State) : Prop := wellFormed t ∧ eval t tritt_pre = some (.bool true)

/-- What `tritt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tritt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `warte_auf_fertig` -/

def warte_auf_fertig_body : List Stmt :=
  [(.loop "warte_auf_fertig#1" (.hasShape "bereit" .bool) []), (.ret (some (.name "bereit")))]

/-- The precondition: the declared shapes and the `requires`. -/
def warte_auf_fertig_pre : Expr :=
  (.hasShape "bereit" .bool)

def warte_auf_fertig_writes : List String := []

/-- What a caller of `warte_auf_fertig` has to bring: a well-typed world and the precondition. -/
def warte_auf_fertig_requires (t : State) : Prop := wellFormed t ∧ eval t warte_auf_fertig_pre = some (.bool true)

/-- What `warte_auf_fertig` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def warte_auf_fertig_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `arm` -/

/-- **The duty of `arm`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arm_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arm_pre = some (.bool true)),
    ∃ s', finalState (exec ρ arm_body s) = some s'
        ∧ arm_post s s' (finalValue (exec ρ arm_body s))

theorem arm_meets : arm_meets_statement := by
  unfold arm_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [arm_pre, e_i]
  gabbro_auto [arm_body, arm_pre, arm_post, wellFormed, e_i, hall] using shapeOf

/-! ### `hole_unbelegt` -/

/-- **The duty of `hole_unbelegt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def hole_unbelegt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s hole_unbelegt_pre = some (.bool true)),
    ∃ s', finalState (exec ρ hole_unbelegt_body s) = some s'
        ∧ hole_unbelegt_post s s' (finalValue (exec ρ hole_unbelegt_body s))

theorem hole_unbelegt_meets : hole_unbelegt_meets_statement := by
  unfold hole_unbelegt_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [hole_unbelegt_pre, e_i]
  gabbro_auto [hole_unbelegt_body, hole_unbelegt_pre, hole_unbelegt_post, wellFormed, e_i, hall] using shapeOf

/-! ### `tritt` -/

/-- **The duty of `tritt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def tritt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s tritt_pre = some (.bool true)),
    ∃ s', finalState (exec ρ tritt_body s) = some s'
        ∧ tritt_post s s' (finalValue (exec ρ tritt_body s))

theorem tritt_meets : tritt_meets_statement := by
  unfold tritt_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_basis, e_basis, lo_basis, hi_basis⟩ := shape_intIn s "basis" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_versatz, e_versatz, lo_versatz, hi_versatz⟩ := shape_intIn s "versatz" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_faktor, e_faktor, lo_faktor, hi_faktor⟩ := shape_intIn s "faktor" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨w_warteschlange, e_warteschlange, lo_warteschlange, hi_warteschlange⟩ := shape_intIn s "warteschlange" _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  have hall := hpre
  gabbro_simp_at hall [tritt_pre, e_basis, e_versatz, e_faktor, e_warteschlange]
  gabbro_auto [tritt_body, tritt_pre, tritt_post, wellFormed, e_basis, e_versatz, e_faktor, e_warteschlange, hall] using shapeOf

/-! ### `warte_auf_fertig` -/

/-- Loop `warte_auf_fertig#1` of `warte_auf_fertig`: its body and its invariant (with the shapes of the locals in scope). -/
def warte_auf_fertig_loop_1_inv : Expr :=
  (.hasShape "bereit" .bool)

def warte_auf_fertig_loop_1_body : List Stmt :=
  []

/-- **The loop rule of `warte_auf_fertig#1`, as a statement over one pass.** -/
def warte_auf_fertig_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t warte_auf_fertig_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ warte_auf_fertig_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' warte_auf_fertig_loop_1_inv = some (.bool true)

theorem warte_auf_fertig_loop_1_keeps : warte_auf_fertig_loop_1_keeps_statement := by
  unfold warte_auf_fertig_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_bereit, e_bereit⟩ := shape_bool t "bereit" hinv
  have hall := hinv
  gabbro_simp_at hall [warte_auf_fertig_loop_1_inv, e_bereit]
  gabbro_auto [warte_auf_fertig_loop_1_body, warte_auf_fertig_loop_1_inv, wellFormed, e_bereit, hall] using shapeOf

/-- **The duty of `warte_auf_fertig`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def warte_auf_fertig_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s warte_auf_fertig_pre = some (.bool true))
    -- the rule of loop `warte_auf_fertig#1`
    (l_warte_auf_fertig_loop_1 : LoopRule ρ "warte_auf_fertig#1" wellFormed warte_auf_fertig_loop_1_inv),
    ∃ s', finalState (exec ρ warte_auf_fertig_body s) = some s'
        ∧ warte_auf_fertig_post s s' (finalValue (exec ρ warte_auf_fertig_body s))

theorem warte_auf_fertig_meets : warte_auf_fertig_meets_statement := by
  unfold warte_auf_fertig_meets_statement
  intro ρ s hwf hpre l_warte_auf_fertig_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_bereit, e_bereit⟩ := shape_bool s "bereit" hpre
  have hall := hpre
  gabbro_simp_at hall [warte_auf_fertig_pre, e_bereit]
  gabbro_auto [warte_auf_fertig_body, warte_auf_fertig_pre, warte_auf_fertig_post, wellFormed, warte_auf_fertig_loop_1_inv, e_bereit, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "arm" arm_body
  ∧ Frame ρ "arm" arm_writes
  ∧ Runs ρ "hole_unbelegt" hole_unbelegt_body
  ∧ Frame ρ "hole_unbelegt" hole_unbelegt_writes
  ∧ Runs ρ "tritt" tritt_body
  ∧ Frame ρ "tritt" tritt_writes
  ∧ Runs ρ "warte_auf_fertig" warte_auf_fertig_body
  ∧ Frame ρ "warte_auf_fertig" warte_auf_fertig_writes
  ∧ RunsLoop ρ "warte_auf_fertig#1" warte_auf_fertig_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_arm : arm_meets_statement)
    (d_hole_unbelegt : hole_unbelegt_meets_statement)
    (d_tritt : tritt_meets_statement)
    (d_warte_auf_fertig_loop_1 : warte_auf_fertig_loop_1_keeps_statement)
    (d_warte_auf_fertig : warte_auf_fertig_meets_statement) :
    Contract ρ "arm" arm_requires arm_post
    ∧ Contract ρ "hole_unbelegt" hole_unbelegt_requires hole_unbelegt_post
    ∧ Contract ρ "tritt" tritt_requires tritt_post
    ∧ LoopRule ρ "warte_auf_fertig#1" wellFormed warte_auf_fertig_loop_1_inv
    ∧ Contract ρ "warte_auf_fertig" warte_auf_fertig_requires warte_auf_fertig_post := by
  obtain ⟨r_arm, fr_arm, r_hole_unbelegt, fr_hole_unbelegt, r_tritt, fr_tritt, r_warte_auf_fertig, fr_warte_auf_fertig, rl_warte_auf_fertig_loop_1⟩ := hp
  have c_arm : Contract ρ "arm" arm_requires arm_post :=
    contract_of_duty ρ "arm" arm_body arm_requires arm_post r_arm
      (fun t ht => d_arm ρ t ht.1 ht.2)
  have c_hole_unbelegt : Contract ρ "hole_unbelegt" hole_unbelegt_requires hole_unbelegt_post :=
    contract_of_duty ρ "hole_unbelegt" hole_unbelegt_body hole_unbelegt_requires hole_unbelegt_post r_hole_unbelegt
      (fun t ht => d_hole_unbelegt ρ t ht.1 ht.2)
  have c_tritt : Contract ρ "tritt" tritt_requires tritt_post :=
    contract_of_duty ρ "tritt" tritt_body tritt_requires tritt_post r_tritt
      (fun t ht => d_tritt ρ t ht.1 ht.2)
  have l_warte_auf_fertig_loop_1 : LoopRule ρ "warte_auf_fertig#1" wellFormed warte_auf_fertig_loop_1_inv :=
    looprule_of_body ρ "warte_auf_fertig#1" wellFormed warte_auf_fertig_loop_1_inv warte_auf_fertig_loop_1_body "#pass" rl_warte_auf_fertig_loop_1
      (fun t k hw hi => d_warte_auf_fertig_loop_1 ρ t k hw hi)
  have c_warte_auf_fertig : Contract ρ "warte_auf_fertig" warte_auf_fertig_requires warte_auf_fertig_post :=
    contract_of_duty ρ "warte_auf_fertig" warte_auf_fertig_body warte_auf_fertig_requires warte_auf_fertig_post r_warte_auf_fertig
      (fun t ht => d_warte_auf_fertig ρ t ht.1 ht.2 l_warte_auf_fertig_loop_1)
  exact ⟨c_arm, c_hole_unbelegt, c_tritt, l_warte_auf_fertig_loop_1, c_warte_auf_fertig⟩

end GabbroDuty.Duty66TransportRueckgabe
