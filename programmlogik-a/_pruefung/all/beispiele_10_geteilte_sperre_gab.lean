/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/10-geteilte-sperre.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty10GeteilteSperre

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kappenraum" _ "belegt" => some .bool
  | .slot "Kappenraum" _ "rechte" => some (.intIn 0 15)
  | .slot "Kappenraum" _ "objekt" => some (.intIn 0 4294967295)
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

/-! ### `rechte_aufloesen` -/

def rechte_aufloesen_body : List Stmt :=
  [(.locked "KAPPEN" [(.ite (.place "Kappenraum" (.name "i") "belegt") [(.ret (some (.place "Kappenraum" (.name "i") "rechte")))] [])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def rechte_aufloesen_pre : Expr :=
  (.hasShape "i" (.intIn 0 4095))

def rechte_aufloesen_writes : List String := []

/-- What a caller of `rechte_aufloesen` has to bring: a well-typed world and the precondition. -/
def rechte_aufloesen_requires (t : State) : Prop := wellFormed t ∧ eval t rechte_aufloesen_pre = some (.bool true)

/-- What `rechte_aufloesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def rechte_aufloesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 15)

/-! ### `rechte_setzen` -/

def rechte_setzen_body : List Stmt :=
  [(.locked "KAPPEN" [(.assign "Kappenraum" (.name "i") "rechte" (.name "r"))])]

/-- The precondition: the declared shapes and the `requires`. -/
def rechte_setzen_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 4095)) (.hasShape "r" (.intIn 0 15)))

def rechte_setzen_writes : List String := ["Kappenraum"]

/-- What a caller of `rechte_setzen` has to bring: a well-typed world and the precondition. -/
def rechte_setzen_requires (t : State) : Prop := wellFormed t ∧ eval t rechte_setzen_pre = some (.bool true)

/-- What `rechte_setzen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def rechte_setzen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `zaehlen` -/

def zaehlen_body : List Stmt :=
  [(.locked "KAPPEN" [(.ite (.place "Kappenraum" (.name "i") "belegt") [(.ret (some (.lit (.int 1))))] [])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def zaehlen_pre : Expr :=
  (.hasShape "i" (.intIn 0 4095))

def zaehlen_writes : List String := []

/-- What a caller of `zaehlen` has to bring: a well-typed world and the precondition. -/
def zaehlen_requires (t : State) : Prop := wellFormed t ∧ eval t zaehlen_pre = some (.bool true)

/-- What `zaehlen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zaehlen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `rechte_aufloesen` -/

/-- **The duty of `rechte_aufloesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def rechte_aufloesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s rechte_aufloesen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ rechte_aufloesen_body s) = some s'
        ∧ rechte_aufloesen_post s s' (finalValue (exec ρ rechte_aufloesen_body s))

theorem rechte_aufloesen_meets : rechte_aufloesen_meets_statement := by
  unfold rechte_aufloesen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Kappenraum_belegt_i, h_Kappenraum_belegt_i⟩ := WF_bool shapeOf s.world (.slot "Kappenraum" w_i "belegt") hwf rfl
  obtain ⟨n_Kappenraum_rechte_i, h_Kappenraum_rechte_i, lo_Kappenraum_rechte_i, hi_Kappenraum_rechte_i⟩ := WF_intIn shapeOf s.world (.slot "Kappenraum" w_i "rechte") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [rechte_aufloesen_pre, e_i, h_Kappenraum_belegt_i, h_Kappenraum_rechte_i]
  gabbro_auto [rechte_aufloesen_body, rechte_aufloesen_pre, rechte_aufloesen_post, wellFormed, e_i, h_Kappenraum_belegt_i, h_Kappenraum_rechte_i, hall] using shapeOf

/-! ### `rechte_setzen` -/

/-- **The duty of `rechte_setzen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def rechte_setzen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s rechte_setzen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ rechte_setzen_body s) = some s'
        ∧ rechte_setzen_post s s' (finalValue (exec ρ rechte_setzen_body s))

theorem rechte_setzen_meets : rechte_setzen_meets_statement := by
  unfold rechte_setzen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_r, e_r, lo_r, hi_r⟩ := shape_intIn s "r" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [rechte_setzen_pre, e_i, e_r]
  gabbro_auto [rechte_setzen_body, rechte_setzen_pre, rechte_setzen_post, wellFormed, e_i, e_r, hall] using shapeOf

/-! ### `zaehlen` -/

/-- **The duty of `zaehlen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def zaehlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s zaehlen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ zaehlen_body s) = some s'
        ∧ zaehlen_post s s' (finalValue (exec ρ zaehlen_body s))

theorem zaehlen_meets : zaehlen_meets_statement := by
  unfold zaehlen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Kappenraum_belegt_i, h_Kappenraum_belegt_i⟩ := WF_bool shapeOf s.world (.slot "Kappenraum" w_i "belegt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [zaehlen_pre, e_i, h_Kappenraum_belegt_i]
  gabbro_auto [zaehlen_body, zaehlen_pre, zaehlen_post, wellFormed, e_i, h_Kappenraum_belegt_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "rechte_aufloesen" rechte_aufloesen_body
  ∧ Frame ρ "rechte_aufloesen" rechte_aufloesen_writes
  ∧ Runs ρ "rechte_setzen" rechte_setzen_body
  ∧ Frame ρ "rechte_setzen" rechte_setzen_writes
  ∧ Runs ρ "zaehlen" zaehlen_body
  ∧ Frame ρ "zaehlen" zaehlen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_rechte_aufloesen : rechte_aufloesen_meets_statement)
    (d_rechte_setzen : rechte_setzen_meets_statement)
    (d_zaehlen : zaehlen_meets_statement) :
    Contract ρ "rechte_aufloesen" rechte_aufloesen_requires rechte_aufloesen_post
    ∧ Contract ρ "rechte_setzen" rechte_setzen_requires rechte_setzen_post
    ∧ Contract ρ "zaehlen" zaehlen_requires zaehlen_post := by
  obtain ⟨r_rechte_aufloesen, fr_rechte_aufloesen, r_rechte_setzen, fr_rechte_setzen, r_zaehlen, fr_zaehlen⟩ := hp
  have c_rechte_aufloesen : Contract ρ "rechte_aufloesen" rechte_aufloesen_requires rechte_aufloesen_post :=
    contract_of_duty ρ "rechte_aufloesen" rechte_aufloesen_body rechte_aufloesen_requires rechte_aufloesen_post r_rechte_aufloesen
      (fun t ht => d_rechte_aufloesen ρ t ht.1 ht.2)
  have c_rechte_setzen : Contract ρ "rechte_setzen" rechte_setzen_requires rechte_setzen_post :=
    contract_of_duty ρ "rechte_setzen" rechte_setzen_body rechte_setzen_requires rechte_setzen_post r_rechte_setzen
      (fun t ht => d_rechte_setzen ρ t ht.1 ht.2)
  have c_zaehlen : Contract ρ "zaehlen" zaehlen_requires zaehlen_post :=
    contract_of_duty ρ "zaehlen" zaehlen_body zaehlen_requires zaehlen_post r_zaehlen
      (fun t ht => d_zaehlen ρ t ht.1 ht.2)
  exact ⟨c_rechte_aufloesen, c_rechte_setzen, c_zaehlen⟩

end GabbroDuty.Duty10GeteilteSperre