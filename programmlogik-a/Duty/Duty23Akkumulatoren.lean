/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/23-akkumulatoren.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty23Akkumulatoren

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "hoechststand" => some (.intIn 0 18446744073709551615)
  | .global "tiefststand" => some (.intIn 0 18446744073709551615)
  | .global "fehlerzahl" => some (.intIn 0 4294967295)
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

/-! ### `fehler` -/

def fehler_body : List Stmt :=
  [(.ret (some (.global "fehlerzahl")))]

/-- The precondition: the declared shapes and the `requires`. -/
def fehler_pre : Expr :=
  (.lit (.bool true))

def fehler_writes : List String := []

/-- What a caller of `fehler` has to bring: a well-typed world and the precondition. -/
def fehler_requires (t : State) : Prop := wellFormed t ∧ eval t fehler_pre = some (.bool true)

/-- What `fehler` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fehler_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `fehler_melden` -/

def fehler_melden_body : List Stmt :=
  [(.assignGlobal "fehlerzahl" (.name "n"))]

/-- The precondition: the declared shapes and the `requires`. -/
def fehler_melden_pre : Expr :=
  (.hasShape "n" (.intIn 0 4294967295))

def fehler_melden_writes : List String := ["fehlerzahl"]

/-- What a caller of `fehler_melden` has to bring: a well-typed world and the precondition. -/
def fehler_melden_requires (t : State) : Prop := wellFormed t ∧ eval t fehler_melden_pre = some (.bool true)

/-- What `fehler_melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fehler_melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `hoechster` -/

def hoechster_body : List Stmt :=
  [(.ret (some (.global "hoechststand")))]

/-- The precondition: the declared shapes and the `requires`. -/
def hoechster_pre : Expr :=
  (.lit (.bool true))

def hoechster_writes : List String := []

/-- What a caller of `hoechster` has to bring: a well-typed world and the precondition. -/
def hoechster_requires (t : State) : Prop := wellFormed t ∧ eval t hoechster_pre = some (.bool true)

/-- What `hoechster` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hoechster_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `melde_hoch` -/

def melde_hoch_body : List Stmt :=
  [(.assignGlobal "hoechststand" (.name "t"))]

/-- The precondition: the declared shapes and the `requires`. -/
def melde_hoch_pre : Expr :=
  (.hasShape "t" (.intIn 0 18446744073709551615))

def melde_hoch_writes : List String := ["hoechststand"]

/-- What a caller of `melde_hoch` has to bring: a well-typed world and the precondition. -/
def melde_hoch_requires (t : State) : Prop := wellFormed t ∧ eval t melde_hoch_pre = some (.bool true)

/-- What `melde_hoch` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def melde_hoch_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `melde_tief` -/

def melde_tief_body : List Stmt :=
  [(.assignGlobal "tiefststand" (.name "t"))]

/-- The precondition: the declared shapes and the `requires`. -/
def melde_tief_pre : Expr :=
  (.hasShape "t" (.intIn 0 18446744073709551615))

def melde_tief_writes : List String := ["tiefststand"]

/-- What a caller of `melde_tief` has to bring: a well-typed world and the precondition. -/
def melde_tief_requires (t : State) : Prop := wellFormed t ∧ eval t melde_tief_pre = some (.bool true)

/-- What `melde_tief` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def melde_tief_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `tiefster` -/

def tiefster_body : List Stmt :=
  [(.ret (some (.global "tiefststand")))]

/-- The precondition: the declared shapes and the `requires`. -/
def tiefster_pre : Expr :=
  (.lit (.bool true))

def tiefster_writes : List String := []

/-- What a caller of `tiefster` has to bring: a well-typed world and the precondition. -/
def tiefster_requires (t : State) : Prop := wellFormed t ∧ eval t tiefster_pre = some (.bool true)

/-- What `tiefster` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tiefster_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `fehler` -/

/-- **The duty of `fehler`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def fehler_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s fehler_pre = some (.bool true)),
    ∃ s', finalState (exec ρ fehler_body s) = some s'
        ∧ fehler_post s s' (finalValue (exec ρ fehler_body s))

theorem fehler_meets : fehler_meets_statement := by
  unfold fehler_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [fehler_pre]
  gabbro_auto [fehler_body, fehler_pre, fehler_post, wellFormed, hall] using shapeOf

/-! ### `fehler_melden` -/

/-- **The duty of `fehler_melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def fehler_melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s fehler_melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ fehler_melden_body s) = some s'
        ∧ fehler_melden_post s s' (finalValue (exec ρ fehler_melden_body s))

theorem fehler_melden_meets : fehler_melden_meets_statement := by
  unfold fehler_melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [fehler_melden_pre, e_n]
  gabbro_auto [fehler_melden_body, fehler_melden_pre, fehler_melden_post, wellFormed, e_n, hall] using shapeOf

/-! ### `hoechster` -/

/-- **The duty of `hoechster`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def hoechster_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s hoechster_pre = some (.bool true)),
    ∃ s', finalState (exec ρ hoechster_body s) = some s'
        ∧ hoechster_post s s' (finalValue (exec ρ hoechster_body s))

theorem hoechster_meets : hoechster_meets_statement := by
  unfold hoechster_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [hoechster_pre]
  gabbro_auto [hoechster_body, hoechster_pre, hoechster_post, wellFormed, hall] using shapeOf

/-! ### `melde_hoch` -/

/-- **The duty of `melde_hoch`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def melde_hoch_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s melde_hoch_pre = some (.bool true)),
    ∃ s', finalState (exec ρ melde_hoch_body s) = some s'
        ∧ melde_hoch_post s s' (finalValue (exec ρ melde_hoch_body s))

theorem melde_hoch_meets : melde_hoch_meets_statement := by
  unfold melde_hoch_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [melde_hoch_pre, e_t]
  gabbro_auto [melde_hoch_body, melde_hoch_pre, melde_hoch_post, wellFormed, e_t, hall] using shapeOf

/-! ### `melde_tief` -/

/-- **The duty of `melde_tief`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def melde_tief_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s melde_tief_pre = some (.bool true)),
    ∃ s', finalState (exec ρ melde_tief_body s) = some s'
        ∧ melde_tief_post s s' (finalValue (exec ρ melde_tief_body s))

theorem melde_tief_meets : melde_tief_meets_statement := by
  unfold melde_tief_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [melde_tief_pre, e_t]
  gabbro_auto [melde_tief_body, melde_tief_pre, melde_tief_post, wellFormed, e_t, hall] using shapeOf

/-! ### `tiefster` -/

/-- **The duty of `tiefster`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def tiefster_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s tiefster_pre = some (.bool true)),
    ∃ s', finalState (exec ρ tiefster_body s) = some s'
        ∧ tiefster_post s s' (finalValue (exec ρ tiefster_body s))

theorem tiefster_meets : tiefster_meets_statement := by
  unfold tiefster_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [tiefster_pre]
  gabbro_auto [tiefster_body, tiefster_pre, tiefster_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "fehler" fehler_body
  ∧ Frame ρ "fehler" fehler_writes
  ∧ Runs ρ "fehler_melden" fehler_melden_body
  ∧ Frame ρ "fehler_melden" fehler_melden_writes
  ∧ Runs ρ "hoechster" hoechster_body
  ∧ Frame ρ "hoechster" hoechster_writes
  ∧ Runs ρ "melde_hoch" melde_hoch_body
  ∧ Frame ρ "melde_hoch" melde_hoch_writes
  ∧ Runs ρ "melde_tief" melde_tief_body
  ∧ Frame ρ "melde_tief" melde_tief_writes
  ∧ Runs ρ "tiefster" tiefster_body
  ∧ Frame ρ "tiefster" tiefster_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_fehler : fehler_meets_statement)
    (d_fehler_melden : fehler_melden_meets_statement)
    (d_hoechster : hoechster_meets_statement)
    (d_melde_hoch : melde_hoch_meets_statement)
    (d_melde_tief : melde_tief_meets_statement)
    (d_tiefster : tiefster_meets_statement) :
    Contract ρ "fehler" fehler_requires fehler_post
    ∧ Contract ρ "fehler_melden" fehler_melden_requires fehler_melden_post
    ∧ Contract ρ "hoechster" hoechster_requires hoechster_post
    ∧ Contract ρ "melde_hoch" melde_hoch_requires melde_hoch_post
    ∧ Contract ρ "melde_tief" melde_tief_requires melde_tief_post
    ∧ Contract ρ "tiefster" tiefster_requires tiefster_post := by
  obtain ⟨r_fehler, fr_fehler, r_fehler_melden, fr_fehler_melden, r_hoechster, fr_hoechster, r_melde_hoch, fr_melde_hoch, r_melde_tief, fr_melde_tief, r_tiefster, fr_tiefster⟩ := hp
  have c_fehler : Contract ρ "fehler" fehler_requires fehler_post :=
    contract_of_duty ρ "fehler" fehler_body fehler_requires fehler_post r_fehler
      (fun t ht => d_fehler ρ t ht.1 ht.2)
  have c_fehler_melden : Contract ρ "fehler_melden" fehler_melden_requires fehler_melden_post :=
    contract_of_duty ρ "fehler_melden" fehler_melden_body fehler_melden_requires fehler_melden_post r_fehler_melden
      (fun t ht => d_fehler_melden ρ t ht.1 ht.2)
  have c_hoechster : Contract ρ "hoechster" hoechster_requires hoechster_post :=
    contract_of_duty ρ "hoechster" hoechster_body hoechster_requires hoechster_post r_hoechster
      (fun t ht => d_hoechster ρ t ht.1 ht.2)
  have c_melde_hoch : Contract ρ "melde_hoch" melde_hoch_requires melde_hoch_post :=
    contract_of_duty ρ "melde_hoch" melde_hoch_body melde_hoch_requires melde_hoch_post r_melde_hoch
      (fun t ht => d_melde_hoch ρ t ht.1 ht.2)
  have c_melde_tief : Contract ρ "melde_tief" melde_tief_requires melde_tief_post :=
    contract_of_duty ρ "melde_tief" melde_tief_body melde_tief_requires melde_tief_post r_melde_tief
      (fun t ht => d_melde_tief ρ t ht.1 ht.2)
  have c_tiefster : Contract ρ "tiefster" tiefster_requires tiefster_post :=
    contract_of_duty ρ "tiefster" tiefster_body tiefster_requires tiefster_post r_tiefster
      (fun t ht => d_tiefster ρ t ht.1 ht.2)
  exact ⟨c_fehler, c_fehler_melden, c_hoechster, c_melde_hoch, c_melde_tief, c_tiefster⟩

end GabbroDuty.Duty23Akkumulatoren
