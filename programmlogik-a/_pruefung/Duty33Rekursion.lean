/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/33-rekursion.gab  total 0  goals 0  refused 0
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
set_option maxHeartbeats 6000000

open Gabbro.Body

namespace GabbroDuty.Duty33Rekursion

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Knoten" _ "elter" => some .opt
  | .slot "Knoten" _ "tiefe" => some .int
  | .global "summe" => some .int
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

/-! ### `absteigen` -/

def absteigen_body : List Stmt :=
  [(.assignGlobal "summe" (.name "n")), (.ite (.bin .eq (.name "n") (.lit (.int 0))) [(.ret (some (.lit (.int 0))))] []), (.retCall "absteigen" ["n"] [(.bin .sub (.name "n") (.lit (.int 1)))] (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512))))))]

/-- The precondition: the declared shapes and the `requires`. -/
def absteigen_pre : Expr :=
  (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512)))))

def absteigen_writes : List String := ["summe"]

/-- What a caller of `absteigen` has to bring: a well-typed world and the precondition. -/
def absteigen_requires (t : State) : Prop := wellFormed t ∧ eval t absteigen_pre = some (.bool true)

/-- What `absteigen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def absteigen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x))

/-- The measure of `absteigen` -- what its `decreases` names; a recursive call is
    below the current state in it. -/
def absteigen_decreases : Expr :=
  (.name "n")

/-! ### `gerade` -/

def gerade_body : List Stmt :=
  [(.assignGlobal "summe" (.name "n")), (.ite (.bin .ge (.name "n") (.lit (.int 1))) [(.retCall "ungerade" ["n"] [(.bin .sub (.name "n") (.lit (.int 1)))] (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512))))))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def gerade_pre : Expr :=
  (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512)))))

def gerade_writes : List String := ["summe"]

/-- What a caller of `gerade` has to bring: a well-typed world and the precondition. -/
def gerade_requires (t : State) : Prop := wellFormed t ∧ eval t gerade_pre = some (.bool true)

/-- What `gerade` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def gerade_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x))

/-- The measure of `gerade` -- what its `decreases` names; a recursive call is
    below the current state in it. -/
def gerade_decreases : Expr :=
  (.name "n")

/-! ### `ungerade` -/

def ungerade_body : List Stmt :=
  [(.assignGlobal "summe" (.name "n")), (.ite (.bin .ge (.name "n") (.lit (.int 1))) [(.retCall "gerade" ["n"] [(.bin .sub (.name "n") (.lit (.int 1)))] (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512))))))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def ungerade_pre : Expr :=
  (.bin .and (.hasShape "n" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "n")) (.bin .le (.name "n") (.lit (.int 512)))))

def ungerade_writes : List String := ["summe"]

/-- What a caller of `ungerade` has to bring: a well-typed world and the precondition. -/
def ungerade_requires (t : State) : Prop := wellFormed t ∧ eval t ungerade_pre = some (.bool true)

/-- What `ungerade` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ungerade_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x))

/-- The measure of `ungerade` -- what its `decreases` names; a recursive call is
    below the current state in it. -/
def ungerade_decreases : Expr :=
  (.name "n")

/-! ## The duties: one statement per routine and per loop -/

/-! ### `absteigen` -/

/-- **The duty of `absteigen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def absteigen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s absteigen_pre = some (.bool true))
    -- the contract of `absteigen` itself, below `s` in its `decreases`
    (c_absteigen : ContractBelow ρ "absteigen" absteigen_decreases s absteigen_requires absteigen_post)
    -- the frame of `absteigen`
    (fr_absteigen : Frame ρ "absteigen" absteigen_writes),
    ∃ s', finalState (exec ρ absteigen_body s) = some s'
        ∧ absteigen_post s s' (finalValue (exec ρ absteigen_body s))

theorem absteigen_meets : absteigen_meets_statement := by
  unfold absteigen_meets_statement
  intro ρ s hwf hpre c_absteigen fr_absteigen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_int_in s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [absteigen_pre, e_n]
  gabbro_auto [absteigen_body, absteigen_pre, absteigen_post, wellFormed, absteigen_pre, absteigen_requires, absteigen_post, absteigen_writes, Frame_read _ _ _ fr_absteigen, absteigen_decreases, absteigen_decreases, e_n, hall] using shapeOf

/-! ### `gerade` -/

/-- **The duty of `gerade`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def gerade_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s gerade_pre = some (.bool true))
    -- the contract of `ungerade` (the same cycle), below `s` in this routine's `decreases`
    (c_ungerade : ContractBelowM ρ ⟨"ungerade", ungerade_body, ungerade_requires, ungerade_post, ungerade_decreases⟩ gerade_decreases s)
    -- the frame of `ungerade`
    (fr_ungerade : Frame ρ "ungerade" ungerade_writes),
    ∃ s', finalState (exec ρ gerade_body s) = some s'
        ∧ gerade_post s s' (finalValue (exec ρ gerade_body s))

theorem gerade_meets : gerade_meets_statement := by
  unfold gerade_meets_statement
  intro ρ s hwf hpre c_ungerade fr_ungerade
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_int_in s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [gerade_pre, e_n]
  gabbro_auto [gerade_body, gerade_pre, gerade_post, wellFormed, ungerade_pre, ungerade_requires, ungerade_post, ungerade_writes, Frame_read _ _ _ fr_ungerade, ungerade_decreases, gerade_decreases, e_n, hall] using shapeOf

/-! ### `ungerade` -/

/-- **The duty of `ungerade`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def ungerade_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s ungerade_pre = some (.bool true))
    -- the contract of `gerade` (the same cycle), below `s` in this routine's `decreases`
    (c_gerade : ContractBelowM ρ ⟨"gerade", gerade_body, gerade_requires, gerade_post, gerade_decreases⟩ ungerade_decreases s)
    -- the frame of `gerade`
    (fr_gerade : Frame ρ "gerade" gerade_writes),
    ∃ s', finalState (exec ρ ungerade_body s) = some s'
        ∧ ungerade_post s s' (finalValue (exec ρ ungerade_body s))

theorem ungerade_meets : ungerade_meets_statement := by
  unfold ungerade_meets_statement
  intro ρ s hwf hpre c_gerade fr_gerade
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_int_in s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [ungerade_pre, e_n]
  gabbro_auto [ungerade_body, ungerade_pre, ungerade_post, wellFormed, gerade_pre, gerade_requires, gerade_post, gerade_writes, Frame_read _ _ _ fr_gerade, gerade_decreases, ungerade_decreases, e_n, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "absteigen" absteigen_body
  ∧ Frame ρ "absteigen" absteigen_writes
  ∧ Runs ρ "gerade" gerade_body
  ∧ Frame ρ "gerade" gerade_writes
  ∧ Runs ρ "ungerade" ungerade_body
  ∧ Frame ρ "ungerade" ungerade_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_absteigen : absteigen_meets_statement)
    (d_gerade : gerade_meets_statement)
    (d_ungerade : ungerade_meets_statement) :
    Contract ρ "absteigen" absteigen_requires absteigen_post
    ∧ Contract ρ "gerade" gerade_requires gerade_post
    ∧ Contract ρ "ungerade" ungerade_requires ungerade_post := by
  obtain ⟨r_absteigen, fr_absteigen, r_gerade, fr_gerade, r_ungerade, fr_ungerade⟩ := hp
  have c_absteigen : Contract ρ "absteigen" absteigen_requires absteigen_post :=
    contract_of_duty_rec ρ "absteigen" absteigen_body absteigen_requires absteigen_post absteigen_decreases r_absteigen
      (fun t ht hrec => d_absteigen ρ t ht.1 ht.2 hrec fr_absteigen)
  have cyc_0 := contracts_of_duties_rec ρ [⟨"gerade", gerade_body, gerade_requires, gerade_post, gerade_decreases⟩, ⟨"ungerade", ungerade_body, ungerade_requires, ungerade_post, ungerade_decreases⟩]
    (by intro r hr; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> assumption)
    (by intro r hr; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro t ht hrec; exact d_gerade ρ t ht.1 ht.2 (hrec ⟨"ungerade", ungerade_body, ungerade_requires, ungerade_post, ungerade_decreases⟩ (by simp)) fr_ungerade
        · intro t ht hrec; exact d_ungerade ρ t ht.1 ht.2 (hrec ⟨"gerade", gerade_body, gerade_requires, gerade_post, gerade_decreases⟩ (by simp)) fr_gerade
    )
  have c_gerade : Contract ρ "gerade" gerade_requires gerade_post := cyc_0 ⟨"gerade", gerade_body, gerade_requires, gerade_post, gerade_decreases⟩ (by simp)
  have c_ungerade : Contract ρ "ungerade" ungerade_requires ungerade_post := cyc_0 ⟨"ungerade", ungerade_body, ungerade_requires, ungerade_post, ungerade_decreases⟩ (by simp)
  exact ⟨c_absteigen, c_gerade, c_ungerade⟩

end GabbroDuty.Duty33Rekursion
