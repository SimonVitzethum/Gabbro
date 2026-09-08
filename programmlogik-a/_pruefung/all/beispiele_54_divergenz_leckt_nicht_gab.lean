/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/54-divergenz-leckt-nicht.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty54DivergenzLecktNicht

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

/-- `nimm` -- a foreign body: its contract is an assumption. -/
def nimm_pre : Expr :=
  (.lit (.bool true))

def nimm_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def nimm_writes : List String := ["m"]

def nimm_requires (t : State) : Prop := wellFormed t ∧ eval t nimm_pre = some (.bool true)

/-- `tue` -- a foreign body: its contract is an assumption. -/
def tue_pre : Expr :=
  (.lit (.bool true))

def tue_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def tue_writes : List String := []

def tue_requires (t : State) : Prop := wellFormed t ∧ eval t tue_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "nimm" nimm_requires nimm_post
  ∧ Frame ρ "nimm" nimm_writes
  ∧ Contract ρ "tue" tue_requires tue_post
  ∧ Frame ρ "tue" tue_writes

/-! ## The routines: body and contract -/

/-! ### `abschluss` -/

def abschluss_body : List Stmt :=
  [(.ite (.name "ist_dienst") [(.loop "abschluss#1" (.hasShape "ist_dienst" .bool) [(.call "tue" [] [] (.lit (.bool true)))])] [(.call "nimm" ["m"] [(.name "m")] (.lit (.bool true)))]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def abschluss_pre : Expr :=
  (.hasShape "ist_dienst" .bool)

def abschluss_writes : List String := ["m"]

/-- What a caller of `abschluss` has to bring: a well-typed world and the precondition. -/
def abschluss_requires (t : State) : Prop := wellFormed t ∧ eval t abschluss_pre = some (.bool true)

/-- What `abschluss` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abschluss_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abschluss` -/

/-- Loop `abschluss#1` of `abschluss`: its body and its invariant (with the shapes of the locals in scope). -/
def abschluss_loop_1_inv : Expr :=
  (.hasShape "ist_dienst" .bool)

def abschluss_loop_1_body : List Stmt :=
  [(.call "tue" [] [] (.lit (.bool true)))]

/-- **The loop rule of `abschluss#1`, as a statement over one pass.** -/
def abschluss_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t abschluss_loop_1_inv = some (.bool true))
    (c_tue : Contract ρ "tue" tue_requires tue_post)
    (fr_tue : Frame ρ "tue" tue_writes),
    ∃ t', finalState (exec ρ abschluss_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' abschluss_loop_1_inv = some (.bool true)

theorem abschluss_loop_1_keeps : abschluss_loop_1_keeps_statement := by
  unfold abschluss_loop_1_keeps_statement
  intro ρ t k hwf hinv c_tue fr_tue
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_ist_dienst, e_ist_dienst⟩ := shape_bool t "ist_dienst" hinv
  have hall := hinv
  gabbro_simp_at hall [abschluss_loop_1_inv, e_ist_dienst]
  gabbro_auto [abschluss_loop_1_body, abschluss_loop_1_inv, wellFormed, tue_pre, tue_requires, tue_post, tue_writes, Frame_read _ _ _ fr_tue, e_ist_dienst, hall] using shapeOf

/-- **The duty of `abschluss`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abschluss_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abschluss_pre = some (.bool true))
    -- the contract of `nimm`
    (c_nimm : Contract ρ "nimm" nimm_requires nimm_post)
    -- the frame of `nimm`
    (fr_nimm : Frame ρ "nimm" nimm_writes)
    -- the contract of `tue`
    (c_tue : Contract ρ "tue" tue_requires tue_post)
    -- the frame of `tue`
    (fr_tue : Frame ρ "tue" tue_writes)
    -- the rule of loop `abschluss#1`
    (l_abschluss_loop_1 : LoopRule ρ "abschluss#1" wellFormed abschluss_loop_1_inv),
    ∃ s', finalState (exec ρ abschluss_body s) = some s'
        ∧ abschluss_post s s' (finalValue (exec ρ abschluss_body s))

theorem abschluss_meets : abschluss_meets_statement := by
  unfold abschluss_meets_statement
  intro ρ s hwf hpre c_nimm fr_nimm c_tue fr_tue l_abschluss_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_ist_dienst, e_ist_dienst⟩ := shape_bool s "ist_dienst" hpre
  have hall := hpre
  gabbro_simp_at hall [abschluss_pre, e_ist_dienst]
  gabbro_auto [abschluss_body, abschluss_pre, abschluss_post, wellFormed, nimm_pre, nimm_requires, nimm_post, nimm_writes, Frame_read _ _ _ fr_nimm, tue_pre, tue_requires, tue_post, tue_writes, Frame_read _ _ _ fr_tue, abschluss_loop_1_inv, e_ist_dienst, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abschluss" abschluss_body
  ∧ Frame ρ "abschluss" abschluss_writes
  ∧ RunsLoop ρ "abschluss#1" abschluss_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abschluss_loop_1 : abschluss_loop_1_keeps_statement)
    (d_abschluss : abschluss_meets_statement) :
    LoopRule ρ "abschluss#1" wellFormed abschluss_loop_1_inv
    ∧ Contract ρ "abschluss" abschluss_requires abschluss_post := by
  obtain ⟨r_abschluss, fr_abschluss, rl_abschluss_loop_1⟩ := hp
  obtain ⟨c_nimm, fr_nimm, c_tue, fr_tue⟩ := ha
  have l_abschluss_loop_1 : LoopRule ρ "abschluss#1" wellFormed abschluss_loop_1_inv :=
    looprule_of_body ρ "abschluss#1" wellFormed abschluss_loop_1_inv abschluss_loop_1_body "#pass" rl_abschluss_loop_1
      (fun t k hw hi => d_abschluss_loop_1 ρ t k hw hi c_tue fr_tue)
  have c_abschluss : Contract ρ "abschluss" abschluss_requires abschluss_post :=
    contract_of_duty ρ "abschluss" abschluss_body abschluss_requires abschluss_post r_abschluss
      (fun t ht => d_abschluss ρ t ht.1 ht.2 c_nimm fr_nimm c_tue fr_tue l_abschluss_loop_1)
  exact ⟨l_abschluss_loop_1, c_abschluss⟩

end GabbroDuty.Duty54DivergenzLecktNicht