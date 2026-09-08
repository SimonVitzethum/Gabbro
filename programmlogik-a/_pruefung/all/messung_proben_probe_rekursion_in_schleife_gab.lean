/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-rekursion-in-schleife.gab  total 2  goals 2  refused 0
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

namespace GabbroDuty.DutyProbeRekursionInSchleife

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  faerben :: loop invariant #1  --  carried by `faerben_loop_1_keeps`
  duty_2  N  faerben :: ensures #1  --  carried by `faerben_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Zelle" _ "marke" => some (.intIn 0 8)
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

/-! ### `faerben` -/

def faerben_body : List Stmt :=
  [(.loop "faerben#1" (.bin .and (.hasShape "n" (.intIn 0 8)) (.bin .le (.name "n") (.lit (.int 8)))) [(.assign "Zelle" (.name "i") "marke" (.name "n")), (.ite (.bin .gt (.name "n") (.lit (.int 0))) [(.call "faerben" ["z", "n"] [(.name "z"), (.bin .sub (.name "n") (.lit (.int 1)))] (.hasShape "n" (.intIn 0 8)))] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def faerben_pre : Expr :=
  (.hasShape "n" (.intIn 0 8))

def faerben_writes : List String := ["Zelle"]

/-- What a caller of `faerben` has to bring: a well-typed world and the precondition. -/
def faerben_requires (t : State) : Prop := wellFormed t ∧ eval t faerben_pre = some (.bool true)

/-- What `faerben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def faerben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "s" 4 (.bin .le (.place "Zelle" (.name "s") "marke") (.lit (.int 8)))) = some (.bool true))

/-- The measure of `faerben` -- what its `decreases` names; a recursive call is
    below the current state in it. -/
def faerben_decreases : Expr :=
  (.name "n")

/-! ## The duties: one statement per routine and per loop -/

/-! ### `faerben` -/

/-- Loop `faerben#1` of `faerben`: its body and its invariant (with the shapes of the locals in scope). -/
def faerben_loop_1_inv : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 8)) (.bin .le (.name "n") (.lit (.int 8))))

def faerben_loop_1_body : List Stmt :=
  [(.assign "Zelle" (.name "i") "marke" (.name "n")), (.ite (.bin .gt (.name "n") (.lit (.int 0))) [(.call "faerben" ["z", "n"] [(.name "z"), (.bin .sub (.name "n") (.lit (.int 1)))] (.hasShape "n" (.intIn 0 8)))] [])]

/-- **The loop rule of `faerben#1`, as a statement over one pass.** -/
def faerben_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 4)
    (hwf : wellFormed t)
    (s0 : State)
    (hmeas : eval t faerben_decreases = eval s0 faerben_decreases)
    (hinv : eval t faerben_loop_1_inv = some (.bool true))
    (c_faerben : ContractBelow ρ "faerben" faerben_decreases s0 faerben_requires faerben_post)
    (fr_faerben : Frame ρ "faerben" faerben_writes),
    ∃ t', finalState (exec ρ faerben_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ (wellFormed t' ∧ eval t' faerben_decreases = eval s0 faerben_decreases) ∧ eval t' faerben_loop_1_inv = some (.bool true)

theorem faerben_loop_1_keeps : faerben_loop_1_keeps_statement := by
  unfold faerben_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf s0 hmeas hinv c_faerben fr_faerben
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_left _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [faerben_loop_1_inv, e_n]
  have hmeas' := hmeas.symm
  gabbro_simp_at hmeas' [faerben_decreases, e_n, hall]
  gabbro_auto [faerben_loop_1_body, faerben_loop_1_inv, wellFormed, faerben_decreases, hmeas', faerben_pre, faerben_requires, faerben_post, faerben_writes, Frame_read _ _ _ fr_faerben, e_n, hall] using shapeOf

/-- **The duty of `faerben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def faerben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s faerben_pre = some (.bool true))
    -- the contract of `faerben` itself, below `s` in its `decreases`
    (c_faerben : ContractBelow ρ "faerben" faerben_decreases s faerben_requires faerben_post)
    -- the frame of `faerben`
    (fr_faerben : Frame ρ "faerben" faerben_writes)
    -- the rule of loop `faerben#1`
    (l_faerben_loop_1 : LoopRule ρ "faerben#1" (fun u => wellFormed u ∧ eval u faerben_decreases = eval s faerben_decreases) faerben_loop_1_inv),
    ∃ s', finalState (exec ρ faerben_body s) = some s'
        ∧ faerben_post s s' (finalValue (exec ρ faerben_body s))

theorem faerben_meets : faerben_meets_statement := by
  unfold faerben_meets_statement
  intro ρ s hwf hpre c_faerben fr_faerben l_faerben_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [faerben_pre, e_n]
  gabbro_auto [faerben_body, faerben_pre, faerben_post, wellFormed, faerben_pre, faerben_requires, faerben_post, faerben_writes, Frame_read _ _ _ fr_faerben, faerben_decreases, faerben_decreases, faerben_loop_1_inv, e_n, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "faerben" faerben_body
  ∧ Frame ρ "faerben" faerben_writes
  ∧ RunsLoopIn ρ "faerben#1" faerben_loop_1_body "i" 0 4

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_faerben_loop_1 : faerben_loop_1_keeps_statement)
    (d_faerben : faerben_meets_statement) :
    LoopRule ρ "faerben#1" wellFormed faerben_loop_1_inv
    ∧ Contract ρ "faerben" faerben_requires faerben_post := by
  obtain ⟨r_faerben, fr_faerben, rl_faerben_loop_1⟩ := hp
  have c_faerben : Contract ρ "faerben" faerben_requires faerben_post :=
    contract_of_duty_rec_loop_in ρ "faerben" faerben_body faerben_requires faerben_post faerben_decreases wellFormed
      "faerben#1" faerben_loop_1_body "i" 0 4 faerben_loop_1_inv r_faerben rl_faerben_loop_1
      (fun s0 _h0 hrec t k hlo hhi hw hm hin => d_faerben_loop_1 ρ t k hlo hhi hw s0 hm hin hrec fr_faerben)
      (fun t ht hrec hlr => d_faerben ρ t ht.1 ht.2 hrec fr_faerben hlr)
  have l_faerben_loop_1 : LoopRule ρ "faerben#1" wellFormed faerben_loop_1_inv :=
    looprule_of_body_in ρ "faerben#1" wellFormed faerben_loop_1_inv faerben_loop_1_body "i" 0 4 rl_faerben_loop_1
      (by intro t k hlo hhi hw hin
          obtain ⟨t', h1, ⟨h2, _⟩, h3⟩ := d_faerben_loop_1 ρ t k hlo hhi hw t rfl hin (contractBelow_of_contract ρ "faerben" faerben_decreases t faerben_requires faerben_post c_faerben) fr_faerben
          exact ⟨t', h1, h2, h3⟩)
  exact ⟨l_faerben_loop_1, c_faerben⟩

end GabbroDuty.DutyProbeRekursionInSchleife