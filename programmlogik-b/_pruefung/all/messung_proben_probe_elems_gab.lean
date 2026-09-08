/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-elems.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.DutyProbeElems

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  als_u64 :: loop invariant #1  --  carried by `als_u64_loop_1_keeps`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Feld.worte" _ "elem" => some (.intIn 0 18446744073709551615)
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

/-! ### `als_u64` -/

def als_u64_body : List Stmt :=
  [(.bindName "n" (.lit (.int 0))), (.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.bindName "#pass" (.lit (.int 0))), (.loop "als_u64#1" (.bin .and (.hasShape "n" (.intIn 0 8192)) (.bin .and (.hasShape "#returned" .bool) (.bin .and (.hasShape "#pass" .int) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 18446744073709551615))) (.bin .and (.un .not (.name "#returned")) (.bin .le (.name "n") (.name "#pass"))))))) [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.name "#returned") [.leave] []), (.ite (.bin .ne (.name "w") (.lit (.int 16045690984833335023))) [(.bindName "#ret" (.name "n")), (.bindName "#returned" (.lit (.bool true))), .leave] []), (.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.name "n")))]

/-- The precondition: the declared shapes and the `requires`. -/
def als_u64_pre : Expr :=
  (.lit (.bool true))

def als_u64_writes : List String := []

/-- What a caller of `als_u64` has to bring: a well-typed world and the precondition. -/
def als_u64_requires (t : State) : Prop := wellFormed t ∧ eval t als_u64_pre = some (.bool true)

/-- What `als_u64` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def als_u64_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `als_u64` -/

/-- Loop `als_u64#1` of `als_u64`: its body and its invariant (with the shapes of the locals in scope). -/
def als_u64_loop_1_inv : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 8192)) (.bin .and (.hasShape "#returned" .bool) (.bin .and (.hasShape "#pass" .int) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 18446744073709551615))) (.bin .and (.un .not (.name "#returned")) (.bin .le (.name "n") (.name "#pass")))))))

def als_u64_loop_1_body : List Stmt :=
  [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.name "#returned") [.leave] []), (.ite (.bin .ne (.name "w") (.lit (.int 16045690984833335023))) [(.bindName "#ret" (.name "n")), (.bindName "#returned" (.lit (.bool true))), .leave] []), (.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))]

/-- **The loop rule of `als_u64#1`, as a statement over one pass.** -/
def als_u64_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int) (i : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 18446744073709551616)
    (hplo : 0 ≤ i)
    (hphi : i < 8192)
    (hpass : t.local' "#pass" = .int i)
    (hwf : wellFormed t)
    (hinv : eval t als_u64_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ als_u64_loop_1_body { t with local' := bindLocal t.local' "w" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' als_u64_loop_1_inv = some (.bool true)
        ∧ t'.local' "#pass" = .int (i + 1)

theorem als_u64_loop_1_keeps : als_u64_loop_1_keeps_statement := by
  unfold als_u64_loop_1_keeps_statement
  intro ρ t k i hlo hhi hplo hphi hpass hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨w__pass, e__pass⟩ := shape_int t "#pass" (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hinv)))
  have hall := hinv
  gabbro_simp_at hall [als_u64_loop_1_inv, e_n, e__returned, e__pass]
  gabbro_auto [als_u64_loop_1_body, als_u64_loop_1_inv, wellFormed, e_n, e__returned, e__pass, hall, hpass] using shapeOf

/-- **The duty of `als_u64`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def als_u64_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s als_u64_pre = some (.bool true))
    -- the rule of loop `als_u64#1`
    (l_als_u64_loop_1 : LoopRuleP ρ "als_u64#1" wellFormed als_u64_loop_1_inv "#pass"),
    ∃ s', finalState (exec ρ als_u64_body s) = some s'
        ∧ als_u64_post s s' (finalValue (exec ρ als_u64_body s))

theorem als_u64_meets : als_u64_meets_statement := by
  unfold als_u64_meets_statement
  intro ρ s hwf hpre l_als_u64_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [als_u64_pre]
  gabbro_auto [als_u64_body, als_u64_pre, als_u64_post, wellFormed, als_u64_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "als_u64" als_u64_body
  ∧ Frame ρ "als_u64" als_u64_writes
  ∧ RunsLoopN ρ "als_u64#1" als_u64_loop_1_body "w" 0 18446744073709551616 8192

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_als_u64_loop_1 : als_u64_loop_1_keeps_statement)
    (d_als_u64 : als_u64_meets_statement) :
    LoopRuleP ρ "als_u64#1" wellFormed als_u64_loop_1_inv "#pass"
    ∧ Contract ρ "als_u64" als_u64_requires als_u64_post := by
  obtain ⟨r_als_u64, fr_als_u64, rl_als_u64_loop_1⟩ := hp
  have l_als_u64_loop_1 : LoopRuleP ρ "als_u64#1" wellFormed als_u64_loop_1_inv "#pass" :=
    looprule_of_body_p ρ "als_u64#1" wellFormed als_u64_loop_1_inv als_u64_loop_1_body "w" "#pass" 0 18446744073709551616 8192 rl_als_u64_loop_1
      (fun t k i hlo hhi hplo hphi hpass hw hin => d_als_u64_loop_1 ρ t k i hlo hhi hplo hphi hpass hw hin)
  have c_als_u64 : Contract ρ "als_u64" als_u64_requires als_u64_post :=
    contract_of_duty ρ "als_u64" als_u64_body als_u64_requires als_u64_post r_als_u64
      (fun t ht => d_als_u64 ρ t ht.1 ht.2 l_als_u64_loop_1)
  exact ⟨l_als_u64_loop_1, c_als_u64⟩

end GabbroDuty.DutyProbeElems
