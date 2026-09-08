/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F06.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.DutyF06

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  unberuehrt :: ensures #1  --  carried by `unberuehrt_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Stack.worte" _ "elem" => some (.intIn 0 18446744073709551615)
  | .field "EichMarke" "leer" => some (.intIn 0 18446744073709551615)
  | .field "EichMarke" "voll" => some (.intIn 0 18446744073709551615)
  | .field "EichMarke" "tiefe" => some (.intIn 0 18446744073709551615)
  | .field "EichMarke" "gelaufen" => some (.intIn 0 4294967295)
  | .field "IrqMarke" "tiefe_max" => some (.intIn 0 18446744073709551615)
  | .field "IrqMarke" "n" => some (.intIn 0 4294967295)
  | .field "Stack" "len" => some (.intIn 0 65536)
  | .global "gefuellt" => some (.intIn 0 4294967295)
  | .global "gemessen" => some (.intIn 0 4294967295)
  | .global "gemessen_tod" => some (.intIn 0 4294967295)
  | .global "tiefe_max" => some (.intIn 0 18446744073709551615)
  | .global "tiefe_tod" => some (.intIn 0 18446744073709551615)
  | .global "tiefe_lebend" => some (.intIn 0 18446744073709551615)
  | .global "frei_min" => some (.intIn 0 18446744073709551615)
  | .global "erschoepft" => some (.intIn 0 4294967295)
  | .global "groesse" => some (.intIn 0 18446744073709551615)
  | .global "tiefster" => some (.intIn 0 4294967295)
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

/-! ### `messen_benutzt` -/

def messen_benutzt_body : List Stmt :=
  [(.bindCall "frei" "unberuehrt" ["s"] [(.name "s")] (.lit (.bool true))), (.bindName "benutzt" (.bin .sub (.fieldOf "Stack" "len") (.name "frei"))), (.ret (some (.name "benutzt")))]

/-- The precondition: the declared shapes and the `requires`. -/
def messen_benutzt_pre : Expr :=
  (.bin .ge (.fieldOf "Stack" "len") (.lit (.int 8)))

def messen_benutzt_writes : List String := ["tiefe_max", "gemessen"]

/-- What a caller of `messen_benutzt` has to bring: a well-typed world and the precondition. -/
def messen_benutzt_requires (t : State) : Prop := wellFormed t ∧ eval t messen_benutzt_pre = some (.bool true)

/-- What `messen_benutzt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def messen_benutzt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `unberuehrt` -/

def unberuehrt_body : List Stmt :=
  [(.bindName "i" (.lit (.int 0))), (.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "unberuehrt#1" (.bin .and (.hasShape "i" (.intIn 0 65536)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.bin .and (.hasShape "#ret" (.intIn 0 18446744073709551615)) (.bin .le (.name "#ret") (.fieldOf "Stack" "len")))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))) [(.ite (.bin .ne (.name "w") (.lit (.int 16045690984833335023))) [(.bindName "#ret" (.bin .mul (.name "i") (.lit (.int 8)))), (.bindName "#returned" (.lit (.bool true))), .leave] []), (.bindName "i" (.bin .add (.name "i") (.lit (.int 1))))]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.bin .mul (.name "i") (.lit (.int 8)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def unberuehrt_pre : Expr :=
  (.lit (.bool true))

def unberuehrt_writes : List String := []

/-- What a caller of `unberuehrt` has to bring: a well-typed world and the precondition. -/
def unberuehrt_requires (t : State) : Prop := wellFormed t ∧ eval t unberuehrt_pre = some (.bool true)

/-- What `unberuehrt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def unberuehrt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)
  ∧ -- ensures #1
  (∃ v, r = some v ∧ eval { world := s'.world, local' := (bindLocal s.local' "result" v) } (.bin .le (.name "result") (.fieldOf "Stack" "len")) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `messen_benutzt` -/

/-- **The duty of `messen_benutzt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def messen_benutzt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s messen_benutzt_pre = some (.bool true))
    -- the contract of `unberuehrt`
    (c_unberuehrt : Contract ρ "unberuehrt" unberuehrt_requires unberuehrt_post)
    -- the frame of `unberuehrt`
    (fr_unberuehrt : Frame ρ "unberuehrt" unberuehrt_writes),
    ∃ s', finalState (exec ρ messen_benutzt_body s) = some s'
        ∧ messen_benutzt_post s s' (finalValue (exec ρ messen_benutzt_body s))

theorem messen_benutzt_meets : messen_benutzt_meets_statement := by
  unfold messen_benutzt_meets_statement
  intro ρ s hwf hpre c_unberuehrt fr_unberuehrt
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Stack_len, h_Stack_len, lo_Stack_len, hi_Stack_len⟩ := WF_intIn shapeOf s.world (.field "Stack" "len") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [messen_benutzt_pre, h_Stack_len]
  gabbro_auto [messen_benutzt_body, messen_benutzt_pre, messen_benutzt_post, wellFormed, unberuehrt_pre, unberuehrt_requires, unberuehrt_post, unberuehrt_writes, Frame_read _ _ _ fr_unberuehrt, h_Stack_len, hall] using shapeOf

/-! ### `unberuehrt` -/

/-- Loop `unberuehrt#1` of `unberuehrt`: its body and its invariant (with the shapes of the locals in scope). -/
def unberuehrt_loop_1_inv : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 65536)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.bin .and (.hasShape "#ret" (.intIn 0 18446744073709551615)) (.bin .le (.name "#ret") (.fieldOf "Stack" "len")))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))

def unberuehrt_loop_1_body : List Stmt :=
  [(.ite (.bin .ne (.name "w") (.lit (.int 16045690984833335023))) [(.bindName "#ret" (.bin .mul (.name "i") (.lit (.int 8)))), (.bindName "#returned" (.lit (.bool true))), .leave] []), (.bindName "i" (.bin .add (.name "i") (.lit (.int 1))))]

/-- **The loop rule of `unberuehrt#1`, as a statement over one pass.** -/
def unberuehrt_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 18446744073709551616)
    (hwf : wellFormed t)
    (hinv : eval t unberuehrt_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ unberuehrt_loop_1_body { t with local' := bindLocal t.local' "w" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' unberuehrt_loop_1_inv = some (.bool true)

theorem unberuehrt_loop_1_keeps : unberuehrt_loop_1_keeps_statement := by
  unfold unberuehrt_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn t "i" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  have hall := hinv
  gabbro_simp_at hall [unberuehrt_loop_1_inv, e_i, e__returned]
  gabbro_auto [unberuehrt_loop_1_body, unberuehrt_loop_1_inv, wellFormed, e_i, e__returned, hall] using shapeOf

/-- **The duty of `unberuehrt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def unberuehrt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s unberuehrt_pre = some (.bool true))
    -- the rule of loop `unberuehrt#1`
    (l_unberuehrt_loop_1 : LoopRule ρ "unberuehrt#1" wellFormed unberuehrt_loop_1_inv),
    ∃ s', finalState (exec ρ unberuehrt_body s) = some s'
        ∧ unberuehrt_post s s' (finalValue (exec ρ unberuehrt_body s))

theorem unberuehrt_meets : unberuehrt_meets_statement := by
  unfold unberuehrt_meets_statement
  intro ρ s hwf hpre l_unberuehrt_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Stack_len, h_Stack_len, lo_Stack_len, hi_Stack_len⟩ := WF_intIn shapeOf s.world (.field "Stack" "len") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [unberuehrt_pre, h_Stack_len]
  gabbro_auto [unberuehrt_body, unberuehrt_pre, unberuehrt_post, wellFormed, unberuehrt_loop_1_inv, h_Stack_len, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "messen_benutzt" messen_benutzt_body
  ∧ Frame ρ "messen_benutzt" messen_benutzt_writes
  ∧ Runs ρ "unberuehrt" unberuehrt_body
  ∧ Frame ρ "unberuehrt" unberuehrt_writes
  ∧ RunsLoopIn ρ "unberuehrt#1" unberuehrt_loop_1_body "w" 0 18446744073709551616

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_unberuehrt_loop_1 : unberuehrt_loop_1_keeps_statement)
    (d_unberuehrt : unberuehrt_meets_statement)
    (d_messen_benutzt : messen_benutzt_meets_statement) :
    LoopRule ρ "unberuehrt#1" wellFormed unberuehrt_loop_1_inv
    ∧ Contract ρ "unberuehrt" unberuehrt_requires unberuehrt_post
    ∧ Contract ρ "messen_benutzt" messen_benutzt_requires messen_benutzt_post := by
  obtain ⟨r_messen_benutzt, fr_messen_benutzt, r_unberuehrt, fr_unberuehrt, rl_unberuehrt_loop_1⟩ := hp
  have l_unberuehrt_loop_1 : LoopRule ρ "unberuehrt#1" wellFormed unberuehrt_loop_1_inv :=
    looprule_of_body_in ρ "unberuehrt#1" wellFormed unberuehrt_loop_1_inv unberuehrt_loop_1_body "w" 0 18446744073709551616 rl_unberuehrt_loop_1
      (fun t k hlo hhi hw hi => d_unberuehrt_loop_1 ρ t k hlo hhi hw hi)
  have c_unberuehrt : Contract ρ "unberuehrt" unberuehrt_requires unberuehrt_post :=
    contract_of_duty ρ "unberuehrt" unberuehrt_body unberuehrt_requires unberuehrt_post r_unberuehrt
      (fun t ht => d_unberuehrt ρ t ht.1 ht.2 l_unberuehrt_loop_1)
  have c_messen_benutzt : Contract ρ "messen_benutzt" messen_benutzt_requires messen_benutzt_post :=
    contract_of_duty ρ "messen_benutzt" messen_benutzt_body messen_benutzt_requires messen_benutzt_post r_messen_benutzt
      (fun t ht => d_messen_benutzt ρ t ht.1 ht.2 c_unberuehrt fr_unberuehrt)
  exact ⟨l_unberuehrt_loop_1, c_unberuehrt, c_messen_benutzt⟩

end GabbroDuty.DutyF06