/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/gift/434-laufvariable-verdeckt-die-tabelle.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty434LaufvariableVerdecktDieTabelle

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Riesen" _ "elter" => some .opt
  | .slot "Riesen" _ "erstes_kind" => some .opt
  | .slot "Riesen" _ "naechstes" => some .opt
  | .slot "Riesen" _ "wert" => some (.intIn 0 4294967295)
  | .slot "Topologie" _ "elter" => some .opt
  | .slot "Topologie" _ "erstes_kind" => some .opt
  | .slot "Topologie" _ "naechstes" => some .opt
  | .slot "Topologie" _ "wert" => some (.intIn 0 4294967295)
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

/-! ### `f` -/

def f_body : List Stmt :=
  [(.bindName "summe" (.lit (.int 0))), (.loop "f#1" (.bin .and (.hasShape "g" (.intIn 0 7)) (.bin .and (.hasShape "v" .int) (.hasShape "summe" (.intIn 0 65535)))) [(.loop "f#2" (.bin .and (.hasShape "g" (.intIn 0 7)) (.bin .and (.hasShape "summe" (.intIn 0 65535)) (.hasShape "v" .int))) [(.ite (.bin .lt (.name "summe") (.lit (.int 60000))) [(.bindName "summe" (.bin .add (.name "summe") (.lit (.int 1))))] [])])]), (.ret (some (.name "summe")))]

/-- The precondition: the declared shapes and the `requires`. -/
def f_pre : Expr :=
  (.bin .and (.hasShape "g" (.intIn 0 7)) (.hasShape "v" (.intIn 0 511)))

def f_writes : List String := []

/-- What a caller of `f` has to bring: a well-typed world and the precondition. -/
def f_requires (t : State) : Prop := wellFormed t ∧ eval t f_pre = some (.bool true)

/-- What `f` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def f_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `f` -/

/-- Loop `f#2` of `f`: its body and its invariant (with the shapes of the locals in scope). -/
def f_loop_2_inv : Expr :=
  (.bin .and (.hasShape "g" (.intIn 0 7)) (.bin .and (.hasShape "summe" (.intIn 0 65535)) (.hasShape "v" .int)))

def f_loop_2_body : List Stmt :=
  [(.ite (.bin .lt (.name "summe") (.lit (.int 60000))) [(.bindName "summe" (.bin .add (.name "summe") (.lit (.int 1))))] [])]

/-- **The loop rule of `f#2`, as a statement over one pass.** -/
def f_loop_2_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t f_loop_2_inv = some (.bool true)),
    ∃ t', finalState (exec ρ f_loop_2_body { t with local' := bindLocal t.local' "d" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' f_loop_2_inv = some (.bool true)

theorem f_loop_2_keeps : f_loop_2_keeps_statement := by
  unfold f_loop_2_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn t "g" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_summe, e_summe, lo_summe, hi_summe⟩ := shape_intIn t "summe" _ _ (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨w_v, e_v⟩ := shape_int t "v" (and_right _ _ _ (and_right _ _ _ hinv))
  have hall := hinv
  gabbro_simp_at hall [f_loop_2_inv, e_g, e_summe, e_v]
  gabbro_auto [f_loop_2_body, f_loop_2_inv, wellFormed, e_g, e_summe, e_v, hall] using shapeOf

/-- Loop `f#1` of `f`: its body and its invariant (with the shapes of the locals in scope). -/
def f_loop_1_inv : Expr :=
  (.bin .and (.hasShape "g" (.intIn 0 7)) (.bin .and (.hasShape "v" .int) (.hasShape "summe" (.intIn 0 65535))))

def f_loop_1_body : List Stmt :=
  [(.loop "f#2" (.bin .and (.hasShape "g" (.intIn 0 7)) (.bin .and (.hasShape "summe" (.intIn 0 65535)) (.hasShape "v" .int))) [(.ite (.bin .lt (.name "summe") (.lit (.int 60000))) [(.bindName "summe" (.bin .add (.name "summe") (.lit (.int 1))))] [])])]

/-- **The loop rule of `f#1`, as a statement over one pass.** -/
def f_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t f_loop_1_inv = some (.bool true))
    (l_f_loop_2 : LoopRule ρ "f#2" wellFormed f_loop_2_inv),
    ∃ t', finalState (exec ρ f_loop_1_body { t with local' := bindLocal t.local' "v" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' f_loop_1_inv = some (.bool true)

theorem f_loop_1_keeps : f_loop_1_keeps_statement := by
  unfold f_loop_1_keeps_statement
  intro ρ t k hwf hinv l_f_loop_2
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn t "g" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_v, e_v⟩ := shape_int t "v" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨w_summe, e_summe, lo_summe, hi_summe⟩ := shape_intIn t "summe" _ _ (and_right _ _ _ (and_right _ _ _ hinv))
  have hall := hinv
  gabbro_simp_at hall [f_loop_1_inv, e_g, e_v, e_summe]
  gabbro_auto [f_loop_1_body, f_loop_1_inv, wellFormed, f_loop_2_inv, e_g, e_v, e_summe, hall] using shapeOf

/-- **The duty of `f`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def f_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s f_pre = some (.bool true))
    -- the rule of loop `f#2`
    (l_f_loop_2 : LoopRule ρ "f#2" wellFormed f_loop_2_inv)
    -- the rule of loop `f#1`
    (l_f_loop_1 : LoopRule ρ "f#1" wellFormed f_loop_1_inv),
    ∃ s', finalState (exec ρ f_body s) = some s'
        ∧ f_post s s' (finalValue (exec ρ f_body s))

theorem f_meets : f_meets_statement := by
  unfold f_meets_statement
  intro ρ s hwf hpre l_f_loop_2 l_f_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn s "g" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_v, e_v, lo_v, hi_v⟩ := shape_intIn s "v" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [f_pre, e_g, e_v]
  gabbro_auto [f_body, f_pre, f_post, wellFormed, f_loop_2_inv, f_loop_1_inv, e_g, e_v, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "f" f_body
  ∧ Frame ρ "f" f_writes
  ∧ RunsLoop ρ "f#2" f_loop_2_body "d"
  ∧ RunsLoop ρ "f#1" f_loop_1_body "v"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_f_loop_2 : f_loop_2_keeps_statement)
    (d_f_loop_1 : f_loop_1_keeps_statement)
    (d_f : f_meets_statement) :
    LoopRule ρ "f#2" wellFormed f_loop_2_inv
    ∧ LoopRule ρ "f#1" wellFormed f_loop_1_inv
    ∧ Contract ρ "f" f_requires f_post := by
  obtain ⟨r_f, fr_f, rl_f_loop_2, rl_f_loop_1⟩ := hp
  have l_f_loop_2 : LoopRule ρ "f#2" wellFormed f_loop_2_inv :=
    looprule_of_body ρ "f#2" wellFormed f_loop_2_inv f_loop_2_body "d" rl_f_loop_2
      (fun t k hw hi => d_f_loop_2 ρ t k hw hi)
  have l_f_loop_1 : LoopRule ρ "f#1" wellFormed f_loop_1_inv :=
    looprule_of_body ρ "f#1" wellFormed f_loop_1_inv f_loop_1_body "v" rl_f_loop_1
      (fun t k hw hi => d_f_loop_1 ρ t k hw hi l_f_loop_2)
  have c_f : Contract ρ "f" f_requires f_post :=
    contract_of_duty ρ "f" f_body f_requires f_post r_f
      (fun t ht => d_f ρ t ht.1 ht.2 l_f_loop_2 l_f_loop_1)
  exact ⟨l_f_loop_2, l_f_loop_1, c_f⟩

end GabbroDuty.Duty434LaufvariableVerdecktDieTabelle