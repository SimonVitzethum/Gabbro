/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/18-vorfahren.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty18Vorfahren

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Topologie :: invariant azyklisch  --  carried by no routine -- nothing in this unit writes the carrier
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Topologie" _ "elter" => some .opt
  | .slot "Topologie" _ "bereich" => some (.intIn 0 255)
  | .slot "Topologie" _ "gesperrt" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `azyklisch` over `Topologie`. -/
def inv_azyklisch : Expr :=
  (.forallSlots "g" 256 (.bin .le (.place "Topologie" (.name "g") "bereich") (.lit (.int 255))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_azyklisch = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `liegt_unter` -/

def liegt_unter_body : List Stmt :=
  [(.locked "TOPO" [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "liegt_unter#1" (.bin .and (.hasShape "g" (.intIn 0 255)) (.bin .and (.hasShape "wurzel" (.intIn 0 255)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .bool)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))) [(.ite (.bin .eq (.name "v") (.name "wurzel")) [(.bindName "#ret" (.lit (.bool true))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] [])]), (.ret (some (.lit (.bool false))))]

/-- The precondition: the declared shapes and the `requires`. -/
def liegt_unter_pre : Expr :=
  (.bin .and (.hasShape "g" (.intIn 0 255)) (.hasShape "wurzel" (.intIn 0 255)))

def liegt_unter_writes : List String := []

/-- What a caller of `liegt_unter` has to bring: a well-typed world and the precondition. -/
def liegt_unter_requires (t : State) : Prop := wellFormed t ∧ eval t liegt_unter_pre = some (.bool true)

/-- What `liegt_unter` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def liegt_unter_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `liegt_unter` -/

/-- Loop `liegt_unter#1` of `liegt_unter`: its body and its invariant (with the shapes of the locals in scope). -/
def liegt_unter_loop_1_inv : Expr :=
  (.bin .and (.hasShape "g" (.intIn 0 255)) (.bin .and (.hasShape "wurzel" (.intIn 0 255)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .bool)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))))

def liegt_unter_loop_1_body : List Stmt :=
  [(.ite (.bin .eq (.name "v") (.name "wurzel")) [(.bindName "#ret" (.lit (.bool true))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]

/-- **The loop rule of `liegt_unter#1`, as a statement over one pass.** -/
def liegt_unter_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t liegt_unter_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ liegt_unter_loop_1_body { t with local' := bindLocal t.local' "v" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' liegt_unter_loop_1_inv = some (.bool true)

theorem liegt_unter_loop_1_keeps : liegt_unter_loop_1_keeps_statement := by
  unfold liegt_unter_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn t "g" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_wurzel, e_wurzel, lo_wurzel, hi_wurzel⟩ := shape_intIn t "wurzel" _ _ (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hinv)))
  have hall := hinv
  gabbro_simp_at hall [liegt_unter_loop_1_inv, e_g, e_wurzel, e__returned]
  gabbro_auto [liegt_unter_loop_1_body, liegt_unter_loop_1_inv, wellFormed, e_g, e_wurzel, e__returned, hall] using shapeOf

/-- **The duty of `liegt_unter`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def liegt_unter_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s liegt_unter_pre = some (.bool true))
    -- the rule of loop `liegt_unter#1`
    (l_liegt_unter_loop_1 : LoopRule ρ "liegt_unter#1" wellFormed liegt_unter_loop_1_inv),
    ∃ s', finalState (exec ρ liegt_unter_body s) = some s'
        ∧ liegt_unter_post s s' (finalValue (exec ρ liegt_unter_body s))

theorem liegt_unter_meets : liegt_unter_meets_statement := by
  unfold liegt_unter_meets_statement
  intro ρ s hwf hpre l_liegt_unter_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_g, e_g, lo_g, hi_g⟩ := shape_intIn s "g" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_wurzel, e_wurzel, lo_wurzel, hi_wurzel⟩ := shape_intIn s "wurzel" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [liegt_unter_pre, e_g, e_wurzel]
  gabbro_auto [liegt_unter_body, liegt_unter_pre, liegt_unter_post, wellFormed, liegt_unter_loop_1_inv, e_g, e_wurzel, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "liegt_unter" liegt_unter_body
  ∧ Frame ρ "liegt_unter" liegt_unter_writes
  ∧ RunsLoop ρ "liegt_unter#1" liegt_unter_loop_1_body "v"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_liegt_unter_loop_1 : liegt_unter_loop_1_keeps_statement)
    (d_liegt_unter : liegt_unter_meets_statement) :
    LoopRule ρ "liegt_unter#1" wellFormed liegt_unter_loop_1_inv
    ∧ Contract ρ "liegt_unter" liegt_unter_requires liegt_unter_post := by
  obtain ⟨r_liegt_unter, fr_liegt_unter, rl_liegt_unter_loop_1⟩ := hp
  have l_liegt_unter_loop_1 : LoopRule ρ "liegt_unter#1" wellFormed liegt_unter_loop_1_inv :=
    looprule_of_body ρ "liegt_unter#1" wellFormed liegt_unter_loop_1_inv liegt_unter_loop_1_body "v" rl_liegt_unter_loop_1
      (fun t k hw hi => d_liegt_unter_loop_1 ρ t k hw hi)
  have c_liegt_unter : Contract ρ "liegt_unter" liegt_unter_requires liegt_unter_post :=
    contract_of_duty ρ "liegt_unter" liegt_unter_body liegt_unter_requires liegt_unter_post r_liegt_unter
      (fun t ht => d_liegt_unter ρ t ht.1 ht.2 l_liegt_unter_loop_1)
  exact ⟨l_liegt_unter_loop_1, c_liegt_unter⟩

end GabbroDuty.Duty18Vorfahren