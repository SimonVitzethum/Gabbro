/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/46-verneinung.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty46Verneinung

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  zaehle_freie :: loop invariant #1  --  carried by `zaehle_freie_loop_1_keeps`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Plaetze" _ "belegt" => some .bool
  | .slot "Plaetze" _ "wert" => some (.intIn 0 4294967295)
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

/-! ### `ist_frei` -/

def ist_frei_body : List Stmt :=
  [(.ret (some (.un .not (.place "Plaetze" (.name "i") "belegt"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def ist_frei_pre : Expr :=
  (.hasShape "i" (.intIn 0 7))

def ist_frei_writes : List String := []

/-- What a caller of `ist_frei` has to bring: a well-typed world and the precondition. -/
def ist_frei_requires (t : State) : Prop := wellFormed t ∧ eval t ist_frei_pre = some (.bool true)

/-- What `ist_frei` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ist_frei_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `zaehle_freie` -/

def zaehle_freie_body : List Stmt :=
  [(.bindName "n" (.lit (.int 0))), (.loop "zaehle_freie#1" (.bin .and (.hasShape "n" (.intIn 0 4294967295)) (.bin .le (.name "n") (.lit (.int 8)))) [(.ite (.un .not (.place "Plaetze" (.name "i") "belegt")) [(.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))] [])]), (.ret (some (.name "n")))]

/-- The precondition: the declared shapes and the `requires`. -/
def zaehle_freie_pre : Expr :=
  (.lit (.bool true))

def zaehle_freie_writes : List String := []

/-- What a caller of `zaehle_freie` has to bring: a well-typed world and the precondition. -/
def zaehle_freie_requires (t : State) : Prop := wellFormed t ∧ eval t zaehle_freie_pre = some (.bool true)

/-- What `zaehle_freie` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zaehle_freie_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `ist_frei` -/

/-- **The duty of `ist_frei`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def ist_frei_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s ist_frei_pre = some (.bool true)),
    ∃ s', finalState (exec ρ ist_frei_body s) = some s'
        ∧ ist_frei_post s s' (finalValue (exec ρ ist_frei_body s))

theorem ist_frei_meets : ist_frei_meets_statement := by
  unfold ist_frei_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Plaetze_belegt_i, h_Plaetze_belegt_i⟩ := WF_bool shapeOf s.world (.slot "Plaetze" w_i "belegt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [ist_frei_pre, e_i, h_Plaetze_belegt_i]
  gabbro_auto [ist_frei_body, ist_frei_pre, ist_frei_post, wellFormed, e_i, h_Plaetze_belegt_i, hall] using shapeOf

/-! ### `zaehle_freie` -/

/-- Loop `zaehle_freie#1` of `zaehle_freie`: its body and its invariant (with the shapes of the locals in scope). -/
def zaehle_freie_loop_1_inv : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 4294967295)) (.bin .le (.name "n") (.lit (.int 8))))

def zaehle_freie_loop_1_body : List Stmt :=
  [(.ite (.un .not (.place "Plaetze" (.name "i") "belegt")) [(.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))] [])]

/-- **The loop rule of `zaehle_freie#1`, as a statement over one pass.** -/
def zaehle_freie_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 8)
    (hwf : wellFormed t)
    (hinv : eval t zaehle_freie_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ zaehle_freie_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' zaehle_freie_loop_1_inv = some (.bool true)

theorem zaehle_freie_loop_1_keeps : zaehle_freie_loop_1_keeps_statement := by
  unfold zaehle_freie_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_left _ _ _ hinv)
  obtain ⟨n_Plaetze_belegt_i, h_Plaetze_belegt_i⟩ := WF_bool shapeOf t.world (.slot "Plaetze" k "belegt") hwf rfl
  have hall := hinv
  gabbro_simp_at hall [zaehle_freie_loop_1_inv, e_n, h_Plaetze_belegt_i]
  gabbro_auto [zaehle_freie_loop_1_body, zaehle_freie_loop_1_inv, wellFormed, e_n, h_Plaetze_belegt_i, hall] using shapeOf

/-- **The duty of `zaehle_freie`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def zaehle_freie_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s zaehle_freie_pre = some (.bool true))
    -- the rule of loop `zaehle_freie#1`
    (l_zaehle_freie_loop_1 : LoopRule ρ "zaehle_freie#1" wellFormed zaehle_freie_loop_1_inv),
    ∃ s', finalState (exec ρ zaehle_freie_body s) = some s'
        ∧ zaehle_freie_post s s' (finalValue (exec ρ zaehle_freie_body s))

theorem zaehle_freie_meets : zaehle_freie_meets_statement := by
  unfold zaehle_freie_meets_statement
  intro ρ s hwf hpre l_zaehle_freie_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [zaehle_freie_pre]
  gabbro_auto [zaehle_freie_body, zaehle_freie_pre, zaehle_freie_post, wellFormed, zaehle_freie_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "ist_frei" ist_frei_body
  ∧ Frame ρ "ist_frei" ist_frei_writes
  ∧ Runs ρ "zaehle_freie" zaehle_freie_body
  ∧ Frame ρ "zaehle_freie" zaehle_freie_writes
  ∧ RunsLoopIn ρ "zaehle_freie#1" zaehle_freie_loop_1_body "i" 0 8

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_ist_frei : ist_frei_meets_statement)
    (d_zaehle_freie_loop_1 : zaehle_freie_loop_1_keeps_statement)
    (d_zaehle_freie : zaehle_freie_meets_statement) :
    Contract ρ "ist_frei" ist_frei_requires ist_frei_post
    ∧ LoopRule ρ "zaehle_freie#1" wellFormed zaehle_freie_loop_1_inv
    ∧ Contract ρ "zaehle_freie" zaehle_freie_requires zaehle_freie_post := by
  obtain ⟨r_ist_frei, fr_ist_frei, r_zaehle_freie, fr_zaehle_freie, rl_zaehle_freie_loop_1⟩ := hp
  have c_ist_frei : Contract ρ "ist_frei" ist_frei_requires ist_frei_post :=
    contract_of_duty ρ "ist_frei" ist_frei_body ist_frei_requires ist_frei_post r_ist_frei
      (fun t ht => d_ist_frei ρ t ht.1 ht.2)
  have l_zaehle_freie_loop_1 : LoopRule ρ "zaehle_freie#1" wellFormed zaehle_freie_loop_1_inv :=
    looprule_of_body_in ρ "zaehle_freie#1" wellFormed zaehle_freie_loop_1_inv zaehle_freie_loop_1_body "i" 0 8 rl_zaehle_freie_loop_1
      (fun t k hlo hhi hw hi => d_zaehle_freie_loop_1 ρ t k hlo hhi hw hi)
  have c_zaehle_freie : Contract ρ "zaehle_freie" zaehle_freie_requires zaehle_freie_post :=
    contract_of_duty ρ "zaehle_freie" zaehle_freie_body zaehle_freie_requires zaehle_freie_post r_zaehle_freie
      (fun t ht => d_zaehle_freie ρ t ht.1 ht.2 l_zaehle_freie_loop_1)
  exact ⟨c_ist_frei, l_zaehle_freie_loop_1, c_zaehle_freie⟩

end GabbroDuty.Duty46Verneinung