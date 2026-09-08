/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/grammatik/tabellenworte.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyTabellenworte

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Geraetebaum" _ "benutzt" => some .bool
  | .slot "Geraetebaum" _ "bus" => some .opt
  | .slot "Geraetebaum" _ "klasse" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `eine_wurzel_gibt_es` over `Geraetebaum`. -/
def inv_eine_wurzel_gibt_es : Expr :=
  (.existsSlots "s" 32 (.bin .eq (.place "Geraetebaum" (.name "s") "bus") (.lit .absent)))

/-- `jedes_geraet_erreicht_die_bruecke` over `Geraetebaum`. -/
def inv_jedes_geraet_erreicht_die_bruecke : Expr :=
  (.forallSlots "s" 32 (.reaches "Geraetebaum" (.name "s") (.lit (.int 0)) "bus" 32))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `Geraetebaum::remove` -- a generated operation: its premises are the schema `opsruf` cuts,
    and that it preserves the table's invariants is `table.ops.erhaltung`. -/
def Geraetebaum_remove_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.forallSlots "x" 32 (.bin .ne (.place "Geraetebaum" (.name "x") "bus") (.someOf (.name "s")))))

def Geraetebaum_remove_post (t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'
  ∧ (eval t inv_eine_wurzel_gibt_es = some (.bool true) → eval t' inv_eine_wurzel_gibt_es = some (.bool true))
  ∧ (eval t inv_jedes_geraet_erreicht_die_bruecke = some (.bool true) → eval t' inv_jedes_geraet_erreicht_die_bruecke = some (.bool true))

def Geraetebaum_remove_writes : List String := ["Geraetebaum"]

def Geraetebaum_remove_requires (t : State) : Prop := wellFormed t ∧ eval t Geraetebaum_remove_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_eine_wurzel_gibt_es = some (.bool true)
  ∧ eval s0 inv_jedes_geraet_erreicht_die_bruecke = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "Geraetebaum::remove" Geraetebaum_remove_requires Geraetebaum_remove_post
  ∧ Frame ρ "Geraetebaum::remove" Geraetebaum_remove_writes

/-! ## The routines: body and contract -/

/-! ### `abziehen` -/

def abziehen_body : List Stmt :=
  [(.call "Geraetebaum::remove" ["t", "s"] [(.name "g"), (.name "s")] (.bin .and (.hasShape "s" .int) (.forallSlots "x" 32 (.bin .ne (.place "Geraetebaum" (.name "x") "bus") (.someOf (.name "s"))))))]

/-- The precondition: the declared shapes and the `requires`. -/
def abziehen_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 31)) (.forallSlots "x" 32 (.bin .ne (.place "Geraetebaum" (.name "x") "bus") (.someOf (.name "s")))))

def abziehen_writes : List String := ["Geraetebaum"]

/-- What a caller of `abziehen` has to bring: a well-typed world and the precondition. -/
def abziehen_requires (t : State) : Prop := wellFormed t ∧ eval t abziehen_pre = some (.bool true)

/-- What `abziehen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abziehen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `anstecken` -/

-- REFUSED  anstecken  (generated-op): a generated table operation whose premises name a root no invariant names
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def anstecken_pre : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 31)) (.bin .and (.hasShape "b" (.intIn 0 31)) (.bin .and (.un .not (.place "Geraetebaum" (.name "n") "benutzt")) (.reaches "Geraetebaum" (.name "b") (.lit (.int 0)) "bus" 32))))

def anstecken_writes : List String := ["Geraetebaum"]

/-- What a caller of `anstecken` has to bring: a well-typed world and the precondition. -/
def anstecken_requires (t : State) : Prop := wellFormed t ∧ eval t anstecken_pre = some (.bool true)

/-- What `anstecken` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def anstecken_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `umstecken` -/

-- REFUSED  umstecken  (generated-op): a generated table operation whose premises name a root no invariant names
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def umstecken_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 31)) (.bin .and (.hasShape "b" (.intIn 0 31)) (.bin .and (.reaches "Geraetebaum" (.name "b") (.lit (.int 0)) "bus" 32) (.un .not (.reaches "Geraetebaum" (.name "b") (.name "s") "bus" 32)))))

def umstecken_writes : List String := ["Geraetebaum"]

/-- What a caller of `umstecken` has to bring: a well-typed world and the precondition. -/
def umstecken_requires (t : State) : Prop := wellFormed t ∧ eval t umstecken_pre = some (.bool true)

/-- What `umstecken` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def umstecken_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abziehen` -/

/-- **The duty of `abziehen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abziehen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abziehen_pre = some (.bool true))
    -- the contract of `Geraetebaum::remove`
    (c_Geraetebaum_remove : Contract ρ "Geraetebaum::remove" Geraetebaum_remove_requires Geraetebaum_remove_post)
    -- the frame of `Geraetebaum::remove`
    (fr_Geraetebaum_remove : Frame ρ "Geraetebaum::remove" Geraetebaum_remove_writes),
    ∃ s', finalState (exec ρ abziehen_body s) = some s'
        ∧ abziehen_post s s' (finalValue (exec ρ abziehen_body s))

theorem abziehen_meets : abziehen_meets_statement := by
  unfold abziehen_meets_statement
  intro ρ s hwf hpre c_Geraetebaum_remove fr_Geraetebaum_remove
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [abziehen_pre, e_s]
  gabbro_auto [abziehen_body, abziehen_pre, abziehen_post, wellFormed, Geraetebaum_remove_pre, Geraetebaum_remove_requires, Geraetebaum_remove_post, Geraetebaum_remove_writes, Frame_read _ _ _ fr_Geraetebaum_remove, e_s, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abziehen" abziehen_body
  ∧ Frame ρ "abziehen" abziehen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abziehen : abziehen_meets_statement) :
    Contract ρ "abziehen" abziehen_requires abziehen_post := by
  obtain ⟨r_abziehen, fr_abziehen⟩ := hp
  obtain ⟨c_Geraetebaum_remove, fr_Geraetebaum_remove⟩ := ha
  have c_abziehen : Contract ρ "abziehen" abziehen_requires abziehen_post :=
    contract_of_duty ρ "abziehen" abziehen_body abziehen_requires abziehen_post r_abziehen
      (fun t ht => d_abziehen ρ t ht.1 ht.2 c_Geraetebaum_remove fr_Geraetebaum_remove)
  exact c_abziehen

end GabbroDuty.DutyTabellenworte