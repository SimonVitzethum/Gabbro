/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/17-gruppe-ueber-zwei-sperren.gab  total 1  goals 1  refused 0
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
set_option maxHeartbeats 8000000

open Gabbro.Body

namespace GabbroDuty.Duty17GruppeUeberZweiSperren

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Zustellung :: invariant wartende_haben_grund  --  carried by `einreihen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Endpunkte" _ "wartet" => some .int
  | .slot "Faeden" _ "gruende" => some .int
  | .slot "Faeden" _ "bereit" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `wartende_haben_grund` over `Endpunkte`, `Faeden`. -/
def inv_wartende_haben_grund : Expr :=
  (.forallSlots "e" 64 (.bin .gt (.place "Faeden" (.place "Endpunkte" (.name "e") "wartet") "gruende") (.lit (.int 0))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_wartende_haben_grund = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `einreihen` -/

def einreihen_body : List Stmt :=
  [(.locked "PUNKTE" [(.locked "PLAN" [(.assign "Endpunkte" (.name "e") "wartet" (.name "t")), (.assign "Faeden" (.name "t") "gruende" (.lit (.int 1)))])])]

/-- The precondition: the declared shapes and the `requires`. -/
def einreihen_pre : Expr :=
  (.bin .and (.bin .and (.hasShape "e" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "e")) (.bin .le (.name "e") (.lit (.int 63))))) (.bin .and (.bin .and (.hasShape "t" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "t")) (.bin .le (.name "t") (.lit (.int 255))))) (.forallSlots "e" 64 (.bin .gt (.place "Faeden" (.place "Endpunkte" (.name "e") "wartet") "gruende") (.lit (.int 0))))))

/-- `wartende_haben_grund`, as `einreihen` keeps it. -/
def einreihen_inv_wartende_haben_grund : Expr :=
  (.forallSlots "e" 64 (.bin .gt (.place "Faeden" (.place "Endpunkte" (.name "e") "wartet") "gruende") (.lit (.int 0))))

def einreihen_writes : List String := ["Endpunkte", "Faeden"]

/-- What a caller of `einreihen` has to bring: a well-typed world and the precondition. -/
def einreihen_requires (t : State) : Prop := wellFormed t ∧ eval t einreihen_pre = some (.bool true)

/-- What `einreihen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einreihen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' einreihen_inv_wartende_haben_grund = some (.bool true)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `einreihen` -/

/-- **The duty of `einreihen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einreihen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einreihen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ einreihen_body s) = some s'
        ∧ einreihen_post s s' (finalValue (exec ρ einreihen_body s))

theorem einreihen_meets : einreihen_meets_statement := by
  unfold einreihen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_wartende_haben_grund := (and_right _ _ _ (and_right _ _ _ hpre))
  gabbro_simp_at hi_wartende_haben_grund [einreihen_inv_wartende_haben_grund, einreihen_pre]
  obtain ⟨w_e, e_e, lo_e, hi_e⟩ := shape_int_in s "e" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_int_in s "t" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  have hall := hpre
  gabbro_simp_at hall [einreihen_pre, e_e, e_t]
  gabbro_pipeline [einreihen_body, einreihen_pre, einreihen_post, wellFormed, einreihen_inv_wartende_haben_grund, e_e, e_t, hall] using shapeOf
  trace_state
  all_goals (try simp_all [einreihen_body, einreihen_pre, einreihen_post, wellFormed, einreihen_inv_wartende_haben_grund, e_e, e_t, hall])
  trace_state
  all_goals sorry

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "einreihen" einreihen_body
  ∧ Frame ρ "einreihen" einreihen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_einreihen : einreihen_meets_statement) :
    Contract ρ "einreihen" einreihen_requires einreihen_post := by
  obtain ⟨r_einreihen, fr_einreihen⟩ := hp
  have c_einreihen : Contract ρ "einreihen" einreihen_requires einreihen_post :=
    contract_of_duty ρ "einreihen" einreihen_body einreihen_requires einreihen_post r_einreihen
      (fun t ht => d_einreihen ρ t ht.1 ht.2)
  exact c_einreihen

end GabbroDuty.Duty17GruppeUeberZweiSperren
