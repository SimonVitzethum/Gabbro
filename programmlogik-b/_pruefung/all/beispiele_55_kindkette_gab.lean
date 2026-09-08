/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/55-kindkette.gab  total 2  goals 2  refused 0
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

namespace GabbroDuty.Duty55Kindkette

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  E  kind_einhaengen :: kind_zeigt_zurueck  --  carried by `kind_einhaengen_meets`
  duty_2  N  kind_einhaengen :: ensures #1  --  carried by `kind_einhaengen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kappraum" _ "belegt" => some .bool
  | .slot "Kappraum" _ "elter" => some .opt
  | .slot "Kappraum" _ "erstes_kind" => some .opt
  | .slot "Kappraum" _ "naechstes_geschwister" => some .opt
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `kind_zeigt_zurueck` over `Kappraum`. -/
def inv_kind_zeigt_zurueck : Expr :=
  (.forallSlots "s" 512 (.forallSlots "k" 512 (.bin .or (.un .not (.chainFrom "Kappraum" (.place "Kappraum" (.name "s") "erstes_kind") (.name "k") "naechstes_geschwister" 512)) (.bin .eq (.place "Kappraum" (.name "k") "elter") (.someOf (.name "s"))))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_kind_zeigt_zurueck = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `kind_einhaengen` -/

def kind_einhaengen_body : List Stmt :=
  [(.breaking ["kind_zeigt_zurueck"] [(.assign "Kappraum" (.name "k") "naechstes_geschwister" (.place "Kappraum" (.name "p") "erstes_kind")), (.assign "Kappraum" (.name "k") "elter" (.someOf (.name "p"))), (.assign "Kappraum" (.name "p") "erstes_kind" (.someOf (.name "k")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def kind_einhaengen_pre : Expr :=
  (.bin .and (.hasShape "p" (.intIn 0 511)) (.bin .and (.hasShape "k" (.intIn 0 511)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappraum" (.name "p") "belegt") (.bin .and (.place "Kappraum" (.name "k") "belegt") (.bin .and (.forallSlots "x" 512 (.bin .or (.un .not (.chainFrom "Kappraum" (.place "Kappraum" (.name "p") "erstes_kind") (.name "x") "naechstes_geschwister" 512)) (.bin .eq (.place "Kappraum" (.name "x") "elter") (.someOf (.name "p"))))) (.forallSlots "s" 512 (.forallSlots "k" 512 (.bin .or (.un .not (.chainFrom "Kappraum" (.place "Kappraum" (.name "s") "erstes_kind") (.name "k") "naechstes_geschwister" 512)) (.bin .eq (.place "Kappraum" (.name "k") "elter") (.someOf (.name "s"))))))))))))

/-- `kind_zeigt_zurueck`, as `kind_einhaengen` keeps it. -/
def kind_einhaengen_inv_kind_zeigt_zurueck : Expr :=
  (.forallSlots "s" 512 (.forallSlots "k" 512 (.bin .or (.un .not (.chainFrom "Kappraum" (.place "Kappraum" (.name "s") "erstes_kind") (.name "k") "naechstes_geschwister" 512)) (.bin .eq (.place "Kappraum" (.name "k") "elter") (.someOf (.name "s"))))))

def kind_einhaengen_writes : List String := ["Kappraum"]

/-- What a caller of `kind_einhaengen` has to bring: a well-typed world and the precondition. -/
def kind_einhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t kind_einhaengen_pre = some (.bool true)

/-- What `kind_einhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kind_einhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' kind_einhaengen_inv_kind_zeigt_zurueck = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "x" 512 (.bin .or (.un .not (.chainFrom "Kappraum" (.place "Kappraum" (.name "p") "erstes_kind") (.name "x") "naechstes_geschwister" 512)) (.bin .eq (.place "Kappraum" (.name "x") "elter") (.someOf (.name "p"))))) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `kind_einhaengen` -/

/-- **The duty of `kind_einhaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kind_einhaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kind_einhaengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ kind_einhaengen_body s) = some s'
        ∧ kind_einhaengen_post s s' (finalValue (exec ρ kind_einhaengen_body s))

theorem kind_einhaengen_meets : kind_einhaengen_meets_statement := by
  unfold kind_einhaengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_kind_zeigt_zurueck := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))))
  gabbro_simp_at hi_kind_zeigt_zurueck [kind_einhaengen_inv_kind_zeigt_zurueck, kind_einhaengen_pre]
  obtain ⟨w_p, e_p, lo_p, hi_p⟩ := shape_intIn s "p" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn s "k" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  have hall := hpre
  gabbro_simp_at hall [kind_einhaengen_pre, e_p, e_k]
  rcases WF_opt shapeOf s.world (.slot "Kappraum" w_p "erstes_kind") hwf rfl with h_Kappraum_erstes_kind_p | ⟨n_Kappraum_erstes_kind_p, h_Kappraum_erstes_kind_p⟩
    <;> gabbro_auto [kind_einhaengen_body, kind_einhaengen_pre, kind_einhaengen_post, wellFormed, kind_einhaengen_inv_kind_zeigt_zurueck, e_p, e_k, h_Kappraum_erstes_kind_p, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "kind_einhaengen" kind_einhaengen_body
  ∧ Frame ρ "kind_einhaengen" kind_einhaengen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_kind_einhaengen : kind_einhaengen_meets_statement) :
    Contract ρ "kind_einhaengen" kind_einhaengen_requires kind_einhaengen_post := by
  obtain ⟨r_kind_einhaengen, fr_kind_einhaengen⟩ := hp
  have c_kind_einhaengen : Contract ρ "kind_einhaengen" kind_einhaengen_requires kind_einhaengen_post :=
    contract_of_duty ρ "kind_einhaengen" kind_einhaengen_body kind_einhaengen_requires kind_einhaengen_post r_kind_einhaengen
      (fun t ht => d_kind_einhaengen ρ t ht.1 ht.2)
  exact c_kind_einhaengen

end GabbroDuty.Duty55Kindkette
