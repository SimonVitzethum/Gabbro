/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/27-freiliste.gab  total 0  goals 0  refused 0
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
    names are two different objects (the alias passes carry it); the
    declared `effects` list is complete (`E008`/`E010`, `Frame` in `Program`);
    the initial world satisfies every invariant (a statement about `boot`,
    booked by no register); and everything `Assumed` names.
-/

import Gabbro.Body

set_option autoImplicit false

open Gabbro.Body

namespace GabbroDuty.Duty27Freiliste

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Halde" _ "kopf" => some .int
  | .slot "Halde" _ "naechst" => some .opt
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body, contract, duty -/

/-! ### `belegen` -/

def belegen_body : List Stmt :=
  [(.onOption (.global "frei") "i" [(.assignGlobal "frei" (.place "Halde" (.name "i") "naechst")), (.ret (some (.someOf (.name "i"))))] [(.ret (some (.lit .absent)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def belegen_pre : Expr :=
  (.lit (.bool true))

def belegen_writes : List String := ["frei"]

/-- What a caller of `belegen` has to bring: a well-typed world and the precondition. -/
def belegen_requires (t : State) : Prop := wellFormed t ∧ eval t belegen_pre = some (.bool true)

/-- What `belegen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def belegen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `belegen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def belegen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s belegen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ belegen_body s) = some s'
        ∧ belegen_post s s' (finalValue (exec ρ belegen_body s))

theorem belegen_meets : belegen_meets_statement := by
  unfold belegen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  gabbro_auto [belegen_body, belegen_pre, belegen_post, wellFormed] using shapeOf

/-! ### `freigeben` -/

def freigeben_body : List Stmt :=
  [(.assign "Halde" (.name "i") "naechst" (.global "frei")), (.assignGlobal "frei" (.someOf (.name "i")))]

/-- The precondition: the declared shapes and the `requires`. -/
def freigeben_pre : Expr :=
  (.hasShape "i" .int)

def freigeben_writes : List String := ["frei", "Halde"]

/-- What a caller of `freigeben` has to bring: a well-typed world and the precondition. -/
def freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t freigeben_pre = some (.bool true)

/-- What `freigeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `freigeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def freigeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s freigeben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ freigeben_body s) = some s'
        ∧ freigeben_post s s' (finalValue (exec ρ freigeben_body s))

theorem freigeben_meets : freigeben_meets_statement := by
  unfold freigeben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i⟩ := shape_int s "i" hpre
  gabbro_auto [freigeben_body, freigeben_pre, freigeben_post, wellFormed, e_i] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "belegen" belegen_body
  ∧ Frame ρ "belegen" belegen_writes
  ∧ Runs ρ "freigeben" freigeben_body
  ∧ Frame ρ "freigeben" freigeben_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_belegen : belegen_meets_statement)
    (d_freigeben : freigeben_meets_statement) :
    Contract ρ "belegen" belegen_requires belegen_post
    ∧ Contract ρ "freigeben" freigeben_requires freigeben_post := by
  obtain ⟨r_belegen, fr_belegen, r_freigeben, fr_freigeben⟩ := hp
  have c_belegen : Contract ρ "belegen" belegen_requires belegen_post :=
    contract_of_duty ρ "belegen" belegen_body belegen_requires belegen_post r_belegen
      (fun t ht => d_belegen ρ t ht.1 ht.2)
  have c_freigeben : Contract ρ "freigeben" freigeben_requires freigeben_post :=
    contract_of_duty ρ "freigeben" freigeben_body freigeben_requires freigeben_post r_freigeben
      (fun t ht => d_freigeben ρ t ht.1 ht.2)
  exact ⟨c_belegen, c_freigeben⟩

end GabbroDuty.Duty27Freiliste
