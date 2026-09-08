/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/58-freiliste-zwei-formen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty58FreilisteZweiFormen

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Halde" _ "wert" => some (.intIn 0 18446744073709551615)
  | .slot "Halde" _ "naechst" => some .opt
  | .global "hinterlegt" => some (.intIn 64 1024)
  | .global "frei" => some .opt
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `abbruch` -- a foreign body: its contract is an assumption. -/
def abbruch_pre : Expr :=
  (.lit (.bool true))

def abbruch_post (t t' : State) (r : Option Value) : Prop :=
  False

def abbruch_writes : List String := []

def abbruch_requires (t : State) : Prop := wellFormed t ∧ eval t abbruch_pre = some (.bool true)

/-- `griff_weg` -- a foreign body: its contract is an assumption. -/
def griff_weg_pre : Expr :=
  (.lit (.bool true))

def griff_weg_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def griff_weg_writes : List String := ["g"]

def griff_weg_requires (t : State) : Prop := wellFormed t ∧ eval t griff_weg_pre = some (.bool true)

/-- `kopf` -- a foreign body: its contract is an assumption. -/
def kopf_pre : Expr :=
  (.lit (.bool true))

def kopf_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615) ∨ ∃ e, r = some (.reason e))

def kopf_writes : List String := []

def kopf_requires (t : State) : Prop := wellFormed t ∧ eval t kopf_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "abbruch" abbruch_requires abbruch_post
  ∧ Frame ρ "abbruch" abbruch_writes
  ∧ Contract ρ "griff_weg" griff_weg_requires griff_weg_post
  ∧ Frame ρ "griff_weg" griff_weg_writes
  ∧ Contract ρ "kopf" kopf_requires kopf_post
  ∧ Frame ρ "kopf" kopf_writes

/-! ## The routines: body and contract -/

/-! ### `belegen` -/

def belegen_body : List Stmt :=
  [(.onOption (.global "frei") "i" [(.ite (.bin .and (.bin .ge (.name "i") (.lit (.int 0))) (.bin .lt (.name "i") (.global "hinterlegt"))) [] [(.ret (some (.lit .absent)))]), (.assignGlobal "frei" (.place "Halde" (.name "i") "naechst")), (.ret (some (.someOf (.name "i"))))] [(.ret (some (.lit .absent)))])]

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
  ∧ -- the answer: a value of the declared shape
  (r = some .absent ∨ ∃ x, r = some (.present x))

/-! ### `freigeben_if` -/

def freigeben_if_body : List Stmt :=
  [(.ite (.bin .ge (.name "i") (.global "hinterlegt")) [(.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true))), (.ret none)] []), (.assign "Halde" (.name "i") "naechst" (.global "frei")), (.assignGlobal "frei" (.someOf (.name "i"))), (.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def freigeben_if_pre : Expr :=
  (.hasShape "i" (.intIn 0 1023))

def freigeben_if_writes : List String := ["frei", "Halde", "g"]

/-- What a caller of `freigeben_if` has to bring: a well-typed world and the precondition. -/
def freigeben_if_requires (t : State) : Prop := wellFormed t ∧ eval t freigeben_if_pre = some (.bool true)

/-- What `freigeben_if` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigeben_if_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `freigeben_narrow` -/

def freigeben_narrow_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "i") (.lit (.int 0))) (.bin .lt (.name "i") (.global "hinterlegt"))) [] [(.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true))), (.ret none)]), (.assign "Halde" (.name "i") "naechst" (.global "frei")), (.assignGlobal "frei" (.someOf (.name "i"))), (.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def freigeben_narrow_pre : Expr :=
  (.hasShape "i" (.intIn 0 1023))

def freigeben_narrow_writes : List String := ["frei", "Halde", "g"]

/-- What a caller of `freigeben_narrow` has to bring: a well-typed world and the precondition. -/
def freigeben_narrow_requires (t : State) : Prop := wellFormed t ∧ eval t freigeben_narrow_pre = some (.bool true)

/-- What `freigeben_narrow` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def freigeben_narrow_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `kopf_lesen` -/

def kopf_lesen_body : List Stmt :=
  [(.bindCallElse "w" "kopf" ["h"] [(.name "h")] (.lit (.bool true)) "e" [(.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true))), (.call "abbruch" [] [] (.lit (.bool true)))]), (.call "griff_weg" ["g"] [(.name "g")] (.lit (.bool true))), (.ret (some (.name "w")))]

/-- The precondition: the declared shapes and the `requires`. -/
def kopf_lesen_pre : Expr :=
  (.lit (.bool true))

def kopf_lesen_writes : List String := ["g"]

/-- What a caller of `kopf_lesen` has to bring: a well-typed world and the precondition. -/
def kopf_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t kopf_lesen_pre = some (.bool true)

/-- What `kopf_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kopf_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `belegen` -/

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
  have hall := hpre
  gabbro_simp_at hall [belegen_pre]
  gabbro_auto [belegen_body, belegen_pre, belegen_post, wellFormed, hall] using shapeOf

/-! ### `freigeben_if` -/

/-- **The duty of `freigeben_if`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def freigeben_if_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s freigeben_if_pre = some (.bool true))
    -- the contract of `griff_weg`
    (c_griff_weg : Contract ρ "griff_weg" griff_weg_requires griff_weg_post)
    -- the frame of `griff_weg`
    (fr_griff_weg : Frame ρ "griff_weg" griff_weg_writes),
    ∃ s', finalState (exec ρ freigeben_if_body s) = some s'
        ∧ freigeben_if_post s s' (finalValue (exec ρ freigeben_if_body s))

theorem freigeben_if_meets : freigeben_if_meets_statement := by
  unfold freigeben_if_meets_statement
  intro ρ s hwf hpre c_griff_weg fr_griff_weg
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [freigeben_if_pre, e_i]
  gabbro_auto [freigeben_if_body, freigeben_if_pre, freigeben_if_post, wellFormed, griff_weg_pre, griff_weg_requires, griff_weg_post, griff_weg_writes, Frame_read _ _ _ fr_griff_weg, e_i, hall] using shapeOf

/-! ### `freigeben_narrow` -/

/-- **The duty of `freigeben_narrow`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def freigeben_narrow_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s freigeben_narrow_pre = some (.bool true))
    -- the contract of `griff_weg`
    (c_griff_weg : Contract ρ "griff_weg" griff_weg_requires griff_weg_post)
    -- the frame of `griff_weg`
    (fr_griff_weg : Frame ρ "griff_weg" griff_weg_writes),
    ∃ s', finalState (exec ρ freigeben_narrow_body s) = some s'
        ∧ freigeben_narrow_post s s' (finalValue (exec ρ freigeben_narrow_body s))

theorem freigeben_narrow_meets : freigeben_narrow_meets_statement := by
  unfold freigeben_narrow_meets_statement
  intro ρ s hwf hpre c_griff_weg fr_griff_weg
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [freigeben_narrow_pre, e_i]
  gabbro_auto [freigeben_narrow_body, freigeben_narrow_pre, freigeben_narrow_post, wellFormed, griff_weg_pre, griff_weg_requires, griff_weg_post, griff_weg_writes, Frame_read _ _ _ fr_griff_weg, e_i, hall] using shapeOf

/-! ### `kopf_lesen` -/

/-- **The duty of `kopf_lesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kopf_lesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kopf_lesen_pre = some (.bool true))
    -- the contract of `abbruch`
    (c_abbruch : Contract ρ "abbruch" abbruch_requires abbruch_post)
    -- the frame of `abbruch`
    (fr_abbruch : Frame ρ "abbruch" abbruch_writes)
    -- the contract of `griff_weg`
    (c_griff_weg : Contract ρ "griff_weg" griff_weg_requires griff_weg_post)
    -- the frame of `griff_weg`
    (fr_griff_weg : Frame ρ "griff_weg" griff_weg_writes)
    -- the contract of `kopf`
    (c_kopf : Contract ρ "kopf" kopf_requires kopf_post)
    -- the frame of `kopf`
    (fr_kopf : Frame ρ "kopf" kopf_writes),
    ∃ s', finalState (exec ρ kopf_lesen_body s) = some s'
        ∧ kopf_lesen_post s s' (finalValue (exec ρ kopf_lesen_body s))

theorem kopf_lesen_meets : kopf_lesen_meets_statement := by
  unfold kopf_lesen_meets_statement
  intro ρ s hwf hpre c_abbruch fr_abbruch c_griff_weg fr_griff_weg c_kopf fr_kopf
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [kopf_lesen_pre]
  gabbro_auto [kopf_lesen_body, kopf_lesen_pre, kopf_lesen_post, wellFormed, abbruch_pre, abbruch_requires, abbruch_post, abbruch_writes, Frame_read _ _ _ fr_abbruch, griff_weg_pre, griff_weg_requires, griff_weg_post, griff_weg_writes, Frame_read _ _ _ fr_griff_weg, kopf_pre, kopf_requires, kopf_post, kopf_writes, Frame_read _ _ _ fr_kopf, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "belegen" belegen_body
  ∧ Frame ρ "belegen" belegen_writes
  ∧ Runs ρ "freigeben_if" freigeben_if_body
  ∧ Frame ρ "freigeben_if" freigeben_if_writes
  ∧ Runs ρ "freigeben_narrow" freigeben_narrow_body
  ∧ Frame ρ "freigeben_narrow" freigeben_narrow_writes
  ∧ Runs ρ "kopf_lesen" kopf_lesen_body
  ∧ Frame ρ "kopf_lesen" kopf_lesen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_belegen : belegen_meets_statement)
    (d_freigeben_if : freigeben_if_meets_statement)
    (d_freigeben_narrow : freigeben_narrow_meets_statement)
    (d_kopf_lesen : kopf_lesen_meets_statement) :
    Contract ρ "belegen" belegen_requires belegen_post
    ∧ Contract ρ "freigeben_if" freigeben_if_requires freigeben_if_post
    ∧ Contract ρ "freigeben_narrow" freigeben_narrow_requires freigeben_narrow_post
    ∧ Contract ρ "kopf_lesen" kopf_lesen_requires kopf_lesen_post := by
  obtain ⟨r_belegen, fr_belegen, r_freigeben_if, fr_freigeben_if, r_freigeben_narrow, fr_freigeben_narrow, r_kopf_lesen, fr_kopf_lesen⟩ := hp
  obtain ⟨c_abbruch, fr_abbruch, c_griff_weg, fr_griff_weg, c_kopf, fr_kopf⟩ := ha
  have c_belegen : Contract ρ "belegen" belegen_requires belegen_post :=
    contract_of_duty ρ "belegen" belegen_body belegen_requires belegen_post r_belegen
      (fun t ht => d_belegen ρ t ht.1 ht.2)
  have c_freigeben_if : Contract ρ "freigeben_if" freigeben_if_requires freigeben_if_post :=
    contract_of_duty ρ "freigeben_if" freigeben_if_body freigeben_if_requires freigeben_if_post r_freigeben_if
      (fun t ht => d_freigeben_if ρ t ht.1 ht.2 c_griff_weg fr_griff_weg)
  have c_freigeben_narrow : Contract ρ "freigeben_narrow" freigeben_narrow_requires freigeben_narrow_post :=
    contract_of_duty ρ "freigeben_narrow" freigeben_narrow_body freigeben_narrow_requires freigeben_narrow_post r_freigeben_narrow
      (fun t ht => d_freigeben_narrow ρ t ht.1 ht.2 c_griff_weg fr_griff_weg)
  have c_kopf_lesen : Contract ρ "kopf_lesen" kopf_lesen_requires kopf_lesen_post :=
    contract_of_duty ρ "kopf_lesen" kopf_lesen_body kopf_lesen_requires kopf_lesen_post r_kopf_lesen
      (fun t ht => d_kopf_lesen ρ t ht.1 ht.2 c_abbruch fr_abbruch c_griff_weg fr_griff_weg c_kopf fr_kopf)
  exact ⟨c_belegen, c_freigeben_if, c_freigeben_narrow, c_kopf_lesen⟩

end GabbroDuty.Duty58FreilisteZweiFormen
