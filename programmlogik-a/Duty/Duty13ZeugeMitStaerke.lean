/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/13-zeuge-mit-staerke.gab  total 2  goals 2  refused 0
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

namespace GabbroDuty.Duty13ZeugeMitStaerke

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  aufloesen :: fremd requires #1  --  carried by `aufloesen_meets`
  duty_2  V  aufloesen :: liest requires #1  --  carried by `aufloesen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Raum" _ "belegt" => some .bool
  | .slot "Raum" _ "rechte" => some (.intIn 0 15)
  | .field "Zaehlwerk" "wert" => some (.intIn 0 4294967295)
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

/-! ### `aufloesen` -/

def aufloesen_body : List Stmt :=
  [(.locked "KAPPEN" [(.call "fremd" ["z"] [(.name "z")] (.lit (.bool true))), (.retCall "liest" ["k", "i"] [(.name "k"), (.name "i")] (.bin .and (.hasShape "i" (.intIn 0 63)) (.lit (.bool true))))]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def aufloesen_pre : Expr :=
  (.hasShape "i" (.intIn 0 63))

def aufloesen_writes : List String := ["Zaehlwerk"]

/-- What a caller of `aufloesen` has to bring: a well-typed world and the precondition. -/
def aufloesen_requires (t : State) : Prop := wellFormed t ∧ eval t aufloesen_pre = some (.bool true)

/-- What `aufloesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aufloesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 15)

/-! ### `fremd` -/

def fremd_body : List Stmt :=
  [(.assignField "Zaehlwerk" "wert" (.lit (.int 0)))]

/-- The precondition: the declared shapes and the `requires`. -/
def fremd_pre : Expr :=
  (.lit (.bool true))

def fremd_writes : List String := ["Zaehlwerk"]

/-- What a caller of `fremd` has to bring: a well-typed world and the precondition. -/
def fremd_requires (t : State) : Prop := wellFormed t ∧ eval t fremd_pre = some (.bool true)

/-- What `fremd` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def fremd_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `liest` -/

def liest_body : List Stmt :=
  [(.ret (some (.place "Raum" (.name "i") "rechte")))]

/-- The precondition: the declared shapes and the `requires`. -/
def liest_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 63)) (.lit (.bool true)))

def liest_writes : List String := []

/-- What a caller of `liest` has to bring: a well-typed world and the precondition. -/
def liest_requires (t : State) : Prop := wellFormed t ∧ eval t liest_pre = some (.bool true)

/-- What `liest` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def liest_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 15)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `aufloesen` -/

/-- **The duty of `aufloesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aufloesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aufloesen_pre = some (.bool true))
    -- the contract of `fremd`
    (c_fremd : Contract ρ "fremd" fremd_requires fremd_post)
    -- the frame of `fremd`
    (fr_fremd : Frame ρ "fremd" fremd_writes)
    -- the contract of `liest`
    (c_liest : Contract ρ "liest" liest_requires liest_post)
    -- the frame of `liest`
    (fr_liest : Frame ρ "liest" liest_writes),
    ∃ s', finalState (exec ρ aufloesen_body s) = some s'
        ∧ aufloesen_post s s' (finalValue (exec ρ aufloesen_body s))

theorem aufloesen_meets : aufloesen_meets_statement := by
  unfold aufloesen_meets_statement
  intro ρ s hwf hpre c_fremd fr_fremd c_liest fr_liest
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [aufloesen_pre, e_i]
  gabbro_auto [aufloesen_body, aufloesen_pre, aufloesen_post, wellFormed, fremd_pre, fremd_requires, fremd_post, fremd_writes, Frame_read _ _ _ fr_fremd, liest_pre, liest_requires, liest_post, liest_writes, Frame_read _ _ _ fr_liest, e_i, hall] using shapeOf

/-! ### `fremd` -/

/-- **The duty of `fremd`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def fremd_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s fremd_pre = some (.bool true)),
    ∃ s', finalState (exec ρ fremd_body s) = some s'
        ∧ fremd_post s s' (finalValue (exec ρ fremd_body s))

theorem fremd_meets : fremd_meets_statement := by
  unfold fremd_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Zaehlwerk_wert, h_Zaehlwerk_wert, lo_Zaehlwerk_wert, hi_Zaehlwerk_wert⟩ := WF_intIn shapeOf s.world (.field "Zaehlwerk" "wert") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [fremd_pre, h_Zaehlwerk_wert]
  gabbro_auto [fremd_body, fremd_pre, fremd_post, wellFormed, h_Zaehlwerk_wert, hall] using shapeOf

/-! ### `liest` -/

/-- **The duty of `liest`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def liest_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s liest_pre = some (.bool true)),
    ∃ s', finalState (exec ρ liest_body s) = some s'
        ∧ liest_post s s' (finalValue (exec ρ liest_body s))

theorem liest_meets : liest_meets_statement := by
  unfold liest_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Raum_rechte_i, h_Raum_rechte_i, lo_Raum_rechte_i, hi_Raum_rechte_i⟩ := WF_intIn shapeOf s.world (.slot "Raum" w_i "rechte") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [liest_pre, e_i, h_Raum_rechte_i]
  gabbro_auto [liest_body, liest_pre, liest_post, wellFormed, e_i, h_Raum_rechte_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aufloesen" aufloesen_body
  ∧ Frame ρ "aufloesen" aufloesen_writes
  ∧ Runs ρ "fremd" fremd_body
  ∧ Frame ρ "fremd" fremd_writes
  ∧ Runs ρ "liest" liest_body
  ∧ Frame ρ "liest" liest_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_fremd : fremd_meets_statement)
    (d_liest : liest_meets_statement)
    (d_aufloesen : aufloesen_meets_statement) :
    Contract ρ "fremd" fremd_requires fremd_post
    ∧ Contract ρ "liest" liest_requires liest_post
    ∧ Contract ρ "aufloesen" aufloesen_requires aufloesen_post := by
  obtain ⟨r_aufloesen, fr_aufloesen, r_fremd, fr_fremd, r_liest, fr_liest⟩ := hp
  have c_fremd : Contract ρ "fremd" fremd_requires fremd_post :=
    contract_of_duty ρ "fremd" fremd_body fremd_requires fremd_post r_fremd
      (fun t ht => d_fremd ρ t ht.1 ht.2)
  have c_liest : Contract ρ "liest" liest_requires liest_post :=
    contract_of_duty ρ "liest" liest_body liest_requires liest_post r_liest
      (fun t ht => d_liest ρ t ht.1 ht.2)
  have c_aufloesen : Contract ρ "aufloesen" aufloesen_requires aufloesen_post :=
    contract_of_duty ρ "aufloesen" aufloesen_body aufloesen_requires aufloesen_post r_aufloesen
      (fun t ht => d_aufloesen ρ t ht.1 ht.2 c_fremd fr_fremd c_liest fr_liest)
  exact ⟨c_fremd, c_liest, c_aufloesen⟩

end GabbroDuty.Duty13ZeugeMitStaerke
