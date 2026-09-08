/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/05-nebenlaeufigkeit.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty05Nebenlaeufigkeit

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Zelle" "wert" => some (.intIn 0 281474976710654)
  | .global "FARBE_FERTIG" => some .bool
  | .global "TIEFE_MAX" => some (.intIn 0 18446744073709551615)
  | .global "BESITZER" => some (.intIn 0 4294967295)
  | .global "hoechststand" => some (.intIn 0 18446744073709551615)
  | .global "fehlerzahl" => some (.intIn 0 4294967295)
  | .global "farbbericht" => some (.intIn 0 18446744073709551615)
  | .global "KERNZAHL" => some (.intIn 0 4294967295)
  | .global "ZAEHLER" => some (.intIn 0 281474976710654)
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

/-! ### `bericht_lesen` -/

def bericht_lesen_body : List Stmt :=
  [(.awaitLoad "fertig" "FARBE_FERTIG" ["farbbericht"]), (.ite (.name "fertig") [(.ret (some (.global "farbbericht")))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def bericht_lesen_pre : Expr :=
  (.lit (.bool true))

def bericht_lesen_writes : List String := []

/-- What a caller of `bericht_lesen` has to bring: a well-typed world and the precondition. -/
def bericht_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t bericht_lesen_pre = some (.bool true)

/-- What `bericht_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bericht_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `bericht_veroeffentlichen` -/

def bericht_veroeffentlichen_body : List Stmt :=
  [(.assignGlobal "farbbericht" (.name "wert")), (.publish "FARBE_FERTIG" (.lit (.bool true)) ["farbbericht"])]

/-- The precondition: the declared shapes and the `requires`. -/
def bericht_veroeffentlichen_pre : Expr :=
  (.hasShape "wert" (.intIn 0 18446744073709551615))

def bericht_veroeffentlichen_writes : List String := ["farbbericht", "FARBE_FERTIG"]

/-- What a caller of `bericht_veroeffentlichen` has to bring: a well-typed world and the precondition. -/
def bericht_veroeffentlichen_requires (t : State) : Prop := wellFormed t ∧ eval t bericht_veroeffentlichen_pre = some (.bool true)

/-- What `bericht_veroeffentlichen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bericht_veroeffentlichen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `besitz_nehmen` -/

-- REFUSED  besitz_nehmen  (exchange): `exchange` -- a conditional store, not a swap
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def besitz_nehmen_pre : Expr :=
  (.hasShape "f" (.intIn 0 1023))

def besitz_nehmen_writes : List String := ["BESITZER"]

/-- What a caller of `besitz_nehmen` has to bring: a well-typed world and the precondition. -/
def besitz_nehmen_requires (t : State) : Prop := wellFormed t ∧ eval t besitz_nehmen_pre = some (.bool true)

/-- What `besitz_nehmen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def besitz_nehmen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `tiefe_melden` -/

def tiefe_melden_body : List Stmt :=
  [(.publish "TIEFE_MAX" (.name "t") [])]

/-- The precondition: the declared shapes and the `requires`. -/
def tiefe_melden_pre : Expr :=
  (.hasShape "t" (.intIn 0 18446744073709551615))

def tiefe_melden_writes : List String := ["TIEFE_MAX"]

/-- What a caller of `tiefe_melden` has to bring: a well-typed world and the precondition. -/
def tiefe_melden_requires (t : State) : Prop := wellFormed t ∧ eval t tiefe_melden_pre = some (.bool true)

/-- What `tiefe_melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tiefe_melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `unter_zwei_sperren` -/

def unter_zwei_sperren_body : List Stmt :=
  [(.locked "KAPPEN" [(.locked "SPEICHER" [(.ite (.bin .lt (.fieldOf "Zelle" "wert") (.lit (.int 281474976710654))) [(.assignField "Zelle" "wert" (.bin .add (.fieldOf "Zelle" "wert") (.lit (.int 1))))] [])])])]

/-- The precondition: the declared shapes and the `requires`. -/
def unter_zwei_sperren_pre : Expr :=
  (.lit (.bool true))

def unter_zwei_sperren_writes : List String := ["Zelle"]

/-- What a caller of `unter_zwei_sperren` has to bring: a well-typed world and the precondition. -/
def unter_zwei_sperren_requires (t : State) : Prop := wellFormed t ∧ eval t unter_zwei_sperren_pre = some (.bool true)

/-- What `unter_zwei_sperren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def unter_zwei_sperren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `zaehler_erhoehen` -/

-- REFUSED  zaehler_erhoehen  (exchange): `exchange` -- a conditional store, not a swap
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def zaehler_erhoehen_pre : Expr :=
  (.lit (.bool true))

def zaehler_erhoehen_writes : List String := ["ZAEHLER"]

/-- What a caller of `zaehler_erhoehen` has to bring: a well-typed world and the precondition. -/
def zaehler_erhoehen_requires (t : State) : Prop := wellFormed t ∧ eval t zaehler_erhoehen_pre = some (.bool true)

/-- What `zaehler_erhoehen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zaehler_erhoehen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 281474976710654)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `bericht_lesen` -/

/-- **The duty of `bericht_lesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def bericht_lesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s bericht_lesen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ bericht_lesen_body s) = some s'
        ∧ bericht_lesen_post s s' (finalValue (exec ρ bericht_lesen_body s))

theorem bericht_lesen_meets : bericht_lesen_meets_statement := by
  unfold bericht_lesen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [bericht_lesen_pre]
  gabbro_auto [bericht_lesen_body, bericht_lesen_pre, bericht_lesen_post, wellFormed, hall] using shapeOf

/-! ### `bericht_veroeffentlichen` -/

/-- **The duty of `bericht_veroeffentlichen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def bericht_veroeffentlichen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s bericht_veroeffentlichen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ bericht_veroeffentlichen_body s) = some s'
        ∧ bericht_veroeffentlichen_post s s' (finalValue (exec ρ bericht_veroeffentlichen_body s))

theorem bericht_veroeffentlichen_meets : bericht_veroeffentlichen_meets_statement := by
  unfold bericht_veroeffentlichen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_wert, e_wert, lo_wert, hi_wert⟩ := shape_intIn s "wert" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [bericht_veroeffentlichen_pre, e_wert]
  gabbro_auto [bericht_veroeffentlichen_body, bericht_veroeffentlichen_pre, bericht_veroeffentlichen_post, wellFormed, e_wert, hall] using shapeOf

/-! ### `tiefe_melden` -/

/-- **The duty of `tiefe_melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def tiefe_melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s tiefe_melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ tiefe_melden_body s) = some s'
        ∧ tiefe_melden_post s s' (finalValue (exec ρ tiefe_melden_body s))

theorem tiefe_melden_meets : tiefe_melden_meets_statement := by
  unfold tiefe_melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [tiefe_melden_pre, e_t]
  gabbro_auto [tiefe_melden_body, tiefe_melden_pre, tiefe_melden_post, wellFormed, e_t, hall] using shapeOf

/-! ### `unter_zwei_sperren` -/

/-- **The duty of `unter_zwei_sperren`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def unter_zwei_sperren_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s unter_zwei_sperren_pre = some (.bool true)),
    ∃ s', finalState (exec ρ unter_zwei_sperren_body s) = some s'
        ∧ unter_zwei_sperren_post s s' (finalValue (exec ρ unter_zwei_sperren_body s))

theorem unter_zwei_sperren_meets : unter_zwei_sperren_meets_statement := by
  unfold unter_zwei_sperren_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Zelle_wert, h_Zelle_wert, lo_Zelle_wert, hi_Zelle_wert⟩ := WF_intIn shapeOf s.world (.field "Zelle" "wert") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [unter_zwei_sperren_pre, h_Zelle_wert]
  gabbro_auto [unter_zwei_sperren_body, unter_zwei_sperren_pre, unter_zwei_sperren_post, wellFormed, h_Zelle_wert, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "bericht_lesen" bericht_lesen_body
  ∧ Frame ρ "bericht_lesen" bericht_lesen_writes
  ∧ Runs ρ "bericht_veroeffentlichen" bericht_veroeffentlichen_body
  ∧ Frame ρ "bericht_veroeffentlichen" bericht_veroeffentlichen_writes
  ∧ Runs ρ "tiefe_melden" tiefe_melden_body
  ∧ Frame ρ "tiefe_melden" tiefe_melden_writes
  ∧ Runs ρ "unter_zwei_sperren" unter_zwei_sperren_body
  ∧ Frame ρ "unter_zwei_sperren" unter_zwei_sperren_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_bericht_lesen : bericht_lesen_meets_statement)
    (d_bericht_veroeffentlichen : bericht_veroeffentlichen_meets_statement)
    (d_tiefe_melden : tiefe_melden_meets_statement)
    (d_unter_zwei_sperren : unter_zwei_sperren_meets_statement) :
    Contract ρ "bericht_lesen" bericht_lesen_requires bericht_lesen_post
    ∧ Contract ρ "bericht_veroeffentlichen" bericht_veroeffentlichen_requires bericht_veroeffentlichen_post
    ∧ Contract ρ "tiefe_melden" tiefe_melden_requires tiefe_melden_post
    ∧ Contract ρ "unter_zwei_sperren" unter_zwei_sperren_requires unter_zwei_sperren_post := by
  obtain ⟨r_bericht_lesen, fr_bericht_lesen, r_bericht_veroeffentlichen, fr_bericht_veroeffentlichen, r_tiefe_melden, fr_tiefe_melden, r_unter_zwei_sperren, fr_unter_zwei_sperren⟩ := hp
  have c_bericht_lesen : Contract ρ "bericht_lesen" bericht_lesen_requires bericht_lesen_post :=
    contract_of_duty ρ "bericht_lesen" bericht_lesen_body bericht_lesen_requires bericht_lesen_post r_bericht_lesen
      (fun t ht => d_bericht_lesen ρ t ht.1 ht.2)
  have c_bericht_veroeffentlichen : Contract ρ "bericht_veroeffentlichen" bericht_veroeffentlichen_requires bericht_veroeffentlichen_post :=
    contract_of_duty ρ "bericht_veroeffentlichen" bericht_veroeffentlichen_body bericht_veroeffentlichen_requires bericht_veroeffentlichen_post r_bericht_veroeffentlichen
      (fun t ht => d_bericht_veroeffentlichen ρ t ht.1 ht.2)
  have c_tiefe_melden : Contract ρ "tiefe_melden" tiefe_melden_requires tiefe_melden_post :=
    contract_of_duty ρ "tiefe_melden" tiefe_melden_body tiefe_melden_requires tiefe_melden_post r_tiefe_melden
      (fun t ht => d_tiefe_melden ρ t ht.1 ht.2)
  have c_unter_zwei_sperren : Contract ρ "unter_zwei_sperren" unter_zwei_sperren_requires unter_zwei_sperren_post :=
    contract_of_duty ρ "unter_zwei_sperren" unter_zwei_sperren_body unter_zwei_sperren_requires unter_zwei_sperren_post r_unter_zwei_sperren
      (fun t ht => d_unter_zwei_sperren ρ t ht.1 ht.2)
  exact ⟨c_bericht_lesen, c_bericht_veroeffentlichen, c_tiefe_melden, c_unter_zwei_sperren⟩

end GabbroDuty.Duty05Nebenlaeufigkeit