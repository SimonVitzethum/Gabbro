/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/grammatik/messreihe.gab  total 1  goals 0  refused 1
        @assumed 0  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 1 are refused forms

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

namespace GabbroDuty.DutyMessreihe

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  layout-buffer-length (1): refused -- `lenof` over a buffer whose length no declaration gives -- `lenof` over a fixed-length array IS carried; give the parameter an array type, or drop the clause
    duty_1  N  folge_lesen :: ensures #1
      (inherited: this clause HAS a term; the body or the `requires` of `folge_lesen` has none)

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  folge_lesen :: ensures #1  --  refused (layout-buffer-length)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "Messkopf" "folge" => some (.intIn 0 18446744073709551615)
  | .field "Messkopf" "kerne" => some (.intIn 0 18446744073709551615)
  | .global "tiefste_temperatur" => some (.intIn 0 4294967295)
  | .global "alle_kalibriert" => some (.intIn 0 4294967295)
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

/-! ### `abweichung_summe` -/

def abweichung_summe_body : List Stmt :=
  [(.ret (some (.bin .add (.name "a") (.name "b"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def abweichung_summe_pre : Expr :=
  (.bin .and (.hasShape "a" (.intIn (-60) 60)) (.hasShape "b" (.intIn (-60) 60)))

def abweichung_summe_writes : List String := []

/-- What a caller of `abweichung_summe` has to bring: a well-typed world and the precondition. -/
def abweichung_summe_requires (t : State) : Prop := wellFormed t ∧ eval t abweichung_summe_pre = some (.bool true)

/-- What `abweichung_summe` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abweichung_summe_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ (-8000) ≤ x ∧ x ≤ 8000)

/-! ### `folge_lesen` -/

-- REFUSED  folge_lesen  (layout-buffer-length): `lenof` over a buffer whose length no declaration gives -- `lenof` over a fixed-length array IS carried; give the parameter an array type, or drop the clause
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def folge_lesen_pre : Expr :=
  (.lit (.bool true))

def folge_lesen_writes : List String := []

/-- What a caller of `folge_lesen` has to bring: a well-typed world and the precondition. -/
def folge_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t folge_lesen_pre = some (.bool true)

/-- What `folge_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def folge_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)
  ∧ -- ensures #1
  (∃ v, r = some v ∧ eval { world := s'.world, local' := (bindLocal s.local' "result" v) } (.bin .eq (.name "result") (.fieldOf "Messkopf" "folge")) = some (.bool true))

/-! ### `kalibrierung_melden` -/

def kalibrierung_melden_body : List Stmt :=
  [(.assignGlobal "alle_kalibriert" (.name "k"))]

/-- The precondition: the declared shapes and the `requires`. -/
def kalibrierung_melden_pre : Expr :=
  (.hasShape "k" (.intIn 0 4294967295))

def kalibrierung_melden_writes : List String := ["alle_kalibriert"]

/-- What a caller of `kalibrierung_melden` has to bring: a well-typed world and the precondition. -/
def kalibrierung_melden_requires (t : State) : Prop := wellFormed t ∧ eval t kalibrierung_melden_pre = some (.bool true)

/-- What `kalibrierung_melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kalibrierung_melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `mittel_bereinigt` -/

-- REFUSED  mittel_bereinigt  (narrow): `narrow` -- the model has no range to narrow into
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def mittel_bereinigt_pre : Expr :=
  (.lit (.bool true))

def mittel_bereinigt_writes : List String := []

/-- What a caller of `mittel_bereinigt` has to bring: a well-typed world and the precondition. -/
def mittel_bereinigt_requires (t : State) : Prop := wellFormed t ∧ eval t mittel_bereinigt_pre = some (.bool true)

/-- What `mittel_bereinigt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def mittel_bereinigt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `tiefstwert_melden` -/

def tiefstwert_melden_body : List Stmt :=
  [(.assignGlobal "tiefste_temperatur" (.name "t"))]

/-- The precondition: the declared shapes and the `requires`. -/
def tiefstwert_melden_pre : Expr :=
  (.hasShape "t" (.intIn 0 4294967295))

def tiefstwert_melden_writes : List String := ["tiefste_temperatur"]

/-- What a caller of `tiefstwert_melden` has to bring: a well-typed world and the precondition. -/
def tiefstwert_melden_requires (t : State) : Prop := wellFormed t ∧ eval t tiefstwert_melden_pre = some (.bool true)

/-- What `tiefstwert_melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def tiefstwert_melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `versatz_weiten` -/

def versatz_weiten_body : List Stmt :=
  [(.ret (some (.name "v")))]

/-- The precondition: the declared shapes and the `requires`. -/
def versatz_weiten_pre : Expr :=
  (.hasShape "v" (.intIn (-1000000) 1000000))

def versatz_weiten_writes : List String := []

/-- What a caller of `versatz_weiten` has to bring: a well-typed world and the precondition. -/
def versatz_weiten_requires (t : State) : Prop := wellFormed t ∧ eval t versatz_weiten_pre = some (.bool true)

/-- What `versatz_weiten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def versatz_weiten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ (-1000000000) ≤ x ∧ x ≤ 1000000000)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abweichung_summe` -/

/-- **The duty of `abweichung_summe`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abweichung_summe_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abweichung_summe_pre = some (.bool true)),
    ∃ s', finalState (exec ρ abweichung_summe_body s) = some s'
        ∧ abweichung_summe_post s s' (finalValue (exec ρ abweichung_summe_body s))

theorem abweichung_summe_meets : abweichung_summe_meets_statement := by
  unfold abweichung_summe_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [abweichung_summe_pre, e_a, e_b]
  gabbro_auto [abweichung_summe_body, abweichung_summe_pre, abweichung_summe_post, wellFormed, e_a, e_b, hall] using shapeOf

/-! ### `kalibrierung_melden` -/

/-- **The duty of `kalibrierung_melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kalibrierung_melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kalibrierung_melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ kalibrierung_melden_body s) = some s'
        ∧ kalibrierung_melden_post s s' (finalValue (exec ρ kalibrierung_melden_body s))

theorem kalibrierung_melden_meets : kalibrierung_melden_meets_statement := by
  unfold kalibrierung_melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_k, e_k, lo_k, hi_k⟩ := shape_intIn s "k" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [kalibrierung_melden_pre, e_k]
  gabbro_auto [kalibrierung_melden_body, kalibrierung_melden_pre, kalibrierung_melden_post, wellFormed, e_k, hall] using shapeOf

/-! ### `tiefstwert_melden` -/

/-- **The duty of `tiefstwert_melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def tiefstwert_melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s tiefstwert_melden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ tiefstwert_melden_body s) = some s'
        ∧ tiefstwert_melden_post s s' (finalValue (exec ρ tiefstwert_melden_body s))

theorem tiefstwert_melden_meets : tiefstwert_melden_meets_statement := by
  unfold tiefstwert_melden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [tiefstwert_melden_pre, e_t]
  gabbro_auto [tiefstwert_melden_body, tiefstwert_melden_pre, tiefstwert_melden_post, wellFormed, e_t, hall] using shapeOf

/-! ### `versatz_weiten` -/

/-- **The duty of `versatz_weiten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def versatz_weiten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s versatz_weiten_pre = some (.bool true)),
    ∃ s', finalState (exec ρ versatz_weiten_body s) = some s'
        ∧ versatz_weiten_post s s' (finalValue (exec ρ versatz_weiten_body s))

theorem versatz_weiten_meets : versatz_weiten_meets_statement := by
  unfold versatz_weiten_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_v, e_v, lo_v, hi_v⟩ := shape_intIn s "v" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [versatz_weiten_pre, e_v]
  gabbro_auto [versatz_weiten_body, versatz_weiten_pre, versatz_weiten_post, wellFormed, e_v, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abweichung_summe" abweichung_summe_body
  ∧ Frame ρ "abweichung_summe" abweichung_summe_writes
  ∧ Runs ρ "kalibrierung_melden" kalibrierung_melden_body
  ∧ Frame ρ "kalibrierung_melden" kalibrierung_melden_writes
  ∧ Runs ρ "tiefstwert_melden" tiefstwert_melden_body
  ∧ Frame ρ "tiefstwert_melden" tiefstwert_melden_writes
  ∧ Runs ρ "versatz_weiten" versatz_weiten_body
  ∧ Frame ρ "versatz_weiten" versatz_weiten_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abweichung_summe : abweichung_summe_meets_statement)
    (d_kalibrierung_melden : kalibrierung_melden_meets_statement)
    (d_tiefstwert_melden : tiefstwert_melden_meets_statement)
    (d_versatz_weiten : versatz_weiten_meets_statement) :
    Contract ρ "abweichung_summe" abweichung_summe_requires abweichung_summe_post
    ∧ Contract ρ "kalibrierung_melden" kalibrierung_melden_requires kalibrierung_melden_post
    ∧ Contract ρ "tiefstwert_melden" tiefstwert_melden_requires tiefstwert_melden_post
    ∧ Contract ρ "versatz_weiten" versatz_weiten_requires versatz_weiten_post := by
  obtain ⟨r_abweichung_summe, fr_abweichung_summe, r_kalibrierung_melden, fr_kalibrierung_melden, r_tiefstwert_melden, fr_tiefstwert_melden, r_versatz_weiten, fr_versatz_weiten⟩ := hp
  have c_abweichung_summe : Contract ρ "abweichung_summe" abweichung_summe_requires abweichung_summe_post :=
    contract_of_duty ρ "abweichung_summe" abweichung_summe_body abweichung_summe_requires abweichung_summe_post r_abweichung_summe
      (fun t ht => d_abweichung_summe ρ t ht.1 ht.2)
  have c_kalibrierung_melden : Contract ρ "kalibrierung_melden" kalibrierung_melden_requires kalibrierung_melden_post :=
    contract_of_duty ρ "kalibrierung_melden" kalibrierung_melden_body kalibrierung_melden_requires kalibrierung_melden_post r_kalibrierung_melden
      (fun t ht => d_kalibrierung_melden ρ t ht.1 ht.2)
  have c_tiefstwert_melden : Contract ρ "tiefstwert_melden" tiefstwert_melden_requires tiefstwert_melden_post :=
    contract_of_duty ρ "tiefstwert_melden" tiefstwert_melden_body tiefstwert_melden_requires tiefstwert_melden_post r_tiefstwert_melden
      (fun t ht => d_tiefstwert_melden ρ t ht.1 ht.2)
  have c_versatz_weiten : Contract ρ "versatz_weiten" versatz_weiten_requires versatz_weiten_post :=
    contract_of_duty ρ "versatz_weiten" versatz_weiten_body versatz_weiten_requires versatz_weiten_post r_versatz_weiten
      (fun t ht => d_versatz_weiten ρ t ht.1 ht.2)
  exact ⟨c_abweichung_summe, c_kalibrierung_melden, c_tiefstwert_melden, c_versatz_weiten⟩

end GabbroDuty.DutyMessreihe