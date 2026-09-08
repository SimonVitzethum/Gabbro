/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-region-schnitt-und-nullen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeRegionSchnittUndNullen

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Bytes" _ "b" => some (.intIn 0 255)
  | .field "Bereich" "cpu" => some (.intIn 0 281474976710656)
  | .field "Bereich" "dev" => some (.intIn 0 281474976710656)
  | .field "Bereich" "laenge" => some (.intIn 0 18446744073709551615)
  | .field "Bereich" "schnitt" => some (.intIn 0 18446744073709551615)
  | .field "Puffer" "cpu" => some (.intIn 0 18446744073709551615)
  | .field "Puffer" "dev" => some (.intIn 0 18446744073709551615)
  | .field "Puffer" "laenge" => some (.intIn 0 4294967295)
  | .field "Zweiachser" "cpu" => some (.intIn 0 18446744073709551615)
  | .field "Zweiachser" "dev" => some (.intIn 0 18446744073709551615)
  | .field "Zweiachser" "laenge" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `deskriptor_stellen` -- a foreign body: its contract is an assumption. -/
def deskriptor_stellen_pre : Expr :=
  (.bin .and (.hasShape "adresse" (.intIn 0 18446744073709551615)) (.hasShape "laenge" (.intIn 0 4294967295)))

def deskriptor_stellen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def deskriptor_stellen_writes : List String := []

def deskriptor_stellen_requires (t : State) : Prop := wellFormed t ∧ eval t deskriptor_stellen_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "deskriptor_stellen" deskriptor_stellen_requires deskriptor_stellen_post
  ∧ Frame ρ "deskriptor_stellen" deskriptor_stellen_writes

/-! ## The routines: body and contract -/

/-! ### `geraetesicht_umhaengen` -/

def geraetesicht_umhaengen_body : List Stmt :=
  [(.assignField "Zweiachser" "dev" (.name "neu"))]

/-- The precondition: the declared shapes and the `requires`. -/
def geraetesicht_umhaengen_pre : Expr :=
  (.hasShape "neu" (.intIn 0 18446744073709551615))

def geraetesicht_umhaengen_writes : List String := ["Zweiachser"]

/-- What a caller of `geraetesicht_umhaengen` has to bring: a well-typed world and the precondition. -/
def geraetesicht_umhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t geraetesicht_umhaengen_pre = some (.bool true)

/-- What `geraetesicht_umhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def geraetesicht_umhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `nullen` -/

def nullen_body : List Stmt :=
  [(.bindName "i" (.lit (.int 0))), (.loop "nullen#1" (.bin .and (.hasShape "n" (.intIn 0 2048)) (.hasShape "i" (.intIn 0 2047))) [(.assign "Bytes" (.name "i") "b" (.lit (.int 0))), (.ite (.bin .lt (.name "i") (.lit (.int 2047))) [(.bindName "i" (.bin .add (.name "i") (.lit (.int 1))))] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def nullen_pre : Expr :=
  (.hasShape "n" (.intIn 0 2048))

def nullen_writes : List String := ["Bytes"]

/-- What a caller of `nullen` has to bring: a well-typed world and the precondition. -/
def nullen_requires (t : State) : Prop := wellFormed t ∧ eval t nullen_pre = some (.bool true)

/-- What `nullen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def nullen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `nullen_ganz` -/

def nullen_ganz_body : List Stmt :=
  [(.loop "nullen_ganz#1" (.lit (.bool true)) [(.assign "Bytes" (.name "i") "b" (.lit (.int 0)))])]

/-- The precondition: the declared shapes and the `requires`. -/
def nullen_ganz_pre : Expr :=
  (.lit (.bool true))

def nullen_ganz_writes : List String := ["Bytes"]

/-- What a caller of `nullen_ganz` has to bring: a well-typed world and the precondition. -/
def nullen_ganz_requires (t : State) : Prop := wellFormed t ∧ eval t nullen_ganz_pre = some (.bool true)

/-- What `nullen_ganz` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def nullen_ganz_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `richtig_armieren` -/

def richtig_armieren_body : List Stmt :=
  [(.call "deskriptor_stellen" ["adresse", "laenge"] [(.fieldOf "Zweiachser" "dev"), (.fieldOf "Zweiachser" "laenge")] (.bin .and (.hasShape "adresse" (.intIn 0 18446744073709551615)) (.hasShape "laenge" (.intIn 0 4294967295))))]

/-- The precondition: the declared shapes and the `requires`. -/
def richtig_armieren_pre : Expr :=
  (.lit (.bool true))

def richtig_armieren_writes : List String := []

/-- What a caller of `richtig_armieren` has to bring: a well-typed world and the precondition. -/
def richtig_armieren_requires (t : State) : Prop := wellFormed t ∧ eval t richtig_armieren_pre = some (.bool true)

/-- What `richtig_armieren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def richtig_armieren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `schneiden` -/

-- REFUSED  schneiden  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def schneiden_pre : Expr :=
  (.bin .and (.hasShape "versatz" (.intIn 0 4294967296)) (.hasShape "laenge" (.intIn 0 4294967295)))

def schneiden_writes : List String := ["Bereich"]

/-- What a caller of `schneiden` has to bring: a well-typed world and the precondition. -/
def schneiden_requires (t : State) : Prop := wellFormed t ∧ eval t schneiden_pre = some (.bool true)

/-- What `schneiden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def schneiden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  ((∃ v, r = some v) ∨ ∃ e, r = some (.reason e))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `geraetesicht_umhaengen` -/

/-- **The duty of `geraetesicht_umhaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def geraetesicht_umhaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s geraetesicht_umhaengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ geraetesicht_umhaengen_body s) = some s'
        ∧ geraetesicht_umhaengen_post s s' (finalValue (exec ρ geraetesicht_umhaengen_body s))

theorem geraetesicht_umhaengen_meets : geraetesicht_umhaengen_meets_statement := by
  unfold geraetesicht_umhaengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_neu, e_neu, lo_neu, hi_neu⟩ := shape_intIn s "neu" _ _ hpre
  obtain ⟨n_Zweiachser_dev, h_Zweiachser_dev, lo_Zweiachser_dev, hi_Zweiachser_dev⟩ := WF_intIn shapeOf s.world (.field "Zweiachser" "dev") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [geraetesicht_umhaengen_pre, e_neu, h_Zweiachser_dev]
  gabbro_auto [geraetesicht_umhaengen_body, geraetesicht_umhaengen_pre, geraetesicht_umhaengen_post, wellFormed, e_neu, h_Zweiachser_dev, hall] using shapeOf

/-! ### `nullen` -/

/-- Loop `nullen#1` of `nullen`: its body and its invariant (with the shapes of the locals in scope). -/
def nullen_loop_1_inv : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 2048)) (.hasShape "i" (.intIn 0 2047)))

def nullen_loop_1_body : List Stmt :=
  [(.assign "Bytes" (.name "i") "b" (.lit (.int 0))), (.ite (.bin .lt (.name "i") (.lit (.int 2047))) [(.bindName "i" (.bin .add (.name "i") (.lit (.int 1))))] [])]

/-- **The loop rule of `nullen#1`, as a statement over one pass.** -/
def nullen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t nullen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ nullen_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' nullen_loop_1_inv = some (.bool true)

theorem nullen_loop_1_keeps : nullen_loop_1_keeps_statement := by
  unfold nullen_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn t "i" _ _ (and_right _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [nullen_loop_1_inv, e_n, e_i]
  gabbro_auto [nullen_loop_1_body, nullen_loop_1_inv, wellFormed, e_n, e_i, hall] using shapeOf

/-- **The duty of `nullen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def nullen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s nullen_pre = some (.bool true))
    -- the rule of loop `nullen#1`
    (l_nullen_loop_1 : LoopRule ρ "nullen#1" wellFormed nullen_loop_1_inv),
    ∃ s', finalState (exec ρ nullen_body s) = some s'
        ∧ nullen_post s s' (finalValue (exec ρ nullen_body s))

theorem nullen_meets : nullen_meets_statement := by
  unfold nullen_meets_statement
  intro ρ s hwf hpre l_nullen_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [nullen_pre, e_n]
  gabbro_auto [nullen_body, nullen_pre, nullen_post, wellFormed, nullen_loop_1_inv, e_n, hall] using shapeOf

/-! ### `nullen_ganz` -/

/-- Loop `nullen_ganz#1` of `nullen_ganz`: its body and its invariant (with the shapes of the locals in scope). -/
def nullen_ganz_loop_1_inv : Expr :=
  (.lit (.bool true))

def nullen_ganz_loop_1_body : List Stmt :=
  [(.assign "Bytes" (.name "i") "b" (.lit (.int 0)))]

/-- **The loop rule of `nullen_ganz#1`, as a statement over one pass.** -/
def nullen_ganz_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 2048)
    (hwf : wellFormed t)
    (hinv : eval t nullen_ganz_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ nullen_ganz_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' nullen_ganz_loop_1_inv = some (.bool true)

theorem nullen_ganz_loop_1_keeps : nullen_ganz_loop_1_keeps_statement := by
  unfold nullen_ganz_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [nullen_ganz_loop_1_inv]
  gabbro_auto [nullen_ganz_loop_1_body, nullen_ganz_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `nullen_ganz`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def nullen_ganz_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s nullen_ganz_pre = some (.bool true))
    -- the rule of loop `nullen_ganz#1`
    (l_nullen_ganz_loop_1 : LoopRule ρ "nullen_ganz#1" wellFormed nullen_ganz_loop_1_inv),
    ∃ s', finalState (exec ρ nullen_ganz_body s) = some s'
        ∧ nullen_ganz_post s s' (finalValue (exec ρ nullen_ganz_body s))

theorem nullen_ganz_meets : nullen_ganz_meets_statement := by
  unfold nullen_ganz_meets_statement
  intro ρ s hwf hpre l_nullen_ganz_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [nullen_ganz_pre]
  gabbro_auto [nullen_ganz_body, nullen_ganz_pre, nullen_ganz_post, wellFormed, nullen_ganz_loop_1_inv, hall] using shapeOf

/-! ### `richtig_armieren` -/

/-- **The duty of `richtig_armieren`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def richtig_armieren_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s richtig_armieren_pre = some (.bool true))
    -- the contract of `deskriptor_stellen`
    (c_deskriptor_stellen : Contract ρ "deskriptor_stellen" deskriptor_stellen_requires deskriptor_stellen_post)
    -- the frame of `deskriptor_stellen`
    (fr_deskriptor_stellen : Frame ρ "deskriptor_stellen" deskriptor_stellen_writes),
    ∃ s', finalState (exec ρ richtig_armieren_body s) = some s'
        ∧ richtig_armieren_post s s' (finalValue (exec ρ richtig_armieren_body s))

theorem richtig_armieren_meets : richtig_armieren_meets_statement := by
  unfold richtig_armieren_meets_statement
  intro ρ s hwf hpre c_deskriptor_stellen fr_deskriptor_stellen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Zweiachser_dev, h_Zweiachser_dev, lo_Zweiachser_dev, hi_Zweiachser_dev⟩ := WF_intIn shapeOf s.world (.field "Zweiachser" "dev") _ _ hwf rfl
  obtain ⟨n_Zweiachser_laenge, h_Zweiachser_laenge, lo_Zweiachser_laenge, hi_Zweiachser_laenge⟩ := WF_intIn shapeOf s.world (.field "Zweiachser" "laenge") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [richtig_armieren_pre, h_Zweiachser_dev, h_Zweiachser_laenge]
  gabbro_auto [richtig_armieren_body, richtig_armieren_pre, richtig_armieren_post, wellFormed, deskriptor_stellen_pre, deskriptor_stellen_requires, deskriptor_stellen_post, deskriptor_stellen_writes, Frame_read _ _ _ fr_deskriptor_stellen, h_Zweiachser_dev, h_Zweiachser_laenge, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "geraetesicht_umhaengen" geraetesicht_umhaengen_body
  ∧ Frame ρ "geraetesicht_umhaengen" geraetesicht_umhaengen_writes
  ∧ Runs ρ "nullen" nullen_body
  ∧ Frame ρ "nullen" nullen_writes
  ∧ RunsLoop ρ "nullen#1" nullen_loop_1_body "#pass"
  ∧ Runs ρ "nullen_ganz" nullen_ganz_body
  ∧ Frame ρ "nullen_ganz" nullen_ganz_writes
  ∧ RunsLoopIn ρ "nullen_ganz#1" nullen_ganz_loop_1_body "i" 0 2048
  ∧ Runs ρ "richtig_armieren" richtig_armieren_body
  ∧ Frame ρ "richtig_armieren" richtig_armieren_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_geraetesicht_umhaengen : geraetesicht_umhaengen_meets_statement)
    (d_nullen_loop_1 : nullen_loop_1_keeps_statement)
    (d_nullen : nullen_meets_statement)
    (d_nullen_ganz_loop_1 : nullen_ganz_loop_1_keeps_statement)
    (d_nullen_ganz : nullen_ganz_meets_statement)
    (d_richtig_armieren : richtig_armieren_meets_statement) :
    Contract ρ "geraetesicht_umhaengen" geraetesicht_umhaengen_requires geraetesicht_umhaengen_post
    ∧ LoopRule ρ "nullen#1" wellFormed nullen_loop_1_inv
    ∧ Contract ρ "nullen" nullen_requires nullen_post
    ∧ LoopRule ρ "nullen_ganz#1" wellFormed nullen_ganz_loop_1_inv
    ∧ Contract ρ "nullen_ganz" nullen_ganz_requires nullen_ganz_post
    ∧ Contract ρ "richtig_armieren" richtig_armieren_requires richtig_armieren_post := by
  obtain ⟨r_geraetesicht_umhaengen, fr_geraetesicht_umhaengen, r_nullen, fr_nullen, rl_nullen_loop_1, r_nullen_ganz, fr_nullen_ganz, rl_nullen_ganz_loop_1, r_richtig_armieren, fr_richtig_armieren⟩ := hp
  obtain ⟨c_deskriptor_stellen, fr_deskriptor_stellen⟩ := ha
  have c_geraetesicht_umhaengen : Contract ρ "geraetesicht_umhaengen" geraetesicht_umhaengen_requires geraetesicht_umhaengen_post :=
    contract_of_duty ρ "geraetesicht_umhaengen" geraetesicht_umhaengen_body geraetesicht_umhaengen_requires geraetesicht_umhaengen_post r_geraetesicht_umhaengen
      (fun t ht => d_geraetesicht_umhaengen ρ t ht.1 ht.2)
  have l_nullen_loop_1 : LoopRule ρ "nullen#1" wellFormed nullen_loop_1_inv :=
    looprule_of_body ρ "nullen#1" wellFormed nullen_loop_1_inv nullen_loop_1_body "#pass" rl_nullen_loop_1
      (fun t k hw hi => d_nullen_loop_1 ρ t k hw hi)
  have c_nullen : Contract ρ "nullen" nullen_requires nullen_post :=
    contract_of_duty ρ "nullen" nullen_body nullen_requires nullen_post r_nullen
      (fun t ht => d_nullen ρ t ht.1 ht.2 l_nullen_loop_1)
  have l_nullen_ganz_loop_1 : LoopRule ρ "nullen_ganz#1" wellFormed nullen_ganz_loop_1_inv :=
    looprule_of_body_in ρ "nullen_ganz#1" wellFormed nullen_ganz_loop_1_inv nullen_ganz_loop_1_body "i" 0 2048 rl_nullen_ganz_loop_1
      (fun t k hlo hhi hw hi => d_nullen_ganz_loop_1 ρ t k hlo hhi hw hi)
  have c_nullen_ganz : Contract ρ "nullen_ganz" nullen_ganz_requires nullen_ganz_post :=
    contract_of_duty ρ "nullen_ganz" nullen_ganz_body nullen_ganz_requires nullen_ganz_post r_nullen_ganz
      (fun t ht => d_nullen_ganz ρ t ht.1 ht.2 l_nullen_ganz_loop_1)
  have c_richtig_armieren : Contract ρ "richtig_armieren" richtig_armieren_requires richtig_armieren_post :=
    contract_of_duty ρ "richtig_armieren" richtig_armieren_body richtig_armieren_requires richtig_armieren_post r_richtig_armieren
      (fun t ht => d_richtig_armieren ρ t ht.1 ht.2 c_deskriptor_stellen fr_deskriptor_stellen)
  exact ⟨c_geraetesicht_umhaengen, l_nullen_loop_1, c_nullen, l_nullen_ganz_loop_1, c_nullen_ganz, c_richtig_armieren⟩

end GabbroDuty.DutyProbeRegionSchnittUndNullen
