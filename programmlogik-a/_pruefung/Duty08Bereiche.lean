/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/08-bereiche.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty08Bereiche

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Marken" _ "marke" => some .int
  | .slot "Marken" _ "gueltig" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body, contract, duty -/

/-! ### `einengen` -/

def einengen_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "roh") (.lit (.int 0))) (.bin .le (.name "roh") (.lit (.int 1000000)))) [] [(.ret (some (.lit (.int 0))))]), (.ret (some (.name "roh")))]

/-- The precondition: the declared shapes and the `requires`. -/
def einengen_pre : Expr :=
  (.hasShape "roh" .int)

def einengen_writes : List String := []

/-- What a caller of `einengen` has to bring: a well-typed world and the precondition. -/
def einengen_requires (t : State) : Prop := wellFormed t ∧ eval t einengen_pre = some (.bool true)

/-- What `einengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `einengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ einengen_body s) = some s'
        ∧ einengen_post s s' (finalValue (exec ρ einengen_body s))

theorem einengen_meets : einengen_meets_statement := by
  unfold einengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_roh, e_roh⟩ := shape_int s "roh" hpre
  gabbro_auto [einengen_body, einengen_pre, einengen_post, wellFormed, e_roh] using shapeOf

/-! ### `last_lesen` -/

-- REFUSED  last_lesen  (carrier-not-a-table): the carrier of a place is not a declared `table`, record or `format`
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def last_lesen_pre : Expr :=
  (.hasShape "k" .int)

def last_lesen_writes : List String := []

/-- What a caller of `last_lesen` has to bring: a well-typed world and the precondition. -/
def last_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t last_lesen_pre = some (.bool true)

/-- What `last_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def last_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `marke_weiterdrehen` -/

def marke_weiterdrehen_body : List Stmt :=
  [(.assign "Marken" (.name "s") "marke" (.wrapTo 32 false (.bin .add (.place "Marken" (.name "s") "marke") (.lit (.int 1)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def marke_weiterdrehen_pre : Expr :=
  (.hasShape "s" .int)

def marke_weiterdrehen_writes : List String := ["Marken"]

/-- What a caller of `marke_weiterdrehen` has to bring: a well-typed world and the precondition. -/
def marke_weiterdrehen_requires (t : State) : Prop := wellFormed t ∧ eval t marke_weiterdrehen_pre = some (.bool true)

/-- What `marke_weiterdrehen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def marke_weiterdrehen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `marke_weiterdrehen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def marke_weiterdrehen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s marke_weiterdrehen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ marke_weiterdrehen_body s) = some s'
        ∧ marke_weiterdrehen_post s s' (finalValue (exec ρ marke_weiterdrehen_body s))

theorem marke_weiterdrehen_meets : marke_weiterdrehen_meets_statement := by
  unfold marke_weiterdrehen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" hpre
  gabbro_auto [marke_weiterdrehen_body, marke_weiterdrehen_pre, marke_weiterdrehen_post, wellFormed, e_s] using shapeOf

/-! ### `v1_erhoehen` -/

def v1_erhoehen_body : List Stmt :=
  [(.ite (.bin .lt (.name "z") (.lit (.int 1000000))) [(.ret (some (.bin .add (.name "z") (.lit (.int 1)))))] []), (.ret (some (.name "z")))]

/-- The precondition: the declared shapes and the `requires`. -/
def v1_erhoehen_pre : Expr :=
  (.hasShape "z" .int)

def v1_erhoehen_writes : List String := []

/-- What a caller of `v1_erhoehen` has to bring: a well-typed world and the precondition. -/
def v1_erhoehen_requires (t : State) : Prop := wellFormed t ∧ eval t v1_erhoehen_pre = some (.bool true)

/-- What `v1_erhoehen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v1_erhoehen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v1_erhoehen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v1_erhoehen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v1_erhoehen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v1_erhoehen_body s) = some s'
        ∧ v1_erhoehen_post s s' (finalValue (exec ρ v1_erhoehen_body s))

theorem v1_erhoehen_meets : v1_erhoehen_meets_statement := by
  unfold v1_erhoehen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_z, e_z⟩ := shape_int s "z" hpre
  gabbro_auto [v1_erhoehen_body, v1_erhoehen_pre, v1_erhoehen_post, wellFormed, e_z] using shapeOf

/-! ### `v1_teilen` -/

def v1_teilen_body : List Stmt :=
  [(.ite (.bin .ge (.name "n") (.lit (.int 1))) [(.ret (some (.bin .div (.name "summe") (.name "n"))))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def v1_teilen_pre : Expr :=
  (.bin .and (.hasShape "n" .int) (.hasShape "summe" .int))

def v1_teilen_writes : List String := []

/-- What a caller of `v1_teilen` has to bring: a well-typed world and the precondition. -/
def v1_teilen_requires (t : State) : Prop := wellFormed t ∧ eval t v1_teilen_pre = some (.bool true)

/-- What `v1_teilen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v1_teilen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v1_teilen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v1_teilen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v1_teilen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v1_teilen_body s) = some s'
        ∧ v1_teilen_post s s' (finalValue (exec ρ v1_teilen_body s))

theorem v1_teilen_meets : v1_teilen_meets_statement := by
  unfold v1_teilen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n⟩ := shape_int s "n" (and_left _ _ _ hpre)
  obtain ⟨w_summe, e_summe⟩ := shape_int s "summe" (and_right _ _ _ hpre)
  gabbro_auto [v1_teilen_body, v1_teilen_pre, v1_teilen_post, wellFormed, e_n, e_summe] using shapeOf

/-! ### `v1_zweiseitig` -/

def v1_zweiseitig_body : List Stmt :=
  [(.ite (.bin .ge (.name "z") (.lit (.int 100))) [(.ret (some (.bin .sub (.name "z") (.lit (.int 100)))))] []), (.ret (some (.name "z")))]

/-- The precondition: the declared shapes and the `requires`. -/
def v1_zweiseitig_pre : Expr :=
  (.hasShape "z" .int)

def v1_zweiseitig_writes : List String := []

/-- What a caller of `v1_zweiseitig` has to bring: a well-typed world and the precondition. -/
def v1_zweiseitig_requires (t : State) : Prop := wellFormed t ∧ eval t v1_zweiseitig_pre = some (.bool true)

/-- What `v1_zweiseitig` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v1_zweiseitig_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v1_zweiseitig`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v1_zweiseitig_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v1_zweiseitig_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v1_zweiseitig_body s) = some s'
        ∧ v1_zweiseitig_post s s' (finalValue (exec ρ v1_zweiseitig_body s))

theorem v1_zweiseitig_meets : v1_zweiseitig_meets_statement := by
  unfold v1_zweiseitig_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_z, e_z⟩ := shape_int s "z" hpre
  gabbro_auto [v1_zweiseitig_body, v1_zweiseitig_pre, v1_zweiseitig_post, wellFormed, e_z] using shapeOf

/-! ### `v2_abstand` -/

def v2_abstand_body : List Stmt :=
  [(.ite (.bin .ge (.name "a") (.name "b")) [(.ret (some (.bin .sub (.name "a") (.name "b"))))] []), (.ret (some (.bin .sub (.name "b") (.name "a"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def v2_abstand_pre : Expr :=
  (.bin .and (.hasShape "a" .int) (.hasShape "b" .int))

def v2_abstand_writes : List String := []

/-- What a caller of `v2_abstand` has to bring: a well-typed world and the precondition. -/
def v2_abstand_requires (t : State) : Prop := wellFormed t ∧ eval t v2_abstand_pre = some (.bool true)

/-- What `v2_abstand` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v2_abstand_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v2_abstand`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v2_abstand_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v2_abstand_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v2_abstand_body s) = some s'
        ∧ v2_abstand_post s s' (finalValue (exec ρ v2_abstand_body s))

theorem v2_abstand_meets : v2_abstand_meets_statement := by
  unfold v2_abstand_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a⟩ := shape_int s "a" (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b⟩ := shape_int s "b" (and_right _ _ _ hpre)
  gabbro_auto [v2_abstand_body, v2_abstand_pre, v2_abstand_post, wellFormed, e_a, e_b] using shapeOf

/-! ### `v2_echt_groesser` -/

def v2_echt_groesser_body : List Stmt :=
  [(.ite (.bin .gt (.name "a") (.name "b")) [(.bindName "d" (.bin .sub (.name "a") (.name "b"))), (.ret (some (.name "d")))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def v2_echt_groesser_pre : Expr :=
  (.bin .and (.hasShape "a" .int) (.hasShape "b" .int))

def v2_echt_groesser_writes : List String := []

/-- What a caller of `v2_echt_groesser` has to bring: a well-typed world and the precondition. -/
def v2_echt_groesser_requires (t : State) : Prop := wellFormed t ∧ eval t v2_echt_groesser_pre = some (.bool true)

/-- What `v2_echt_groesser` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v2_echt_groesser_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v2_echt_groesser`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v2_echt_groesser_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v2_echt_groesser_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v2_echt_groesser_body s) = some s'
        ∧ v2_echt_groesser_post s s' (finalValue (exec ρ v2_echt_groesser_body s))

theorem v2_echt_groesser_meets : v2_echt_groesser_meets_statement := by
  unfold v2_echt_groesser_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a⟩ := shape_int s "a" (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b⟩ := shape_int s "b" (and_right _ _ _ hpre)
  gabbro_auto [v2_echt_groesser_body, v2_echt_groesser_pre, v2_echt_groesser_post, wellFormed, e_a, e_b] using shapeOf

/-! ### `v3_auswerten` -/

def v3_auswerten_body : List Stmt :=
  [(.onTag (.name "m") [("Leer", none, [(.ret (some (.lit (.int 0))))]), ("Kurz", some "k", [(.ite (.bin .le (.name "k") (.lit (.int 1000000))) [(.ret (some (.name "k")))] []), (.ret (some (.lit (.int 0))))]), ("Lang", some "p", [(.ret (some (.lit (.int 1))))]), ("Antwort", some "f", [(.ret (some (.lit (.int 2))))])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def v3_auswerten_pre : Expr :=
  (.hasShape "m" .sum)

def v3_auswerten_writes : List String := []

/-- What a caller of `v3_auswerten` has to bring: a well-typed world and the precondition. -/
def v3_auswerten_requires (t : State) : Prop := wellFormed t ∧ eval t v3_auswerten_pre = some (.bool true)

/-- What `v3_auswerten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def v3_auswerten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `v3_auswerten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def v3_auswerten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s v3_auswerten_pre = some (.bool true)),
    ∃ s', finalState (exec ρ v3_auswerten_body s) = some s'
        ∧ v3_auswerten_post s s' (finalValue (exec ρ v3_auswerten_body s))

theorem v3_auswerten_meets : v3_auswerten_meets_statement := by
  unfold v3_auswerten_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_m, p_m, e_m⟩ := shape_sum s "m" hpre
  gabbro_auto [v3_auswerten_body, v3_auswerten_pre, v3_auswerten_post, wellFormed, e_m] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "einengen" einengen_body
  ∧ Frame ρ "einengen" einengen_writes
  ∧ Runs ρ "marke_weiterdrehen" marke_weiterdrehen_body
  ∧ Frame ρ "marke_weiterdrehen" marke_weiterdrehen_writes
  ∧ Runs ρ "v1_erhoehen" v1_erhoehen_body
  ∧ Frame ρ "v1_erhoehen" v1_erhoehen_writes
  ∧ Runs ρ "v1_teilen" v1_teilen_body
  ∧ Frame ρ "v1_teilen" v1_teilen_writes
  ∧ Runs ρ "v1_zweiseitig" v1_zweiseitig_body
  ∧ Frame ρ "v1_zweiseitig" v1_zweiseitig_writes
  ∧ Runs ρ "v2_abstand" v2_abstand_body
  ∧ Frame ρ "v2_abstand" v2_abstand_writes
  ∧ Runs ρ "v2_echt_groesser" v2_echt_groesser_body
  ∧ Frame ρ "v2_echt_groesser" v2_echt_groesser_writes
  ∧ Runs ρ "v3_auswerten" v3_auswerten_body
  ∧ Frame ρ "v3_auswerten" v3_auswerten_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_einengen : einengen_meets_statement)
    (d_marke_weiterdrehen : marke_weiterdrehen_meets_statement)
    (d_v1_erhoehen : v1_erhoehen_meets_statement)
    (d_v1_teilen : v1_teilen_meets_statement)
    (d_v1_zweiseitig : v1_zweiseitig_meets_statement)
    (d_v2_abstand : v2_abstand_meets_statement)
    (d_v2_echt_groesser : v2_echt_groesser_meets_statement)
    (d_v3_auswerten : v3_auswerten_meets_statement) :
    Contract ρ "einengen" einengen_requires einengen_post
    ∧ Contract ρ "marke_weiterdrehen" marke_weiterdrehen_requires marke_weiterdrehen_post
    ∧ Contract ρ "v1_erhoehen" v1_erhoehen_requires v1_erhoehen_post
    ∧ Contract ρ "v1_teilen" v1_teilen_requires v1_teilen_post
    ∧ Contract ρ "v1_zweiseitig" v1_zweiseitig_requires v1_zweiseitig_post
    ∧ Contract ρ "v2_abstand" v2_abstand_requires v2_abstand_post
    ∧ Contract ρ "v2_echt_groesser" v2_echt_groesser_requires v2_echt_groesser_post
    ∧ Contract ρ "v3_auswerten" v3_auswerten_requires v3_auswerten_post := by
  obtain ⟨r_einengen, fr_einengen, r_marke_weiterdrehen, fr_marke_weiterdrehen, r_v1_erhoehen, fr_v1_erhoehen, r_v1_teilen, fr_v1_teilen, r_v1_zweiseitig, fr_v1_zweiseitig, r_v2_abstand, fr_v2_abstand, r_v2_echt_groesser, fr_v2_echt_groesser, r_v3_auswerten, fr_v3_auswerten⟩ := hp
  have c_einengen : Contract ρ "einengen" einengen_requires einengen_post :=
    contract_of_duty ρ "einengen" einengen_body einengen_requires einengen_post r_einengen
      (fun t ht => d_einengen ρ t ht.1 ht.2)
  have c_marke_weiterdrehen : Contract ρ "marke_weiterdrehen" marke_weiterdrehen_requires marke_weiterdrehen_post :=
    contract_of_duty ρ "marke_weiterdrehen" marke_weiterdrehen_body marke_weiterdrehen_requires marke_weiterdrehen_post r_marke_weiterdrehen
      (fun t ht => d_marke_weiterdrehen ρ t ht.1 ht.2)
  have c_v1_erhoehen : Contract ρ "v1_erhoehen" v1_erhoehen_requires v1_erhoehen_post :=
    contract_of_duty ρ "v1_erhoehen" v1_erhoehen_body v1_erhoehen_requires v1_erhoehen_post r_v1_erhoehen
      (fun t ht => d_v1_erhoehen ρ t ht.1 ht.2)
  have c_v1_teilen : Contract ρ "v1_teilen" v1_teilen_requires v1_teilen_post :=
    contract_of_duty ρ "v1_teilen" v1_teilen_body v1_teilen_requires v1_teilen_post r_v1_teilen
      (fun t ht => d_v1_teilen ρ t ht.1 ht.2)
  have c_v1_zweiseitig : Contract ρ "v1_zweiseitig" v1_zweiseitig_requires v1_zweiseitig_post :=
    contract_of_duty ρ "v1_zweiseitig" v1_zweiseitig_body v1_zweiseitig_requires v1_zweiseitig_post r_v1_zweiseitig
      (fun t ht => d_v1_zweiseitig ρ t ht.1 ht.2)
  have c_v2_abstand : Contract ρ "v2_abstand" v2_abstand_requires v2_abstand_post :=
    contract_of_duty ρ "v2_abstand" v2_abstand_body v2_abstand_requires v2_abstand_post r_v2_abstand
      (fun t ht => d_v2_abstand ρ t ht.1 ht.2)
  have c_v2_echt_groesser : Contract ρ "v2_echt_groesser" v2_echt_groesser_requires v2_echt_groesser_post :=
    contract_of_duty ρ "v2_echt_groesser" v2_echt_groesser_body v2_echt_groesser_requires v2_echt_groesser_post r_v2_echt_groesser
      (fun t ht => d_v2_echt_groesser ρ t ht.1 ht.2)
  have c_v3_auswerten : Contract ρ "v3_auswerten" v3_auswerten_requires v3_auswerten_post :=
    contract_of_duty ρ "v3_auswerten" v3_auswerten_body v3_auswerten_requires v3_auswerten_post r_v3_auswerten
      (fun t ht => d_v3_auswerten ρ t ht.1 ht.2)
  exact ⟨c_einengen, c_marke_weiterdrehen, c_v1_erhoehen, c_v1_teilen, c_v1_zweiseitig, c_v2_abstand, c_v2_echt_groesser, c_v3_auswerten⟩

end GabbroDuty.Duty08Bereiche
