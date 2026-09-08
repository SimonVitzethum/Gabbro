/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/41-handschlag.gab  total 1  goals 0  refused 1
        @assumed 1  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty41Handschlag

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (1): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_1  F  naechster_puffer :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  F  naechster_puffer :: ensures #1  --  ASSUMED (foreign-body)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Ring" _ "art" => some (.sum [("Sendet", (some (some (1, 4096)))), ("Empfaengt", (some none)), ("Frei", none)])
  | .slot "Ring" _ "laenge" => some (.intIn 1 4096)
  | .slot "Ring" _ "offen" => some .bool
  | .global "AVAIL_IDX" => some (.intIn 0 4294967295)
  | .global "ARBEIT_DA" => some .bool
  | .global "GESENDET" => some (.intIn 0 65534)
  | .global "KLINGELRECHT" => some (.intIn 0 4294967295)
  | .global "arbeitsmenge" => some (.intIn 0 65534)
  | .global "deskring_gesehen" => some (.intIn 1 4096)
  | .global "gestellt" => some (.intIn 0 8)
  | .global "uebertragen" => some (.intIn 0 65534)
  | .global "frei" => some .opt
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `abschaltung_angefordert` -- a foreign body: its contract is an assumption. -/
def abschaltung_angefordert_pre : Expr :=
  (.lit (.bool true))

def abschaltung_angefordert_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ b, r = some (.bool b))

def abschaltung_angefordert_writes : List String := []

def abschaltung_angefordert_requires (t : State) : Prop := wellFormed t ∧ eval t abschaltung_angefordert_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post
  ∧ Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes

/-! ## The routines: body and contract -/

/-! ### `arbeit_anmelden` -/

def arbeit_anmelden_body : List Stmt :=
  [(.assignGlobal "arbeitsmenge" (.name "n")), (.publish "ARBEIT_DA" (.lit (.bool true)) ["arbeitsmenge"])]

/-- The precondition: the declared shapes and the `requires`. -/
def arbeit_anmelden_pre : Expr :=
  (.hasShape "n" (.intIn 0 65534))

def arbeit_anmelden_writes : List String := ["arbeitsmenge", "ARBEIT_DA"]

/-- What a caller of `arbeit_anmelden` has to bring: a well-typed world and the precondition. -/
def arbeit_anmelden_requires (t : State) : Prop := wellFormed t ∧ eval t arbeit_anmelden_pre = some (.bool true)

/-- What `arbeit_anmelden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arbeit_anmelden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `bereitmachen` -/

-- REFUSED  bereitmachen  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def bereitmachen_pre : Expr :=
  (.lit (.bool true))

def bereitmachen_writes : List String := ["k"]

/-- What a caller of `bereitmachen` has to bring: a well-typed world and the precondition. -/
def bereitmachen_requires (t : State) : Prop := wellFormed t ∧ eval t bereitmachen_pre = some (.bool true)

/-- What `bereitmachen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bereitmachen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `kern_starten` -/

def kern_starten_body : List Stmt :=
  [(.onTag (.name "rolle") [("Boot", none, [(.loop "kern_starten#1" (.hasShape "rolle" (.sum [("Boot", none), ("Helfer", none)])) [(.bindCall "#m1" "bereitmachen" ["k"] [(.name "k")] (.lit (.bool true))), (.ite (.name "#m1") [.leave] [])])]), ("Helfer", none, [(.bindCall "#m2" "abschaltung_angefordert" [] [] (.lit (.bool true))), (.ite (.name "#m2") [(.loop "kern_starten#2" (.bin .and (.hasShape "rolle" (.sum [("Boot", none), ("Helfer", none)])) (.hasShape "#m2" .bool)) [.leave])] [])])]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def kern_starten_pre : Expr :=
  (.hasShape "rolle" (.sum [("Boot", none), ("Helfer", none)]))

def kern_starten_writes : List String := ["k"]

/-- What a caller of `kern_starten` has to bring: a well-typed world and the precondition. -/
def kern_starten_requires (t : State) : Prop := wellFormed t ∧ eval t kern_starten_pre = some (.bool true)

/-- What `kern_starten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kern_starten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `platz_freigeben` -/

def platz_freigeben_body : List Stmt :=
  [(.assignGlobal "frei" (.someOf (.name "i")))]

/-- The precondition: the declared shapes and the `requires`. -/
def platz_freigeben_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def platz_freigeben_writes : List String := ["frei"]

/-- What a caller of `platz_freigeben` has to bring: a well-typed world and the precondition. -/
def platz_freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t platz_freigeben_pre = some (.bool true)

/-- What `platz_freigeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def platz_freigeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `uebertragen_lassen` -/

-- REFUSED  uebertragen_lassen  (exchange): `exchange` -- a conditional store, not a swap
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def uebertragen_lassen_pre : Expr :=
  (.lit (.bool true))

def uebertragen_lassen_writes : List String := ["k", "Ring", "gestellt", "deskring_gesehen", "uebertragen", "AVAIL_IDX", "GESENDET", "KLINGELRECHT"]

/-- What a caller of `uebertragen_lassen` has to bring: a well-typed world and the precondition. -/
def uebertragen_lassen_requires (t : State) : Prop := wellFormed t ∧ eval t uebertragen_lassen_pre = some (.bool true)

/-- What `uebertragen_lassen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def uebertragen_lassen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `arbeit_anmelden` -/

/-- **The duty of `arbeit_anmelden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arbeit_anmelden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arbeit_anmelden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ arbeit_anmelden_body s) = some s'
        ∧ arbeit_anmelden_post s s' (finalValue (exec ρ arbeit_anmelden_body s))

theorem arbeit_anmelden_meets : arbeit_anmelden_meets_statement := by
  unfold arbeit_anmelden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn s "n" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [arbeit_anmelden_pre, e_n]
  gabbro_auto [arbeit_anmelden_body, arbeit_anmelden_pre, arbeit_anmelden_post, wellFormed, e_n, hall] using shapeOf

/-! ### `kern_starten` -/

/-- Loop `kern_starten#1` of `kern_starten`: its body and its invariant (with the shapes of the locals in scope). -/
def kern_starten_loop_1_inv : Expr :=
  (.hasShape "rolle" (.sum [("Boot", none), ("Helfer", none)]))

def kern_starten_loop_1_body : List Stmt :=
  [(.bindCall "#m1" "bereitmachen" ["k"] [(.name "k")] (.lit (.bool true))), (.ite (.name "#m1") [.leave] [])]

/-- **The loop rule of `kern_starten#1`, as a statement over one pass.** -/
def kern_starten_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t kern_starten_loop_1_inv = some (.bool true))
    (c_bereitmachen : Contract ρ "bereitmachen" bereitmachen_requires bereitmachen_post)
    (fr_bereitmachen : Frame ρ "bereitmachen" bereitmachen_writes),
    ∃ t', finalState (exec ρ kern_starten_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' kern_starten_loop_1_inv = some (.bool true)

theorem kern_starten_loop_1_keeps : kern_starten_loop_1_keeps_statement := by
  unfold kern_starten_loop_1_keeps_statement
  intro ρ t k hwf hinv c_bereitmachen fr_bereitmachen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_rolle, p_rolle, e_rolle, c_rolle⟩ := shape_sum t "rolle" _ hinv
  have hall := hinv
  gabbro_simp_at hall [kern_starten_loop_1_inv, e_rolle]
  gabbro_auto [kern_starten_loop_1_body, kern_starten_loop_1_inv, wellFormed, bereitmachen_pre, bereitmachen_requires, bereitmachen_post, bereitmachen_writes, Frame_read _ _ _ fr_bereitmachen, e_rolle, c_rolle, hall] using shapeOf

/-- Loop `kern_starten#2` of `kern_starten`: its body and its invariant (with the shapes of the locals in scope). -/
def kern_starten_loop_2_inv : Expr :=
  (.bin .and (.hasShape "rolle" (.sum [("Boot", none), ("Helfer", none)])) (.hasShape "#m2" .bool))

def kern_starten_loop_2_body : List Stmt :=
  [.leave]

/-- **The loop rule of `kern_starten#2`, as a statement over one pass.** -/
def kern_starten_loop_2_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t kern_starten_loop_2_inv = some (.bool true)),
    ∃ t', finalState (exec ρ kern_starten_loop_2_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' kern_starten_loop_2_inv = some (.bool true)

theorem kern_starten_loop_2_keeps : kern_starten_loop_2_keeps_statement := by
  unfold kern_starten_loop_2_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_rolle, p_rolle, e_rolle, c_rolle⟩ := shape_sum t "rolle" _ (and_left _ _ _ hinv)
  obtain ⟨w__m2, e__m2⟩ := shape_bool t "#m2" (and_right _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [kern_starten_loop_2_inv, e_rolle, e__m2]
  gabbro_auto [kern_starten_loop_2_body, kern_starten_loop_2_inv, wellFormed, e_rolle, c_rolle, e__m2, hall] using shapeOf

/-- **The duty of `kern_starten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kern_starten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kern_starten_pre = some (.bool true))
    -- the contract of `abschaltung_angefordert`
    (c_abschaltung_angefordert : Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post)
    -- the frame of `abschaltung_angefordert`
    (fr_abschaltung_angefordert : Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes)
    -- the contract of `bereitmachen`
    (c_bereitmachen : Contract ρ "bereitmachen" bereitmachen_requires bereitmachen_post)
    -- the frame of `bereitmachen`
    (fr_bereitmachen : Frame ρ "bereitmachen" bereitmachen_writes)
    -- the rule of loop `kern_starten#1`
    (l_kern_starten_loop_1 : LoopRule ρ "kern_starten#1" wellFormed kern_starten_loop_1_inv)
    -- the rule of loop `kern_starten#2`
    (l_kern_starten_loop_2 : LoopRule ρ "kern_starten#2" wellFormed kern_starten_loop_2_inv),
    ∃ s', finalState (exec ρ kern_starten_body s) = some s'
        ∧ kern_starten_post s s' (finalValue (exec ρ kern_starten_body s))

theorem kern_starten_meets : kern_starten_meets_statement := by
  unfold kern_starten_meets_statement
  intro ρ s hwf hpre c_abschaltung_angefordert fr_abschaltung_angefordert c_bereitmachen fr_bereitmachen l_kern_starten_loop_1 l_kern_starten_loop_2
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_rolle, p_rolle, e_rolle, c_rolle⟩ := shape_sum s "rolle" _ hpre
  have hall := hpre
  gabbro_simp_at hall [kern_starten_pre, e_rolle]
  gabbro_auto [kern_starten_body, kern_starten_pre, kern_starten_post, wellFormed, abschaltung_angefordert_pre, abschaltung_angefordert_requires, abschaltung_angefordert_post, abschaltung_angefordert_writes, Frame_read _ _ _ fr_abschaltung_angefordert, bereitmachen_pre, bereitmachen_requires, bereitmachen_post, bereitmachen_writes, Frame_read _ _ _ fr_bereitmachen, kern_starten_loop_1_inv, kern_starten_loop_2_inv, e_rolle, c_rolle, hall] using shapeOf

/-! ### `platz_freigeben` -/

/-- **The duty of `platz_freigeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def platz_freigeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s platz_freigeben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ platz_freigeben_body s) = some s'
        ∧ platz_freigeben_post s s' (finalValue (exec ρ platz_freigeben_body s))

theorem platz_freigeben_meets : platz_freigeben_meets_statement := by
  unfold platz_freigeben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [platz_freigeben_pre, e_i]
  gabbro_auto [platz_freigeben_body, platz_freigeben_pre, platz_freigeben_post, wellFormed, e_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "arbeit_anmelden" arbeit_anmelden_body
  ∧ Frame ρ "arbeit_anmelden" arbeit_anmelden_writes
  ∧ Runs ρ "kern_starten" kern_starten_body
  ∧ Frame ρ "kern_starten" kern_starten_writes
  ∧ RunsLoop ρ "kern_starten#1" kern_starten_loop_1_body "#pass"
  ∧ RunsLoop ρ "kern_starten#2" kern_starten_loop_2_body "#pass"
  ∧ Runs ρ "platz_freigeben" platz_freigeben_body
  ∧ Frame ρ "platz_freigeben" platz_freigeben_writes

/-  NOT WIRED -- the duty is stated above; the step from it to the contract is not:
      kern_starten: callee `bereitmachen` refused
    Each line above names the construct and the way out. What IS wired: a
    self-recursion, by induction over its `decreases` (`contract_of_duty_rec`);
    a cycle of routines, over their shared measure (`contracts_of_duties_rec`);
    a recursive call inside ONE ranged loop, by the induction outside the loop
    rule (`contract_of_duty_rec_loop_in`, 2026-09-08). A caller of a REFUSED
    callee has no contract to compose with: the callee's refusal above is the
    line to read, and fixing it wires the caller too. -/

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_arbeit_anmelden : arbeit_anmelden_meets_statement)
    (d_platz_freigeben : platz_freigeben_meets_statement) :
    Contract ρ "arbeit_anmelden" arbeit_anmelden_requires arbeit_anmelden_post
    ∧ Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post := by
  obtain ⟨r_arbeit_anmelden, fr_arbeit_anmelden, r_kern_starten, fr_kern_starten, rl_kern_starten_loop_1, rl_kern_starten_loop_2, r_platz_freigeben, fr_platz_freigeben⟩ := hp
  obtain ⟨c_abschaltung_angefordert, fr_abschaltung_angefordert⟩ := ha
  have c_arbeit_anmelden : Contract ρ "arbeit_anmelden" arbeit_anmelden_requires arbeit_anmelden_post :=
    contract_of_duty ρ "arbeit_anmelden" arbeit_anmelden_body arbeit_anmelden_requires arbeit_anmelden_post r_arbeit_anmelden
      (fun t ht => d_arbeit_anmelden ρ t ht.1 ht.2)
  have c_platz_freigeben : Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post :=
    contract_of_duty ρ "platz_freigeben" platz_freigeben_body platz_freigeben_requires platz_freigeben_post r_platz_freigeben
      (fun t ht => d_platz_freigeben ρ t ht.1 ht.2)
  exact ⟨c_arbeit_anmelden, c_platz_freigeben⟩

end GabbroDuty.Duty41Handschlag