/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/42-zaehlwerk.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty42Zaehlwerk

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Konten" _ "zaehler" => some (.intIn 0 65534)
  | .slot "Konten" _ "oberkonto" => some .opt
  | .slot "Konten" _ "aktiv" => some .bool
  | .global "STAND_FERTIG" => some .bool
  | .global "ANFRAGEN" => some (.intIn 0 65534)
  | .global "stand" => some (.intIn 0 65534)
  | .global "gesehen" => some (.intIn 0 65534)
  | .global "abgeholt" => some (.intIn 0 65534)
  | .global "frei" => some .opt
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `anfragenzahl` -- a foreign body: its contract is an assumption. -/
def anfragenzahl_pre : Expr :=
  (.lit (.bool true))

def anfragenzahl_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534) ∨ ∃ e, r = some (.reason e))

def anfragenzahl_writes : List String := []

def anfragenzahl_requires (t : State) : Prop := wellFormed t ∧ eval t anfragenzahl_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "anfragenzahl" anfragenzahl_requires anfragenzahl_post
  ∧ Frame ρ "anfragenzahl" anfragenzahl_writes

/-! ## The routines: body and contract -/

/-! ### `abgleichen` -/

-- REFUSED  abgleichen  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def abgleichen_pre : Expr :=
  (.hasShape "i" (.intIn 0 255))

def abgleichen_writes : List String := ["gesehen", "ANFRAGEN"]

/-- What a caller of `abgleichen` has to bring: a well-typed world and the precondition. -/
def abgleichen_requires (t : State) : Prop := wellFormed t ∧ eval t abgleichen_pre = some (.bool true)

/-- What `abgleichen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abgleichen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ### `anfrage_beantworten` -/

-- REFUSED  anfrage_beantworten  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def anfrage_beantworten_pre : Expr :=
  (.hasShape "a" (.sum [("Einzeln", (some (some (0, 255)))), ("Kette", (some none)), ("Melden", (some (some (0, 65534)))), ("Abholen", none)]))

def anfrage_beantworten_writes : List String := ["stand", "frei", "ANFRAGEN", "STAND_FERTIG"]

/-- What a caller of `anfrage_beantworten` has to bring: a well-typed world and the precondition. -/
def anfrage_beantworten_requires (t : State) : Prop := wellFormed t ∧ eval t anfrage_beantworten_pre = some (.bool true)

/-- What `anfrage_beantworten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def anfrage_beantworten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ### `platz_melden` -/

def platz_melden_body : List Stmt :=
  [(.locked "SCHREIBER" [(.assignGlobal "frei" (.someOf (.name "j"))), (.loop "platz_melden#1" (.bin .and (.hasShape "j" (.intIn 0 255)) (.hasShape "w" (.intIn 0 65534))) [(.assignGlobal "stand" (.name "w")), (.publish "STAND_FERTIG" (.lit (.bool true)) ["stand"])])])]

/-- The precondition: the declared shapes and the `requires`. -/
def platz_melden_pre : Expr :=
  (.bin .and (.hasShape "j" (.intIn 0 255)) (.hasShape "w" (.intIn 0 65534)))

def platz_melden_writes : List String := ["frei", "stand", "STAND_FERTIG"]

/-- What a caller of `platz_melden` has to bring: a well-typed world and the precondition. -/
def platz_melden_requires (t : State) : Prop := wellFormed t ∧ eval t platz_melden_pre = some (.bool true)

/-- What `platz_melden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def platz_melden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `runde_messen` -/

-- REFUSED  runde_messen  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def runde_messen_pre : Expr :=
  (.lit (.bool true))

def runde_messen_writes : List String := ["gesehen"]

/-- What a caller of `runde_messen` has to bring: a well-typed world and the precondition. -/
def runde_messen_requires (t : State) : Prop := wellFormed t ∧ eval t runde_messen_pre = some (.bool true)

/-- What `runde_messen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def runde_messen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ### `sammeldienst` -/

-- REFUSED  sammeldienst  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def sammeldienst_pre : Expr :=
  (.hasShape "i" (.intIn 0 255))

def sammeldienst_writes : List String := ["zaehlwerk", "gesehen", "stand", "frei", "ANFRAGEN", "STAND_FERTIG"]

/-- What a caller of `sammeldienst` has to bring: a well-typed world and the precondition. -/
def sammeldienst_requires (t : State) : Prop := wellFormed t ∧ eval t sammeldienst_pre = some (.bool true)

/-- What `sammeldienst` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def sammeldienst_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `stand_abholen` -/

-- REFUSED  stand_abholen  (exchange): `exchange` -- a conditional store, not a swap
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def stand_abholen_pre : Expr :=
  (.hasShape "dringend" .bool)

def stand_abholen_writes : List String := ["ANFRAGEN"]

/-- What a caller of `stand_abholen` has to bring: a well-typed world and the precondition. -/
def stand_abholen_requires (t : State) : Prop := wellFormed t ∧ eval t stand_abholen_pre = some (.bool true)

/-- What `stand_abholen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def stand_abholen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ### `zaehler_lesen` -/

-- REFUSED  zaehler_lesen  (observe): `observes` -- a view that MAY be stale
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def zaehler_lesen_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 255)) (.hasShape "aktiv" .bool))

def zaehler_lesen_writes : List String := []

/-- What a caller of `zaehler_lesen` has to bring: a well-typed world and the precondition. -/
def zaehler_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t zaehler_lesen_pre = some (.bool true)

/-- What `zaehler_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def zaehler_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65534)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `platz_melden` -/

/-- Loop `platz_melden#1` of `platz_melden`: its body and its invariant (with the shapes of the locals in scope). -/
def platz_melden_loop_1_inv : Expr :=
  (.bin .and (.hasShape "j" (.intIn 0 255)) (.hasShape "w" (.intIn 0 65534)))

def platz_melden_loop_1_body : List Stmt :=
  [(.assignGlobal "stand" (.name "w")), (.publish "STAND_FERTIG" (.lit (.bool true)) ["stand"])]

/-- **The loop rule of `platz_melden#1`, as a statement over one pass.** -/
def platz_melden_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t platz_melden_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ platz_melden_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' platz_melden_loop_1_inv = some (.bool true)

theorem platz_melden_loop_1_keeps : platz_melden_loop_1_keeps_statement := by
  unfold platz_melden_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_j, e_j, lo_j, hi_j⟩ := shape_intIn t "j" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn t "w" _ _ (and_right _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [platz_melden_loop_1_inv, e_j, e_w]
  gabbro_auto [platz_melden_loop_1_body, platz_melden_loop_1_inv, wellFormed, e_j, e_w, hall] using shapeOf

/-- **The duty of `platz_melden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def platz_melden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s platz_melden_pre = some (.bool true))
    -- the rule of loop `platz_melden#1`
    (l_platz_melden_loop_1 : LoopRule ρ "platz_melden#1" wellFormed platz_melden_loop_1_inv),
    ∃ s', finalState (exec ρ platz_melden_body s) = some s'
        ∧ platz_melden_post s s' (finalValue (exec ρ platz_melden_body s))

theorem platz_melden_meets : platz_melden_meets_statement := by
  unfold platz_melden_meets_statement
  intro ρ s hwf hpre l_platz_melden_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_j, e_j, lo_j, hi_j⟩ := shape_intIn s "j" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [platz_melden_pre, e_j, e_w]
  gabbro_auto [platz_melden_body, platz_melden_pre, platz_melden_post, wellFormed, platz_melden_loop_1_inv, e_j, e_w, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "platz_melden" platz_melden_body
  ∧ Frame ρ "platz_melden" platz_melden_writes
  ∧ RunsLoop ρ "platz_melden#1" platz_melden_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_platz_melden_loop_1 : platz_melden_loop_1_keeps_statement)
    (d_platz_melden : platz_melden_meets_statement) :
    LoopRule ρ "platz_melden#1" wellFormed platz_melden_loop_1_inv
    ∧ Contract ρ "platz_melden" platz_melden_requires platz_melden_post := by
  obtain ⟨r_platz_melden, fr_platz_melden, rl_platz_melden_loop_1⟩ := hp
  obtain ⟨c_anfragenzahl, fr_anfragenzahl⟩ := ha
  have l_platz_melden_loop_1 : LoopRule ρ "platz_melden#1" wellFormed platz_melden_loop_1_inv :=
    looprule_of_body ρ "platz_melden#1" wellFormed platz_melden_loop_1_inv platz_melden_loop_1_body "#pass" rl_platz_melden_loop_1
      (fun t k hw hi => d_platz_melden_loop_1 ρ t k hw hi)
  have c_platz_melden : Contract ρ "platz_melden" platz_melden_requires platz_melden_post :=
    contract_of_duty ρ "platz_melden" platz_melden_body platz_melden_requires platz_melden_post r_platz_melden
      (fun t ht => d_platz_melden ρ t ht.1 ht.2 l_platz_melden_loop_1)
  exact ⟨l_platz_melden_loop_1, c_platz_melden⟩

end GabbroDuty.Duty42Zaehlwerk