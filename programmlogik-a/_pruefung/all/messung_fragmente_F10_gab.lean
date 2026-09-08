/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F10.gab  total 2  goals 1  refused 1
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

namespace GabbroDuty.DutyF10

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (1): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_1  F  naechstes_token :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  F  naechstes_token :: ensures #1  --  ASSUMED (foreign-body)
  duty_2  S  kerne_zaehlen :: loop invariant #1  --  carried by `kerne_zaehlen_loop_1_keeps`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "DtbKopf" "magie" => some (.intIn 0 4294967295)
  | .field "DtbKopf" "gesamtlaenge" => some (.intIn 0 4294967295)
  | .field "DtbKopf" "off_struct" => some (.intIn 0 4294967295)
  | .field "DtbKopf" "off_strings" => some (.intIn 0 4294967295)
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

/-! ### `kerne_zaehlen` -/

def kerne_zaehlen_body : List Stmt :=
  [(.bindName "tiefe" (.lit (.int 0))), (.bindName "zahl" (.lit (.int 0))), (.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "kerne_zaehlen#1" (.bin .and (.hasShape "tiefe" (.intIn 0 64)) (.bin .and (.hasShape "zahl" (.intIn 0 1024)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 4294967295))) (.bin .and (.un .not (.name "#returned")) (.bin .le (.name "tiefe") (.lit (.int 64)))))))) [(.ite (.bin .and (.bin .ge (.name "tiefe") (.lit (.int 0))) (.bin .lt (.name "tiefe") (.lit (.int 64)))) [] [(.bindName "#ret" (.name "zahl")), (.bindName "#returned" (.lit (.bool true))), .leave]), (.bindName "tiefe" (.bin .add (.name "tiefe") (.lit (.int 1))))]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.name "zahl")))]

/-- The precondition: the declared shapes and the `requires`. -/
def kerne_zaehlen_pre : Expr :=
  (.lit (.bool true))

def kerne_zaehlen_writes : List String := []

/-- What a caller of `kerne_zaehlen` has to bring: a well-typed world and the precondition. -/
def kerne_zaehlen_requires (t : State) : Prop := wellFormed t ∧ eval t kerne_zaehlen_pre = some (.bool true)

/-- What `kerne_zaehlen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kerne_zaehlen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `kerne_zaehlen` -/

/-- Loop `kerne_zaehlen#1` of `kerne_zaehlen`: its body and its invariant (with the shapes of the locals in scope). -/
def kerne_zaehlen_loop_1_inv : Expr :=
  (.bin .and (.hasShape "tiefe" (.intIn 0 64)) (.bin .and (.hasShape "zahl" (.intIn 0 1024)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 4294967295))) (.bin .and (.un .not (.name "#returned")) (.bin .le (.name "tiefe") (.lit (.int 64))))))))

def kerne_zaehlen_loop_1_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "tiefe") (.lit (.int 0))) (.bin .lt (.name "tiefe") (.lit (.int 64)))) [] [(.bindName "#ret" (.name "zahl")), (.bindName "#returned" (.lit (.bool true))), .leave]), (.bindName "tiefe" (.bin .add (.name "tiefe") (.lit (.int 1))))]

/-- **The loop rule of `kerne_zaehlen#1`, as a statement over one pass.** -/
def kerne_zaehlen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t kerne_zaehlen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ kerne_zaehlen_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' kerne_zaehlen_loop_1_inv = some (.bool true)

theorem kerne_zaehlen_loop_1_keeps : kerne_zaehlen_loop_1_keeps_statement := by
  unfold kerne_zaehlen_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_tiefe, e_tiefe, lo_tiefe, hi_tiefe⟩ := shape_intIn t "tiefe" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_zahl, e_zahl, lo_zahl, hi_zahl⟩ := shape_intIn t "zahl" _ _ (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hinv)))
  have hall := hinv
  gabbro_simp_at hall [kerne_zaehlen_loop_1_inv, e_tiefe, e_zahl, e__returned]
  gabbro_auto [kerne_zaehlen_loop_1_body, kerne_zaehlen_loop_1_inv, wellFormed, e_tiefe, e_zahl, e__returned, hall] using shapeOf

/-- **The duty of `kerne_zaehlen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kerne_zaehlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kerne_zaehlen_pre = some (.bool true))
    -- the rule of loop `kerne_zaehlen#1`
    (l_kerne_zaehlen_loop_1 : LoopRule ρ "kerne_zaehlen#1" wellFormed kerne_zaehlen_loop_1_inv),
    ∃ s', finalState (exec ρ kerne_zaehlen_body s) = some s'
        ∧ kerne_zaehlen_post s s' (finalValue (exec ρ kerne_zaehlen_body s))

theorem kerne_zaehlen_meets : kerne_zaehlen_meets_statement := by
  unfold kerne_zaehlen_meets_statement
  intro ρ s hwf hpre l_kerne_zaehlen_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [kerne_zaehlen_pre]
  gabbro_auto [kerne_zaehlen_body, kerne_zaehlen_pre, kerne_zaehlen_post, wellFormed, kerne_zaehlen_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "kerne_zaehlen" kerne_zaehlen_body
  ∧ Frame ρ "kerne_zaehlen" kerne_zaehlen_writes
  ∧ RunsLoop ρ "kerne_zaehlen#1" kerne_zaehlen_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_kerne_zaehlen_loop_1 : kerne_zaehlen_loop_1_keeps_statement)
    (d_kerne_zaehlen : kerne_zaehlen_meets_statement) :
    LoopRule ρ "kerne_zaehlen#1" wellFormed kerne_zaehlen_loop_1_inv
    ∧ Contract ρ "kerne_zaehlen" kerne_zaehlen_requires kerne_zaehlen_post := by
  obtain ⟨r_kerne_zaehlen, fr_kerne_zaehlen, rl_kerne_zaehlen_loop_1⟩ := hp
  have l_kerne_zaehlen_loop_1 : LoopRule ρ "kerne_zaehlen#1" wellFormed kerne_zaehlen_loop_1_inv :=
    looprule_of_body ρ "kerne_zaehlen#1" wellFormed kerne_zaehlen_loop_1_inv kerne_zaehlen_loop_1_body "#pass" rl_kerne_zaehlen_loop_1
      (fun t k hw hi => d_kerne_zaehlen_loop_1 ρ t k hw hi)
  have c_kerne_zaehlen : Contract ρ "kerne_zaehlen" kerne_zaehlen_requires kerne_zaehlen_post :=
    contract_of_duty ρ "kerne_zaehlen" kerne_zaehlen_body kerne_zaehlen_requires kerne_zaehlen_post r_kerne_zaehlen
      (fun t ht => d_kerne_zaehlen ρ t ht.1 ht.2 l_kerne_zaehlen_loop_1)
  exact ⟨l_kerne_zaehlen_loop_1, c_kerne_zaehlen⟩

end GabbroDuty.DutyF10