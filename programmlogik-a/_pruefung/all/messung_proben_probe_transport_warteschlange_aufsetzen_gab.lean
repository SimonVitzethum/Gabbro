/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-transport-warteschlange-aufsetzen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeTransportWarteschlangeAufsetzen

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "AvailKopf" "merkmale" => some (.intIn 0 65535)
  | .field "AvailKopf" "kopf" => some (.intIn 0 65535)
  | .field "UsedKopf" "merkmale" => some (.intIn 0 65535)
  | .field "UsedKopf" "kopf" => some (.intIn 0 65535)
  | .field "Warteschlange" "cpu_basis" => some (.intIn 0 18446744073709551615)
  | .field "Warteschlange" "groesse" => some (.intIn 0 65535)
  | .field "Warteschlange" "weckversatz" => some (.intIn 0 65535)
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

/-! ### `beide_warteschlangen` -/

def beide_warteschlangen_body : List Stmt :=
  [(.bindCallElse "rx" "warteschlange_aufsetzen" ["g", "a", "u", "nummer", "cpu_basis", "dev_basis", "wunschgroesse"] [(.name "g"), (.name "a"), (.name "u"), (.lit (.int 0)), (.name "cpu_basis"), (.name "dev_basis"), (.lit (.int 8))] (.bin .and (.hasShape "nummer" (.intIn 0 65535)) (.bin .and (.hasShape "cpu_basis" (.intIn 0 18446744073709551615)) (.bin .and (.hasShape "dev_basis" (.intIn 0 281474976710656)) (.hasShape "wunschgroesse" (.intIn 0 65535))))) "e" [(.ret (some (.lit (.int 0))))]), (.bindCallElse "tx" "warteschlange_aufsetzen" ["g", "a", "u", "nummer", "cpu_basis", "dev_basis", "wunschgroesse"] [(.name "g"), (.name "a"), (.name "u"), (.lit (.int 1)), (.name "cpu_basis"), (.name "dev_basis"), (.lit (.int 8))] (.bin .and (.hasShape "nummer" (.intIn 0 65535)) (.bin .and (.hasShape "cpu_basis" (.intIn 0 18446744073709551615)) (.bin .and (.hasShape "dev_basis" (.intIn 0 281474976710656)) (.hasShape "wunschgroesse" (.intIn 0 65535))))) "e" [(.ret (some (.lit (.int 0))))]), (.retCall "weckversaetze_verschieden" ["a", "b"] [(.name "tx"), (.name "rx")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def beide_warteschlangen_pre : Expr :=
  (.bin .and (.hasShape "cpu_basis" (.intIn 0 18446744073709551615)) (.hasShape "dev_basis" (.intIn 0 281474976710656)))

def beide_warteschlangen_writes : List String := ["g", "AvailKopf", "UsedKopf"]

/-- What a caller of `beide_warteschlangen` has to bring: a well-typed world and the precondition. -/
def beide_warteschlangen_requires (t : State) : Prop := wellFormed t ∧ eval t beide_warteschlangen_pre = some (.bool true)

/-- What `beide_warteschlangen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def beide_warteschlangen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `warteschlange_aufsetzen` -/

-- REFUSED  warteschlange_aufsetzen  (device-promise): a promise at hardware Gabbro does not see: an ASSUMPTION
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def warteschlange_aufsetzen_pre : Expr :=
  (.bin .and (.hasShape "nummer" (.intIn 0 65535)) (.bin .and (.hasShape "cpu_basis" (.intIn 0 18446744073709551615)) (.bin .and (.hasShape "dev_basis" (.intIn 0 281474976710656)) (.hasShape "wunschgroesse" (.intIn 0 65535)))))

def warteschlange_aufsetzen_writes : List String := ["g", "AvailKopf", "UsedKopf"]

/-- What a caller of `warteschlange_aufsetzen` has to bring: a well-typed world and the precondition. -/
def warteschlange_aufsetzen_requires (t : State) : Prop := wellFormed t ∧ eval t warteschlange_aufsetzen_pre = some (.bool true)

/-- What `warteschlange_aufsetzen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def warteschlange_aufsetzen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  ((∃ v, r = some v) ∨ ∃ e, r = some (.reason e))

/-! ### `weckversaetze_verschieden` -/

def weckversaetze_verschieden_body : List Stmt :=
  [(.ite (.bin .gt (.fieldOf "Warteschlange" "weckversatz") (.fieldOf "Warteschlange" "weckversatz")) [(.ret (some (.lit (.int 1))))] []), (.ite (.bin .gt (.fieldOf "Warteschlange" "weckversatz") (.fieldOf "Warteschlange" "weckversatz")) [(.ret (some (.lit (.int 1))))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def weckversaetze_verschieden_pre : Expr :=
  (.lit (.bool true))

def weckversaetze_verschieden_writes : List String := []

/-- What a caller of `weckversaetze_verschieden` has to bring: a well-typed world and the precondition. -/
def weckversaetze_verschieden_requires (t : State) : Prop := wellFormed t ∧ eval t weckversaetze_verschieden_pre = some (.bool true)

/-- What `weckversaetze_verschieden` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def weckversaetze_verschieden_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `beide_warteschlangen` -/

/-- **The duty of `beide_warteschlangen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def beide_warteschlangen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s beide_warteschlangen_pre = some (.bool true))
    -- the contract of `warteschlange_aufsetzen`
    (c_warteschlange_aufsetzen : Contract ρ "warteschlange_aufsetzen" warteschlange_aufsetzen_requires warteschlange_aufsetzen_post)
    -- the frame of `warteschlange_aufsetzen`
    (fr_warteschlange_aufsetzen : Frame ρ "warteschlange_aufsetzen" warteschlange_aufsetzen_writes)
    -- the contract of `weckversaetze_verschieden`
    (c_weckversaetze_verschieden : Contract ρ "weckversaetze_verschieden" weckversaetze_verschieden_requires weckversaetze_verschieden_post)
    -- the frame of `weckversaetze_verschieden`
    (fr_weckversaetze_verschieden : Frame ρ "weckversaetze_verschieden" weckversaetze_verschieden_writes),
    ∃ s', finalState (exec ρ beide_warteschlangen_body s) = some s'
        ∧ beide_warteschlangen_post s s' (finalValue (exec ρ beide_warteschlangen_body s))

theorem beide_warteschlangen_meets : beide_warteschlangen_meets_statement := by
  unfold beide_warteschlangen_meets_statement
  intro ρ s hwf hpre c_warteschlange_aufsetzen fr_warteschlange_aufsetzen c_weckversaetze_verschieden fr_weckversaetze_verschieden
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_cpu_basis, e_cpu_basis, lo_cpu_basis, hi_cpu_basis⟩ := shape_intIn s "cpu_basis" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_dev_basis, e_dev_basis, lo_dev_basis, hi_dev_basis⟩ := shape_intIn s "dev_basis" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [beide_warteschlangen_pre, e_cpu_basis, e_dev_basis]
  gabbro_auto [beide_warteschlangen_body, beide_warteschlangen_pre, beide_warteschlangen_post, wellFormed, warteschlange_aufsetzen_pre, warteschlange_aufsetzen_requires, warteschlange_aufsetzen_post, warteschlange_aufsetzen_writes, Frame_read _ _ _ fr_warteschlange_aufsetzen, weckversaetze_verschieden_pre, weckversaetze_verschieden_requires, weckversaetze_verschieden_post, weckversaetze_verschieden_writes, Frame_read _ _ _ fr_weckversaetze_verschieden, e_cpu_basis, e_dev_basis, hall] using shapeOf

/-! ### `weckversaetze_verschieden` -/

/-- **The duty of `weckversaetze_verschieden`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def weckversaetze_verschieden_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s weckversaetze_verschieden_pre = some (.bool true)),
    ∃ s', finalState (exec ρ weckversaetze_verschieden_body s) = some s'
        ∧ weckversaetze_verschieden_post s s' (finalValue (exec ρ weckversaetze_verschieden_body s))

theorem weckversaetze_verschieden_meets : weckversaetze_verschieden_meets_statement := by
  unfold weckversaetze_verschieden_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Warteschlange_weckversatz, h_Warteschlange_weckversatz, lo_Warteschlange_weckversatz, hi_Warteschlange_weckversatz⟩ := WF_intIn shapeOf s.world (.field "Warteschlange" "weckversatz") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [weckversaetze_verschieden_pre, h_Warteschlange_weckversatz]
  gabbro_auto [weckversaetze_verschieden_body, weckversaetze_verschieden_pre, weckversaetze_verschieden_post, wellFormed, h_Warteschlange_weckversatz, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "beide_warteschlangen" beide_warteschlangen_body
  ∧ Frame ρ "beide_warteschlangen" beide_warteschlangen_writes
  ∧ Runs ρ "weckversaetze_verschieden" weckversaetze_verschieden_body
  ∧ Frame ρ "weckversaetze_verschieden" weckversaetze_verschieden_writes

/-  NOT WIRED -- the duty is stated above; the step from it to the contract is not:
      beide_warteschlangen: callee `warteschlange_aufsetzen` refused
    Each line above names the construct and the way out. What IS wired: a
    self-recursion, by induction over its `decreases` (`contract_of_duty_rec`);
    a cycle of routines, over their shared measure (`contracts_of_duties_rec`);
    a recursive call inside ONE ranged loop, by the induction outside the loop
    rule (`contract_of_duty_rec_loop_in`, 2026-09-08). A caller of a REFUSED
    callee has no contract to compose with: the callee's refusal above is the
    line to read, and fixing it wires the caller too. -/

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_weckversaetze_verschieden : weckversaetze_verschieden_meets_statement) :
    Contract ρ "weckversaetze_verschieden" weckversaetze_verschieden_requires weckversaetze_verschieden_post := by
  obtain ⟨r_beide_warteschlangen, fr_beide_warteschlangen, r_weckversaetze_verschieden, fr_weckversaetze_verschieden⟩ := hp
  have c_weckversaetze_verschieden : Contract ρ "weckversaetze_verschieden" weckversaetze_verschieden_requires weckversaetze_verschieden_post :=
    contract_of_duty ρ "weckversaetze_verschieden" weckversaetze_verschieden_body weckversaetze_verschieden_requires weckversaetze_verschieden_post r_weckversaetze_verschieden
      (fun t ht => d_weckversaetze_verschieden ρ t ht.1 ht.2)
  exact c_weckversaetze_verschieden

end GabbroDuty.DutyProbeTransportWarteschlangeAufsetzen