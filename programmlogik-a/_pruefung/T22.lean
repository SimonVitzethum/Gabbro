/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/22-bootstrecke.gab  total 7  goals 0  refused 7
        @assumed 7  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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
set_option maxHeartbeats 9600000

open Gabbro.Body

namespace GabbroDuty.Duty22Bootstrecke

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (7): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_1  F  melde_roh :: ensures #1
    duty_2  F  mmu_an :: ensures #1
    duty_3  F  cap_tabellen :: ensures #1
    duty_4  F  ipc_tabellen :: ensures #1
    duty_5  F  autoritaet_melden :: ensures #1
    duty_6  F  verifizierer_starten :: ensures #1
    duty_7  F  root_task_starten :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  F  melde_roh :: ensures #1  --  ASSUMED (foreign-body)
  duty_2  F  mmu_an :: ensures #1  --  ASSUMED (foreign-body)
  duty_3  F  cap_tabellen :: ensures #1  --  ASSUMED (foreign-body)
  duty_4  F  ipc_tabellen :: ensures #1  --  ASSUMED (foreign-body)
  duty_5  F  autoritaet_melden :: ensures #1  --  ASSUMED (foreign-body)
  duty_6  F  verifizierer_starten :: ensures #1  --  ASSUMED (foreign-body)
  duty_7  F  root_task_starten :: ensures #1  --  ASSUMED (foreign-body)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .global "mmu_an_zahl" => some (.intIn 0 4294967295)
  | .global "caps_bereit" => some (.intIn 0 4294967295)
  | .global "eps_bereit" => some (.intIn 0 4294967295)
  | .global "gemeldet" => some (.intIn 0 4294967295)
  | .global "faeden" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `autoritaet_melden` -- a foreign body: its contract is an assumption. -/
def autoritaet_melden_pre : Expr :=
  (.lit (.bool true))

def autoritaet_melden_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .eq (.global "gemeldet") (.lit (.int 1))) = some (.bool true))

def autoritaet_melden_writes : List String := ["p", "gemeldet"]

def autoritaet_melden_requires (t : State) : Prop := wellFormed t ∧ eval t autoritaet_melden_pre = some (.bool true)

/-- `cap_tabellen` -- a foreign body: its contract is an assumption. -/
def cap_tabellen_pre : Expr :=
  (.lit (.bool true))

def cap_tabellen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .eq (.global "caps_bereit") (.lit (.int 1))) = some (.bool true))

def cap_tabellen_writes : List String := ["p", "caps_bereit"]

def cap_tabellen_requires (t : State) : Prop := wellFormed t ∧ eval t cap_tabellen_pre = some (.bool true)

/-- `ipc_tabellen` -- a foreign body: its contract is an assumption. -/
def ipc_tabellen_pre : Expr :=
  (.lit (.bool true))

def ipc_tabellen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .eq (.global "eps_bereit") (.lit (.int 1))) = some (.bool true))

def ipc_tabellen_writes : List String := ["p", "eps_bereit"]

def ipc_tabellen_requires (t : State) : Prop := wellFormed t ∧ eval t ipc_tabellen_pre = some (.bool true)

/-- `mmu_an` -- a foreign body: its contract is an assumption. -/
def mmu_an_pre : Expr :=
  (.lit (.bool true))

def mmu_an_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .eq (.global "mmu_an_zahl") (.lit (.int 1))) = some (.bool true))

def mmu_an_writes : List String := ["p", "mmu_an_zahl"]

def mmu_an_requires (t : State) : Prop := wellFormed t ∧ eval t mmu_an_pre = some (.bool true)

/-- `root_task_starten` -- a foreign body: its contract is an assumption. -/
def root_task_starten_pre : Expr :=
  (.lit (.bool true))

def root_task_starten_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .ge (.global "faeden") (.lit (.int 2))) = some (.bool true))

def root_task_starten_writes : List String := ["p", "faeden"]

def root_task_starten_requires (t : State) : Prop := wellFormed t ∧ eval t root_task_starten_pre = some (.bool true)

/-- `verifizierer_starten` -- a foreign body: its contract is an assumption. -/
def verifizierer_starten_pre : Expr :=
  (.lit (.bool true))

def verifizierer_starten_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ v, r = some v)
  ∧ (eval { world := t'.world, local' := t.local' } (.bin .ge (.global "faeden") (.lit (.int 1))) = some (.bool true))

def verifizierer_starten_writes : List String := ["p", "faeden"]

def verifizierer_starten_requires (t : State) : Prop := wellFormed t ∧ eval t verifizierer_starten_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "autoritaet_melden" autoritaet_melden_requires autoritaet_melden_post
  ∧ Frame ρ "autoritaet_melden" autoritaet_melden_writes
  ∧ Contract ρ "cap_tabellen" cap_tabellen_requires cap_tabellen_post
  ∧ Frame ρ "cap_tabellen" cap_tabellen_writes
  ∧ Contract ρ "ipc_tabellen" ipc_tabellen_requires ipc_tabellen_post
  ∧ Frame ρ "ipc_tabellen" ipc_tabellen_writes
  ∧ Contract ρ "mmu_an" mmu_an_requires mmu_an_post
  ∧ Frame ρ "mmu_an" mmu_an_writes
  ∧ Contract ρ "root_task_starten" root_task_starten_requires root_task_starten_post
  ∧ Frame ρ "root_task_starten" root_task_starten_writes
  ∧ Contract ρ "verifizierer_starten" verifizierer_starten_requires verifizierer_starten_post
  ∧ Frame ρ "verifizierer_starten" verifizierer_starten_writes

/-! ## The routines: body and contract -/

/-! ### `hochlauf` -/

def hochlauf_body : List Stmt :=
  [(.bindCall "p1" "mmu_an" ["p"] [(.name "p")] (.lit (.bool true))), (.bindCall "p2" "cap_tabellen" ["p"] [(.name "p1")] (.lit (.bool true))), (.bindCall "p3" "ipc_tabellen" ["p"] [(.name "p2")] (.lit (.bool true))), (.bindCall "p4" "autoritaet_melden" ["p"] [(.name "p3")] (.lit (.bool true))), (.bindCall "p5" "verifizierer_starten" ["p"] [(.name "p4")] (.lit (.bool true))), (.call "root_task_starten" ["p"] [(.name "p5")] (.lit (.bool true)))]

/-- The precondition: the declared shapes and the `requires`. -/
def hochlauf_pre : Expr :=
  (.lit (.bool true))

def hochlauf_writes : List String := ["p", "mmu_an_zahl", "caps_bereit", "eps_bereit", "gemeldet", "faeden"]

/-- What a caller of `hochlauf` has to bring: a well-typed world and the precondition. -/
def hochlauf_requires (t : State) : Prop := wellFormed t ∧ eval t hochlauf_pre = some (.bool true)

/-- What `hochlauf` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def hochlauf_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `hochlauf` -/

/-- **The duty of `hochlauf`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def hochlauf_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s hochlauf_pre = some (.bool true))
    -- the contract of `autoritaet_melden`
    (c_autoritaet_melden : Contract ρ "autoritaet_melden" autoritaet_melden_requires autoritaet_melden_post)
    -- the frame of `autoritaet_melden`
    (fr_autoritaet_melden : Frame ρ "autoritaet_melden" autoritaet_melden_writes)
    -- the contract of `cap_tabellen`
    (c_cap_tabellen : Contract ρ "cap_tabellen" cap_tabellen_requires cap_tabellen_post)
    -- the frame of `cap_tabellen`
    (fr_cap_tabellen : Frame ρ "cap_tabellen" cap_tabellen_writes)
    -- the contract of `ipc_tabellen`
    (c_ipc_tabellen : Contract ρ "ipc_tabellen" ipc_tabellen_requires ipc_tabellen_post)
    -- the frame of `ipc_tabellen`
    (fr_ipc_tabellen : Frame ρ "ipc_tabellen" ipc_tabellen_writes)
    -- the contract of `mmu_an`
    (c_mmu_an : Contract ρ "mmu_an" mmu_an_requires mmu_an_post)
    -- the frame of `mmu_an`
    (fr_mmu_an : Frame ρ "mmu_an" mmu_an_writes)
    -- the contract of `root_task_starten`
    (c_root_task_starten : Contract ρ "root_task_starten" root_task_starten_requires root_task_starten_post)
    -- the frame of `root_task_starten`
    (fr_root_task_starten : Frame ρ "root_task_starten" root_task_starten_writes)
    -- the contract of `verifizierer_starten`
    (c_verifizierer_starten : Contract ρ "verifizierer_starten" verifizierer_starten_requires verifizierer_starten_post)
    -- the frame of `verifizierer_starten`
    (fr_verifizierer_starten : Frame ρ "verifizierer_starten" verifizierer_starten_writes),
    ∃ s', finalState (exec ρ hochlauf_body s) = some s'
        ∧ hochlauf_post s s' (finalValue (exec ρ hochlauf_body s))

theorem hochlauf_meets : hochlauf_meets_statement := by
  unfold hochlauf_meets_statement
  intro ρ s hwf hpre c_autoritaet_melden fr_autoritaet_melden c_cap_tabellen fr_cap_tabellen c_ipc_tabellen fr_ipc_tabellen c_mmu_an fr_mmu_an c_root_task_starten fr_root_task_starten c_verifizierer_starten fr_verifizierer_starten
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [hochlauf_pre]
  gabbro_simp [hochlauf_body, hochlauf_pre, hochlauf_post, wellFormed, autoritaet_melden_pre, autoritaet_melden_requires, autoritaet_melden_post, autoritaet_melden_writes, Frame_read _ _ _ fr_autoritaet_melden, cap_tabellen_pre, cap_tabellen_requires, cap_tabellen_post, cap_tabellen_writes, Frame_read _ _ _ fr_cap_tabellen, ipc_tabellen_pre, ipc_tabellen_requires, ipc_tabellen_post, ipc_tabellen_writes, Frame_read _ _ _ fr_ipc_tabellen, mmu_an_pre, mmu_an_requires, mmu_an_post, mmu_an_writes, Frame_read _ _ _ fr_mmu_an, root_task_starten_pre, root_task_starten_requires, root_task_starten_post, root_task_starten_writes, Frame_read _ _ _ fr_root_task_starten, verifizierer_starten_pre, verifizierer_starten_requires, verifizierer_starten_post, verifizierer_starten_writes, Frame_read _ _ _ fr_verifizierer_starten, hall]
  gabbro_try 5000 (all_goals (try gabbro_calls shapeOf [hochlauf_body, hochlauf_pre, hochlauf_post, wellFormed, autoritaet_melden_pre, autoritaet_melden_requires, autoritaet_melden_post, autoritaet_melden_writes, Frame_read _ _ _ fr_autoritaet_melden, cap_tabellen_pre, cap_tabellen_requires, cap_tabellen_post, cap_tabellen_writes, Frame_read _ _ _ fr_cap_tabellen, ipc_tabellen_pre, ipc_tabellen_requires, ipc_tabellen_post, ipc_tabellen_writes, Frame_read _ _ _ fr_ipc_tabellen, mmu_an_pre, mmu_an_requires, mmu_an_post, mmu_an_writes, Frame_read _ _ _ fr_mmu_an, root_task_starten_pre, root_task_starten_requires, root_task_starten_post, root_task_starten_writes, Frame_read _ _ _ fr_root_task_starten, verifizierer_starten_pre, verifizierer_starten_requires, verifizierer_starten_post, verifizierer_starten_writes, Frame_read _ _ _ fr_verifizierer_starten, hall]))
  trace_state
  all_goals sorry
