/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-neun-domaenen.gab  total 11  goals 6  refused 5
        @assumed 2  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 3 are refused forms

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

namespace GabbroDuty.DutyProbeNeunDomaenen

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  walk-invariant (2): ASSUMED -- an invariant of a `walk` -- a statement about a hardware table: an ASSUMPTION
    duty_1  W  Baum :: down
    duty_2  W  Baum :: leaf

  quantified (3): refused -- a quantifier over a domain other than `slots of`, or a membership
    duty_9  N  d6_fields :: ensures #1
    duty_10  N  d9_mappings :: ensures #1
    duty_11  N  d8_threads :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Baum :: down  --  ASSUMED (walk-invariant)
  duty_2  W  Baum :: leaf  --  ASSUMED (walk-invariant)
  duty_3  N  d1_slots :: ensures #1  --  carried by `d1_slots_meets`
  duty_4  N  d2_chain :: ensures #1  --  carried by `d2_chain_meets`
  duty_5  N  d3_descendants :: ensures #1  --  carried by `d3_descendants_meets`
  duty_6  N  d4_ancestors :: ensures #1  --  carried by `d4_ancestors_meets`
  duty_7  N  d5_queue :: ensures #1  --  carried by `d5_queue_meets`
  duty_8  N  d7_elems :: ensures #1  --  carried by `d7_elems_meets`
  duty_9  N  d6_fields :: ensures #1  --  refused (quantified)
  duty_10  N  d9_mappings :: ensures #1  --  refused (quantified)
  duty_11  N  d8_threads :: ensures #1  --  refused (quantified)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Knoten" _ "belegt" => some .bool
  | .slot "Knoten" _ "marke" => some (.intIn 0 4294967295)
  | .slot "Knoten" _ "elter" => some .opt
  | .slot "Knoten" _ "erstes_kind" => some .opt
  | .slot "Knoten" _ "naechstes_geschwister" => some .opt
  | .slot "Knoten" _ "fremd" => some .opt
  | .slot "Nachbar" _ "wert" => some (.intIn 0 4294967295)
  | .slot "Ring.plaetze" _ "elem" => some (.intIn 0 31)
  | .field "Ring" "kopf" => some (.intIn 0 4294967295)
  | .field "Ring" "zahl" => some (.intIn 0 4294967295)
  | .field "Wort" "gueltigkeit" => some .bool
  | .field "Wort" "schreibbar" => some .bool
  | .field "Wort" "rahmen" => some (.intIn 0 18446744073709551615)
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

/-! ### `d1_slots` -/

def d1_slots_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d1_slots_pre : Expr :=
  (.lit (.bool true))

def d1_slots_writes : List String := ["Knoten"]

/-- What a caller of `d1_slots` has to bring: a well-typed world and the precondition. -/
def d1_slots_requires (t : State) : Prop := wellFormed t ∧ eval t d1_slots_pre = some (.bool true)

/-- What `d1_slots` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d1_slots_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "s" 64 (.bin .eq (.place "Knoten" (.name "s") "marke") (.lit (.int 0)))) = some (.bool true))

/-! ### `d2_chain` -/

def d2_chain_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d2_chain_pre : Expr :=
  (.hasShape "p" (.intIn 0 63))

def d2_chain_writes : List String := ["Knoten"]

/-- What a caller of `d2_chain` has to bring: a well-typed world and the precondition. -/
def d2_chain_requires (t : State) : Prop := wellFormed t ∧ eval t d2_chain_pre = some (.bool true)

/-- What `d2_chain` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d2_chain_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "x" 64 (.bin .or (.un .not (.chainFrom "Knoten" (.place "Knoten" (.name "p") "erstes_kind") (.name "x") "naechstes_geschwister" 64)) (.bin .eq (.place "Knoten" (.name "x") "elter") (.someOf (.name "p"))))) = some (.bool true))

/-! ### `d3_descendants` -/

def d3_descendants_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d3_descendants_pre : Expr :=
  (.hasShape "s" (.intIn 0 63))

def d3_descendants_writes : List String := ["Knoten"]

/-- What a caller of `d3_descendants` has to bring: a well-typed world and the precondition. -/
def d3_descendants_requires (t : State) : Prop := wellFormed t ∧ eval t d3_descendants_pre = some (.bool true)

/-- What `d3_descendants` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d3_descendants_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.un .not (.existsSlots "x" 64 (.bin .and (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "x") (.name "s") "elter" 64)) (.place "Knoten" (.name "x") "belegt")))) = some (.bool true))

/-! ### `d4_ancestors` -/

def d4_ancestors_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d4_ancestors_pre : Expr :=
  (.hasShape "s" (.intIn 0 63))

def d4_ancestors_writes : List String := ["Knoten"]

/-- What a caller of `d4_ancestors` has to bring: a well-typed world and the precondition. -/
def d4_ancestors_requires (t : State) : Prop := wellFormed t ∧ eval t d4_ancestors_pre = some (.bool true)

/-- What `d4_ancestors` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d4_ancestors_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "x" 64 (.bin .or (.un .not (.bin .and (.bin .ne (.name "x") (.name "s")) (.reaches "Knoten" (.name "s") (.name "x") "elter" 64))) (.place "Knoten" (.name "x") "belegt"))) = some (.bool true))

/-! ### `d5_queue` -/

def d5_queue_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d5_queue_pre : Expr :=
  (.lit (.bool true))

def d5_queue_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `d5_queue` has to bring: a well-typed world and the precondition. -/
def d5_queue_requires (t : State) : Prop := wellFormed t ∧ eval t d5_queue_pre = some (.bool true)

/-- What `d5_queue` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d5_queue_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "j" 32 (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64)))) = some (.bool true))

/-! ### `d6_fields` -/

def d6_fields_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d6_fields_pre : Expr :=
  (.lit (.bool true))

def d6_fields_writes : List String := ["Knoten"]

/-- What a caller of `d6_fields` has to bring: a well-typed world and the precondition. -/
def d6_fields_requires (t : State) : Prop := wellFormed t ∧ eval t d6_fields_pre = some (.bool true)

/-- What `d6_fields` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d6_fields_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1: NOT SAID (quantified) -- a promise fewer makes a caller's goal harder, never wrong
  True

/-! ### `d7_elems` -/

def d7_elems_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d7_elems_pre : Expr :=
  (.lit (.bool true))

def d7_elems_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `d7_elems` has to bring: a well-typed world and the precondition. -/
def d7_elems_requires (t : State) : Prop := wellFormed t ∧ eval t d7_elems_pre = some (.bool true)

/-- What `d7_elems` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d7_elems_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.forallSlots "j" 32 (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64)))) = some (.bool true))

/-! ### `d8_threads` -/

def d8_threads_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d8_threads_pre : Expr :=
  (.lit (.bool true))

def d8_threads_writes : List String := ["Knoten"]

/-- What a caller of `d8_threads` has to bring: a well-typed world and the precondition. -/
def d8_threads_requires (t : State) : Prop := wellFormed t ∧ eval t d8_threads_pre = some (.bool true)

/-- What `d8_threads` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d8_threads_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1: NOT SAID (quantified) -- a promise fewer makes a caller's goal harder, never wrong
  True

/-! ### `d9_mappings` -/

def d9_mappings_body : List Stmt :=
  []

/-- The precondition: the declared shapes and the `requires`. -/
def d9_mappings_pre : Expr :=
  (.lit (.bool true))

def d9_mappings_writes : List String := ["w"]

/-- What a caller of `d9_mappings` has to bring: a well-typed world and the precondition. -/
def d9_mappings_requires (t : State) : Prop := wellFormed t ∧ eval t d9_mappings_pre = some (.bool true)

/-- What `d9_mappings` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def d9_mappings_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1: NOT SAID (quantified) -- a promise fewer makes a caller's goal harder, never wrong
  True

/-! ## The duties: one statement per routine and per loop -/

/-! ### `d1_slots` -/

/-- **The duty of `d1_slots`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d1_slots_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d1_slots_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d1_slots_body s) = some s'
        ∧ d1_slots_post s s' (finalValue (exec ρ d1_slots_body s))

theorem d1_slots_meets : d1_slots_meets_statement := by
  unfold d1_slots_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d1_slots_pre]
  gabbro_auto [d1_slots_body, d1_slots_pre, d1_slots_post, wellFormed, hall] using shapeOf

/-! ### `d2_chain` -/

/-- **The duty of `d2_chain`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d2_chain_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d2_chain_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d2_chain_body s) = some s'
        ∧ d2_chain_post s s' (finalValue (exec ρ d2_chain_body s))

theorem d2_chain_meets : d2_chain_meets_statement := by
  unfold d2_chain_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_p, e_p, lo_p, hi_p⟩ := shape_intIn s "p" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [d2_chain_pre, e_p]
  gabbro_auto [d2_chain_body, d2_chain_pre, d2_chain_post, wellFormed, e_p, hall] using shapeOf

/-! ### `d3_descendants` -/

/-- **The duty of `d3_descendants`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d3_descendants_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d3_descendants_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d3_descendants_body s) = some s'
        ∧ d3_descendants_post s s' (finalValue (exec ρ d3_descendants_body s))

theorem d3_descendants_meets : d3_descendants_meets_statement := by
  unfold d3_descendants_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [d3_descendants_pre, e_s]
  gabbro_auto [d3_descendants_body, d3_descendants_pre, d3_descendants_post, wellFormed, e_s, hall] using shapeOf

/-! ### `d4_ancestors` -/

/-- **The duty of `d4_ancestors`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d4_ancestors_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d4_ancestors_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d4_ancestors_body s) = some s'
        ∧ d4_ancestors_post s s' (finalValue (exec ρ d4_ancestors_body s))

theorem d4_ancestors_meets : d4_ancestors_meets_statement := by
  unfold d4_ancestors_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [d4_ancestors_pre, e_s]
  gabbro_auto [d4_ancestors_body, d4_ancestors_pre, d4_ancestors_post, wellFormed, e_s, hall] using shapeOf

/-! ### `d5_queue` -/

/-- **The duty of `d5_queue`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d5_queue_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d5_queue_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d5_queue_body s) = some s'
        ∧ d5_queue_post s s' (finalValue (exec ρ d5_queue_body s))

theorem d5_queue_meets : d5_queue_meets_statement := by
  unfold d5_queue_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d5_queue_pre]
  gabbro_auto [d5_queue_body, d5_queue_pre, d5_queue_post, wellFormed, hall] using shapeOf

/-! ### `d6_fields` -/

/-- **The duty of `d6_fields`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d6_fields_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d6_fields_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d6_fields_body s) = some s'
        ∧ d6_fields_post s s' (finalValue (exec ρ d6_fields_body s))

theorem d6_fields_meets : d6_fields_meets_statement := by
  unfold d6_fields_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d6_fields_pre]
  gabbro_auto [d6_fields_body, d6_fields_pre, d6_fields_post, wellFormed, hall] using shapeOf

/-! ### `d7_elems` -/

/-- **The duty of `d7_elems`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d7_elems_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d7_elems_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d7_elems_body s) = some s'
        ∧ d7_elems_post s s' (finalValue (exec ρ d7_elems_body s))

theorem d7_elems_meets : d7_elems_meets_statement := by
  unfold d7_elems_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d7_elems_pre]
  gabbro_auto [d7_elems_body, d7_elems_pre, d7_elems_post, wellFormed, hall] using shapeOf

/-! ### `d8_threads` -/

/-- **The duty of `d8_threads`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d8_threads_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d8_threads_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d8_threads_body s) = some s'
        ∧ d8_threads_post s s' (finalValue (exec ρ d8_threads_body s))

theorem d8_threads_meets : d8_threads_meets_statement := by
  unfold d8_threads_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d8_threads_pre]
  gabbro_auto [d8_threads_body, d8_threads_pre, d8_threads_post, wellFormed, hall] using shapeOf

/-! ### `d9_mappings` -/

/-- **The duty of `d9_mappings`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def d9_mappings_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s d9_mappings_pre = some (.bool true)),
    ∃ s', finalState (exec ρ d9_mappings_body s) = some s'
        ∧ d9_mappings_post s s' (finalValue (exec ρ d9_mappings_body s))

theorem d9_mappings_meets : d9_mappings_meets_statement := by
  unfold d9_mappings_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [d9_mappings_pre]
  gabbro_auto [d9_mappings_body, d9_mappings_pre, d9_mappings_post, wellFormed, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "d1_slots" d1_slots_body
  ∧ Frame ρ "d1_slots" d1_slots_writes
  ∧ Runs ρ "d2_chain" d2_chain_body
  ∧ Frame ρ "d2_chain" d2_chain_writes
  ∧ Runs ρ "d3_descendants" d3_descendants_body
  ∧ Frame ρ "d3_descendants" d3_descendants_writes
  ∧ Runs ρ "d4_ancestors" d4_ancestors_body
  ∧ Frame ρ "d4_ancestors" d4_ancestors_writes
  ∧ Runs ρ "d5_queue" d5_queue_body
  ∧ Frame ρ "d5_queue" d5_queue_writes
  ∧ Runs ρ "d6_fields" d6_fields_body
  ∧ Frame ρ "d6_fields" d6_fields_writes
  ∧ Runs ρ "d7_elems" d7_elems_body
  ∧ Frame ρ "d7_elems" d7_elems_writes
  ∧ Runs ρ "d8_threads" d8_threads_body
  ∧ Frame ρ "d8_threads" d8_threads_writes
  ∧ Runs ρ "d9_mappings" d9_mappings_body
  ∧ Frame ρ "d9_mappings" d9_mappings_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_d1_slots : d1_slots_meets_statement)
    (d_d2_chain : d2_chain_meets_statement)
    (d_d3_descendants : d3_descendants_meets_statement)
    (d_d4_ancestors : d4_ancestors_meets_statement)
    (d_d5_queue : d5_queue_meets_statement)
    (d_d6_fields : d6_fields_meets_statement)
    (d_d7_elems : d7_elems_meets_statement)
    (d_d8_threads : d8_threads_meets_statement)
    (d_d9_mappings : d9_mappings_meets_statement) :
    Contract ρ "d1_slots" d1_slots_requires d1_slots_post
    ∧ Contract ρ "d2_chain" d2_chain_requires d2_chain_post
    ∧ Contract ρ "d3_descendants" d3_descendants_requires d3_descendants_post
    ∧ Contract ρ "d4_ancestors" d4_ancestors_requires d4_ancestors_post
    ∧ Contract ρ "d5_queue" d5_queue_requires d5_queue_post
    ∧ Contract ρ "d6_fields" d6_fields_requires d6_fields_post
    ∧ Contract ρ "d7_elems" d7_elems_requires d7_elems_post
    ∧ Contract ρ "d8_threads" d8_threads_requires d8_threads_post
    ∧ Contract ρ "d9_mappings" d9_mappings_requires d9_mappings_post := by
  obtain ⟨r_d1_slots, fr_d1_slots, r_d2_chain, fr_d2_chain, r_d3_descendants, fr_d3_descendants, r_d4_ancestors, fr_d4_ancestors, r_d5_queue, fr_d5_queue, r_d6_fields, fr_d6_fields, r_d7_elems, fr_d7_elems, r_d8_threads, fr_d8_threads, r_d9_mappings, fr_d9_mappings⟩ := hp
  have c_d1_slots : Contract ρ "d1_slots" d1_slots_requires d1_slots_post :=
    contract_of_duty ρ "d1_slots" d1_slots_body d1_slots_requires d1_slots_post r_d1_slots
      (fun t ht => d_d1_slots ρ t ht.1 ht.2)
  have c_d2_chain : Contract ρ "d2_chain" d2_chain_requires d2_chain_post :=
    contract_of_duty ρ "d2_chain" d2_chain_body d2_chain_requires d2_chain_post r_d2_chain
      (fun t ht => d_d2_chain ρ t ht.1 ht.2)
  have c_d3_descendants : Contract ρ "d3_descendants" d3_descendants_requires d3_descendants_post :=
    contract_of_duty ρ "d3_descendants" d3_descendants_body d3_descendants_requires d3_descendants_post r_d3_descendants
      (fun t ht => d_d3_descendants ρ t ht.1 ht.2)
  have c_d4_ancestors : Contract ρ "d4_ancestors" d4_ancestors_requires d4_ancestors_post :=
    contract_of_duty ρ "d4_ancestors" d4_ancestors_body d4_ancestors_requires d4_ancestors_post r_d4_ancestors
      (fun t ht => d_d4_ancestors ρ t ht.1 ht.2)
  have c_d5_queue : Contract ρ "d5_queue" d5_queue_requires d5_queue_post :=
    contract_of_duty ρ "d5_queue" d5_queue_body d5_queue_requires d5_queue_post r_d5_queue
      (fun t ht => d_d5_queue ρ t ht.1 ht.2)
  have c_d6_fields : Contract ρ "d6_fields" d6_fields_requires d6_fields_post :=
    contract_of_duty ρ "d6_fields" d6_fields_body d6_fields_requires d6_fields_post r_d6_fields
      (fun t ht => d_d6_fields ρ t ht.1 ht.2)
  have c_d7_elems : Contract ρ "d7_elems" d7_elems_requires d7_elems_post :=
    contract_of_duty ρ "d7_elems" d7_elems_body d7_elems_requires d7_elems_post r_d7_elems
      (fun t ht => d_d7_elems ρ t ht.1 ht.2)
  have c_d8_threads : Contract ρ "d8_threads" d8_threads_requires d8_threads_post :=
    contract_of_duty ρ "d8_threads" d8_threads_body d8_threads_requires d8_threads_post r_d8_threads
      (fun t ht => d_d8_threads ρ t ht.1 ht.2)
  have c_d9_mappings : Contract ρ "d9_mappings" d9_mappings_requires d9_mappings_post :=
    contract_of_duty ρ "d9_mappings" d9_mappings_body d9_mappings_requires d9_mappings_post r_d9_mappings
      (fun t ht => d_d9_mappings ρ t ht.1 ht.2)
  exact ⟨c_d1_slots, c_d2_chain, c_d3_descendants, c_d4_ancestors, c_d5_queue, c_d6_fields, c_d7_elems, c_d8_threads, c_d9_mappings⟩

end GabbroDuty.DutyProbeNeunDomaenen
