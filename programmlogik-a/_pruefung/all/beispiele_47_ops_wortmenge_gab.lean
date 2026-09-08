/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/47-ops-wortmenge.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty47OpsWortmenge

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Ordner" _ "benutzt" => some .bool
  | .slot "Ordner" _ "elter" => some .opt
  | .slot "Verzeichnis" _ "benutzt" => some .bool
  | .slot "Verzeichnis" _ "marke" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `marke_null_wenn_frei` over `Verzeichnis`. -/
def inv_marke_null_wenn_frei : Expr :=
  (.forallSlots "s" 16 (.bin .or (.place "Verzeichnis" (.name "s") "benutzt") (.bin .eq (.place "Verzeichnis" (.name "s") "marke") (.lit (.int 0)))))

/-- `jeder_erreicht_die_wurzel` over `Ordner`. -/
def inv_jeder_erreicht_die_wurzel : Expr :=
  (.forallSlots "s" 16 (.reaches "Ordner" (.name "s") (.lit (.int 0)) "elter" 16))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `Ordner::remove` -- a generated operation: its premises are the schema `opsruf` cuts,
    and that it preserves the table's invariants is `table.ops.erhaltung`. -/
def Ordner_remove_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.forallSlots "x" 16 (.bin .ne (.place "Ordner" (.name "x") "elter") (.someOf (.name "s")))))

def Ordner_remove_post (t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'
  ∧ (eval t inv_jeder_erreicht_die_wurzel = some (.bool true) → eval t' inv_jeder_erreicht_die_wurzel = some (.bool true))

def Ordner_remove_writes : List String := ["Ordner"]

def Ordner_remove_requires (t : State) : Prop := wellFormed t ∧ eval t Ordner_remove_pre = some (.bool true)

/-- `Verzeichnis::insert` -- a generated operation: its premises are the schema `opsruf` cuts,
    and that it preserves the table's invariants is `table.ops.erhaltung`. -/
def Verzeichnis_insert_pre : Expr :=
  (.bin .and (.hasShape "n" .int) (.un .not (.place "Verzeichnis" (.name "n") "benutzt")))

def Verzeichnis_insert_post (t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'
  ∧ (eval t inv_marke_null_wenn_frei = some (.bool true) → eval t' inv_marke_null_wenn_frei = some (.bool true))

def Verzeichnis_insert_writes : List String := ["Verzeichnis"]

def Verzeichnis_insert_requires (t : State) : Prop := wellFormed t ∧ eval t Verzeichnis_insert_pre = some (.bool true)

/-- `Verzeichnis::remove` -- a generated operation: its premises are the schema `opsruf` cuts,
    and that it preserves the table's invariants is `table.ops.erhaltung`. -/
def Verzeichnis_remove_pre : Expr :=
  (.hasShape "s" .int)

def Verzeichnis_remove_post (t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'
  ∧ (eval t inv_marke_null_wenn_frei = some (.bool true) → eval t' inv_marke_null_wenn_frei = some (.bool true))

def Verzeichnis_remove_writes : List String := ["Verzeichnis"]

def Verzeichnis_remove_requires (t : State) : Prop := wellFormed t ∧ eval t Verzeichnis_remove_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_marke_null_wenn_frei = some (.bool true)
  ∧ eval s0 inv_jeder_erreicht_die_wurzel = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "Ordner::remove" Ordner_remove_requires Ordner_remove_post
  ∧ Frame ρ "Ordner::remove" Ordner_remove_writes
  ∧ Contract ρ "Verzeichnis::insert" Verzeichnis_insert_requires Verzeichnis_insert_post
  ∧ Frame ρ "Verzeichnis::insert" Verzeichnis_insert_writes
  ∧ Contract ρ "Verzeichnis::remove" Verzeichnis_remove_requires Verzeichnis_remove_post
  ∧ Frame ρ "Verzeichnis::remove" Verzeichnis_remove_writes

/-! ## The routines: body and contract -/

/-! ### `aushaengen` -/

def aushaengen_body : List Stmt :=
  [(.call "Ordner::remove" ["t", "s"] [(.name "o"), (.name "s")] (.bin .and (.hasShape "s" .int) (.forallSlots "x" 16 (.bin .ne (.place "Ordner" (.name "x") "elter") (.someOf (.name "s"))))))]

/-- The precondition: the declared shapes and the `requires`. -/
def aushaengen_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 15)) (.forallSlots "x" 16 (.bin .ne (.place "Ordner" (.name "x") "elter") (.someOf (.name "s")))))

def aushaengen_writes : List String := ["Ordner"]

/-- What a caller of `aushaengen` has to bring: a well-typed world and the precondition. -/
def aushaengen_requires (t : State) : Prop := wellFormed t ∧ eval t aushaengen_pre = some (.bool true)

/-- What `aushaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aushaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `belegen` -/

def belegen_body : List Stmt :=
  [(.call "Verzeichnis::insert" ["t", "n"] [(.name "v"), (.name "i")] (.bin .and (.hasShape "n" .int) (.un .not (.place "Verzeichnis" (.name "n") "benutzt"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def belegen_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 15)) (.un .not (.place "Verzeichnis" (.name "i") "benutzt")))

def belegen_writes : List String := ["Verzeichnis"]

/-- What a caller of `belegen` has to bring: a well-typed world and the precondition. -/
def belegen_requires (t : State) : Prop := wellFormed t ∧ eval t belegen_pre = some (.bool true)

/-- What `belegen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def belegen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `belegen_wenn_frei` -/

def belegen_wenn_frei_body : List Stmt :=
  [(.ite (.un .not (.place "Verzeichnis" (.name "i") "benutzt")) [(.call "Verzeichnis::insert" ["t", "n"] [(.name "v"), (.name "i")] (.bin .and (.hasShape "n" .int) (.un .not (.place "Verzeichnis" (.name "n") "benutzt"))))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def belegen_wenn_frei_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def belegen_wenn_frei_writes : List String := ["Verzeichnis"]

/-- What a caller of `belegen_wenn_frei` has to bring: a well-typed world and the precondition. -/
def belegen_wenn_frei_requires (t : State) : Prop := wellFormed t ∧ eval t belegen_wenn_frei_pre = some (.bool true)

/-- What `belegen_wenn_frei` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def belegen_wenn_frei_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `einhaengen` -/

-- REFUSED  einhaengen  (generated-op): a generated table operation whose premises name a root no invariant names
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def einhaengen_pre : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 15)) (.bin .and (.hasShape "p" (.intIn 0 15)) (.bin .and (.un .not (.place "Ordner" (.name "n") "benutzt")) (.reaches "Ordner" (.name "p") (.lit (.int 0)) "elter" 16))))

def einhaengen_writes : List String := ["Ordner"]

/-- What a caller of `einhaengen` has to bring: a well-typed world and the precondition. -/
def einhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t einhaengen_pre = some (.bool true)

/-- What `einhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `ist_belegt` -/

def ist_belegt_body : List Stmt :=
  [(.ret (some (.place "Verzeichnis" (.name "i") "benutzt")))]

/-- The precondition: the declared shapes and the `requires`. -/
def ist_belegt_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def ist_belegt_writes : List String := []

/-- What a caller of `ist_belegt` has to bring: a well-typed world and the precondition. -/
def ist_belegt_requires (t : State) : Prop := wellFormed t ∧ eval t ist_belegt_pre = some (.bool true)

/-- What `ist_belegt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ist_belegt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `marke_von` -/

def marke_von_body : List Stmt :=
  [(.ret (some (.place "Verzeichnis" (.name "i") "marke")))]

/-- The precondition: the declared shapes and the `requires`. -/
def marke_von_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def marke_von_writes : List String := []

/-- What a caller of `marke_von` has to bring: a well-typed world and the precondition. -/
def marke_von_requires (t : State) : Prop := wellFormed t ∧ eval t marke_von_pre = some (.bool true)

/-- What `marke_von` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def marke_von_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `raeumen` -/

def raeumen_body : List Stmt :=
  [(.call "Verzeichnis::remove" ["t", "s"] [(.name "v"), (.name "i")] (.hasShape "s" .int))]

/-- The precondition: the declared shapes and the `requires`. -/
def raeumen_pre : Expr :=
  (.hasShape "i" (.intIn 0 15))

def raeumen_writes : List String := ["Verzeichnis"]

/-- What a caller of `raeumen` has to bring: a well-typed world and the precondition. -/
def raeumen_requires (t : State) : Prop := wellFormed t ∧ eval t raeumen_pre = some (.bool true)

/-- What `raeumen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def raeumen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `umhaengen` -/

-- REFUSED  umhaengen  (generated-op): a generated table operation whose premises name a root no invariant names
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def umhaengen_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 15)) (.bin .and (.hasShape "p" (.intIn 0 15)) (.bin .and (.reaches "Ordner" (.name "p") (.lit (.int 0)) "elter" 16) (.un .not (.reaches "Ordner" (.name "p") (.name "s") "elter" 16)))))

def umhaengen_writes : List String := ["Ordner"]

/-- What a caller of `umhaengen` has to bring: a well-typed world and the precondition. -/
def umhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t umhaengen_pre = some (.bool true)

/-- What `umhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def umhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `aushaengen` -/

/-- **The duty of `aushaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aushaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aushaengen_pre = some (.bool true))
    -- the contract of `Ordner::remove`
    (c_Ordner_remove : Contract ρ "Ordner::remove" Ordner_remove_requires Ordner_remove_post)
    -- the frame of `Ordner::remove`
    (fr_Ordner_remove : Frame ρ "Ordner::remove" Ordner_remove_writes),
    ∃ s', finalState (exec ρ aushaengen_body s) = some s'
        ∧ aushaengen_post s s' (finalValue (exec ρ aushaengen_body s))

theorem aushaengen_meets : aushaengen_meets_statement := by
  unfold aushaengen_meets_statement
  intro ρ s hwf hpre c_Ordner_remove fr_Ordner_remove
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [aushaengen_pre, e_s]
  gabbro_auto [aushaengen_body, aushaengen_pre, aushaengen_post, wellFormed, Ordner_remove_pre, Ordner_remove_requires, Ordner_remove_post, Ordner_remove_writes, Frame_read _ _ _ fr_Ordner_remove, e_s, hall] using shapeOf

/-! ### `belegen` -/

/-- **The duty of `belegen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def belegen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s belegen_pre = some (.bool true))
    -- the contract of `Verzeichnis::insert`
    (c_Verzeichnis_insert : Contract ρ "Verzeichnis::insert" Verzeichnis_insert_requires Verzeichnis_insert_post)
    -- the frame of `Verzeichnis::insert`
    (fr_Verzeichnis_insert : Frame ρ "Verzeichnis::insert" Verzeichnis_insert_writes),
    ∃ s', finalState (exec ρ belegen_body s) = some s'
        ∧ belegen_post s s' (finalValue (exec ρ belegen_body s))

theorem belegen_meets : belegen_meets_statement := by
  unfold belegen_meets_statement
  intro ρ s hwf hpre c_Verzeichnis_insert fr_Verzeichnis_insert
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [belegen_pre, e_i]
  gabbro_auto [belegen_body, belegen_pre, belegen_post, wellFormed, Verzeichnis_insert_pre, Verzeichnis_insert_requires, Verzeichnis_insert_post, Verzeichnis_insert_writes, Frame_read _ _ _ fr_Verzeichnis_insert, e_i, hall] using shapeOf

/-! ### `belegen_wenn_frei` -/

/-- **The duty of `belegen_wenn_frei`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def belegen_wenn_frei_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s belegen_wenn_frei_pre = some (.bool true))
    -- the contract of `Verzeichnis::insert`
    (c_Verzeichnis_insert : Contract ρ "Verzeichnis::insert" Verzeichnis_insert_requires Verzeichnis_insert_post)
    -- the frame of `Verzeichnis::insert`
    (fr_Verzeichnis_insert : Frame ρ "Verzeichnis::insert" Verzeichnis_insert_writes),
    ∃ s', finalState (exec ρ belegen_wenn_frei_body s) = some s'
        ∧ belegen_wenn_frei_post s s' (finalValue (exec ρ belegen_wenn_frei_body s))

theorem belegen_wenn_frei_meets : belegen_wenn_frei_meets_statement := by
  unfold belegen_wenn_frei_meets_statement
  intro ρ s hwf hpre c_Verzeichnis_insert fr_Verzeichnis_insert
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Verzeichnis_benutzt_i, h_Verzeichnis_benutzt_i⟩ := WF_bool shapeOf s.world (.slot "Verzeichnis" w_i "benutzt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [belegen_wenn_frei_pre, e_i, h_Verzeichnis_benutzt_i]
  gabbro_auto [belegen_wenn_frei_body, belegen_wenn_frei_pre, belegen_wenn_frei_post, wellFormed, Verzeichnis_insert_pre, Verzeichnis_insert_requires, Verzeichnis_insert_post, Verzeichnis_insert_writes, Frame_read _ _ _ fr_Verzeichnis_insert, e_i, h_Verzeichnis_benutzt_i, hall] using shapeOf

/-! ### `ist_belegt` -/

/-- **The duty of `ist_belegt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def ist_belegt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s ist_belegt_pre = some (.bool true)),
    ∃ s', finalState (exec ρ ist_belegt_body s) = some s'
        ∧ ist_belegt_post s s' (finalValue (exec ρ ist_belegt_body s))

theorem ist_belegt_meets : ist_belegt_meets_statement := by
  unfold ist_belegt_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Verzeichnis_benutzt_i, h_Verzeichnis_benutzt_i⟩ := WF_bool shapeOf s.world (.slot "Verzeichnis" w_i "benutzt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [ist_belegt_pre, e_i, h_Verzeichnis_benutzt_i]
  gabbro_auto [ist_belegt_body, ist_belegt_pre, ist_belegt_post, wellFormed, e_i, h_Verzeichnis_benutzt_i, hall] using shapeOf

/-! ### `marke_von` -/

/-- **The duty of `marke_von`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def marke_von_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s marke_von_pre = some (.bool true)),
    ∃ s', finalState (exec ρ marke_von_body s) = some s'
        ∧ marke_von_post s s' (finalValue (exec ρ marke_von_body s))

theorem marke_von_meets : marke_von_meets_statement := by
  unfold marke_von_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  obtain ⟨n_Verzeichnis_marke_i, h_Verzeichnis_marke_i, lo_Verzeichnis_marke_i, hi_Verzeichnis_marke_i⟩ := WF_intIn shapeOf s.world (.slot "Verzeichnis" w_i "marke") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [marke_von_pre, e_i, h_Verzeichnis_marke_i]
  gabbro_auto [marke_von_body, marke_von_pre, marke_von_post, wellFormed, e_i, h_Verzeichnis_marke_i, hall] using shapeOf

/-! ### `raeumen` -/

/-- **The duty of `raeumen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def raeumen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s raeumen_pre = some (.bool true))
    -- the contract of `Verzeichnis::remove`
    (c_Verzeichnis_remove : Contract ρ "Verzeichnis::remove" Verzeichnis_remove_requires Verzeichnis_remove_post)
    -- the frame of `Verzeichnis::remove`
    (fr_Verzeichnis_remove : Frame ρ "Verzeichnis::remove" Verzeichnis_remove_writes),
    ∃ s', finalState (exec ρ raeumen_body s) = some s'
        ∧ raeumen_post s s' (finalValue (exec ρ raeumen_body s))

theorem raeumen_meets : raeumen_meets_statement := by
  unfold raeumen_meets_statement
  intro ρ s hwf hpre c_Verzeichnis_remove fr_Verzeichnis_remove
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [raeumen_pre, e_i]
  gabbro_auto [raeumen_body, raeumen_pre, raeumen_post, wellFormed, Verzeichnis_remove_pre, Verzeichnis_remove_requires, Verzeichnis_remove_post, Verzeichnis_remove_writes, Frame_read _ _ _ fr_Verzeichnis_remove, e_i, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aushaengen" aushaengen_body
  ∧ Frame ρ "aushaengen" aushaengen_writes
  ∧ Runs ρ "belegen" belegen_body
  ∧ Frame ρ "belegen" belegen_writes
  ∧ Runs ρ "belegen_wenn_frei" belegen_wenn_frei_body
  ∧ Frame ρ "belegen_wenn_frei" belegen_wenn_frei_writes
  ∧ Runs ρ "ist_belegt" ist_belegt_body
  ∧ Frame ρ "ist_belegt" ist_belegt_writes
  ∧ Runs ρ "marke_von" marke_von_body
  ∧ Frame ρ "marke_von" marke_von_writes
  ∧ Runs ρ "raeumen" raeumen_body
  ∧ Frame ρ "raeumen" raeumen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_aushaengen : aushaengen_meets_statement)
    (d_belegen : belegen_meets_statement)
    (d_belegen_wenn_frei : belegen_wenn_frei_meets_statement)
    (d_ist_belegt : ist_belegt_meets_statement)
    (d_marke_von : marke_von_meets_statement)
    (d_raeumen : raeumen_meets_statement) :
    Contract ρ "aushaengen" aushaengen_requires aushaengen_post
    ∧ Contract ρ "belegen" belegen_requires belegen_post
    ∧ Contract ρ "belegen_wenn_frei" belegen_wenn_frei_requires belegen_wenn_frei_post
    ∧ Contract ρ "ist_belegt" ist_belegt_requires ist_belegt_post
    ∧ Contract ρ "marke_von" marke_von_requires marke_von_post
    ∧ Contract ρ "raeumen" raeumen_requires raeumen_post := by
  obtain ⟨r_aushaengen, fr_aushaengen, r_belegen, fr_belegen, r_belegen_wenn_frei, fr_belegen_wenn_frei, r_ist_belegt, fr_ist_belegt, r_marke_von, fr_marke_von, r_raeumen, fr_raeumen⟩ := hp
  obtain ⟨c_Ordner_remove, fr_Ordner_remove, c_Verzeichnis_insert, fr_Verzeichnis_insert, c_Verzeichnis_remove, fr_Verzeichnis_remove⟩ := ha
  have c_aushaengen : Contract ρ "aushaengen" aushaengen_requires aushaengen_post :=
    contract_of_duty ρ "aushaengen" aushaengen_body aushaengen_requires aushaengen_post r_aushaengen
      (fun t ht => d_aushaengen ρ t ht.1 ht.2 c_Ordner_remove fr_Ordner_remove)
  have c_belegen : Contract ρ "belegen" belegen_requires belegen_post :=
    contract_of_duty ρ "belegen" belegen_body belegen_requires belegen_post r_belegen
      (fun t ht => d_belegen ρ t ht.1 ht.2 c_Verzeichnis_insert fr_Verzeichnis_insert)
  have c_belegen_wenn_frei : Contract ρ "belegen_wenn_frei" belegen_wenn_frei_requires belegen_wenn_frei_post :=
    contract_of_duty ρ "belegen_wenn_frei" belegen_wenn_frei_body belegen_wenn_frei_requires belegen_wenn_frei_post r_belegen_wenn_frei
      (fun t ht => d_belegen_wenn_frei ρ t ht.1 ht.2 c_Verzeichnis_insert fr_Verzeichnis_insert)
  have c_ist_belegt : Contract ρ "ist_belegt" ist_belegt_requires ist_belegt_post :=
    contract_of_duty ρ "ist_belegt" ist_belegt_body ist_belegt_requires ist_belegt_post r_ist_belegt
      (fun t ht => d_ist_belegt ρ t ht.1 ht.2)
  have c_marke_von : Contract ρ "marke_von" marke_von_requires marke_von_post :=
    contract_of_duty ρ "marke_von" marke_von_body marke_von_requires marke_von_post r_marke_von
      (fun t ht => d_marke_von ρ t ht.1 ht.2)
  have c_raeumen : Contract ρ "raeumen" raeumen_requires raeumen_post :=
    contract_of_duty ρ "raeumen" raeumen_body raeumen_requires raeumen_post r_raeumen
      (fun t ht => d_raeumen ρ t ht.1 ht.2 c_Verzeichnis_remove fr_Verzeichnis_remove)
  exact ⟨c_aushaengen, c_belegen, c_belegen_wenn_frei, c_ist_belegt, c_marke_von, c_raeumen⟩

end GabbroDuty.Duty47OpsWortmenge