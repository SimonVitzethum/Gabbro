/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/unseen-fat-reader2.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyUnseenFatReader2

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
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

/-! ### `cluster_ok` -/

def cluster_ok_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "cluster") (.lit (.int 4085))) (.bin .le (.name "cluster") (.lit (.int 65524)))) [] [(.ret (some (.lit (.bool false))))]), (.ret (some (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def cluster_ok_pre : Expr :=
  (.hasShape "cluster" (.intIn 0 4294967295))

def cluster_ok_writes : List String := []

/-- What a caller of `cluster_ok` has to bring: a well-typed world and the precondition. -/
def cluster_ok_requires (t : State) : Prop := wellFormed t ∧ eval t cluster_ok_pre = some (.bool true)

/-- What `cluster_ok` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def cluster_ok_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `end_lba` -/

def end_lba_body : List Stmt :=
  [(.bindName "a" (.name "fat_lba")), (.bindName "b" (.name "nfat")), (.bindName "c" (.name "fat_sec")), (.ret (some (.bin .add (.name "a") (.bin .mul (.name "b") (.name "c")))))]

/-- The precondition: the declared shapes and the `requires`. -/
def end_lba_pre : Expr :=
  (.bin .and (.hasShape "fat_lba" (.intIn 0 4294967295)) (.bin .and (.hasShape "nfat" (.intIn 1 4)) (.hasShape "fat_sec" (.intIn 0 4294967295))))

def end_lba_writes : List String := []

/-- What a caller of `end_lba` has to bring: a well-typed world and the precondition. -/
def end_lba_requires (t : State) : Prop := wellFormed t ∧ eval t end_lba_pre = some (.bool true)

/-- What `end_lba` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def end_lba_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ### `spc_ok` -/

def spc_ok_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "spc") (.lit (.int 1))) (.bin .le (.name "spc") (.lit (.int 128)))) [] [(.ret (some (.lit (.bool false))))]), (.ret (some (.bin .eq (.bin .band (.name "spc") (.bin .sub (.name "spc") (.lit (.int 1)))) (.lit (.int 0)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def spc_ok_pre : Expr :=
  (.hasShape "spc" (.intIn 1 128))

def spc_ok_writes : List String := []

/-- What a caller of `spc_ok` has to bring: a well-typed world and the precondition. -/
def spc_ok_requires (t : State) : Prop := wellFormed t ∧ eval t spc_ok_pre = some (.bool true)

/-- What `spc_ok` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def spc_ok_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `cluster_ok` -/

/-- **The duty of `cluster_ok`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def cluster_ok_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s cluster_ok_pre = some (.bool true)),
    ∃ s', finalState (exec ρ cluster_ok_body s) = some s'
        ∧ cluster_ok_post s s' (finalValue (exec ρ cluster_ok_body s))

theorem cluster_ok_meets : cluster_ok_meets_statement := by
  unfold cluster_ok_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_cluster, e_cluster, lo_cluster, hi_cluster⟩ := shape_intIn s "cluster" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [cluster_ok_pre, e_cluster]
  gabbro_auto [cluster_ok_body, cluster_ok_pre, cluster_ok_post, wellFormed, e_cluster, hall] using shapeOf

/-! ### `end_lba` -/

/-- **The duty of `end_lba`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def end_lba_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s end_lba_pre = some (.bool true)),
    ∃ s', finalState (exec ρ end_lba_body s) = some s'
        ∧ end_lba_post s s' (finalValue (exec ρ end_lba_body s))

theorem end_lba_meets : end_lba_meets_statement := by
  unfold end_lba_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_fat_lba, e_fat_lba, lo_fat_lba, hi_fat_lba⟩ := shape_intIn s "fat_lba" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_nfat, e_nfat, lo_nfat, hi_nfat⟩ := shape_intIn s "nfat" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_fat_sec, e_fat_sec, lo_fat_sec, hi_fat_sec⟩ := shape_intIn s "fat_sec" _ _ (and_right _ _ _ (and_right _ _ _ hpre))
  have hall := hpre
  gabbro_simp_at hall [end_lba_pre, e_fat_lba, e_nfat, e_fat_sec]
  gabbro_auto [end_lba_body, end_lba_pre, end_lba_post, wellFormed, e_fat_lba, e_nfat, e_fat_sec, hall] using shapeOf

/-! ### `spc_ok` -/

/-- **The duty of `spc_ok`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def spc_ok_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s spc_ok_pre = some (.bool true)),
    ∃ s', finalState (exec ρ spc_ok_body s) = some s'
        ∧ spc_ok_post s s' (finalValue (exec ρ spc_ok_body s))

theorem spc_ok_meets : spc_ok_meets_statement := by
  unfold spc_ok_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_spc, e_spc, lo_spc, hi_spc⟩ := shape_intIn s "spc" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [spc_ok_pre, e_spc]
  gabbro_auto [spc_ok_body, spc_ok_pre, spc_ok_post, wellFormed, e_spc, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "cluster_ok" cluster_ok_body
  ∧ Frame ρ "cluster_ok" cluster_ok_writes
  ∧ Runs ρ "end_lba" end_lba_body
  ∧ Frame ρ "end_lba" end_lba_writes
  ∧ Runs ρ "spc_ok" spc_ok_body
  ∧ Frame ρ "spc_ok" spc_ok_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_cluster_ok : cluster_ok_meets_statement)
    (d_end_lba : end_lba_meets_statement)
    (d_spc_ok : spc_ok_meets_statement) :
    Contract ρ "cluster_ok" cluster_ok_requires cluster_ok_post
    ∧ Contract ρ "end_lba" end_lba_requires end_lba_post
    ∧ Contract ρ "spc_ok" spc_ok_requires spc_ok_post := by
  obtain ⟨r_cluster_ok, fr_cluster_ok, r_end_lba, fr_end_lba, r_spc_ok, fr_spc_ok⟩ := hp
  have c_cluster_ok : Contract ρ "cluster_ok" cluster_ok_requires cluster_ok_post :=
    contract_of_duty ρ "cluster_ok" cluster_ok_body cluster_ok_requires cluster_ok_post r_cluster_ok
      (fun t ht => d_cluster_ok ρ t ht.1 ht.2)
  have c_end_lba : Contract ρ "end_lba" end_lba_requires end_lba_post :=
    contract_of_duty ρ "end_lba" end_lba_body end_lba_requires end_lba_post r_end_lba
      (fun t ht => d_end_lba ρ t ht.1 ht.2)
  have c_spc_ok : Contract ρ "spc_ok" spc_ok_requires spc_ok_post :=
    contract_of_duty ρ "spc_ok" spc_ok_body spc_ok_requires spc_ok_post r_spc_ok
      (fun t ht => d_spc_ok ρ t ht.1 ht.2)
  exact ⟨c_cluster_ok, c_end_lba, c_spc_ok⟩

end GabbroDuty.DutyUnseenFatReader2
