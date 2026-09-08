/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/70-kernel-namen.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty70KernelNamen

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  vertragswoerter :: ensures #1  --  carried by `vertragswoerter_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "entry" "node" => some (.intIn 0 4294967295)
  | .field "entry" "next" => some (.intIn 0 4294967295)
  | .field "entry" "index" => some (.intIn 0 4294967295)
  | .field "entry" "state" => some (.intIn 0 4294967295)
  | .field "entry" "stack" => some (.intIn 0 4294967295)
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

/-! ### `beides` -/

def beides_body : List Stmt :=
  [(.bindName "next" (.name "a")), (.loop "beides#1" (.bin .and (.hasShape "a" (.intIn 0 10)) (.hasShape "next" (.intIn 0 10))) [(.bindName "next" (.name "a")), (.bindName "next" (.bin .add (.name "next") (.lit (.int 0)))), (.ite (.bin .eq (.name "next") (.lit (.int 0))) [.leave] []), .exit])]

/-- The precondition: the declared shapes and the `requires`. -/
def beides_pre : Expr :=
  (.hasShape "a" (.intIn 0 10))

def beides_writes : List String := []

/-- What a caller of `beides` has to bring: a well-typed world and the precondition. -/
def beides_requires (t : State) : Prop := wellFormed t ∧ eval t beides_pre = some (.bool true)

/-- What `beides` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def beides_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `haeufigste` -/

def haeufigste_body : List Stmt :=
  [(.bindName "count" (.name "a")), (.bindName "cpu" (.name "count")), (.bindName "order" (.name "cpu")), (.bindName "type" (.name "order")), (.bindName "ptr" (.name "type")), (.bindName "table" (.name "ptr")), (.bindName "lock" (.name "table")), (.bindName "class" (.name "lock")), (.bindName "walk" (.name "class")), (.ret (some (.name "walk")))]

/-- The precondition: the declared shapes and the `requires`. -/
def haeufigste_pre : Expr :=
  (.hasShape "a" (.intIn 0 10))

def haeufigste_writes : List String := []

/-- What a caller of `haeufigste` has to bring: a well-typed world and the precondition. -/
def haeufigste_requires (t : State) : Prop := wellFormed t ∧ eval t haeufigste_pre = some (.bool true)

/-- What `haeufigste` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def haeufigste_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 10)

/-! ### `k3_namen` -/

def k3_namen_body : List Stmt :=
  [(.ret (some (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.name "node") (.name "old")) (.name "next")) (.name "progress")) (.name "release")) (.name "stack")) (.name "index")) (.name "to"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def k3_namen_pre : Expr :=
  (.bin .and (.hasShape "node" (.intIn 0 10)) (.bin .and (.hasShape "old" (.intIn 0 10)) (.bin .and (.hasShape "next" (.intIn 0 10)) (.bin .and (.hasShape "progress" (.intIn 0 10)) (.bin .and (.hasShape "release" (.intIn 0 10)) (.bin .and (.hasShape "stack" (.intIn 0 10)) (.bin .and (.hasShape "index" (.intIn 0 10)) (.hasShape "to" (.intIn 0 10)))))))))

def k3_namen_writes : List String := []

/-- What a caller of `k3_namen` has to bring: a well-typed world and the precondition. -/
def k3_namen_requires (t : State) : Prop := wellFormed t ∧ eval t k3_namen_pre = some (.bool true)

/-- What `k3_namen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def k3_namen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 80)

/-! ### `vertragswoerter` -/

def vertragswoerter_body : List Stmt :=
  [(.bindName "old" (.name "a")), (.bindName "result" (.name "old")), (.ret (some (.name "result")))]

/-- The precondition: the declared shapes and the `requires`. -/
def vertragswoerter_pre : Expr :=
  (.hasShape "a" (.intIn 0 10))

def vertragswoerter_writes : List String := []

/-- What a caller of `vertragswoerter` has to bring: a well-typed world and the precondition. -/
def vertragswoerter_requires (t : State) : Prop := wellFormed t ∧ eval t vertragswoerter_pre = some (.bool true)

/-- What `vertragswoerter` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def vertragswoerter_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 10)
  ∧ -- ensures #1
  (∃ v, r = some v ∧ eval { world := s'.world, local' := (bindLocal s.local' "result" v) } (.bin .eq (.name "result") (.name "a")) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `beides` -/

/-- Loop `beides#1` of `beides`: its body and its invariant (with the shapes of the locals in scope). -/
def beides_loop_1_inv : Expr :=
  (.bin .and (.hasShape "a" (.intIn 0 10)) (.hasShape "next" (.intIn 0 10)))

def beides_loop_1_body : List Stmt :=
  [(.bindName "next" (.name "a")), (.bindName "next" (.bin .add (.name "next") (.lit (.int 0)))), (.ite (.bin .eq (.name "next") (.lit (.int 0))) [.leave] []), .exit]

/-- **The loop rule of `beides#1`, as a statement over one pass.** -/
def beides_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t beides_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ beides_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' beides_loop_1_inv = some (.bool true)

theorem beides_loop_1_keeps : beides_loop_1_keeps_statement := by
  unfold beides_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn t "a" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_next, e_next, lo_next, hi_next⟩ := shape_intIn t "next" _ _ (and_right _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [beides_loop_1_inv, e_a, e_next]
  gabbro_auto [beides_loop_1_body, beides_loop_1_inv, wellFormed, e_a, e_next, hall] using shapeOf

/-- **The duty of `beides`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def beides_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s beides_pre = some (.bool true))
    -- the rule of loop `beides#1`
    (l_beides_loop_1 : LoopRule ρ "beides#1" wellFormed beides_loop_1_inv),
    ∃ s', finalState (exec ρ beides_body s) = some s'
        ∧ beides_post s s' (finalValue (exec ρ beides_body s))

theorem beides_meets : beides_meets_statement := by
  unfold beides_meets_statement
  intro ρ s hwf hpre l_beides_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [beides_pre, e_a]
  gabbro_auto [beides_body, beides_pre, beides_post, wellFormed, beides_loop_1_inv, e_a, hall] using shapeOf

/-! ### `haeufigste` -/

/-- **The duty of `haeufigste`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def haeufigste_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s haeufigste_pre = some (.bool true)),
    ∃ s', finalState (exec ρ haeufigste_body s) = some s'
        ∧ haeufigste_post s s' (finalValue (exec ρ haeufigste_body s))

theorem haeufigste_meets : haeufigste_meets_statement := by
  unfold haeufigste_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [haeufigste_pre, e_a]
  gabbro_auto [haeufigste_body, haeufigste_pre, haeufigste_post, wellFormed, e_a, hall] using shapeOf

/-! ### `k3_namen` -/

/-- **The duty of `k3_namen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def k3_namen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s k3_namen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ k3_namen_body s) = some s'
        ∧ k3_namen_post s s' (finalValue (exec ρ k3_namen_body s))

theorem k3_namen_meets : k3_namen_meets_statement := by
  unfold k3_namen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_node, e_node, lo_node, hi_node⟩ := shape_intIn s "node" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_old, e_old, lo_old, hi_old⟩ := shape_intIn s "old" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_next, e_next, lo_next, hi_next⟩ := shape_intIn s "next" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨w_progress, e_progress, lo_progress, hi_progress⟩ := shape_intIn s "progress" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))
  obtain ⟨w_release, e_release, lo_release, hi_release⟩ := shape_intIn s "release" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))
  obtain ⟨w_stack, e_stack, lo_stack, hi_stack⟩ := shape_intIn s "stack" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))))
  obtain ⟨w_index, e_index, lo_index, hi_index⟩ := shape_intIn s "index" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))))
  obtain ⟨w_to, e_to, lo_to, hi_to⟩ := shape_intIn s "to" _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))))
  have hall := hpre
  gabbro_simp_at hall [k3_namen_pre, e_node, e_old, e_next, e_progress, e_release, e_stack, e_index, e_to]
  gabbro_auto [k3_namen_body, k3_namen_pre, k3_namen_post, wellFormed, e_node, e_old, e_next, e_progress, e_release, e_stack, e_index, e_to, hall] using shapeOf

/-! ### `vertragswoerter` -/

/-- **The duty of `vertragswoerter`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def vertragswoerter_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s vertragswoerter_pre = some (.bool true)),
    ∃ s', finalState (exec ρ vertragswoerter_body s) = some s'
        ∧ vertragswoerter_post s s' (finalValue (exec ρ vertragswoerter_body s))

theorem vertragswoerter_meets : vertragswoerter_meets_statement := by
  unfold vertragswoerter_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [vertragswoerter_pre, e_a]
  gabbro_auto [vertragswoerter_body, vertragswoerter_pre, vertragswoerter_post, wellFormed, e_a, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "beides" beides_body
  ∧ Frame ρ "beides" beides_writes
  ∧ RunsLoop ρ "beides#1" beides_loop_1_body "#pass"
  ∧ Runs ρ "haeufigste" haeufigste_body
  ∧ Frame ρ "haeufigste" haeufigste_writes
  ∧ Runs ρ "k3_namen" k3_namen_body
  ∧ Frame ρ "k3_namen" k3_namen_writes
  ∧ Runs ρ "vertragswoerter" vertragswoerter_body
  ∧ Frame ρ "vertragswoerter" vertragswoerter_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_beides_loop_1 : beides_loop_1_keeps_statement)
    (d_beides : beides_meets_statement)
    (d_haeufigste : haeufigste_meets_statement)
    (d_k3_namen : k3_namen_meets_statement)
    (d_vertragswoerter : vertragswoerter_meets_statement) :
    LoopRule ρ "beides#1" wellFormed beides_loop_1_inv
    ∧ Contract ρ "beides" beides_requires beides_post
    ∧ Contract ρ "haeufigste" haeufigste_requires haeufigste_post
    ∧ Contract ρ "k3_namen" k3_namen_requires k3_namen_post
    ∧ Contract ρ "vertragswoerter" vertragswoerter_requires vertragswoerter_post := by
  obtain ⟨r_beides, fr_beides, rl_beides_loop_1, r_haeufigste, fr_haeufigste, r_k3_namen, fr_k3_namen, r_vertragswoerter, fr_vertragswoerter⟩ := hp
  have l_beides_loop_1 : LoopRule ρ "beides#1" wellFormed beides_loop_1_inv :=
    looprule_of_body ρ "beides#1" wellFormed beides_loop_1_inv beides_loop_1_body "#pass" rl_beides_loop_1
      (fun t k hw hi => d_beides_loop_1 ρ t k hw hi)
  have c_beides : Contract ρ "beides" beides_requires beides_post :=
    contract_of_duty ρ "beides" beides_body beides_requires beides_post r_beides
      (fun t ht => d_beides ρ t ht.1 ht.2 l_beides_loop_1)
  have c_haeufigste : Contract ρ "haeufigste" haeufigste_requires haeufigste_post :=
    contract_of_duty ρ "haeufigste" haeufigste_body haeufigste_requires haeufigste_post r_haeufigste
      (fun t ht => d_haeufigste ρ t ht.1 ht.2)
  have c_k3_namen : Contract ρ "k3_namen" k3_namen_requires k3_namen_post :=
    contract_of_duty ρ "k3_namen" k3_namen_body k3_namen_requires k3_namen_post r_k3_namen
      (fun t ht => d_k3_namen ρ t ht.1 ht.2)
  have c_vertragswoerter : Contract ρ "vertragswoerter" vertragswoerter_requires vertragswoerter_post :=
    contract_of_duty ρ "vertragswoerter" vertragswoerter_body vertragswoerter_requires vertragswoerter_post r_vertragswoerter
      (fun t ht => d_vertragswoerter ρ t ht.1 ht.2)
  exact ⟨l_beides_loop_1, c_beides, c_haeufigste, c_k3_namen, c_vertragswoerter⟩

end GabbroDuty.Duty70KernelNamen
