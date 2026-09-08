/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-ipc-fastpath-durchgestochen.gab  total 1  goals 0  refused 1
        @assumed 0  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 1 are refused forms

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

namespace GabbroDuty.DutyProbeIpcFastpathDurchgestochen

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  slot-record-array (1): refused -- an array inside a record held in a table SLOT (`e.slots[i].q.buf[j]`) -- one object per record TYPE here, so every slot's copy would be the SAME place; lift the array into a table
    duty_1  E  call :: antwortpflicht_paarig
      (inherited: this clause HAS a term; the body or the `requires` of `call` has none)

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  E  call :: antwortpflicht_paarig  --  refused (slot-record-array)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Endpoint" _ "used" => some .bool
  | .slot "Endpoint" _ "quiescing" => some .bool
  | .slot "Endpoint" _ "caller" => some .opt
  | .slot "Endpoint" _ "reply_owner" => some .opt
  | .slot "Frame.msg" _ "elem" => some (.intIn 0 4294967295)
  | .slot "Frame.regs" _ "elem" => some (.intIn 0 18446744073709551615)
  | .slot "Rahmen" _ "m0" => some (.intIn 0 4294967295)
  | .slot "Rahmen" _ "m1" => some (.intIn 0 4294967295)
  | .slot "Rahmen" _ "m2" => some (.intIn 0 4294967295)
  | .slot "Rahmen" _ "m3" => some (.intIn 0 4294967295)
  | .slot "Rahmen" _ "m4" => some (.intIn 0 4294967295)
  | .slot "Rahmen" _ "m5" => some (.intIn 0 4294967295)
  | .slot "Threads" _ "da" => some .bool
  | .slot "TidQueue.buf" _ "elem" => some (.intIn 0 4294967295)
  | .field "TidQueue" "head" => some (.intIn 0 31)
  | .field "TidQueue" "tail" => some (.intIn 0 31)
  | .field "TidQueue" "count" => some (.intIn 0 32)
  | .global "picked" => some .opt
  | .global "gesehen" => some (.intIn 0 4294967295)
  | .global "e_schutz" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `antwortpflicht_paarig` over `Endpoint`. -/
def inv_antwortpflicht_paarig : Expr :=
  (.forallSlots "e" 64 (.bin .eq (.bin .eq (.place "Endpoint" (.name "e") "caller") (.lit .absent)) (.bin .eq (.place "Endpoint" (.name "e") "reply_owner") (.lit .absent))))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `current_id` -- a foreign body: its contract is an assumption. -/
def current_id_pre : Expr :=
  (.hasShape "core" (.intIn 0 63))

def current_id_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 1023)

def current_id_writes : List String := []

def current_id_requires (t : State) : Prop := wellFormed t ∧ eval t current_id_pre = some (.bool true)

/-- `melde_grund` -- a foreign body: its contract is an assumption. -/
def melde_grund_pre : Expr :=
  (.lit (.bool true))

def melde_grund_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

def melde_grund_writes : List String := []

def melde_grund_requires (t : State) : Prop := wellFormed t ∧ eval t melde_grund_pre = some (.bool true)

/-- `set_reg` -- a foreign body: its contract is an assumption. -/
def set_reg_pre : Expr :=
  (.bin .and (.hasShape "r" (.intIn 0 4294967295)) (.hasShape "wz" (.intIn 0 4294967295)))

def set_reg_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def set_reg_writes : List String := ["Frame.msg", "Frame.regs", "Frame"]

def set_reg_requires (t : State) : Prop := wellFormed t ∧ eval t set_reg_pre = some (.bool true)

/-- `wirklich_einreihen` -- a foreign body: its contract is an assumption. -/
def wirklich_einreihen_pre : Expr :=
  (.hasShape "t" (.intIn 0 4294967295))

def wirklich_einreihen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

def wirklich_einreihen_writes : List String := []

def wirklich_einreihen_requires (t : State) : Prop := wellFormed t ∧ eval t wirklich_einreihen_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_antwortpflicht_paarig = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "current_id" current_id_requires current_id_post
  ∧ Frame ρ "current_id" current_id_writes
  ∧ Contract ρ "melde_grund" melde_grund_requires melde_grund_post
  ∧ Frame ρ "melde_grund" melde_grund_writes
  ∧ Contract ρ "set_reg" set_reg_requires set_reg_post
  ∧ Frame ρ "set_reg" set_reg_writes
  ∧ Contract ρ "wirklich_einreihen" wirklich_einreihen_requires wirklich_einreihen_post
  ∧ Frame ρ "wirklich_einreihen" wirklich_einreihen_writes

/-! ## The routines: body and contract -/

/-! ### `Rahmen_schreiben` -/

def Rahmen_schreiben_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.name "s") (.lit (.int 0))) (.bin .lt (.name "s") (.lit (.int 1024)))) [] [(.ret (some (.lit (.int 999))))]), (.assign "Rahmen" (.name "s") "m0" (.name "a")), (.assign "Rahmen" (.name "s") "m1" (.name "b")), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def Rahmen_schreiben_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 4294967295)) (.bin .and (.hasShape "a" (.intIn 0 4294967295)) (.hasShape "b" (.intIn 0 4294967295))))

def Rahmen_schreiben_writes : List String := ["Rahmen"]

/-- What a caller of `Rahmen_schreiben` has to bring: a well-typed world and the precondition. -/
def Rahmen_schreiben_requires (t : State) : Prop := wellFormed t ∧ eval t Rahmen_schreiben_pre = some (.bool true)

/-- What `Rahmen_schreiben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def Rahmen_schreiben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `call` -/

-- REFUSED  call  (slot-record-array): an array inside a record held in a table SLOT (`e.slots[i].q.buf[j]`) -- one object per record TYPE here, so every slot's copy would be the SAME place; lift the array into a table
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def call_pre : Expr :=
  (.bin .and (.hasShape "core" (.intIn 0 63)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Endpoint" (.name "core") "used") (.forallSlots "e" 64 (.bin .eq (.bin .eq (.place "Endpoint" (.name "e") "caller") (.lit .absent)) (.bin .eq (.place "Endpoint" (.name "e") "reply_owner") (.lit .absent)))))))

/-- `antwortpflicht_paarig`, as `call` keeps it. -/
def call_inv_antwortpflicht_paarig : Expr :=
  (.forallSlots "e" 64 (.bin .eq (.bin .eq (.place "Endpoint" (.name "e") "caller") (.lit .absent)) (.bin .eq (.place "Endpoint" (.name "e") "reply_owner") (.lit .absent))))

def call_writes : List String := ["Endpoint", "frames", "Rahmen", "picked", "gesehen"]

/-- What a caller of `call` has to bring: a well-typed world and the precondition. -/
def call_requires (t : State) : Prop := wellFormed t ∧ eval t call_pre = some (.bool true)

/-- What `call` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def call_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)
  ∧ eval s' call_inv_antwortpflicht_paarig = some (.bool true)

/-! ### `enqueue` -/

def enqueue_body : List Stmt :=
  [(.bindCall "#m1" "voll" ["q"] [(.name "q")] (.lit (.bool true))), (.ite (.name "#m1") [(.ret (some (.lit (.reason "Voll"))))] []), (.retCall "wirklich_einreihen" ["q", "t"] [(.name "q"), (.name "t")] (.hasShape "t" (.intIn 0 4294967295)))]

/-- The precondition: the declared shapes and the `requires`. -/
def enqueue_pre : Expr :=
  (.hasShape "t" (.intIn 0 4294967295))

def enqueue_writes : List String := []

/-- What a caller of `enqueue` has to bring: a well-typed world and the precondition. -/
def enqueue_requires (t : State) : Prop := wellFormed t ∧ eval t enqueue_pre = some (.bool true)

/-- What `enqueue` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def enqueue_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295) ∨ ∃ e, r = some (.reason e))

/-! ### `voll` -/

def voll_body : List Stmt :=
  [(.ret (some (.bin .ge (.fieldOf "TidQueue" "count") (.lit (.int 32)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def voll_pre : Expr :=
  (.lit (.bool true))

def voll_writes : List String := []

/-- What a caller of `voll` has to bring: a well-typed world and the precondition. -/
def voll_requires (t : State) : Prop := wellFormed t ∧ eval t voll_pre = some (.bool true)

/-- What `voll` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def voll_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `Rahmen_schreiben` -/

/-- **The duty of `Rahmen_schreiben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def Rahmen_schreiben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s Rahmen_schreiben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ Rahmen_schreiben_body s) = some s'
        ∧ Rahmen_schreiben_post s s' (finalValue (exec ρ Rahmen_schreiben_body s))

theorem Rahmen_schreiben_meets : Rahmen_schreiben_meets_statement := by
  unfold Rahmen_schreiben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_right _ _ _ (and_right _ _ _ hpre))
  have hall := hpre
  gabbro_simp_at hall [Rahmen_schreiben_pre, e_s, e_a, e_b]
  gabbro_auto [Rahmen_schreiben_body, Rahmen_schreiben_pre, Rahmen_schreiben_post, wellFormed, e_s, e_a, e_b, hall] using shapeOf

/-! ### `enqueue` -/

/-- **The duty of `enqueue`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def enqueue_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s enqueue_pre = some (.bool true))
    -- the contract of `voll`
    (c_voll : Contract ρ "voll" voll_requires voll_post)
    -- the frame of `voll`
    (fr_voll : Frame ρ "voll" voll_writes)
    -- the contract of `wirklich_einreihen`
    (c_wirklich_einreihen : Contract ρ "wirklich_einreihen" wirklich_einreihen_requires wirklich_einreihen_post)
    -- the frame of `wirklich_einreihen`
    (fr_wirklich_einreihen : Frame ρ "wirklich_einreihen" wirklich_einreihen_writes),
    ∃ s', finalState (exec ρ enqueue_body s) = some s'
        ∧ enqueue_post s s' (finalValue (exec ρ enqueue_body s))

theorem enqueue_meets : enqueue_meets_statement := by
  unfold enqueue_meets_statement
  intro ρ s hwf hpre c_voll fr_voll c_wirklich_einreihen fr_wirklich_einreihen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [enqueue_pre, e_t]
  gabbro_auto [enqueue_body, enqueue_pre, enqueue_post, wellFormed, voll_pre, voll_requires, voll_post, voll_writes, Frame_read _ _ _ fr_voll, wirklich_einreihen_pre, wirklich_einreihen_requires, wirklich_einreihen_post, wirklich_einreihen_writes, Frame_read _ _ _ fr_wirklich_einreihen, e_t, hall] using shapeOf

/-! ### `voll` -/

/-- **The duty of `voll`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def voll_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s voll_pre = some (.bool true)),
    ∃ s', finalState (exec ρ voll_body s) = some s'
        ∧ voll_post s s' (finalValue (exec ρ voll_body s))

theorem voll_meets : voll_meets_statement := by
  unfold voll_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_TidQueue_count, h_TidQueue_count, lo_TidQueue_count, hi_TidQueue_count⟩ := WF_intIn shapeOf s.world (.field "TidQueue" "count") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [voll_pre, h_TidQueue_count]
  gabbro_auto [voll_body, voll_pre, voll_post, wellFormed, h_TidQueue_count, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "Rahmen_schreiben" Rahmen_schreiben_body
  ∧ Frame ρ "Rahmen_schreiben" Rahmen_schreiben_writes
  ∧ Runs ρ "enqueue" enqueue_body
  ∧ Frame ρ "enqueue" enqueue_writes
  ∧ Runs ρ "voll" voll_body
  ∧ Frame ρ "voll" voll_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_Rahmen_schreiben : Rahmen_schreiben_meets_statement)
    (d_voll : voll_meets_statement)
    (d_enqueue : enqueue_meets_statement) :
    Contract ρ "Rahmen_schreiben" Rahmen_schreiben_requires Rahmen_schreiben_post
    ∧ Contract ρ "voll" voll_requires voll_post
    ∧ Contract ρ "enqueue" enqueue_requires enqueue_post := by
  obtain ⟨r_Rahmen_schreiben, fr_Rahmen_schreiben, r_enqueue, fr_enqueue, r_voll, fr_voll⟩ := hp
  obtain ⟨c_current_id, fr_current_id, c_melde_grund, fr_melde_grund, c_set_reg, fr_set_reg, c_wirklich_einreihen, fr_wirklich_einreihen⟩ := ha
  have c_Rahmen_schreiben : Contract ρ "Rahmen_schreiben" Rahmen_schreiben_requires Rahmen_schreiben_post :=
    contract_of_duty ρ "Rahmen_schreiben" Rahmen_schreiben_body Rahmen_schreiben_requires Rahmen_schreiben_post r_Rahmen_schreiben
      (fun t ht => d_Rahmen_schreiben ρ t ht.1 ht.2)
  have c_voll : Contract ρ "voll" voll_requires voll_post :=
    contract_of_duty ρ "voll" voll_body voll_requires voll_post r_voll
      (fun t ht => d_voll ρ t ht.1 ht.2)
  have c_enqueue : Contract ρ "enqueue" enqueue_requires enqueue_post :=
    contract_of_duty ρ "enqueue" enqueue_body enqueue_requires enqueue_post r_enqueue
      (fun t ht => d_enqueue ρ t ht.1 ht.2 c_voll fr_voll c_wirklich_einreihen fr_wirklich_einreihen)
  exact ⟨c_Rahmen_schreiben, c_voll, c_enqueue⟩

end GabbroDuty.DutyProbeIpcFastpathDurchgestochen