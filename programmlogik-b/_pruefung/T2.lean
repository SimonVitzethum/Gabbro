/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-c-namen-frei.gab  total 0  goals 0  refused 0
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
set_option maxHeartbeats 9000000

open Gabbro.Body

namespace GabbroDuty.DutyProbeCNamenFrei

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

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `close` -- a foreign body: its contract is an assumption. -/
def close_pre : Expr :=
  (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647)))))

def close_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ (-2147483648) ≤ x ∧ x ≤ 2147483647)

def close_writes : List String := ["ausgabe"]

def close_requires (t : State) : Prop := wellFormed t ∧ eval t close_pre = some (.bool true)

/-- `mmap` -- a foreign body: its contract is an assumption. -/
def mmap_pre : Expr :=
  (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "a")) (.bin .le (.name "a") (.lit (.int 18446744073709551615)))))

def mmap_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

def mmap_writes : List String := []

def mmap_requires (t : State) : Prop := wellFormed t ∧ eval t mmap_pre = some (.bool true)

/-- `nimm_wache` -- a foreign body: its contract is an assumption. -/
def nimm_wache_pre : Expr :=
  (.bin .and (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "a")) (.bin .le (.name "a") (.lit (.int 18446744073709551615))))) (.bin .and (.hasShape "w" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "w")) (.bin .le (.name "w") (.lit (.int 18446744073709551615))))))

def nimm_wache_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def nimm_wache_writes : List String := ["a"]

def nimm_wache_requires (t : State) : Prop := wellFormed t ∧ eval t nimm_wache_pre = some (.bool true)

/-- `plattenschritt` -- a foreign body: its contract is an assumption. -/
def plattenschritt_pre : Expr :=
  (.bin .and (.hasShape "fd" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "fd")) (.bin .le (.name "fd") (.lit (.int 18446744073709551615)))))

def plattenschritt_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

def plattenschritt_writes : List String := []

def plattenschritt_requires (t : State) : Prop := wellFormed t ∧ eval t plattenschritt_pre = some (.bool true)

/-- `pthread_self` -- a foreign body: its contract is an assumption. -/
def pthread_self_pre : Expr :=
  (.lit (.bool true))

def pthread_self_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

def pthread_self_writes : List String := []

def pthread_self_requires (t : State) : Prop := wellFormed t ∧ eval t pthread_self_pre = some (.bool true)

/-- `raise` -- a foreign body: its contract is an assumption. -/
def raise_pre : Expr :=
  (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647)))))

def raise_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ (-2147483648) ≤ x ∧ x ≤ 2147483647)

def raise_writes : List String := ["ausgabe"]

def raise_requires (t : State) : Prop := wellFormed t ∧ eval t raise_pre = some (.bool true)

/-- `shutdown` -- a foreign body: its contract is an assumption. -/
def shutdown_pre : Expr :=
  (.bin .and (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647))))) (.bin .and (.hasShape "b" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "b")) (.bin .le (.name "b") (.lit (.int 2147483647))))))

def shutdown_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ (-2147483648) ≤ x ∧ x ≤ 2147483647)

def shutdown_writes : List String := ["ausgabe"]

def shutdown_requires (t : State) : Prop := wellFormed t ∧ eval t shutdown_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "close" close_requires close_post
  ∧ Frame ρ "close" close_writes
  ∧ Contract ρ "mmap" mmap_requires mmap_post
  ∧ Frame ρ "mmap" mmap_writes
  ∧ Contract ρ "nimm_wache" nimm_wache_requires nimm_wache_post
  ∧ Frame ρ "nimm_wache" nimm_wache_writes
  ∧ Contract ρ "plattenschritt" plattenschritt_requires plattenschritt_post
  ∧ Frame ρ "plattenschritt" plattenschritt_writes
  ∧ Contract ρ "pthread_self" pthread_self_requires pthread_self_post
  ∧ Frame ρ "pthread_self" pthread_self_writes
  ∧ Contract ρ "raise" raise_requires raise_post
  ∧ Frame ρ "raise" raise_writes
  ∧ Contract ρ "shutdown" shutdown_requires shutdown_post
  ∧ Frame ρ "shutdown" shutdown_writes

/-! ## The routines: body and contract -/

/-! ### `haupt` -/

def haupt_body : List Stmt :=
  [(.bindCall "a" "plattenschritt" ["fd"] [(.name "fd")] (.bin .and (.hasShape "fd" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "fd")) (.bin .le (.name "fd") (.lit (.int 18446744073709551615)))))), (.call "nimm_wache" ["a", "w"] [(.name "fd"), (.name "a")] (.bin .and (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "a")) (.bin .le (.name "a") (.lit (.int 18446744073709551615))))) (.bin .and (.hasShape "w" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "w")) (.bin .le (.name "w") (.lit (.int 18446744073709551615))))))), (.bindCall "s" "close" ["a"] [(.lit (.int 1))] (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647)))))), (.bindCall "r" "raise" ["a"] [(.lit (.int 2))] (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647)))))), (.bindCall "t" "shutdown" ["a", "b"] [(.lit (.int 3)), (.lit (.int 0))] (.bin .and (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "a")) (.bin .le (.name "a") (.lit (.int 2147483647))))) (.bin .and (.hasShape "b" .int) (.bin .and (.bin .le (.lit (.int (-2147483648))) (.name "b")) (.bin .le (.name "b") (.lit (.int 2147483647))))))), (.bindCall "p" "pthread_self" [] [] (.lit (.bool true))), (.retCall "mmap" ["a"] [(.name "a")] (.bin .and (.hasShape "a" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "a")) (.bin .le (.name "a") (.lit (.int 18446744073709551615))))))]

/-- The precondition: the declared shapes and the `requires`. -/
def haupt_pre : Expr :=
  (.bin .and (.hasShape "fd" .int) (.bin .and (.bin .le (.lit (.int 0)) (.name "fd")) (.bin .le (.name "fd") (.lit (.int 18446744073709551615)))))

def haupt_writes : List String := ["fd", "ausgabe"]

/-- What a caller of `haupt` has to bring: a well-typed world and the precondition. -/
def haupt_requires (t : State) : Prop := wellFormed t ∧ eval t haupt_pre = some (.bool true)

/-- What `haupt` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def haupt_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 18446744073709551615)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `haupt` -/

/-- **The duty of `haupt`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def haupt_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s haupt_pre = some (.bool true))
    -- the contract of `close`
    (c_close : Contract ρ "close" close_requires close_post)
    -- the frame of `close`
    (fr_close : Frame ρ "close" close_writes)
    -- the contract of `mmap`
    (c_mmap : Contract ρ "mmap" mmap_requires mmap_post)
    -- the frame of `mmap`
    (fr_mmap : Frame ρ "mmap" mmap_writes)
    -- the contract of `nimm_wache`
    (c_nimm_wache : Contract ρ "nimm_wache" nimm_wache_requires nimm_wache_post)
    -- the frame of `nimm_wache`
    (fr_nimm_wache : Frame ρ "nimm_wache" nimm_wache_writes)
    -- the contract of `plattenschritt`
    (c_plattenschritt : Contract ρ "plattenschritt" plattenschritt_requires plattenschritt_post)
    -- the frame of `plattenschritt`
    (fr_plattenschritt : Frame ρ "plattenschritt" plattenschritt_writes)
    -- the contract of `pthread_self`
    (c_pthread_self : Contract ρ "pthread_self" pthread_self_requires pthread_self_post)
    -- the frame of `pthread_self`
    (fr_pthread_self : Frame ρ "pthread_self" pthread_self_writes)
    -- the contract of `raise`
    (c_raise : Contract ρ "raise" raise_requires raise_post)
    -- the frame of `raise`
    (fr_raise : Frame ρ "raise" raise_writes)
    -- the contract of `shutdown`
    (c_shutdown : Contract ρ "shutdown" shutdown_requires shutdown_post)
    -- the frame of `shutdown`
    (fr_shutdown : Frame ρ "shutdown" shutdown_writes),
    ∃ s', finalState (exec ρ haupt_body s) = some s'
        ∧ haupt_post s s' (finalValue (exec ρ haupt_body s))

theorem haupt_meets : haupt_meets_statement := by
  unfold haupt_meets_statement
  intro ρ s hwf hpre c_close fr_close c_mmap fr_mmap c_nimm_wache fr_nimm_wache c_plattenschritt fr_plattenschritt c_pthread_self fr_pthread_self c_raise fr_raise c_shutdown fr_shutdown
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_fd, e_fd, lo_fd, hi_fd⟩ := shape_int_in s "fd" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [haupt_pre, e_fd]
  gabbro_simp [haupt_body, haupt_pre, haupt_post, wellFormed, close_pre, close_requires, close_post, close_writes, Frame_read _ _ _ fr_close, mmap_pre, mmap_requires, mmap_post, mmap_writes, Frame_read _ _ _ fr_mmap, nimm_wache_pre, nimm_wache_requires, nimm_wache_post, nimm_wache_writes, Frame_read _ _ _ fr_nimm_wache, plattenschritt_pre, plattenschritt_requires, plattenschritt_post, plattenschritt_writes, Frame_read _ _ _ fr_plattenschritt, pthread_self_pre, pthread_self_requires, pthread_self_post, pthread_self_writes, Frame_read _ _ _ fr_pthread_self, raise_pre, raise_requires, raise_post, raise_writes, Frame_read _ _ _ fr_raise, shutdown_pre, shutdown_requires, shutdown_post, shutdown_writes, Frame_read _ _ _ fr_shutdown, e_fd, hall]
  gabbro_try 3000 (all_goals (try gabbro_cases 4 [haupt_body, haupt_pre, haupt_post, wellFormed, close_pre, close_requires, close_post, close_writes, Frame_read _ _ _ fr_close, mmap_pre, mmap_requires, mmap_post, mmap_writes, Frame_read _ _ _ fr_mmap, nimm_wache_pre, nimm_wache_requires, nimm_wache_post, nimm_wache_writes, Frame_read _ _ _ fr_nimm_wache, plattenschritt_pre, plattenschritt_requires, plattenschritt_post, plattenschritt_writes, Frame_read _ _ _ fr_plattenschritt, pthread_self_pre, pthread_self_requires, pthread_self_post, pthread_self_writes, Frame_read _ _ _ fr_pthread_self, raise_pre, raise_requires, raise_post, raise_writes, Frame_read _ _ _ fr_raise, shutdown_pre, shutdown_requires, shutdown_post, shutdown_writes, Frame_read _ _ _ fr_shutdown, e_fd, hall]))
  all_goals (gabbro_calls shapeOf [haupt_body, haupt_pre, haupt_post, wellFormed, close_pre, close_requires, close_post, close_writes, Frame_read _ _ _ fr_close, mmap_pre, mmap_requires, mmap_post, mmap_writes, Frame_read _ _ _ fr_mmap, nimm_wache_pre, nimm_wache_requires, nimm_wache_post, nimm_wache_writes, Frame_read _ _ _ fr_nimm_wache, plattenschritt_pre, plattenschritt_requires, plattenschritt_post, plattenschritt_writes, Frame_read _ _ _ fr_plattenschritt, pthread_self_pre, pthread_self_requires, pthread_self_post, pthread_self_writes, Frame_read _ _ _ fr_pthread_self, raise_pre, raise_requires, raise_post, raise_writes, Frame_read _ _ _ fr_raise, shutdown_pre, shutdown_requires, shutdown_post, shutdown_writes, Frame_read _ _ _ fr_shutdown, e_fd, hall])
  all_goals (gabbro_calls shapeOf [haupt_body, haupt_pre, haupt_post, wellFormed, close_pre, close_requires, close_post, close_writes, Frame_read _ _ _ fr_close, mmap_pre, mmap_requires, mmap_post, mmap_writes, Frame_read _ _ _ fr_mmap, nimm_wache_pre, nimm_wache_requires, nimm_wache_post, nimm_wache_writes, Frame_read _ _ _ fr_nimm_wache, plattenschritt_pre, plattenschritt_requires, plattenschritt_post, plattenschritt_writes, Frame_read _ _ _ fr_plattenschritt, pthread_self_pre, pthread_self_requires, pthread_self_post, pthread_self_writes, Frame_read _ _ _ fr_pthread_self, raise_pre, raise_requires, raise_post, raise_writes, Frame_read _ _ _ fr_raise, shutdown_pre, shutdown_requires, shutdown_post, shutdown_writes, Frame_read _ _ _ fr_shutdown, e_fd, hall])
  trace_state
  all_goals sorry
