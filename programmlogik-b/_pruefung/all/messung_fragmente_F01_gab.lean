/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/fragmente/F01.gab  total 17  goals 17  refused 0
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

namespace GabbroDuty.DutyF01

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  CapSpace :: invariant wurzel_ohne_vorgaenger  --  carried by `delete_leaf_meets`, `release_slot_meets`, `revoke_meets`, `unlink_meets`
  duty_2  E  unlink :: cdt_wohlgeformt  --  carried by `unlink_meets`
  duty_3  N  unlink :: ensures #1  --  carried by `unlink_meets`
  duty_4  N  unlink :: ensures #2  --  carried by `unlink_meets`
  duty_5  N  unlink :: ensures #3  --  carried by `unlink_meets`
  duty_6  N  release_slot :: ensures #1  --  carried by `release_slot_meets`
  duty_7  E  delete_leaf :: cdt_wohlgeformt  --  carried by `delete_leaf_meets`
  duty_8  N  delete_leaf :: ensures #1  --  carried by `delete_leaf_meets`
  duty_9  N  delete_leaf :: ensures #2  --  carried by `delete_leaf_meets`
  duty_10  E  revoke :: cdt_wohlgeformt  --  carried by `revoke_meets`
  duty_11  V  delete_leaf :: unlink requires #1  --  carried by `delete_leaf_meets`
  duty_12  V  delete_leaf :: unlink requires #2  --  carried by `delete_leaf_meets`
  duty_13  V  delete_leaf :: release_slot requires #1  --  carried by `delete_leaf_meets`
  duty_14  V  revoke :: delete_leaf requires #1  --  carried by `revoke_meets`
  duty_15  V  revoke :: delete_leaf requires #2  --  carried by `revoke_meets`
  duty_16  V  revoke :: delete_leaf requires #3  --  carried by `revoke_meets`
  duty_17  V  revoke :: delete_leaf requires #4  --  carried by `revoke_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "CapObjects" _ "used" => some .bool
  | .slot "CapObjects" _ "gen" => some .int
  | .slot "CapObjects" _ "kind" => some (.sum [("Memory", (some (some (0, 18446744073709551615)))), ("Endpoint", (some (some (0, 4294967295)))), ("Notification", (some (some (0, 4294967295)))), ("Tcb", (some (some (0, 4294967295)))), ("SchedContext", (some none)), ("Reply", (some none)), ("PdControl", (some (some (0, 65535)))), ("Loader", (some (some (0, 4294967295)))), ("Mmio", (some none)), ("Irq", (some (some (0, 4294967295)))), ("Dma", (some none)), ("SyscallHandler", (some none)), ("FaultHandler", (some none))])
  | .slot "CapObjects" _ "refcount" => some (.intIn 0 80255)
  | .slot "CapSpace" _ "used" => some .bool
  | .slot "CapSpace" _ "gen" => some .int
  | .slot "CapSpace" _ "object" => some .int
  | .slot "CapSpace" _ "rights" => some (.intIn 0 4294967295)
  | .slot "CapSpace" _ "badge" => some (.intIn 0 18446744073709551615)
  | .slot "CapSpace" _ "parent" => some .opt
  | .slot "CapSpace" _ "first_child" => some .opt
  | .slot "CapSpace" _ "next_sibling" => some .opt
  | .slot "CapSpace" _ "prev_sibling" => some .opt
  | .field "DmaRef" "phys" => some (.intIn 0 18446744073709551615)
  | .field "DmaRef" "len" => some (.intIn 0 18446744073709551615)
  | .field "DmaRef" "dir" => some (.intIn 0 255)
  | .field "DmaRef" "coherence" => some (.intIn 0 255)
  | .field "HandlerRef" "ep" => some (.intIn 0 4294967295)
  | .field "HandlerRef" "pd" => some (.intIn 0 65535)
  | .field "HandlerRef" "sidecar" => some (.intIn 0 18446744073709551615)
  | .field "HandlerRef" "len" => some (.intIn 0 18446744073709551615)
  | .field "MmioRange" "phys" => some (.intIn 0 18446744073709551615)
  | .field "MmioRange" "len" => some (.intIn 0 18446744073709551615)
  | .field "ReplyRef" "ep" => some (.intIn 0 4294967295)
  | .field "ReplyRef" "caller" => some (.intIn 0 4294967295)
  | .field "SchedParams" "budget" => some (.intIn 0 4294967295)
  | .field "SchedParams" "period" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `wurzel_ohne_vorgaenger` over `CapSpace`. -/
def inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `free_region` -- a foreign body: its contract is an assumption. -/
def free_region_pre : Expr :=
  (.hasShape "m" (.intIn 0 18446744073709551615))

def free_region_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def free_region_writes : List String := ["a"]

def free_region_requires (t : State) : Prop := wellFormed t ∧ eval t free_region_pre = some (.bool true)

/-- `push_dma` -- a foreign body: its contract is an assumption. -/
def push_dma_pre : Expr :=
  (.lit (.bool true))

def push_dma_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def push_dma_writes : List String := ["rf"]

def push_dma_requires (t : State) : Prop := wellFormed t ∧ eval t push_dma_pre = some (.bool true)

/-- `push_reply` -- a foreign body: its contract is an assumption. -/
def push_reply_pre : Expr :=
  (.lit (.bool true))

def push_reply_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def push_reply_writes : List String := ["rf"]

def push_reply_requires (t : State) : Prop := wellFormed t ∧ eval t push_reply_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_wurzel_ohne_vorgaenger = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "free_region" free_region_requires free_region_post
  ∧ Frame ρ "free_region" free_region_writes
  ∧ Contract ρ "push_dma" push_dma_requires push_dma_post
  ∧ Frame ρ "push_dma" push_dma_writes
  ∧ Contract ρ "push_reply" push_reply_requires push_reply_post
  ∧ Frame ρ "push_reply" push_reply_writes

/-! ## The routines: body and contract -/

/-! ### `delete_leaf` -/

def delete_leaf_body : List Stmt :=
  [(.bindName "obj" (.place "CapSpace" (.name "s") "object")), (.call "unlink" ["c", "s"] [(.name "c"), (.name "s")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))))))), (.call "release_slot" ["c", "s"] [(.name "c"), (.name "s")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))))), (.ite (.bin .and (.bin .ge (.place "CapObjects" (.name "obj") "refcount") (.lit (.int 1))) (.bin .le (.place "CapObjects" (.name "obj") "refcount") (.lit (.int 80255)))) [] [(.ret (some (.lit (.reason "Buchfuehrung"))))]), (.assign "CapObjects" (.name "obj") "refcount" (.bin .sub (.place "CapObjects" (.name "obj") "refcount") (.lit (.int 1)))), (.ite (.bin .eq (.place "CapObjects" (.name "obj") "refcount") (.lit (.int 0))) [(.onTag (.place "CapObjects" (.name "obj") "kind") [("Memory", some "m", [(.call "free_region" ["a", "m"] [(.name "a"), (.name "m")] (.hasShape "m" (.intIn 0 18446744073709551615)))]), ("Dma", some "d", [(.call "push_dma" ["rf", "d"] [(.name "rf"), (.name "d")] (.lit (.bool true)))]), ("Reply", some "r", [(.call "push_reply" ["rf", "r"] [(.name "rf"), (.name "r")] (.lit (.bool true)))]), ("Endpoint", some "e1", []), ("Notification", some "n1", []), ("Tcb", some "t1", []), ("SchedContext", some "sc1", []), ("PdControl", some "pd1", []), ("Loader", some "l1", []), ("Mmio", some "mm1", []), ("Irq", some "i1", []), ("SyscallHandler", some "h1", []), ("FaultHandler", some "f1", [])]), (.assign "CapObjects" (.name "obj") "gen" (.wrapTo 32 false (.bin .add (.place "CapObjects" (.name "obj") "gen") (.lit (.int 1))))), (.assign "CapObjects" (.name "obj") "used" (.lit (.bool false)))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def delete_leaf_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.lit (.bool true)) (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .and (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .eq (.place "CapSpace" (.name "s") "first_child") (.lit .absent))) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))))))))

/-- `cdt_wohlgeformt`, as `delete_leaf` keeps it. -/
def delete_leaf_inv_cdt_wohlgeformt : Expr :=
  (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256))

/-- `wurzel_ohne_vorgaenger`, as `delete_leaf` keeps it. -/
def delete_leaf_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))

def delete_leaf_writes : List String := ["CapSpace", "CapObjects", "rf"]

/-- What a caller of `delete_leaf` has to bring: a well-typed world and the precondition. -/
def delete_leaf_requires (t : State) : Prop := wellFormed t ∧ eval t delete_leaf_pre = some (.bool true)

/-- What `delete_leaf` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def delete_leaf_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = none ∨ ∃ e, r = some (.reason e))
  ∧ eval s' delete_leaf_inv_cdt_wohlgeformt = some (.bool true)
  ∧ eval s' delete_leaf_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.un .not (.place "CapSpace" (.name "s") "used")) = some (.bool true))
  ∧ -- ensures #2
  (∀ o1, eval s (.place "CapSpace" (.name "s") "object") = some o1 → ∀ o2, eval s (.place "CapObjects" (.place "CapSpace" (.name "s") "object") "refcount") = some o2 → eval { world := s'.world, local' := (bindLocal (bindLocal s.local' "old#1" o1) "old#2" o2) } (.bin .eq (.bin .add (.place "CapObjects" (.name "old#1") "refcount") (.lit (.int 1))) (.name "old#2")) = some (.bool true))

/-! ### `release_slot` -/

def release_slot_body : List Stmt :=
  [(.assign "CapSpace" (.name "s") "gen" (.wrapTo 32 false (.bin .add (.place "CapSpace" (.name "s") "gen") (.lit (.int 1))))), (.assign "CapSpace" (.name "s") "used" (.lit (.bool false))), (.assign "CapSpace" (.name "s") "badge" (.lit (.int 0)))]

/-- The precondition: the declared shapes and the `requires`. -/
def release_slot_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))))

/-- `wurzel_ohne_vorgaenger`, as `release_slot` keeps it. -/
def release_slot_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))

def release_slot_writes : List String := ["CapSpace"]

/-- What a caller of `release_slot` has to bring: a well-typed world and the precondition. -/
def release_slot_requires (t : State) : Prop := wellFormed t ∧ eval t release_slot_pre = some (.bool true)

/-- What `release_slot` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def release_slot_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' release_slot_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.un .not (.place "CapSpace" (.name "s") "used")) = some (.bool true))

/-! ### `revoke` -/

def revoke_body : List Stmt :=
  [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "revoke#1" (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.hasShape "#returned" .bool) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.bin .and (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))) (.bin .or (.bin .and (.name "#returned") (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))))) [(.bindCallElse "ok" "delete_leaf" ["c", "o", "a", "rf", "s"] [(.name "c"), (.name "o"), (.name "a"), (.name "rf"), (.name "victim")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.lit (.bool true)) (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .and (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .eq (.place "CapSpace" (.name "s") "first_child") (.lit .absent))) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))))))))) "e" [(.bindName "#ret" (.name "e")), (.bindName "#returned" (.lit (.bool true))), .leave])]), (.ite (.name "#returned") [(.ret none)] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def revoke_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.lit (.bool true)) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))))))))

/-- `cdt_wohlgeformt`, as `revoke` keeps it. -/
def revoke_inv_cdt_wohlgeformt : Expr :=
  (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256))

/-- `wurzel_ohne_vorgaenger`, as `revoke` keeps it. -/
def revoke_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))

def revoke_writes : List String := ["CapSpace", "CapObjects", "rf"]

/-- What a caller of `revoke` has to bring: a well-typed world and the precondition. -/
def revoke_requires (t : State) : Prop := wellFormed t ∧ eval t revoke_pre = some (.bool true)

/-- What `revoke` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def revoke_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = none ∨ ∃ e, r = some (.reason e))
  ∧ eval s' revoke_inv_cdt_wohlgeformt = some (.bool true)
  ∧ eval s' revoke_inv_wurzel_ohne_vorgaenger = some (.bool true)

/-! ### `unlink` -/

def unlink_body : List Stmt :=
  [(.onOption (.place "CapSpace" (.name "s") "prev_sibling") "p" [(.assign "CapSpace" (.name "p") "next_sibling" (.place "CapSpace" (.name "s") "next_sibling"))] [(.onOption (.place "CapSpace" (.name "s") "parent") "par" [(.assign "CapSpace" (.name "par") "first_child" (.place "CapSpace" (.name "s") "next_sibling"))] [])]), (.onOption (.place "CapSpace" (.name "s") "next_sibling") "n" [(.assign "CapSpace" (.name "n") "prev_sibling" (.place "CapSpace" (.name "s") "prev_sibling"))] []), (.assign "CapSpace" (.name "s") "parent" (.lit .absent)), (.assign "CapSpace" (.name "s") "first_child" (.lit .absent)), (.assign "CapSpace" (.name "s") "next_sibling" (.lit .absent)), (.assign "CapSpace" (.name "s") "prev_sibling" (.lit .absent))]

/-- The precondition: the declared shapes and the `requires`. -/
def unlink_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))))))

/-- `cdt_wohlgeformt`, as `unlink` keeps it. -/
def unlink_inv_cdt_wohlgeformt : Expr :=
  (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256))

/-- `wurzel_ohne_vorgaenger`, as `unlink` keeps it. -/
def unlink_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent))))

def unlink_writes : List String := ["CapSpace"]

/-- What a caller of `unlink` has to bring: a well-typed world and the precondition. -/
def unlink_requires (t : State) : Prop := wellFormed t ∧ eval t unlink_pre = some (.bool true)

/-- What `unlink` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def unlink_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' unlink_inv_cdt_wohlgeformt = some (.bool true)
  ∧ eval s' unlink_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent)) = some (.bool true))
  ∧ -- ensures #2
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)) = some (.bool true))
  ∧ -- ensures #3
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "CapSpace" (.name "s") "next_sibling") (.lit .absent)) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `delete_leaf` -/

/-- **The duty of `delete_leaf`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def delete_leaf_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s delete_leaf_pre = some (.bool true))
    -- the contract of `free_region`
    (c_free_region : Contract ρ "free_region" free_region_requires free_region_post)
    -- the frame of `free_region`
    (fr_free_region : Frame ρ "free_region" free_region_writes)
    -- the contract of `push_dma`
    (c_push_dma : Contract ρ "push_dma" push_dma_requires push_dma_post)
    -- the frame of `push_dma`
    (fr_push_dma : Frame ρ "push_dma" push_dma_writes)
    -- the contract of `push_reply`
    (c_push_reply : Contract ρ "push_reply" push_reply_requires push_reply_post)
    -- the frame of `push_reply`
    (fr_push_reply : Frame ρ "push_reply" push_reply_writes)
    -- the contract of `release_slot`
    (c_release_slot : Contract ρ "release_slot" release_slot_requires release_slot_post)
    -- the frame of `release_slot`
    (fr_release_slot : Frame ρ "release_slot" release_slot_writes)
    -- the contract of `unlink`
    (c_unlink : Contract ρ "unlink" unlink_requires unlink_post)
    -- the frame of `unlink`
    (fr_unlink : Frame ρ "unlink" unlink_writes),
    ∃ s', finalState (exec ρ delete_leaf_body s) = some s'
        ∧ delete_leaf_post s s' (finalValue (exec ρ delete_leaf_body s))

theorem delete_leaf_meets : delete_leaf_meets_statement := by
  unfold delete_leaf_meets_statement
  intro ρ s hwf hpre c_free_region fr_free_region c_push_dma fr_push_dma c_push_reply fr_push_reply c_release_slot fr_release_slot c_unlink fr_unlink
  simp only [wellFormed] at hwf ⊢
  have hi_cdt_wohlgeformt := (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))))
  gabbro_simp_at hi_cdt_wohlgeformt [delete_leaf_inv_cdt_wohlgeformt, delete_leaf_pre]
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [delete_leaf_inv_wurzel_ohne_vorgaenger, delete_leaf_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_CapSpace_object_s, h_CapSpace_object_s⟩ := WF_int shapeOf s.world (.slot "CapSpace" w_s "object") hwf rfl
  obtain ⟨n_CapSpace_used_s, h_CapSpace_used_s⟩ := WF_bool shapeOf s.world (.slot "CapSpace" w_s "used") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [delete_leaf_pre, e_s, h_CapSpace_object_s, h_CapSpace_used_s]
  gabbro_auto [delete_leaf_body, delete_leaf_pre, delete_leaf_post, wellFormed, delete_leaf_inv_cdt_wohlgeformt, delete_leaf_inv_wurzel_ohne_vorgaenger, free_region_pre, free_region_requires, free_region_post, free_region_writes, Frame_read _ _ _ fr_free_region, push_dma_pre, push_dma_requires, push_dma_post, push_dma_writes, Frame_read _ _ _ fr_push_dma, push_reply_pre, push_reply_requires, push_reply_post, push_reply_writes, Frame_read _ _ _ fr_push_reply, release_slot_pre, release_slot_requires, release_slot_post, release_slot_writes, Frame_read _ _ _ fr_release_slot, unlink_pre, unlink_requires, unlink_post, unlink_writes, Frame_read _ _ _ fr_unlink, e_s, h_CapSpace_object_s, h_CapSpace_used_s, hall] using shapeOf

/-! ### `release_slot` -/

/-- **The duty of `release_slot`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def release_slot_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s release_slot_pre = some (.bool true)),
    ∃ s', finalState (exec ρ release_slot_body s) = some s'
        ∧ release_slot_post s s' (finalValue (exec ρ release_slot_body s))

theorem release_slot_meets : release_slot_meets_statement := by
  unfold release_slot_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ hpre))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [release_slot_inv_wurzel_ohne_vorgaenger, release_slot_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_CapSpace_used_s, h_CapSpace_used_s⟩ := WF_bool shapeOf s.world (.slot "CapSpace" w_s "used") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [release_slot_pre, e_s, h_CapSpace_used_s]
  gabbro_auto [release_slot_body, release_slot_pre, release_slot_post, wellFormed, release_slot_inv_wurzel_ohne_vorgaenger, e_s, h_CapSpace_used_s, hall] using shapeOf

/-! ### `revoke` -/

/-- Loop `revoke#1` of `revoke`: its body and its invariant (with the shapes of the locals in scope). -/
def revoke_loop_1_inv : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.hasShape "#returned" .bool) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.bin .and (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))) (.bin .or (.bin .and (.name "#returned") (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))))

def revoke_loop_1_body : List Stmt :=
  [(.bindCallElse "ok" "delete_leaf" ["c", "o", "a", "rf", "s"] [(.name "c"), (.name "o"), (.name "a"), (.name "rf"), (.name "victim")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.lit (.bool true)) (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .and (.bin .and (.place "CapSpace" (.name "s") "used") (.bin .eq (.place "CapSpace" (.name "s") "first_child") (.lit .absent))) (.bin .and (.forallSlots "s" 80256 (.reaches "CapSpace" (.name "s") (.lit (.int 0)) "parent" 80256)) (.forallSlots "s" 80256 (.bin .or (.un .not (.bin .eq (.place "CapSpace" (.name "s") "parent") (.lit .absent))) (.bin .eq (.place "CapSpace" (.name "s") "prev_sibling") (.lit .absent)))))))))) "e" [(.bindName "#ret" (.name "e")), (.bindName "#returned" (.lit (.bool true))), .leave])]

/-- **The loop rule of `revoke#1`, as a statement over one pass.** -/
def revoke_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 80256)
    (hwf : wellFormed t)
    (hinv : eval t revoke_loop_1_inv = some (.bool true))
    (c_delete_leaf : Contract ρ "delete_leaf" delete_leaf_requires delete_leaf_post)
    (fr_delete_leaf : Frame ρ "delete_leaf" delete_leaf_writes),
    ∃ t', finalState (exec ρ revoke_loop_1_body { t with local' := bindLocal t.local' "victim" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' revoke_loop_1_inv = some (.bool true)

theorem revoke_loop_1_keeps : revoke_loop_1_keeps_statement := by
  unfold revoke_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv c_delete_leaf fr_delete_leaf
  simp only [wellFormed] at hwf ⊢
  have hi_cdt_wohlgeformt := (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hinv)))
  gabbro_simp_at hi_cdt_wohlgeformt [revoke_inv_cdt_wohlgeformt, revoke_loop_1_inv]
  have hi_wurzel_ohne_vorgaenger := (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hinv))))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [revoke_inv_wurzel_ohne_vorgaenger, revoke_loop_1_inv]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn t "s" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  have hall := hinv
  gabbro_simp_at hall [revoke_loop_1_inv, e_s, e__returned]
  gabbro_auto [revoke_loop_1_body, revoke_loop_1_inv, wellFormed, delete_leaf_pre, delete_leaf_requires, delete_leaf_post, delete_leaf_writes, Frame_read _ _ _ fr_delete_leaf, e_s, e__returned, hall] using shapeOf

/-- **The duty of `revoke`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def revoke_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s revoke_pre = some (.bool true))
    -- the contract of `delete_leaf`
    (c_delete_leaf : Contract ρ "delete_leaf" delete_leaf_requires delete_leaf_post)
    -- the frame of `delete_leaf`
    (fr_delete_leaf : Frame ρ "delete_leaf" delete_leaf_writes)
    -- the rule of loop `revoke#1`
    (l_revoke_loop_1 : LoopRule ρ "revoke#1" wellFormed revoke_loop_1_inv),
    ∃ s', finalState (exec ρ revoke_body s) = some s'
        ∧ revoke_post s s' (finalValue (exec ρ revoke_body s))

theorem revoke_meets : revoke_meets_statement := by
  unfold revoke_meets_statement
  intro ρ s hwf hpre c_delete_leaf fr_delete_leaf l_revoke_loop_1
  simp only [wellFormed] at hwf ⊢
  have hi_cdt_wohlgeformt := (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))
  gabbro_simp_at hi_cdt_wohlgeformt [revoke_inv_cdt_wohlgeformt, revoke_pre]
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [revoke_inv_wurzel_ohne_vorgaenger, revoke_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [revoke_pre, e_s]
  gabbro_auto [revoke_body, revoke_pre, revoke_post, wellFormed, revoke_inv_cdt_wohlgeformt, revoke_inv_wurzel_ohne_vorgaenger, delete_leaf_pre, delete_leaf_requires, delete_leaf_post, delete_leaf_writes, Frame_read _ _ _ fr_delete_leaf, revoke_loop_1_inv, e_s, hall] using shapeOf

/-! ### `unlink` -/

/-- **The duty of `unlink`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def unlink_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s unlink_pre = some (.bool true)),
    ∃ s', finalState (exec ρ unlink_body s) = some s'
        ∧ unlink_post s s' (finalValue (exec ρ unlink_body s))

theorem unlink_meets : unlink_meets_statement := by
  unfold unlink_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_cdt_wohlgeformt := (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))
  gabbro_simp_at hi_cdt_wohlgeformt [unlink_inv_cdt_wohlgeformt, unlink_pre]
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [unlink_inv_wurzel_ohne_vorgaenger, unlink_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [unlink_pre, e_s]
  rcases WF_opt shapeOf s.world (.slot "CapSpace" w_s "prev_sibling") hwf rfl with h_CapSpace_prev_sibling_s | ⟨n_CapSpace_prev_sibling_s, h_CapSpace_prev_sibling_s⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "CapSpace" w_s "next_sibling") hwf rfl with h_CapSpace_next_sibling_s | ⟨n_CapSpace_next_sibling_s, h_CapSpace_next_sibling_s⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "CapSpace" w_s "parent") hwf rfl with h_CapSpace_parent_s | ⟨n_CapSpace_parent_s, h_CapSpace_parent_s⟩
    <;> gabbro_auto [unlink_body, unlink_pre, unlink_post, wellFormed, unlink_inv_cdt_wohlgeformt, unlink_inv_wurzel_ohne_vorgaenger, e_s, h_CapSpace_prev_sibling_s, h_CapSpace_next_sibling_s, h_CapSpace_parent_s, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "delete_leaf" delete_leaf_body
  ∧ Frame ρ "delete_leaf" delete_leaf_writes
  ∧ Runs ρ "release_slot" release_slot_body
  ∧ Frame ρ "release_slot" release_slot_writes
  ∧ Runs ρ "revoke" revoke_body
  ∧ Frame ρ "revoke" revoke_writes
  ∧ RunsLoopIn ρ "revoke#1" revoke_loop_1_body "victim" 0 80256
  ∧ Runs ρ "unlink" unlink_body
  ∧ Frame ρ "unlink" unlink_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_release_slot : release_slot_meets_statement)
    (d_unlink : unlink_meets_statement)
    (d_delete_leaf : delete_leaf_meets_statement)
    (d_revoke_loop_1 : revoke_loop_1_keeps_statement)
    (d_revoke : revoke_meets_statement) :
    Contract ρ "release_slot" release_slot_requires release_slot_post
    ∧ Contract ρ "unlink" unlink_requires unlink_post
    ∧ Contract ρ "delete_leaf" delete_leaf_requires delete_leaf_post
    ∧ LoopRule ρ "revoke#1" wellFormed revoke_loop_1_inv
    ∧ Contract ρ "revoke" revoke_requires revoke_post := by
  obtain ⟨r_delete_leaf, fr_delete_leaf, r_release_slot, fr_release_slot, r_revoke, fr_revoke, rl_revoke_loop_1, r_unlink, fr_unlink⟩ := hp
  obtain ⟨c_free_region, fr_free_region, c_push_dma, fr_push_dma, c_push_reply, fr_push_reply⟩ := ha
  have c_release_slot : Contract ρ "release_slot" release_slot_requires release_slot_post :=
    contract_of_duty ρ "release_slot" release_slot_body release_slot_requires release_slot_post r_release_slot
      (fun t ht => d_release_slot ρ t ht.1 ht.2)
  have c_unlink : Contract ρ "unlink" unlink_requires unlink_post :=
    contract_of_duty ρ "unlink" unlink_body unlink_requires unlink_post r_unlink
      (fun t ht => d_unlink ρ t ht.1 ht.2)
  have c_delete_leaf : Contract ρ "delete_leaf" delete_leaf_requires delete_leaf_post :=
    contract_of_duty ρ "delete_leaf" delete_leaf_body delete_leaf_requires delete_leaf_post r_delete_leaf
      (fun t ht => d_delete_leaf ρ t ht.1 ht.2 c_free_region fr_free_region c_push_dma fr_push_dma c_push_reply fr_push_reply c_release_slot fr_release_slot c_unlink fr_unlink)
  have l_revoke_loop_1 : LoopRule ρ "revoke#1" wellFormed revoke_loop_1_inv :=
    looprule_of_body_in ρ "revoke#1" wellFormed revoke_loop_1_inv revoke_loop_1_body "victim" 0 80256 rl_revoke_loop_1
      (fun t k hlo hhi hw hi => d_revoke_loop_1 ρ t k hlo hhi hw hi c_delete_leaf fr_delete_leaf)
  have c_revoke : Contract ρ "revoke" revoke_requires revoke_post :=
    contract_of_duty ρ "revoke" revoke_body revoke_requires revoke_post r_revoke
      (fun t ht => d_revoke ρ t ht.1 ht.2 c_delete_leaf fr_delete_leaf l_revoke_loop_1)
  exact ⟨c_release_slot, c_unlink, c_delete_leaf, l_revoke_loop_1, c_revoke⟩

end GabbroDuty.DutyF01
