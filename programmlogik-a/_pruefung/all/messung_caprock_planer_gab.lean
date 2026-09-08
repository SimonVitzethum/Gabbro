/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/caprock/planer.gab  total 3  goals 3  refused 0
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

namespace GabbroDuty.DutyPlaner

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  unblock :: einreihen requires #1  --  carried by `unblock_meets`
  duty_2  V  resume :: einreihen requires #1  --  carried by `resume_meets`
  duty_3  V  unpark :: einreihen requires #1  --  carried by `unpark_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Faeden" _ "lebt" => some .bool
  | .slot "Faeden" _ "gruende" => some (.intIn 0 255)
  | .slot "Faeden" _ "kern" => some (.intIn 0 255)
  | .slot "Faeden" _ "prio" => some (.intIn 0 255)
  | .field "Gruende" "ipc" => some .bool
  | .field "Gruende" "budget" => some .bool
  | .field "Gruende" "pause" => some .bool
  | .field "Gruende" "park" => some .bool
  | .field "Gruende" "handler" => some .bool
  | .field "Gruende" "load" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `einreihen` -- a foreign body: its contract is an assumption. -/
def einreihen_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))

def einreihen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def einreihen_writes : List String := ["Faeden"]

def einreihen_requires (t : State) : Prop := wellFormed t ∧ eval t einreihen_pre = some (.bool true)

/-- `ipc_grund_weg` -- a foreign body: its contract is an assumption. -/
def ipc_grund_weg_pre : Expr :=
  (.lit (.bool true))

def ipc_grund_weg_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def ipc_grund_weg_writes : List String := ["w"]

def ipc_grund_weg_requires (t : State) : Prop := wellFormed t ∧ eval t ipc_grund_weg_pre = some (.bool true)

/-- `park_grund_weg` -- a foreign body: its contract is an assumption. -/
def park_grund_weg_pre : Expr :=
  (.lit (.bool true))

def park_grund_weg_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def park_grund_weg_writes : List String := ["w"]

def park_grund_weg_requires (t : State) : Prop := wellFormed t ∧ eval t park_grund_weg_pre = some (.bool true)

/-- `pause_grund_weg` -- a foreign body: its contract is an assumption. -/
def pause_grund_weg_pre : Expr :=
  (.lit (.bool true))

def pause_grund_weg_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def pause_grund_weg_writes : List String := ["w"]

def pause_grund_weg_requires (t : State) : Prop := wellFormed t ∧ eval t pause_grund_weg_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "einreihen" einreihen_requires einreihen_post
  ∧ Frame ρ "einreihen" einreihen_writes
  ∧ Contract ρ "ipc_grund_weg" ipc_grund_weg_requires ipc_grund_weg_post
  ∧ Frame ρ "ipc_grund_weg" ipc_grund_weg_writes
  ∧ Contract ρ "park_grund_weg" park_grund_weg_requires park_grund_weg_post
  ∧ Frame ρ "park_grund_weg" park_grund_weg_writes
  ∧ Contract ρ "pause_grund_weg" pause_grund_weg_requires pause_grund_weg_post
  ∧ Frame ρ "pause_grund_weg" pause_grund_weg_writes

/-! ## The routines: body and contract -/

/-! ### `resume` -/

def resume_body : List Stmt :=
  [(.call "pause_grund_weg" ["w"] [(.name "w")] (.lit (.bool true))), (.assign "Faeden" (.name "t") "gruende" (.bin .band (.place "Faeden" (.name "t") "gruende") (.lit (.int 251)))), (.ite (.bin .eq (.place "Faeden" (.name "t") "gruende") (.lit (.int 0))) [(.call "einreihen" ["f", "t"] [(.name "f"), (.name "t")] (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true))))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def resume_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))

def resume_writes : List String := ["w", "Faeden"]

/-- What a caller of `resume` has to bring: a well-typed world and the precondition. -/
def resume_requires (t : State) : Prop := wellFormed t ∧ eval t resume_pre = some (.bool true)

/-- What `resume` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def resume_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `unblock` -/

def unblock_body : List Stmt :=
  [(.call "ipc_grund_weg" ["w"] [(.name "w")] (.lit (.bool true))), (.assign "Faeden" (.name "t") "gruende" (.bin .band (.place "Faeden" (.name "t") "gruende") (.lit (.int 254)))), (.ite (.bin .eq (.place "Faeden" (.name "t") "gruende") (.lit (.int 0))) [(.call "einreihen" ["f", "t"] [(.name "f"), (.name "t")] (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true))))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def unblock_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))

def unblock_writes : List String := ["w", "Faeden"]

/-- What a caller of `unblock` has to bring: a well-typed world and the precondition. -/
def unblock_requires (t : State) : Prop := wellFormed t ∧ eval t unblock_pre = some (.bool true)

/-- What `unblock` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def unblock_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `unpark` -/

def unpark_body : List Stmt :=
  [(.call "park_grund_weg" ["w"] [(.name "w")] (.lit (.bool true))), (.assign "Faeden" (.name "t") "gruende" (.bin .band (.place "Faeden" (.name "t") "gruende") (.lit (.int 247)))), (.ite (.bin .eq (.place "Faeden" (.name "t") "gruende") (.lit (.int 0))) [(.call "einreihen" ["f", "t"] [(.name "f"), (.name "t")] (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true))))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def unpark_pre : Expr :=
  (.bin .and (.hasShape "t" (.intIn 0 1023)) (.lit (.bool true)))

def unpark_writes : List String := ["w", "Faeden"]

/-- What a caller of `unpark` has to bring: a well-typed world and the precondition. -/
def unpark_requires (t : State) : Prop := wellFormed t ∧ eval t unpark_pre = some (.bool true)

/-- What `unpark` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def unpark_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `resume` -/

/-- **The duty of `resume`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def resume_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s resume_pre = some (.bool true))
    -- the contract of `einreihen`
    (c_einreihen : Contract ρ "einreihen" einreihen_requires einreihen_post)
    -- the frame of `einreihen`
    (fr_einreihen : Frame ρ "einreihen" einreihen_writes)
    -- the contract of `pause_grund_weg`
    (c_pause_grund_weg : Contract ρ "pause_grund_weg" pause_grund_weg_requires pause_grund_weg_post)
    -- the frame of `pause_grund_weg`
    (fr_pause_grund_weg : Frame ρ "pause_grund_weg" pause_grund_weg_writes),
    ∃ s', finalState (exec ρ resume_body s) = some s'
        ∧ resume_post s s' (finalValue (exec ρ resume_body s))

theorem resume_meets : resume_meets_statement := by
  unfold resume_meets_statement
  intro ρ s hwf hpre c_einreihen fr_einreihen c_pause_grund_weg fr_pause_grund_weg
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Faeden_gruende_t, h_Faeden_gruende_t, lo_Faeden_gruende_t, hi_Faeden_gruende_t⟩ := WF_intIn shapeOf s.world (.slot "Faeden" w_t "gruende") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [resume_pre, e_t, h_Faeden_gruende_t]
  gabbro_auto [resume_body, resume_pre, resume_post, wellFormed, einreihen_pre, einreihen_requires, einreihen_post, einreihen_writes, Frame_read _ _ _ fr_einreihen, pause_grund_weg_pre, pause_grund_weg_requires, pause_grund_weg_post, pause_grund_weg_writes, Frame_read _ _ _ fr_pause_grund_weg, e_t, h_Faeden_gruende_t, hall] using shapeOf

/-! ### `unblock` -/

/-- **The duty of `unblock`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def unblock_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s unblock_pre = some (.bool true))
    -- the contract of `einreihen`
    (c_einreihen : Contract ρ "einreihen" einreihen_requires einreihen_post)
    -- the frame of `einreihen`
    (fr_einreihen : Frame ρ "einreihen" einreihen_writes)
    -- the contract of `ipc_grund_weg`
    (c_ipc_grund_weg : Contract ρ "ipc_grund_weg" ipc_grund_weg_requires ipc_grund_weg_post)
    -- the frame of `ipc_grund_weg`
    (fr_ipc_grund_weg : Frame ρ "ipc_grund_weg" ipc_grund_weg_writes),
    ∃ s', finalState (exec ρ unblock_body s) = some s'
        ∧ unblock_post s s' (finalValue (exec ρ unblock_body s))

theorem unblock_meets : unblock_meets_statement := by
  unfold unblock_meets_statement
  intro ρ s hwf hpre c_einreihen fr_einreihen c_ipc_grund_weg fr_ipc_grund_weg
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Faeden_gruende_t, h_Faeden_gruende_t, lo_Faeden_gruende_t, hi_Faeden_gruende_t⟩ := WF_intIn shapeOf s.world (.slot "Faeden" w_t "gruende") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [unblock_pre, e_t, h_Faeden_gruende_t]
  gabbro_auto [unblock_body, unblock_pre, unblock_post, wellFormed, einreihen_pre, einreihen_requires, einreihen_post, einreihen_writes, Frame_read _ _ _ fr_einreihen, ipc_grund_weg_pre, ipc_grund_weg_requires, ipc_grund_weg_post, ipc_grund_weg_writes, Frame_read _ _ _ fr_ipc_grund_weg, e_t, h_Faeden_gruende_t, hall] using shapeOf

/-! ### `unpark` -/

/-- **The duty of `unpark`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def unpark_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s unpark_pre = some (.bool true))
    -- the contract of `einreihen`
    (c_einreihen : Contract ρ "einreihen" einreihen_requires einreihen_post)
    -- the frame of `einreihen`
    (fr_einreihen : Frame ρ "einreihen" einreihen_writes)
    -- the contract of `park_grund_weg`
    (c_park_grund_weg : Contract ρ "park_grund_weg" park_grund_weg_requires park_grund_weg_post)
    -- the frame of `park_grund_weg`
    (fr_park_grund_weg : Frame ρ "park_grund_weg" park_grund_weg_writes),
    ∃ s', finalState (exec ρ unpark_body s) = some s'
        ∧ unpark_post s s' (finalValue (exec ρ unpark_body s))

theorem unpark_meets : unpark_meets_statement := by
  unfold unpark_meets_statement
  intro ρ s hwf hpre c_einreihen fr_einreihen c_park_grund_weg fr_park_grund_weg
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_t, e_t, lo_t, hi_t⟩ := shape_intIn s "t" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Faeden_gruende_t, h_Faeden_gruende_t, lo_Faeden_gruende_t, hi_Faeden_gruende_t⟩ := WF_intIn shapeOf s.world (.slot "Faeden" w_t "gruende") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [unpark_pre, e_t, h_Faeden_gruende_t]
  gabbro_auto [unpark_body, unpark_pre, unpark_post, wellFormed, einreihen_pre, einreihen_requires, einreihen_post, einreihen_writes, Frame_read _ _ _ fr_einreihen, park_grund_weg_pre, park_grund_weg_requires, park_grund_weg_post, park_grund_weg_writes, Frame_read _ _ _ fr_park_grund_weg, e_t, h_Faeden_gruende_t, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "resume" resume_body
  ∧ Frame ρ "resume" resume_writes
  ∧ Runs ρ "unblock" unblock_body
  ∧ Frame ρ "unblock" unblock_writes
  ∧ Runs ρ "unpark" unpark_body
  ∧ Frame ρ "unpark" unpark_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_resume : resume_meets_statement)
    (d_unblock : unblock_meets_statement)
    (d_unpark : unpark_meets_statement) :
    Contract ρ "resume" resume_requires resume_post
    ∧ Contract ρ "unblock" unblock_requires unblock_post
    ∧ Contract ρ "unpark" unpark_requires unpark_post := by
  obtain ⟨r_resume, fr_resume, r_unblock, fr_unblock, r_unpark, fr_unpark⟩ := hp
  obtain ⟨c_einreihen, fr_einreihen, c_ipc_grund_weg, fr_ipc_grund_weg, c_park_grund_weg, fr_park_grund_weg, c_pause_grund_weg, fr_pause_grund_weg⟩ := ha
  have c_resume : Contract ρ "resume" resume_requires resume_post :=
    contract_of_duty ρ "resume" resume_body resume_requires resume_post r_resume
      (fun t ht => d_resume ρ t ht.1 ht.2 c_einreihen fr_einreihen c_pause_grund_weg fr_pause_grund_weg)
  have c_unblock : Contract ρ "unblock" unblock_requires unblock_post :=
    contract_of_duty ρ "unblock" unblock_body unblock_requires unblock_post r_unblock
      (fun t ht => d_unblock ρ t ht.1 ht.2 c_einreihen fr_einreihen c_ipc_grund_weg fr_ipc_grund_weg)
  have c_unpark : Contract ρ "unpark" unpark_requires unpark_post :=
    contract_of_duty ρ "unpark" unpark_body unpark_requires unpark_post r_unpark
      (fun t ht => d_unpark ρ t ht.1 ht.2 c_einreihen fr_einreihen c_park_grund_weg fr_park_grund_weg)
  exact ⟨c_resume, c_unblock, c_unpark⟩

end GabbroDuty.DutyPlaner