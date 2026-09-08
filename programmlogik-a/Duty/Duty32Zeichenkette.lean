/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/32-zeichenkette.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty32Zeichenkette

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Text.bytes" _ "elem" => some (.intIn 0 255)
  | .field "Text" "len" => some (.intIn 0 64)
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

/-! ### `anhaengen` -/

def anhaengen_body : List Stmt :=
  [(.ite (.bin .and (.bin .ge (.fieldOf "Text" "len") (.lit (.int 0))) (.bin .lt (.fieldOf "Text" "len") (.lit (.int 64)))) [] [(.ret (some (.lit (.bool false))))]), (.assign "Text.bytes" (.fieldOf "Text" "len") "elem" (.name "b")), (.assignField "Text" "len" (.bin .add (.fieldOf "Text" "len") (.lit (.int 1)))), (.ret (some (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def anhaengen_pre : Expr :=
  (.hasShape "b" (.intIn 0 255))

def anhaengen_writes : List String := ["Text.bytes", "Text"]

/-- What a caller of `anhaengen` has to bring: a well-typed world and the precondition. -/
def anhaengen_requires (t : State) : Prop := wellFormed t ∧ eval t anhaengen_pre = some (.bool true)

/-- What `anhaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def anhaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `byte_an` -/

def byte_an_body : List Stmt :=
  [(.ret (some (.place "Text.bytes" (.name "i") "elem")))]

/-- The precondition: the declared shapes and the `requires`. -/
def byte_an_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 63)) (.bin .lt (.name "i") (.fieldOf "Text" "len")))

def byte_an_writes : List String := []

/-- What a caller of `byte_an` has to bring: a well-typed world and the precondition. -/
def byte_an_requires (t : State) : Prop := wellFormed t ∧ eval t byte_an_pre = some (.bool true)

/-- What `byte_an` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def byte_an_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 255)

/-! ### `laenge` -/

def laenge_body : List Stmt :=
  [(.ret (some (.fieldOf "Text" "len")))]

/-- The precondition: the declared shapes and the `requires`. -/
def laenge_pre : Expr :=
  (.lit (.bool true))

def laenge_writes : List String := []

/-- What a caller of `laenge` has to bring: a well-typed world and the precondition. -/
def laenge_requires (t : State) : Prop := wellFormed t ∧ eval t laenge_pre = some (.bool true)

/-- What `laenge` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def laenge_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 64)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `anhaengen` -/

/-- **The duty of `anhaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def anhaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s anhaengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ anhaengen_body s) = some s'
        ∧ anhaengen_post s s' (finalValue (exec ρ anhaengen_body s))

theorem anhaengen_meets : anhaengen_meets_statement := by
  unfold anhaengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ hpre
  obtain ⟨n_Text_len, h_Text_len, lo_Text_len, hi_Text_len⟩ := WF_intIn shapeOf s.world (.field "Text" "len") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [anhaengen_pre, e_b, h_Text_len]
  gabbro_auto [anhaengen_body, anhaengen_pre, anhaengen_post, wellFormed, e_b, h_Text_len, hall] using shapeOf

/-! ### `byte_an` -/

/-- **The duty of `byte_an`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def byte_an_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s byte_an_pre = some (.bool true)),
    ∃ s', finalState (exec ρ byte_an_body s) = some s'
        ∧ byte_an_post s s' (finalValue (exec ρ byte_an_body s))

theorem byte_an_meets : byte_an_meets_statement := by
  unfold byte_an_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Text.bytes_elem_i, h_Text.bytes_elem_i, lo_Text.bytes_elem_i, hi_Text.bytes_elem_i⟩ := WF_intIn shapeOf s.world (.slot "Text.bytes" w_i "elem") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [byte_an_pre, e_i, h_Text.bytes_elem_i]
  gabbro_auto [byte_an_body, byte_an_pre, byte_an_post, wellFormed, e_i, h_Text.bytes_elem_i, hall] using shapeOf

/-! ### `laenge` -/

/-- **The duty of `laenge`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def laenge_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s laenge_pre = some (.bool true)),
    ∃ s', finalState (exec ρ laenge_body s) = some s'
        ∧ laenge_post s s' (finalValue (exec ρ laenge_body s))

theorem laenge_meets : laenge_meets_statement := by
  unfold laenge_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Text_len, h_Text_len, lo_Text_len, hi_Text_len⟩ := WF_intIn shapeOf s.world (.field "Text" "len") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [laenge_pre, h_Text_len]
  gabbro_auto [laenge_body, laenge_pre, laenge_post, wellFormed, h_Text_len, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "anhaengen" anhaengen_body
  ∧ Frame ρ "anhaengen" anhaengen_writes
  ∧ Runs ρ "byte_an" byte_an_body
  ∧ Frame ρ "byte_an" byte_an_writes
  ∧ Runs ρ "laenge" laenge_body
  ∧ Frame ρ "laenge" laenge_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_anhaengen : anhaengen_meets_statement)
    (d_byte_an : byte_an_meets_statement)
    (d_laenge : laenge_meets_statement) :
    Contract ρ "anhaengen" anhaengen_requires anhaengen_post
    ∧ Contract ρ "byte_an" byte_an_requires byte_an_post
    ∧ Contract ρ "laenge" laenge_requires laenge_post := by
  obtain ⟨r_anhaengen, fr_anhaengen, r_byte_an, fr_byte_an, r_laenge, fr_laenge⟩ := hp
  have c_anhaengen : Contract ρ "anhaengen" anhaengen_requires anhaengen_post :=
    contract_of_duty ρ "anhaengen" anhaengen_body anhaengen_requires anhaengen_post r_anhaengen
      (fun t ht => d_anhaengen ρ t ht.1 ht.2)
  have c_byte_an : Contract ρ "byte_an" byte_an_requires byte_an_post :=
    contract_of_duty ρ "byte_an" byte_an_body byte_an_requires byte_an_post r_byte_an
      (fun t ht => d_byte_an ρ t ht.1 ht.2)
  have c_laenge : Contract ρ "laenge" laenge_requires laenge_post :=
    contract_of_duty ρ "laenge" laenge_body laenge_requires laenge_post r_laenge
      (fun t ht => d_laenge ρ t ht.1 ht.2)
  exact ⟨c_anhaengen, c_byte_an, c_laenge⟩

end GabbroDuty.Duty32Zeichenkette
