/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/56-auftragsring.gab  total 3  goals 3  refused 0
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

namespace GabbroDuty.Duty56Auftragsring

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  N  einreihen :: ensures #1  --  carried by `einreihen_meets`
  duty_2  N  einreihen :: ensures #2  --  carried by `einreihen_meets`
  duty_3  N  entnehmen :: ensures #1  --  carried by `entnehmen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Auftrag" _ "belegt" => some .bool
  | .slot "Auftrag" _ "last" => some (.intIn 0 4294967295)
  | .slot "Ring.plaetze" _ "elem" => some (.intIn 0 64)
  | .field "Ring" "kopf" => some (.intIn 0 4294967295)
  | .field "Ring" "zahl" => some (.intIn 0 4294967295)
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

/-! ### `einreihen` -/

def einreihen_body : List Stmt :=
  [(.assign "Ring.plaetze" (.name "p") "elem" (.name "i"))]

/-- The precondition: the declared shapes and the `requires`. -/
def einreihen_pre : Expr :=
  (.bin .and (.hasShape "p" (.intIn 0 31)) (.bin .and (.hasShape "i" (.intIn 0 64)) (.bin .and (.lit (.bool true)) (.bin .and (.bin .eq (.place "Ring.plaetze" (.name "p") "elem") (.lit (.int 64))) (.bin .and (.bin .ne (.name "i") (.lit (.int 64))) (.forallSlots "j" 32 (.forallSlots "k" 32 (.bin .or (.bin .or (.bin .eq (.name "j") (.name "k")) (.bin .eq (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64)))) (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.place "Ring.plaetze" (.name "k") "elem"))))))))))

def einreihen_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `einreihen` has to bring: a well-typed world and the precondition. -/
def einreihen_requires (t : State) : Prop := wellFormed t ∧ eval t einreihen_pre = some (.bool true)

/-- What `einreihen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einreihen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Ring.plaetze" (.name "p") "elem") (.name "i")) = some (.bool true))
  ∧ -- ensures #2
  (eval { world := s'.world, local' := s.local' } (.forallSlots "j" 32 (.forallSlots "k" 32 (.bin .or (.bin .or (.bin .eq (.name "j") (.name "k")) (.bin .eq (.place "Ring.plaetze" (.name "j") "elem") (.lit (.int 64)))) (.bin .ne (.place "Ring.plaetze" (.name "j") "elem") (.place "Ring.plaetze" (.name "k") "elem"))))) = some (.bool true))

/-! ### `entnehmen` -/

def entnehmen_body : List Stmt :=
  [(.assign "Ring.plaetze" (.name "p") "elem" (.lit (.int 64)))]

/-- The precondition: the declared shapes and the `requires`. -/
def entnehmen_pre : Expr :=
  (.bin .and (.hasShape "p" (.intIn 0 31)) (.lit (.bool true)))

def entnehmen_writes : List String := ["Ring.plaetze", "Ring"]

/-- What a caller of `entnehmen` has to bring: a well-typed world and the precondition. -/
def entnehmen_requires (t : State) : Prop := wellFormed t ∧ eval t entnehmen_pre = some (.bool true)

/-- What `entnehmen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def entnehmen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Ring.plaetze" (.name "p") "elem") (.lit (.int 64))) = some (.bool true))

/-! ### `ist_leer` -/

def ist_leer_body : List Stmt :=
  [(.ret (some (.bin .eq (.fieldOf "Ring" "zahl") (.lit (.int 0)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def ist_leer_pre : Expr :=
  (.lit (.bool true))

def ist_leer_writes : List String := []

/-- What a caller of `ist_leer` has to bring: a well-typed world and the precondition. -/
def ist_leer_requires (t : State) : Prop := wellFormed t ∧ eval t ist_leer_pre = some (.bool true)

/-- What `ist_leer` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def ist_leer_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `einreihen` -/

/-- **The duty of `einreihen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einreihen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einreihen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ einreihen_body s) = some s'
        ∧ einreihen_post s s' (finalValue (exec ρ einreihen_body s))

theorem einreihen_meets : einreihen_meets_statement := by
  unfold einreihen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_p, e_p, lo_p, hi_p⟩ := shape_intIn s "p" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨n_Ring.plaetze_elem_p, h_Ring.plaetze_elem_p, lo_Ring.plaetze_elem_p, hi_Ring.plaetze_elem_p⟩ := WF_intIn shapeOf s.world (.slot "Ring.plaetze" w_p "elem") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [einreihen_pre, e_p, e_i, h_Ring.plaetze_elem_p]
  gabbro_auto [einreihen_body, einreihen_pre, einreihen_post, wellFormed, e_p, e_i, h_Ring.plaetze_elem_p, hall] using shapeOf

/-! ### `entnehmen` -/

/-- **The duty of `entnehmen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def entnehmen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s entnehmen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ entnehmen_body s) = some s'
        ∧ entnehmen_post s s' (finalValue (exec ρ entnehmen_body s))

theorem entnehmen_meets : entnehmen_meets_statement := by
  unfold entnehmen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_p, e_p, lo_p, hi_p⟩ := shape_intIn s "p" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Ring.plaetze_elem_p, h_Ring.plaetze_elem_p, lo_Ring.plaetze_elem_p, hi_Ring.plaetze_elem_p⟩ := WF_intIn shapeOf s.world (.slot "Ring.plaetze" w_p "elem") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [entnehmen_pre, e_p, h_Ring.plaetze_elem_p]
  gabbro_auto [entnehmen_body, entnehmen_pre, entnehmen_post, wellFormed, e_p, h_Ring.plaetze_elem_p, hall] using shapeOf

/-! ### `ist_leer` -/

/-- **The duty of `ist_leer`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def ist_leer_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s ist_leer_pre = some (.bool true)),
    ∃ s', finalState (exec ρ ist_leer_body s) = some s'
        ∧ ist_leer_post s s' (finalValue (exec ρ ist_leer_body s))

theorem ist_leer_meets : ist_leer_meets_statement := by
  unfold ist_leer_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Ring_zahl, h_Ring_zahl, lo_Ring_zahl, hi_Ring_zahl⟩ := WF_intIn shapeOf s.world (.field "Ring" "zahl") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [ist_leer_pre, h_Ring_zahl]
  gabbro_auto [ist_leer_body, ist_leer_pre, ist_leer_post, wellFormed, h_Ring_zahl, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "einreihen" einreihen_body
  ∧ Frame ρ "einreihen" einreihen_writes
  ∧ Runs ρ "entnehmen" entnehmen_body
  ∧ Frame ρ "entnehmen" entnehmen_writes
  ∧ Runs ρ "ist_leer" ist_leer_body
  ∧ Frame ρ "ist_leer" ist_leer_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_einreihen : einreihen_meets_statement)
    (d_entnehmen : entnehmen_meets_statement)
    (d_ist_leer : ist_leer_meets_statement) :
    Contract ρ "einreihen" einreihen_requires einreihen_post
    ∧ Contract ρ "entnehmen" entnehmen_requires entnehmen_post
    ∧ Contract ρ "ist_leer" ist_leer_requires ist_leer_post := by
  obtain ⟨r_einreihen, fr_einreihen, r_entnehmen, fr_entnehmen, r_ist_leer, fr_ist_leer⟩ := hp
  have c_einreihen : Contract ρ "einreihen" einreihen_requires einreihen_post :=
    contract_of_duty ρ "einreihen" einreihen_body einreihen_requires einreihen_post r_einreihen
      (fun t ht => d_einreihen ρ t ht.1 ht.2)
  have c_entnehmen : Contract ρ "entnehmen" entnehmen_requires entnehmen_post :=
    contract_of_duty ρ "entnehmen" entnehmen_body entnehmen_requires entnehmen_post r_entnehmen
      (fun t ht => d_entnehmen ρ t ht.1 ht.2)
  have c_ist_leer : Contract ρ "ist_leer" ist_leer_requires ist_leer_post :=
    contract_of_duty ρ "ist_leer" ist_leer_body ist_leer_requires ist_leer_post r_ist_leer
      (fun t ht => d_ist_leer ρ t ht.1 ht.2)
  exact ⟨c_einreihen, c_entnehmen, c_ist_leer⟩

end GabbroDuty.Duty56Auftragsring
