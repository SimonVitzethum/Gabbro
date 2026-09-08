/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/53-zwei-orte.gab  total 6  goals 6  refused 0
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

namespace GabbroDuty.Duty53ZweiOrte

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  E  treffen_oeffnen :: antwortpflicht_paarig  --  carried by `treffen_oeffnen_meets`
  duty_2  N  treffen_oeffnen :: ensures #1  --  carried by `treffen_oeffnen_meets`
  duty_3  N  treffen_oeffnen :: ensures #2  --  carried by `treffen_oeffnen_meets`
  duty_4  E  treffen_schliessen :: antwortpflicht_paarig  --  carried by `treffen_schliessen_meets`
  duty_5  N  treffen_schliessen :: ensures #1  --  carried by `treffen_schliessen_meets`
  duty_6  N  treffen_schliessen :: ensures #2  --  carried by `treffen_schliessen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Endpunkt" _ "benutzt" => some .bool
  | .slot "Endpunkt" _ "anrufer" => some .opt
  | .slot "Endpunkt" _ "antwortende" => some .opt
  | .slot "Faden" _ "benutzt" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `antwortpflicht_paarig` over `Endpunkt`. -/
def inv_antwortpflicht_paarig : Expr :=
  (.forallSlots "e" 4 (.bin .eq (.bin .eq (.place "Endpunkt" (.name "e") "anrufer") (.lit .absent)) (.bin .eq (.place "Endpunkt" (.name "e") "antwortende") (.lit .absent))))

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_antwortpflicht_paarig = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  True

/-! ## The routines: body and contract -/

/-! ### `treffen_oeffnen` -/

def treffen_oeffnen_body : List Stmt :=
  [(.breaking ["antwortpflicht_paarig"] [(.assign "Endpunkt" (.name "kern") "anrufer" (.someOf (.name "ruft"))), (.assign "Endpunkt" (.name "kern") "antwortende" (.someOf (.name "dient")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def treffen_oeffnen_pre : Expr :=
  (.bin .and (.hasShape "kern" (.intIn 0 3)) (.bin .and (.hasShape "ruft" (.intIn 0 63)) (.bin .and (.hasShape "dient" (.intIn 0 63)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Endpunkt" (.name "kern") "benutzt") (.forallSlots "e" 4 (.bin .eq (.bin .eq (.place "Endpunkt" (.name "e") "anrufer") (.lit .absent)) (.bin .eq (.place "Endpunkt" (.name "e") "antwortende") (.lit .absent)))))))))

/-- `antwortpflicht_paarig`, as `treffen_oeffnen` keeps it. -/
def treffen_oeffnen_inv_antwortpflicht_paarig : Expr :=
  (.forallSlots "e" 4 (.bin .eq (.bin .eq (.place "Endpunkt" (.name "e") "anrufer") (.lit .absent)) (.bin .eq (.place "Endpunkt" (.name "e") "antwortende") (.lit .absent))))

def treffen_oeffnen_writes : List String := ["Endpunkt"]

/-- What a caller of `treffen_oeffnen` has to bring: a well-typed world and the precondition. -/
def treffen_oeffnen_requires (t : State) : Prop := wellFormed t ∧ eval t treffen_oeffnen_pre = some (.bool true)

/-- What `treffen_oeffnen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def treffen_oeffnen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' treffen_oeffnen_inv_antwortpflicht_paarig = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Endpunkt" (.name "kern") "anrufer") (.someOf (.name "ruft"))) = some (.bool true))
  ∧ -- ensures #2
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Endpunkt" (.name "kern") "antwortende") (.someOf (.name "dient"))) = some (.bool true))

/-! ### `treffen_schliessen` -/

def treffen_schliessen_body : List Stmt :=
  [(.breaking ["antwortpflicht_paarig"] [(.assign "Endpunkt" (.name "kern") "anrufer" (.lit .absent)), (.assign "Endpunkt" (.name "kern") "antwortende" (.lit .absent))])]

/-- The precondition: the declared shapes and the `requires`. -/
def treffen_schliessen_pre : Expr :=
  (.bin .and (.hasShape "kern" (.intIn 0 3)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Endpunkt" (.name "kern") "benutzt") (.forallSlots "e" 4 (.bin .eq (.bin .eq (.place "Endpunkt" (.name "e") "anrufer") (.lit .absent)) (.bin .eq (.place "Endpunkt" (.name "e") "antwortende") (.lit .absent)))))))

/-- `antwortpflicht_paarig`, as `treffen_schliessen` keeps it. -/
def treffen_schliessen_inv_antwortpflicht_paarig : Expr :=
  (.forallSlots "e" 4 (.bin .eq (.bin .eq (.place "Endpunkt" (.name "e") "anrufer") (.lit .absent)) (.bin .eq (.place "Endpunkt" (.name "e") "antwortende") (.lit .absent))))

def treffen_schliessen_writes : List String := ["Endpunkt"]

/-- What a caller of `treffen_schliessen` has to bring: a well-typed world and the precondition. -/
def treffen_schliessen_requires (t : State) : Prop := wellFormed t ∧ eval t treffen_schliessen_pre = some (.bool true)

/-- What `treffen_schliessen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def treffen_schliessen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' treffen_schliessen_inv_antwortpflicht_paarig = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Endpunkt" (.name "kern") "anrufer") (.lit .absent)) = some (.bool true))
  ∧ -- ensures #2
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Endpunkt" (.name "kern") "antwortende") (.lit .absent)) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `treffen_oeffnen` -/

/-- **The duty of `treffen_oeffnen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def treffen_oeffnen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s treffen_oeffnen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ treffen_oeffnen_body s) = some s'
        ∧ treffen_oeffnen_post s s' (finalValue (exec ρ treffen_oeffnen_body s))

theorem treffen_oeffnen_meets : treffen_oeffnen_meets_statement := by
  unfold treffen_oeffnen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_antwortpflicht_paarig := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))
  gabbro_simp_at hi_antwortpflicht_paarig [treffen_oeffnen_inv_antwortpflicht_paarig, treffen_oeffnen_pre]
  obtain ⟨w_kern, e_kern, lo_kern, hi_kern⟩ := shape_intIn s "kern" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_ruft, e_ruft, lo_ruft, hi_ruft⟩ := shape_intIn s "ruft" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_dient, e_dient, lo_dient, hi_dient⟩ := shape_intIn s "dient" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  have hall := hpre
  gabbro_simp_at hall [treffen_oeffnen_pre, e_kern, e_ruft, e_dient]
  rcases WF_opt shapeOf s.world (.slot "Endpunkt" w_kern "anrufer") hwf rfl with h_Endpunkt_anrufer_kern | ⟨n_Endpunkt_anrufer_kern, h_Endpunkt_anrufer_kern⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "Endpunkt" w_kern "antwortende") hwf rfl with h_Endpunkt_antwortende_kern | ⟨n_Endpunkt_antwortende_kern, h_Endpunkt_antwortende_kern⟩
    <;> gabbro_auto [treffen_oeffnen_body, treffen_oeffnen_pre, treffen_oeffnen_post, wellFormed, treffen_oeffnen_inv_antwortpflicht_paarig, e_kern, e_ruft, e_dient, h_Endpunkt_anrufer_kern, h_Endpunkt_antwortende_kern, hall] using shapeOf

/-! ### `treffen_schliessen` -/

/-- **The duty of `treffen_schliessen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def treffen_schliessen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s treffen_schliessen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ treffen_schliessen_body s) = some s'
        ∧ treffen_schliessen_post s s' (finalValue (exec ρ treffen_schliessen_body s))

theorem treffen_schliessen_meets : treffen_schliessen_meets_statement := by
  unfold treffen_schliessen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_antwortpflicht_paarig := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  gabbro_simp_at hi_antwortpflicht_paarig [treffen_schliessen_inv_antwortpflicht_paarig, treffen_schliessen_pre]
  obtain ⟨w_kern, e_kern, lo_kern, hi_kern⟩ := shape_intIn s "kern" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [treffen_schliessen_pre, e_kern]
  rcases WF_opt shapeOf s.world (.slot "Endpunkt" w_kern "anrufer") hwf rfl with h_Endpunkt_anrufer_kern | ⟨n_Endpunkt_anrufer_kern, h_Endpunkt_anrufer_kern⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "Endpunkt" w_kern "antwortende") hwf rfl with h_Endpunkt_antwortende_kern | ⟨n_Endpunkt_antwortende_kern, h_Endpunkt_antwortende_kern⟩
    <;> gabbro_auto [treffen_schliessen_body, treffen_schliessen_pre, treffen_schliessen_post, wellFormed, treffen_schliessen_inv_antwortpflicht_paarig, e_kern, h_Endpunkt_anrufer_kern, h_Endpunkt_antwortende_kern, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "treffen_oeffnen" treffen_oeffnen_body
  ∧ Frame ρ "treffen_oeffnen" treffen_oeffnen_writes
  ∧ Runs ρ "treffen_schliessen" treffen_schliessen_body
  ∧ Frame ρ "treffen_schliessen" treffen_schliessen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_treffen_oeffnen : treffen_oeffnen_meets_statement)
    (d_treffen_schliessen : treffen_schliessen_meets_statement) :
    Contract ρ "treffen_oeffnen" treffen_oeffnen_requires treffen_oeffnen_post
    ∧ Contract ρ "treffen_schliessen" treffen_schliessen_requires treffen_schliessen_post := by
  obtain ⟨r_treffen_oeffnen, fr_treffen_oeffnen, r_treffen_schliessen, fr_treffen_schliessen⟩ := hp
  have c_treffen_oeffnen : Contract ρ "treffen_oeffnen" treffen_oeffnen_requires treffen_oeffnen_post :=
    contract_of_duty ρ "treffen_oeffnen" treffen_oeffnen_body treffen_oeffnen_requires treffen_oeffnen_post r_treffen_oeffnen
      (fun t ht => d_treffen_oeffnen ρ t ht.1 ht.2)
  have c_treffen_schliessen : Contract ρ "treffen_schliessen" treffen_schliessen_requires treffen_schliessen_post :=
    contract_of_duty ρ "treffen_schliessen" treffen_schliessen_body treffen_schliessen_requires treffen_schliessen_post r_treffen_schliessen
      (fun t ht => d_treffen_schliessen ρ t ht.1 ht.2)
  exact ⟨c_treffen_oeffnen, c_treffen_schliessen⟩

end GabbroDuty.Duty53ZweiOrte
