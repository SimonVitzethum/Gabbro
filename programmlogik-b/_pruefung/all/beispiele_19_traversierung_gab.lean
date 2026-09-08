/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/19-traversierung.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.Duty19Traversierung

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  aktive_zaehlen :: loop invariant #1  --  carried by `aktive_zaehlen_loop_1_keeps`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Werte" _ "aktiv" => some .bool
  | .slot "Werte" _ "wert" => some (.intIn 0 65535)
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

/-! ### `aktive_loeschen` -/

def aktive_loeschen_body : List Stmt :=
  [(.loop "aktive_loeschen#1" (.lit (.bool true)) [(.ite (.place "Werte" (.name "i") "aktiv") [(.assign "Werte" (.name "i") "aktiv" (.lit (.bool false)))] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def aktive_loeschen_pre : Expr :=
  (.lit (.bool true))

def aktive_loeschen_writes : List String := ["Werte"]

/-- What a caller of `aktive_loeschen` has to bring: a well-typed world and the precondition. -/
def aktive_loeschen_requires (t : State) : Prop := wellFormed t ∧ eval t aktive_loeschen_pre = some (.bool true)

/-- What `aktive_loeschen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aktive_loeschen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `aktive_zaehlen` -/

def aktive_zaehlen_body : List Stmt :=
  [(.bindName "n" (.lit (.int 0))), (.bindName "#pass" (.lit (.int 0))), (.loop "aktive_zaehlen#1" (.bin .and (.hasShape "n" (.intIn 0 16)) (.bin .and (.hasShape "#pass" .int) (.bin .le (.name "n") (.name "#pass")))) [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.place "Werte" (.name "i") "aktiv") [(.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))] [])]), (.ret (some (.name "n")))]

/-- The precondition: the declared shapes and the `requires`. -/
def aktive_zaehlen_pre : Expr :=
  (.lit (.bool true))

def aktive_zaehlen_writes : List String := []

/-- What a caller of `aktive_zaehlen` has to bring: a well-typed world and the precondition. -/
def aktive_zaehlen_requires (t : State) : Prop := wellFormed t ∧ eval t aktive_zaehlen_pre = some (.bool true)

/-- What `aktive_zaehlen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aktive_zaehlen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `aktive_loeschen` -/

/-- Loop `aktive_loeschen#1` of `aktive_loeschen`: its body and its invariant (with the shapes of the locals in scope). -/
def aktive_loeschen_loop_1_inv : Expr :=
  (.lit (.bool true))

def aktive_loeschen_loop_1_body : List Stmt :=
  [(.ite (.place "Werte" (.name "i") "aktiv") [(.assign "Werte" (.name "i") "aktiv" (.lit (.bool false)))] [])]

/-- **The loop rule of `aktive_loeschen#1`, as a statement over one pass.** -/
def aktive_loeschen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hwf : wellFormed t)
    (hinv : eval t aktive_loeschen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ aktive_loeschen_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' aktive_loeschen_loop_1_inv = some (.bool true)

theorem aktive_loeschen_loop_1_keeps : aktive_loeschen_loop_1_keeps_statement := by
  unfold aktive_loeschen_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Werte_aktiv_i, h_Werte_aktiv_i⟩ := WF_bool shapeOf t.world (.slot "Werte" k "aktiv") hwf rfl
  have hall := hinv
  gabbro_simp_at hall [aktive_loeschen_loop_1_inv, h_Werte_aktiv_i]
  gabbro_auto [aktive_loeschen_loop_1_body, aktive_loeschen_loop_1_inv, wellFormed, h_Werte_aktiv_i, hall] using shapeOf

/-- **The duty of `aktive_loeschen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aktive_loeschen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aktive_loeschen_pre = some (.bool true))
    -- the rule of loop `aktive_loeschen#1`
    (l_aktive_loeschen_loop_1 : LoopRule ρ "aktive_loeschen#1" wellFormed aktive_loeschen_loop_1_inv),
    ∃ s', finalState (exec ρ aktive_loeschen_body s) = some s'
        ∧ aktive_loeschen_post s s' (finalValue (exec ρ aktive_loeschen_body s))

theorem aktive_loeschen_meets : aktive_loeschen_meets_statement := by
  unfold aktive_loeschen_meets_statement
  intro ρ s hwf hpre l_aktive_loeschen_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [aktive_loeschen_pre]
  gabbro_auto [aktive_loeschen_body, aktive_loeschen_pre, aktive_loeschen_post, wellFormed, aktive_loeschen_loop_1_inv, hall] using shapeOf

/-! ### `aktive_zaehlen` -/

/-- Loop `aktive_zaehlen#1` of `aktive_zaehlen`: its body and its invariant (with the shapes of the locals in scope). -/
def aktive_zaehlen_loop_1_inv : Expr :=
  (.bin .and (.hasShape "n" (.intIn 0 16)) (.bin .and (.hasShape "#pass" .int) (.bin .le (.name "n") (.name "#pass"))))

def aktive_zaehlen_loop_1_body : List Stmt :=
  [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.place "Werte" (.name "i") "aktiv") [(.bindName "n" (.bin .add (.name "n") (.lit (.int 1))))] [])]

/-- **The loop rule of `aktive_zaehlen#1`, as a statement over one pass.** -/
def aktive_zaehlen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int) (i : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hplo : 0 ≤ i)
    (hphi : i < 16)
    (hpass : t.local' "#pass" = .int i)
    (hwf : wellFormed t)
    (hinv : eval t aktive_zaehlen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ aktive_zaehlen_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' aktive_zaehlen_loop_1_inv = some (.bool true)
        ∧ t'.local' "#pass" = .int (i + 1)

theorem aktive_zaehlen_loop_1_keeps : aktive_zaehlen_loop_1_keeps_statement := by
  unfold aktive_zaehlen_loop_1_keeps_statement
  intro ρ t k i hlo hhi hplo hphi hpass hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_n, e_n, lo_n, hi_n⟩ := shape_intIn t "n" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__pass, e__pass⟩ := shape_int t "#pass" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨n_Werte_aktiv_i, h_Werte_aktiv_i⟩ := WF_bool shapeOf t.world (.slot "Werte" k "aktiv") hwf rfl
  have hall := hinv
  gabbro_simp_at hall [aktive_zaehlen_loop_1_inv, e_n, e__pass, h_Werte_aktiv_i]
  gabbro_auto [aktive_zaehlen_loop_1_body, aktive_zaehlen_loop_1_inv, wellFormed, e_n, e__pass, h_Werte_aktiv_i, hall, hpass] using shapeOf

/-- **The duty of `aktive_zaehlen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aktive_zaehlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aktive_zaehlen_pre = some (.bool true))
    -- the rule of loop `aktive_zaehlen#1`
    (l_aktive_zaehlen_loop_1 : LoopRuleP ρ "aktive_zaehlen#1" wellFormed aktive_zaehlen_loop_1_inv "#pass"),
    ∃ s', finalState (exec ρ aktive_zaehlen_body s) = some s'
        ∧ aktive_zaehlen_post s s' (finalValue (exec ρ aktive_zaehlen_body s))

theorem aktive_zaehlen_meets : aktive_zaehlen_meets_statement := by
  unfold aktive_zaehlen_meets_statement
  intro ρ s hwf hpre l_aktive_zaehlen_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [aktive_zaehlen_pre]
  gabbro_auto [aktive_zaehlen_body, aktive_zaehlen_pre, aktive_zaehlen_post, wellFormed, aktive_zaehlen_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aktive_loeschen" aktive_loeschen_body
  ∧ Frame ρ "aktive_loeschen" aktive_loeschen_writes
  ∧ RunsLoopIn ρ "aktive_loeschen#1" aktive_loeschen_loop_1_body "i" 0 16
  ∧ Runs ρ "aktive_zaehlen" aktive_zaehlen_body
  ∧ Frame ρ "aktive_zaehlen" aktive_zaehlen_writes
  ∧ RunsLoopN ρ "aktive_zaehlen#1" aktive_zaehlen_loop_1_body "i" 0 16 16

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_aktive_loeschen_loop_1 : aktive_loeschen_loop_1_keeps_statement)
    (d_aktive_loeschen : aktive_loeschen_meets_statement)
    (d_aktive_zaehlen_loop_1 : aktive_zaehlen_loop_1_keeps_statement)
    (d_aktive_zaehlen : aktive_zaehlen_meets_statement) :
    LoopRule ρ "aktive_loeschen#1" wellFormed aktive_loeschen_loop_1_inv
    ∧ Contract ρ "aktive_loeschen" aktive_loeschen_requires aktive_loeschen_post
    ∧ LoopRuleP ρ "aktive_zaehlen#1" wellFormed aktive_zaehlen_loop_1_inv "#pass"
    ∧ Contract ρ "aktive_zaehlen" aktive_zaehlen_requires aktive_zaehlen_post := by
  obtain ⟨r_aktive_loeschen, fr_aktive_loeschen, rl_aktive_loeschen_loop_1, r_aktive_zaehlen, fr_aktive_zaehlen, rl_aktive_zaehlen_loop_1⟩ := hp
  have l_aktive_loeschen_loop_1 : LoopRule ρ "aktive_loeschen#1" wellFormed aktive_loeschen_loop_1_inv :=
    looprule_of_body_in ρ "aktive_loeschen#1" wellFormed aktive_loeschen_loop_1_inv aktive_loeschen_loop_1_body "i" 0 16 rl_aktive_loeschen_loop_1
      (fun t k hlo hhi hw hi => d_aktive_loeschen_loop_1 ρ t k hlo hhi hw hi)
  have c_aktive_loeschen : Contract ρ "aktive_loeschen" aktive_loeschen_requires aktive_loeschen_post :=
    contract_of_duty ρ "aktive_loeschen" aktive_loeschen_body aktive_loeschen_requires aktive_loeschen_post r_aktive_loeschen
      (fun t ht => d_aktive_loeschen ρ t ht.1 ht.2 l_aktive_loeschen_loop_1)
  have l_aktive_zaehlen_loop_1 : LoopRuleP ρ "aktive_zaehlen#1" wellFormed aktive_zaehlen_loop_1_inv "#pass" :=
    looprule_of_body_p ρ "aktive_zaehlen#1" wellFormed aktive_zaehlen_loop_1_inv aktive_zaehlen_loop_1_body "i" "#pass" 0 16 16 rl_aktive_zaehlen_loop_1
      (fun t k i hlo hhi hplo hphi hpass hw hin => d_aktive_zaehlen_loop_1 ρ t k i hlo hhi hplo hphi hpass hw hin)
  have c_aktive_zaehlen : Contract ρ "aktive_zaehlen" aktive_zaehlen_requires aktive_zaehlen_post :=
    contract_of_duty ρ "aktive_zaehlen" aktive_zaehlen_body aktive_zaehlen_requires aktive_zaehlen_post r_aktive_zaehlen
      (fun t ht => d_aktive_zaehlen ρ t ht.1 ht.2 l_aktive_zaehlen_loop_1)
  exact ⟨l_aktive_loeschen_loop_1, c_aktive_loeschen, l_aktive_zaehlen_loop_1, c_aktive_zaehlen⟩

end GabbroDuty.Duty19Traversierung
