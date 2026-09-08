/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-suchschleife-passfach.gab  total 1  goals 1  refused 0
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

namespace GabbroDuty.DutyProbeSuchschleifePassfach

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  kostenprobe :: loop invariant #1  --  carried by `kostenprobe_loop_1_keeps`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Tafel" _ "belegt" => some .bool
  | .slot "Tafel" _ "schluessel" => some (.intIn 0 4294967295)
  | .slot "Tafel" _ "wert" => some (.intIn 0 4294967295)
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

/-! ### `erster_treffer` -/

def erster_treffer_body : List Stmt :=
  [(.bindName "treffer" (.lit (.int 0))), (.loop "erster_treffer#1" (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295))) [(.ite (.bin .and (.bin .and (.bin .eq (.name "treffer") (.lit (.int 0))) (.place "Tafel" (.name "s") "belegt")) (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]), (.ret (some (.name "treffer")))]

/-- The precondition: the declared shapes and the `requires`. -/
def erster_treffer_pre : Expr :=
  (.hasShape "schluessel" (.intIn 0 4294967295))

def erster_treffer_writes : List String := []

/-- What a caller of `erster_treffer` has to bring: a well-typed world and the precondition. -/
def erster_treffer_requires (t : State) : Prop := wellFormed t ∧ eval t erster_treffer_pre = some (.bool true)

/-- What `erster_treffer` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def erster_treffer_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `kostenprobe` -/

def kostenprobe_body : List Stmt :=
  [(.bindName "summe" (.lit (.int 0))), (.bindName "#pass" (.lit (.int 0))), (.loop "kostenprobe#1" (.bin .and (.hasShape "summe" (.intIn 0 65535)) (.bin .and (.hasShape "#pass" .int) (.bin .le (.name "summe") (.name "#pass")))) [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.place "Tafel" (.name "s") "belegt") [(.bindName "summe" (.bin .add (.name "summe") (.lit (.int 1))))] [])]), (.ret (some (.name "summe")))]

/-- The precondition: the declared shapes and the `requires`. -/
def kostenprobe_pre : Expr :=
  (.lit (.bool true))

def kostenprobe_writes : List String := []

/-- What a caller of `kostenprobe` has to bring: a well-typed world and the precondition. -/
def kostenprobe_requires (t : State) : Prop := wellFormed t ∧ eval t kostenprobe_pre = some (.bool true)

/-- What `kostenprobe` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kostenprobe_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `letzter_treffer` -/

def letzter_treffer_body : List Stmt :=
  [(.bindName "treffer" (.lit (.int 0))), (.loop "letzter_treffer#1" (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295))) [(.ite (.bin .and (.place "Tafel" (.name "s") "belegt") (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]), (.ret (some (.name "treffer")))]

/-- The precondition: the declared shapes and the `requires`. -/
def letzter_treffer_pre : Expr :=
  (.hasShape "schluessel" (.intIn 0 4294967295))

def letzter_treffer_writes : List String := []

/-- What a caller of `letzter_treffer` has to bring: a well-typed world and the precondition. -/
def letzter_treffer_requires (t : State) : Prop := wellFormed t ∧ eval t letzter_treffer_pre = some (.bool true)

/-- What `letzter_treffer` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def letzter_treffer_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `treffer_aendern` -/

def treffer_aendern_body : List Stmt :=
  [(.bindName "treffer" (.lit (.int 0))), (.loop "treffer_aendern#1" (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295))) [(.ite (.bin .and (.bin .and (.bin .eq (.name "treffer") (.lit (.int 0))) (.place "Tafel" (.name "s") "belegt")) (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.assign "Tafel" (.name "s") "belegt" (.lit (.bool false))), (.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]), (.ret (some (.name "treffer")))]

/-- The precondition: the declared shapes and the `requires`. -/
def treffer_aendern_pre : Expr :=
  (.hasShape "schluessel" (.intIn 0 4294967295))

def treffer_aendern_writes : List String := ["Tafel"]

/-- What a caller of `treffer_aendern` has to bring: a well-typed world and the precondition. -/
def treffer_aendern_requires (t : State) : Prop := wellFormed t ∧ eval t treffer_aendern_pre = some (.bool true)

/-- What `treffer_aendern` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def treffer_aendern_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `erster_treffer` -/

/-- Loop `erster_treffer#1` of `erster_treffer`: its body and its invariant (with the shapes of the locals in scope). -/
def erster_treffer_loop_1_inv : Expr :=
  (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295)))

def erster_treffer_loop_1_body : List Stmt :=
  [(.ite (.bin .and (.bin .and (.bin .eq (.name "treffer") (.lit (.int 0))) (.place "Tafel" (.name "s") "belegt")) (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]

/-- **The loop rule of `erster_treffer#1`, as a statement over one pass.** -/
def erster_treffer_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hwf : wellFormed t)
    (hinv : eval t erster_treffer_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ erster_treffer_loop_1_body { t with local' := bindLocal t.local' "s" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' erster_treffer_loop_1_inv = some (.bool true)

theorem erster_treffer_loop_1_keeps : erster_treffer_loop_1_keeps_statement := by
  unfold erster_treffer_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn t "schluessel" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_treffer, e_treffer, lo_treffer, hi_treffer⟩ := shape_intIn t "treffer" _ _ (and_right _ _ _ hinv)
  obtain ⟨n_Tafel_belegt_s, h_Tafel_belegt_s⟩ := WF_bool shapeOf t.world (.slot "Tafel" k "belegt") hwf rfl
  obtain ⟨n_Tafel_schluessel_s, h_Tafel_schluessel_s, lo_Tafel_schluessel_s, hi_Tafel_schluessel_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "schluessel") _ _ hwf rfl
  obtain ⟨n_Tafel_wert_s, h_Tafel_wert_s, lo_Tafel_wert_s, hi_Tafel_wert_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "wert") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [erster_treffer_loop_1_inv, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s]
  gabbro_auto [erster_treffer_loop_1_body, erster_treffer_loop_1_inv, wellFormed, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s, hall] using shapeOf

/-- **The duty of `erster_treffer`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def erster_treffer_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s erster_treffer_pre = some (.bool true))
    -- the rule of loop `erster_treffer#1`
    (l_erster_treffer_loop_1 : LoopRule ρ "erster_treffer#1" wellFormed erster_treffer_loop_1_inv),
    ∃ s', finalState (exec ρ erster_treffer_body s) = some s'
        ∧ erster_treffer_post s s' (finalValue (exec ρ erster_treffer_body s))

theorem erster_treffer_meets : erster_treffer_meets_statement := by
  unfold erster_treffer_meets_statement
  intro ρ s hwf hpre l_erster_treffer_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn s "schluessel" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [erster_treffer_pre, e_schluessel]
  gabbro_auto [erster_treffer_body, erster_treffer_pre, erster_treffer_post, wellFormed, erster_treffer_loop_1_inv, e_schluessel, hall] using shapeOf

/-! ### `kostenprobe` -/

/-- Loop `kostenprobe#1` of `kostenprobe`: its body and its invariant (with the shapes of the locals in scope). -/
def kostenprobe_loop_1_inv : Expr :=
  (.bin .and (.hasShape "summe" (.intIn 0 65535)) (.bin .and (.hasShape "#pass" .int) (.bin .le (.name "summe") (.name "#pass"))))

def kostenprobe_loop_1_body : List Stmt :=
  [(.bindName "#pass" (.bin .add (.name "#pass") (.lit (.int 1)))), (.ite (.place "Tafel" (.name "s") "belegt") [(.bindName "summe" (.bin .add (.name "summe") (.lit (.int 1))))] [])]

/-- **The loop rule of `kostenprobe#1`, as a statement over one pass.** -/
def kostenprobe_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int) (i : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hplo : 0 ≤ i)
    (hphi : i < 16)
    (hpass : t.local' "#pass" = .int i)
    (hwf : wellFormed t)
    (hinv : eval t kostenprobe_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ kostenprobe_loop_1_body { t with local' := bindLocal t.local' "s" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' kostenprobe_loop_1_inv = some (.bool true)
        ∧ t'.local' "#pass" = .int (i + 1)

theorem kostenprobe_loop_1_keeps : kostenprobe_loop_1_keeps_statement := by
  unfold kostenprobe_loop_1_keeps_statement
  intro ρ t k i hlo hhi hplo hphi hpass hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_summe, e_summe, lo_summe, hi_summe⟩ := shape_intIn t "summe" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__pass, e__pass⟩ := shape_int t "#pass" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨n_Tafel_belegt_s, h_Tafel_belegt_s⟩ := WF_bool shapeOf t.world (.slot "Tafel" k "belegt") hwf rfl
  have hall := hinv
  gabbro_simp_at hall [kostenprobe_loop_1_inv, e_summe, e__pass, h_Tafel_belegt_s]
  gabbro_auto [kostenprobe_loop_1_body, kostenprobe_loop_1_inv, wellFormed, e_summe, e__pass, h_Tafel_belegt_s, hall, hpass] using shapeOf

/-- **The duty of `kostenprobe`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kostenprobe_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kostenprobe_pre = some (.bool true))
    -- the rule of loop `kostenprobe#1`
    (l_kostenprobe_loop_1 : LoopRuleP ρ "kostenprobe#1" wellFormed kostenprobe_loop_1_inv "#pass"),
    ∃ s', finalState (exec ρ kostenprobe_body s) = some s'
        ∧ kostenprobe_post s s' (finalValue (exec ρ kostenprobe_body s))

theorem kostenprobe_meets : kostenprobe_meets_statement := by
  unfold kostenprobe_meets_statement
  intro ρ s hwf hpre l_kostenprobe_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [kostenprobe_pre]
  gabbro_auto [kostenprobe_body, kostenprobe_pre, kostenprobe_post, wellFormed, kostenprobe_loop_1_inv, hall] using shapeOf

/-! ### `letzter_treffer` -/

/-- Loop `letzter_treffer#1` of `letzter_treffer`: its body and its invariant (with the shapes of the locals in scope). -/
def letzter_treffer_loop_1_inv : Expr :=
  (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295)))

def letzter_treffer_loop_1_body : List Stmt :=
  [(.ite (.bin .and (.place "Tafel" (.name "s") "belegt") (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]

/-- **The loop rule of `letzter_treffer#1`, as a statement over one pass.** -/
def letzter_treffer_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hwf : wellFormed t)
    (hinv : eval t letzter_treffer_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ letzter_treffer_loop_1_body { t with local' := bindLocal t.local' "s" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' letzter_treffer_loop_1_inv = some (.bool true)

theorem letzter_treffer_loop_1_keeps : letzter_treffer_loop_1_keeps_statement := by
  unfold letzter_treffer_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn t "schluessel" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_treffer, e_treffer, lo_treffer, hi_treffer⟩ := shape_intIn t "treffer" _ _ (and_right _ _ _ hinv)
  obtain ⟨n_Tafel_belegt_s, h_Tafel_belegt_s⟩ := WF_bool shapeOf t.world (.slot "Tafel" k "belegt") hwf rfl
  obtain ⟨n_Tafel_schluessel_s, h_Tafel_schluessel_s, lo_Tafel_schluessel_s, hi_Tafel_schluessel_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "schluessel") _ _ hwf rfl
  obtain ⟨n_Tafel_wert_s, h_Tafel_wert_s, lo_Tafel_wert_s, hi_Tafel_wert_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "wert") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [letzter_treffer_loop_1_inv, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s]
  gabbro_auto [letzter_treffer_loop_1_body, letzter_treffer_loop_1_inv, wellFormed, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s, hall] using shapeOf

/-- **The duty of `letzter_treffer`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def letzter_treffer_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s letzter_treffer_pre = some (.bool true))
    -- the rule of loop `letzter_treffer#1`
    (l_letzter_treffer_loop_1 : LoopRule ρ "letzter_treffer#1" wellFormed letzter_treffer_loop_1_inv),
    ∃ s', finalState (exec ρ letzter_treffer_body s) = some s'
        ∧ letzter_treffer_post s s' (finalValue (exec ρ letzter_treffer_body s))

theorem letzter_treffer_meets : letzter_treffer_meets_statement := by
  unfold letzter_treffer_meets_statement
  intro ρ s hwf hpre l_letzter_treffer_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn s "schluessel" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [letzter_treffer_pre, e_schluessel]
  gabbro_auto [letzter_treffer_body, letzter_treffer_pre, letzter_treffer_post, wellFormed, letzter_treffer_loop_1_inv, e_schluessel, hall] using shapeOf

/-! ### `treffer_aendern` -/

/-- Loop `treffer_aendern#1` of `treffer_aendern`: its body and its invariant (with the shapes of the locals in scope). -/
def treffer_aendern_loop_1_inv : Expr :=
  (.bin .and (.hasShape "schluessel" (.intIn 0 4294967295)) (.hasShape "treffer" (.intIn 0 4294967295)))

def treffer_aendern_loop_1_body : List Stmt :=
  [(.ite (.bin .and (.bin .and (.bin .eq (.name "treffer") (.lit (.int 0))) (.place "Tafel" (.name "s") "belegt")) (.bin .eq (.place "Tafel" (.name "s") "schluessel") (.name "schluessel"))) [(.assign "Tafel" (.name "s") "belegt" (.lit (.bool false))), (.bindName "treffer" (.place "Tafel" (.name "s") "wert"))] [])]

/-- **The loop rule of `treffer_aendern#1`, as a statement over one pass.** -/
def treffer_aendern_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hwf : wellFormed t)
    (hinv : eval t treffer_aendern_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ treffer_aendern_loop_1_body { t with local' := bindLocal t.local' "s" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' treffer_aendern_loop_1_inv = some (.bool true)

theorem treffer_aendern_loop_1_keeps : treffer_aendern_loop_1_keeps_statement := by
  unfold treffer_aendern_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn t "schluessel" _ _ (and_left _ _ _ hinv)
  obtain ⟨w_treffer, e_treffer, lo_treffer, hi_treffer⟩ := shape_intIn t "treffer" _ _ (and_right _ _ _ hinv)
  obtain ⟨n_Tafel_belegt_s, h_Tafel_belegt_s⟩ := WF_bool shapeOf t.world (.slot "Tafel" k "belegt") hwf rfl
  obtain ⟨n_Tafel_schluessel_s, h_Tafel_schluessel_s, lo_Tafel_schluessel_s, hi_Tafel_schluessel_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "schluessel") _ _ hwf rfl
  obtain ⟨n_Tafel_wert_s, h_Tafel_wert_s, lo_Tafel_wert_s, hi_Tafel_wert_s⟩ := WF_intIn shapeOf t.world (.slot "Tafel" k "wert") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [treffer_aendern_loop_1_inv, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s]
  gabbro_auto [treffer_aendern_loop_1_body, treffer_aendern_loop_1_inv, wellFormed, e_schluessel, e_treffer, h_Tafel_belegt_s, h_Tafel_schluessel_s, h_Tafel_wert_s, hall] using shapeOf

/-- **The duty of `treffer_aendern`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def treffer_aendern_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s treffer_aendern_pre = some (.bool true))
    -- the rule of loop `treffer_aendern#1`
    (l_treffer_aendern_loop_1 : LoopRule ρ "treffer_aendern#1" wellFormed treffer_aendern_loop_1_inv),
    ∃ s', finalState (exec ρ treffer_aendern_body s) = some s'
        ∧ treffer_aendern_post s s' (finalValue (exec ρ treffer_aendern_body s))

theorem treffer_aendern_meets : treffer_aendern_meets_statement := by
  unfold treffer_aendern_meets_statement
  intro ρ s hwf hpre l_treffer_aendern_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schluessel, e_schluessel, lo_schluessel, hi_schluessel⟩ := shape_intIn s "schluessel" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [treffer_aendern_pre, e_schluessel]
  gabbro_auto [treffer_aendern_body, treffer_aendern_pre, treffer_aendern_post, wellFormed, treffer_aendern_loop_1_inv, e_schluessel, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "erster_treffer" erster_treffer_body
  ∧ Frame ρ "erster_treffer" erster_treffer_writes
  ∧ RunsLoopIn ρ "erster_treffer#1" erster_treffer_loop_1_body "s" 0 16
  ∧ Runs ρ "kostenprobe" kostenprobe_body
  ∧ Frame ρ "kostenprobe" kostenprobe_writes
  ∧ RunsLoopN ρ "kostenprobe#1" kostenprobe_loop_1_body "s" 0 16 16
  ∧ Runs ρ "letzter_treffer" letzter_treffer_body
  ∧ Frame ρ "letzter_treffer" letzter_treffer_writes
  ∧ RunsLoopIn ρ "letzter_treffer#1" letzter_treffer_loop_1_body "s" 0 16
  ∧ Runs ρ "treffer_aendern" treffer_aendern_body
  ∧ Frame ρ "treffer_aendern" treffer_aendern_writes
  ∧ RunsLoopIn ρ "treffer_aendern#1" treffer_aendern_loop_1_body "s" 0 16

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_erster_treffer_loop_1 : erster_treffer_loop_1_keeps_statement)
    (d_erster_treffer : erster_treffer_meets_statement)
    (d_kostenprobe_loop_1 : kostenprobe_loop_1_keeps_statement)
    (d_kostenprobe : kostenprobe_meets_statement)
    (d_letzter_treffer_loop_1 : letzter_treffer_loop_1_keeps_statement)
    (d_letzter_treffer : letzter_treffer_meets_statement)
    (d_treffer_aendern_loop_1 : treffer_aendern_loop_1_keeps_statement)
    (d_treffer_aendern : treffer_aendern_meets_statement) :
    LoopRule ρ "erster_treffer#1" wellFormed erster_treffer_loop_1_inv
    ∧ Contract ρ "erster_treffer" erster_treffer_requires erster_treffer_post
    ∧ LoopRuleP ρ "kostenprobe#1" wellFormed kostenprobe_loop_1_inv "#pass"
    ∧ Contract ρ "kostenprobe" kostenprobe_requires kostenprobe_post
    ∧ LoopRule ρ "letzter_treffer#1" wellFormed letzter_treffer_loop_1_inv
    ∧ Contract ρ "letzter_treffer" letzter_treffer_requires letzter_treffer_post
    ∧ LoopRule ρ "treffer_aendern#1" wellFormed treffer_aendern_loop_1_inv
    ∧ Contract ρ "treffer_aendern" treffer_aendern_requires treffer_aendern_post := by
  obtain ⟨r_erster_treffer, fr_erster_treffer, rl_erster_treffer_loop_1, r_kostenprobe, fr_kostenprobe, rl_kostenprobe_loop_1, r_letzter_treffer, fr_letzter_treffer, rl_letzter_treffer_loop_1, r_treffer_aendern, fr_treffer_aendern, rl_treffer_aendern_loop_1⟩ := hp
  have l_erster_treffer_loop_1 : LoopRule ρ "erster_treffer#1" wellFormed erster_treffer_loop_1_inv :=
    looprule_of_body_in ρ "erster_treffer#1" wellFormed erster_treffer_loop_1_inv erster_treffer_loop_1_body "s" 0 16 rl_erster_treffer_loop_1
      (fun t k hlo hhi hw hi => d_erster_treffer_loop_1 ρ t k hlo hhi hw hi)
  have c_erster_treffer : Contract ρ "erster_treffer" erster_treffer_requires erster_treffer_post :=
    contract_of_duty ρ "erster_treffer" erster_treffer_body erster_treffer_requires erster_treffer_post r_erster_treffer
      (fun t ht => d_erster_treffer ρ t ht.1 ht.2 l_erster_treffer_loop_1)
  have l_kostenprobe_loop_1 : LoopRuleP ρ "kostenprobe#1" wellFormed kostenprobe_loop_1_inv "#pass" :=
    looprule_of_body_p ρ "kostenprobe#1" wellFormed kostenprobe_loop_1_inv kostenprobe_loop_1_body "s" "#pass" 0 16 16 rl_kostenprobe_loop_1
      (fun t k i hlo hhi hplo hphi hpass hw hin => d_kostenprobe_loop_1 ρ t k i hlo hhi hplo hphi hpass hw hin)
  have c_kostenprobe : Contract ρ "kostenprobe" kostenprobe_requires kostenprobe_post :=
    contract_of_duty ρ "kostenprobe" kostenprobe_body kostenprobe_requires kostenprobe_post r_kostenprobe
      (fun t ht => d_kostenprobe ρ t ht.1 ht.2 l_kostenprobe_loop_1)
  have l_letzter_treffer_loop_1 : LoopRule ρ "letzter_treffer#1" wellFormed letzter_treffer_loop_1_inv :=
    looprule_of_body_in ρ "letzter_treffer#1" wellFormed letzter_treffer_loop_1_inv letzter_treffer_loop_1_body "s" 0 16 rl_letzter_treffer_loop_1
      (fun t k hlo hhi hw hi => d_letzter_treffer_loop_1 ρ t k hlo hhi hw hi)
  have c_letzter_treffer : Contract ρ "letzter_treffer" letzter_treffer_requires letzter_treffer_post :=
    contract_of_duty ρ "letzter_treffer" letzter_treffer_body letzter_treffer_requires letzter_treffer_post r_letzter_treffer
      (fun t ht => d_letzter_treffer ρ t ht.1 ht.2 l_letzter_treffer_loop_1)
  have l_treffer_aendern_loop_1 : LoopRule ρ "treffer_aendern#1" wellFormed treffer_aendern_loop_1_inv :=
    looprule_of_body_in ρ "treffer_aendern#1" wellFormed treffer_aendern_loop_1_inv treffer_aendern_loop_1_body "s" 0 16 rl_treffer_aendern_loop_1
      (fun t k hlo hhi hw hi => d_treffer_aendern_loop_1 ρ t k hlo hhi hw hi)
  have c_treffer_aendern : Contract ρ "treffer_aendern" treffer_aendern_requires treffer_aendern_post :=
    contract_of_duty ρ "treffer_aendern" treffer_aendern_body treffer_aendern_requires treffer_aendern_post r_treffer_aendern
      (fun t ht => d_treffer_aendern ρ t ht.1 ht.2 l_treffer_aendern_loop_1)
  exact ⟨l_erster_treffer_loop_1, c_erster_treffer, l_kostenprobe_loop_1, c_kostenprobe, l_letzter_treffer_loop_1, c_letzter_treffer, l_treffer_aendern_loop_1, c_treffer_aendern⟩

end GabbroDuty.DutyProbeSuchschleifePassfach
