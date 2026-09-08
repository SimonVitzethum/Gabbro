/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/04-schleifen.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.Duty04Schleifen

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Warteschlange" _ "aktiv" => some .bool
  | .slot "Warteschlange" _ "frist" => some (.intIn 1 1000000)
  | .slot "Warteschlange" _ "naechst" => some .opt
  | .field "Manifest" "saetze" => some (.intIn 0 4294967295)
  | .field "Manifest" "laenge" => some (.intIn 0 4294967295)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `abschaltung_angefordert` -- a foreign body: its contract is an assumption. -/
def abschaltung_angefordert_pre : Expr :=
  (.lit (.bool true))

def abschaltung_angefordert_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ b, r = some (.bool b))

def abschaltung_angefordert_writes : List String := []

def abschaltung_angefordert_requires (t : State) : Prop := wellFormed t ∧ eval t abschaltung_angefordert_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post
  ∧ Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes

/-! ## The routines: body and contract -/

/-! ### `auf_quittung_warten` -/

def auf_quittung_warten_body : List Stmt :=
  [(.loop "auf_quittung_warten#1" (.lit (.bool true)) []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def auf_quittung_warten_pre : Expr :=
  (.lit (.bool true))

def auf_quittung_warten_writes : List String := []

/-- What a caller of `auf_quittung_warten` has to bring: a well-typed world and the precondition. -/
def auf_quittung_warten_requires (t : State) : Prop := wellFormed t ∧ eval t auf_quittung_warten_pre = some (.bool true)

/-- What `auf_quittung_warten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def auf_quittung_warten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `dienstschleife` -/

def dienstschleife_body : List Stmt :=
  [(.loop "dienstschleife#1" (.lit (.bool true)) [(.loop "dienstschleife#2" (.lit (.bool true)) [(.locked "PLANER" [(.ite (.place "Warteschlange" (.name "e") "aktiv") [(.assign "Warteschlange" (.name "e") "aktiv" (.lit (.bool false)))] [])])]), (.bindCall "#m1" "abschaltung_angefordert" [] [] (.lit (.bool true))), (.ite (.name "#m1") [.leave] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def dienstschleife_pre : Expr :=
  (.lit (.bool true))

def dienstschleife_writes : List String := ["Warteschlange"]

/-- What a caller of `dienstschleife` has to bring: a well-typed world and the precondition. -/
def dienstschleife_requires (t : State) : Prop := wellFormed t ∧ eval t dienstschleife_pre = some (.bool true)

/-- What `dienstschleife` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def dienstschleife_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `faellige_wecken` -/

def faellige_wecken_body : List Stmt :=
  [(.loop "faellige_wecken#1" (.hasShape "jetzt" (.intIn 1 1000000)) [(.ite (.bin .le (.place "Warteschlange" (.name "eintrag") "frist") (.name "jetzt")) [(.assign "Warteschlange" (.name "eintrag") "aktiv" (.lit (.bool true)))] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def faellige_wecken_pre : Expr :=
  (.bin .and (.hasShape "jetzt" (.intIn 1 1000000)) (.lit (.bool true)))

def faellige_wecken_writes : List String := ["Warteschlange"]

/-- What a caller of `faellige_wecken` has to bring: a well-typed world and the precondition. -/
def faellige_wecken_requires (t : State) : Prop := wellFormed t ∧ eval t faellige_wecken_pre = some (.bool true)

/-- What `faellige_wecken` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def faellige_wecken_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `manifest_pruefen` -/

def manifest_pruefen_body : List Stmt :=
  [(.loop "manifest_pruefen#1" (.lit (.bool true)) [.leave]), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def manifest_pruefen_pre : Expr :=
  (.lit (.bool true))

def manifest_pruefen_writes : List String := []

/-- What a caller of `manifest_pruefen` has to bring: a well-typed world and the precondition. -/
def manifest_pruefen_requires (t : State) : Prop := wellFormed t ∧ eval t manifest_pruefen_pre = some (.bool true)

/-- What `manifest_pruefen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def manifest_pruefen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `auf_quittung_warten` -/

/-- Loop `auf_quittung_warten#1` of `auf_quittung_warten`: its body and its invariant (with the shapes of the locals in scope). -/
def auf_quittung_warten_loop_1_inv : Expr :=
  (.lit (.bool true))

def auf_quittung_warten_loop_1_body : List Stmt :=
  []

/-- **The loop rule of `auf_quittung_warten#1`, as a statement over one pass.** -/
def auf_quittung_warten_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t auf_quittung_warten_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ auf_quittung_warten_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' auf_quittung_warten_loop_1_inv = some (.bool true)

theorem auf_quittung_warten_loop_1_keeps : auf_quittung_warten_loop_1_keeps_statement := by
  unfold auf_quittung_warten_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [auf_quittung_warten_loop_1_inv]
  gabbro_auto [auf_quittung_warten_loop_1_body, auf_quittung_warten_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `auf_quittung_warten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def auf_quittung_warten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s auf_quittung_warten_pre = some (.bool true))
    -- the rule of loop `auf_quittung_warten#1`
    (l_auf_quittung_warten_loop_1 : LoopRule ρ "auf_quittung_warten#1" wellFormed auf_quittung_warten_loop_1_inv),
    ∃ s', finalState (exec ρ auf_quittung_warten_body s) = some s'
        ∧ auf_quittung_warten_post s s' (finalValue (exec ρ auf_quittung_warten_body s))

theorem auf_quittung_warten_meets : auf_quittung_warten_meets_statement := by
  unfold auf_quittung_warten_meets_statement
  intro ρ s hwf hpre l_auf_quittung_warten_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [auf_quittung_warten_pre]
  gabbro_auto [auf_quittung_warten_body, auf_quittung_warten_pre, auf_quittung_warten_post, wellFormed, auf_quittung_warten_loop_1_inv, hall] using shapeOf

/-! ### `dienstschleife` -/

/-- Loop `dienstschleife#2` of `dienstschleife`: its body and its invariant (with the shapes of the locals in scope). -/
def dienstschleife_loop_2_inv : Expr :=
  (.lit (.bool true))

def dienstschleife_loop_2_body : List Stmt :=
  [(.locked "PLANER" [(.ite (.place "Warteschlange" (.name "e") "aktiv") [(.assign "Warteschlange" (.name "e") "aktiv" (.lit (.bool false)))] [])])]

/-- **The loop rule of `dienstschleife#2`, as a statement over one pass.** -/
def dienstschleife_loop_2_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 1024)
    (hwf : wellFormed t)
    (hinv : eval t dienstschleife_loop_2_inv = some (.bool true)),
    ∃ t', finalState (exec ρ dienstschleife_loop_2_body { t with local' := bindLocal t.local' "e" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' dienstschleife_loop_2_inv = some (.bool true)

theorem dienstschleife_loop_2_keeps : dienstschleife_loop_2_keeps_statement := by
  unfold dienstschleife_loop_2_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_Warteschlange_aktiv_e, h_Warteschlange_aktiv_e⟩ := WF_bool shapeOf t.world (.slot "Warteschlange" k "aktiv") hwf rfl
  have hall := hinv
  gabbro_simp_at hall [dienstschleife_loop_2_inv, h_Warteschlange_aktiv_e]
  gabbro_auto [dienstschleife_loop_2_body, dienstschleife_loop_2_inv, wellFormed, h_Warteschlange_aktiv_e, hall] using shapeOf

/-- Loop `dienstschleife#1` of `dienstschleife`: its body and its invariant (with the shapes of the locals in scope). -/
def dienstschleife_loop_1_inv : Expr :=
  (.lit (.bool true))

def dienstschleife_loop_1_body : List Stmt :=
  [(.loop "dienstschleife#2" (.lit (.bool true)) [(.locked "PLANER" [(.ite (.place "Warteschlange" (.name "e") "aktiv") [(.assign "Warteschlange" (.name "e") "aktiv" (.lit (.bool false)))] [])])]), (.bindCall "#m1" "abschaltung_angefordert" [] [] (.lit (.bool true))), (.ite (.name "#m1") [.leave] [])]

/-- **The loop rule of `dienstschleife#1`, as a statement over one pass.** -/
def dienstschleife_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t dienstschleife_loop_1_inv = some (.bool true))
    (c_abschaltung_angefordert : Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post)
    (fr_abschaltung_angefordert : Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes)
    (l_dienstschleife_loop_2 : LoopRule ρ "dienstschleife#2" wellFormed dienstschleife_loop_2_inv),
    ∃ t', finalState (exec ρ dienstschleife_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' dienstschleife_loop_1_inv = some (.bool true)

theorem dienstschleife_loop_1_keeps : dienstschleife_loop_1_keeps_statement := by
  unfold dienstschleife_loop_1_keeps_statement
  intro ρ t k hwf hinv c_abschaltung_angefordert fr_abschaltung_angefordert l_dienstschleife_loop_2
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [dienstschleife_loop_1_inv]
  gabbro_auto [dienstschleife_loop_1_body, dienstschleife_loop_1_inv, wellFormed, abschaltung_angefordert_pre, abschaltung_angefordert_requires, abschaltung_angefordert_post, abschaltung_angefordert_writes, Frame_read _ _ _ fr_abschaltung_angefordert, dienstschleife_loop_2_inv, hall] using shapeOf

/-- **The duty of `dienstschleife`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def dienstschleife_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s dienstschleife_pre = some (.bool true))
    -- the contract of `abschaltung_angefordert`
    (c_abschaltung_angefordert : Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post)
    -- the frame of `abschaltung_angefordert`
    (fr_abschaltung_angefordert : Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes)
    -- the rule of loop `dienstschleife#2`
    (l_dienstschleife_loop_2 : LoopRule ρ "dienstschleife#2" wellFormed dienstschleife_loop_2_inv)
    -- the rule of loop `dienstschleife#1`
    (l_dienstschleife_loop_1 : LoopRule ρ "dienstschleife#1" wellFormed dienstschleife_loop_1_inv),
    ∃ s', finalState (exec ρ dienstschleife_body s) = some s'
        ∧ dienstschleife_post s s' (finalValue (exec ρ dienstschleife_body s))

theorem dienstschleife_meets : dienstschleife_meets_statement := by
  unfold dienstschleife_meets_statement
  intro ρ s hwf hpre c_abschaltung_angefordert fr_abschaltung_angefordert l_dienstschleife_loop_2 l_dienstschleife_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [dienstschleife_pre]
  gabbro_auto [dienstschleife_body, dienstschleife_pre, dienstschleife_post, wellFormed, abschaltung_angefordert_pre, abschaltung_angefordert_requires, abschaltung_angefordert_post, abschaltung_angefordert_writes, Frame_read _ _ _ fr_abschaltung_angefordert, dienstschleife_loop_2_inv, dienstschleife_loop_1_inv, hall] using shapeOf

/-! ### `faellige_wecken` -/

/-- Loop `faellige_wecken#1` of `faellige_wecken`: its body and its invariant (with the shapes of the locals in scope). -/
def faellige_wecken_loop_1_inv : Expr :=
  (.hasShape "jetzt" (.intIn 1 1000000))

def faellige_wecken_loop_1_body : List Stmt :=
  [(.ite (.bin .le (.place "Warteschlange" (.name "eintrag") "frist") (.name "jetzt")) [(.assign "Warteschlange" (.name "eintrag") "aktiv" (.lit (.bool true)))] [])]

/-- **The loop rule of `faellige_wecken#1`, as a statement over one pass.** -/
def faellige_wecken_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 1024)
    (hwf : wellFormed t)
    (hinv : eval t faellige_wecken_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ faellige_wecken_loop_1_body { t with local' := bindLocal t.local' "eintrag" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' faellige_wecken_loop_1_inv = some (.bool true)

theorem faellige_wecken_loop_1_keeps : faellige_wecken_loop_1_keeps_statement := by
  unfold faellige_wecken_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_jetzt, e_jetzt, lo_jetzt, hi_jetzt⟩ := shape_intIn t "jetzt" _ _ hinv
  obtain ⟨n_Warteschlange_frist_eintrag, h_Warteschlange_frist_eintrag, lo_Warteschlange_frist_eintrag, hi_Warteschlange_frist_eintrag⟩ := WF_intIn shapeOf t.world (.slot "Warteschlange" k "frist") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [faellige_wecken_loop_1_inv, e_jetzt, h_Warteschlange_frist_eintrag]
  gabbro_auto [faellige_wecken_loop_1_body, faellige_wecken_loop_1_inv, wellFormed, e_jetzt, h_Warteschlange_frist_eintrag, hall] using shapeOf

/-- **The duty of `faellige_wecken`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def faellige_wecken_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s faellige_wecken_pre = some (.bool true))
    -- the rule of loop `faellige_wecken#1`
    (l_faellige_wecken_loop_1 : LoopRule ρ "faellige_wecken#1" wellFormed faellige_wecken_loop_1_inv),
    ∃ s', finalState (exec ρ faellige_wecken_body s) = some s'
        ∧ faellige_wecken_post s s' (finalValue (exec ρ faellige_wecken_body s))

theorem faellige_wecken_meets : faellige_wecken_meets_statement := by
  unfold faellige_wecken_meets_statement
  intro ρ s hwf hpre l_faellige_wecken_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_jetzt, e_jetzt, lo_jetzt, hi_jetzt⟩ := shape_intIn s "jetzt" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [faellige_wecken_pre, e_jetzt]
  gabbro_auto [faellige_wecken_body, faellige_wecken_pre, faellige_wecken_post, wellFormed, faellige_wecken_loop_1_inv, e_jetzt, hall] using shapeOf

/-! ### `manifest_pruefen` -/

/-- Loop `manifest_pruefen#1` of `manifest_pruefen`: its body and its invariant (with the shapes of the locals in scope). -/
def manifest_pruefen_loop_1_inv : Expr :=
  (.lit (.bool true))

def manifest_pruefen_loop_1_body : List Stmt :=
  [.leave]

/-- **The loop rule of `manifest_pruefen#1`, as a statement over one pass.** -/
def manifest_pruefen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t manifest_pruefen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ manifest_pruefen_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' manifest_pruefen_loop_1_inv = some (.bool true)

theorem manifest_pruefen_loop_1_keeps : manifest_pruefen_loop_1_keeps_statement := by
  unfold manifest_pruefen_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [manifest_pruefen_loop_1_inv]
  gabbro_auto [manifest_pruefen_loop_1_body, manifest_pruefen_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `manifest_pruefen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def manifest_pruefen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s manifest_pruefen_pre = some (.bool true))
    -- the rule of loop `manifest_pruefen#1`
    (l_manifest_pruefen_loop_1 : LoopRule ρ "manifest_pruefen#1" wellFormed manifest_pruefen_loop_1_inv),
    ∃ s', finalState (exec ρ manifest_pruefen_body s) = some s'
        ∧ manifest_pruefen_post s s' (finalValue (exec ρ manifest_pruefen_body s))

theorem manifest_pruefen_meets : manifest_pruefen_meets_statement := by
  unfold manifest_pruefen_meets_statement
  intro ρ s hwf hpre l_manifest_pruefen_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [manifest_pruefen_pre]
  gabbro_auto [manifest_pruefen_body, manifest_pruefen_pre, manifest_pruefen_post, wellFormed, manifest_pruefen_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "auf_quittung_warten" auf_quittung_warten_body
  ∧ Frame ρ "auf_quittung_warten" auf_quittung_warten_writes
  ∧ RunsLoop ρ "auf_quittung_warten#1" auf_quittung_warten_loop_1_body "#pass"
  ∧ Runs ρ "dienstschleife" dienstschleife_body
  ∧ Frame ρ "dienstschleife" dienstschleife_writes
  ∧ RunsLoopIn ρ "dienstschleife#2" dienstschleife_loop_2_body "e" 0 1024
  ∧ RunsLoop ρ "dienstschleife#1" dienstschleife_loop_1_body "#pass"
  ∧ Runs ρ "faellige_wecken" faellige_wecken_body
  ∧ Frame ρ "faellige_wecken" faellige_wecken_writes
  ∧ RunsLoopIn ρ "faellige_wecken#1" faellige_wecken_loop_1_body "eintrag" 0 1024
  ∧ Runs ρ "manifest_pruefen" manifest_pruefen_body
  ∧ Frame ρ "manifest_pruefen" manifest_pruefen_writes
  ∧ RunsLoop ρ "manifest_pruefen#1" manifest_pruefen_loop_1_body "#pass"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_auf_quittung_warten_loop_1 : auf_quittung_warten_loop_1_keeps_statement)
    (d_auf_quittung_warten : auf_quittung_warten_meets_statement)
    (d_dienstschleife_loop_2 : dienstschleife_loop_2_keeps_statement)
    (d_dienstschleife_loop_1 : dienstschleife_loop_1_keeps_statement)
    (d_dienstschleife : dienstschleife_meets_statement)
    (d_faellige_wecken_loop_1 : faellige_wecken_loop_1_keeps_statement)
    (d_faellige_wecken : faellige_wecken_meets_statement)
    (d_manifest_pruefen_loop_1 : manifest_pruefen_loop_1_keeps_statement)
    (d_manifest_pruefen : manifest_pruefen_meets_statement) :
    LoopRule ρ "auf_quittung_warten#1" wellFormed auf_quittung_warten_loop_1_inv
    ∧ Contract ρ "auf_quittung_warten" auf_quittung_warten_requires auf_quittung_warten_post
    ∧ LoopRule ρ "dienstschleife#2" wellFormed dienstschleife_loop_2_inv
    ∧ LoopRule ρ "dienstschleife#1" wellFormed dienstschleife_loop_1_inv
    ∧ Contract ρ "dienstschleife" dienstschleife_requires dienstschleife_post
    ∧ LoopRule ρ "faellige_wecken#1" wellFormed faellige_wecken_loop_1_inv
    ∧ Contract ρ "faellige_wecken" faellige_wecken_requires faellige_wecken_post
    ∧ LoopRule ρ "manifest_pruefen#1" wellFormed manifest_pruefen_loop_1_inv
    ∧ Contract ρ "manifest_pruefen" manifest_pruefen_requires manifest_pruefen_post := by
  obtain ⟨r_auf_quittung_warten, fr_auf_quittung_warten, rl_auf_quittung_warten_loop_1, r_dienstschleife, fr_dienstschleife, rl_dienstschleife_loop_2, rl_dienstschleife_loop_1, r_faellige_wecken, fr_faellige_wecken, rl_faellige_wecken_loop_1, r_manifest_pruefen, fr_manifest_pruefen, rl_manifest_pruefen_loop_1⟩ := hp
  obtain ⟨c_abschaltung_angefordert, fr_abschaltung_angefordert⟩ := ha
  have l_auf_quittung_warten_loop_1 : LoopRule ρ "auf_quittung_warten#1" wellFormed auf_quittung_warten_loop_1_inv :=
    looprule_of_body ρ "auf_quittung_warten#1" wellFormed auf_quittung_warten_loop_1_inv auf_quittung_warten_loop_1_body "#pass" rl_auf_quittung_warten_loop_1
      (fun t k hw hi => d_auf_quittung_warten_loop_1 ρ t k hw hi)
  have c_auf_quittung_warten : Contract ρ "auf_quittung_warten" auf_quittung_warten_requires auf_quittung_warten_post :=
    contract_of_duty ρ "auf_quittung_warten" auf_quittung_warten_body auf_quittung_warten_requires auf_quittung_warten_post r_auf_quittung_warten
      (fun t ht => d_auf_quittung_warten ρ t ht.1 ht.2 l_auf_quittung_warten_loop_1)
  have l_dienstschleife_loop_2 : LoopRule ρ "dienstschleife#2" wellFormed dienstschleife_loop_2_inv :=
    looprule_of_body_in ρ "dienstschleife#2" wellFormed dienstschleife_loop_2_inv dienstschleife_loop_2_body "e" 0 1024 rl_dienstschleife_loop_2
      (fun t k hlo hhi hw hi => d_dienstschleife_loop_2 ρ t k hlo hhi hw hi)
  have l_dienstschleife_loop_1 : LoopRule ρ "dienstschleife#1" wellFormed dienstschleife_loop_1_inv :=
    looprule_of_body ρ "dienstschleife#1" wellFormed dienstschleife_loop_1_inv dienstschleife_loop_1_body "#pass" rl_dienstschleife_loop_1
      (fun t k hw hi => d_dienstschleife_loop_1 ρ t k hw hi c_abschaltung_angefordert fr_abschaltung_angefordert l_dienstschleife_loop_2)
  have c_dienstschleife : Contract ρ "dienstschleife" dienstschleife_requires dienstschleife_post :=
    contract_of_duty ρ "dienstschleife" dienstschleife_body dienstschleife_requires dienstschleife_post r_dienstschleife
      (fun t ht => d_dienstschleife ρ t ht.1 ht.2 c_abschaltung_angefordert fr_abschaltung_angefordert l_dienstschleife_loop_2 l_dienstschleife_loop_1)
  have l_faellige_wecken_loop_1 : LoopRule ρ "faellige_wecken#1" wellFormed faellige_wecken_loop_1_inv :=
    looprule_of_body_in ρ "faellige_wecken#1" wellFormed faellige_wecken_loop_1_inv faellige_wecken_loop_1_body "eintrag" 0 1024 rl_faellige_wecken_loop_1
      (fun t k hlo hhi hw hi => d_faellige_wecken_loop_1 ρ t k hlo hhi hw hi)
  have c_faellige_wecken : Contract ρ "faellige_wecken" faellige_wecken_requires faellige_wecken_post :=
    contract_of_duty ρ "faellige_wecken" faellige_wecken_body faellige_wecken_requires faellige_wecken_post r_faellige_wecken
      (fun t ht => d_faellige_wecken ρ t ht.1 ht.2 l_faellige_wecken_loop_1)
  have l_manifest_pruefen_loop_1 : LoopRule ρ "manifest_pruefen#1" wellFormed manifest_pruefen_loop_1_inv :=
    looprule_of_body ρ "manifest_pruefen#1" wellFormed manifest_pruefen_loop_1_inv manifest_pruefen_loop_1_body "#pass" rl_manifest_pruefen_loop_1
      (fun t k hw hi => d_manifest_pruefen_loop_1 ρ t k hw hi)
  have c_manifest_pruefen : Contract ρ "manifest_pruefen" manifest_pruefen_requires manifest_pruefen_post :=
    contract_of_duty ρ "manifest_pruefen" manifest_pruefen_body manifest_pruefen_requires manifest_pruefen_post r_manifest_pruefen
      (fun t ht => d_manifest_pruefen ρ t ht.1 ht.2 l_manifest_pruefen_loop_1)
  exact ⟨l_auf_quittung_warten_loop_1, c_auf_quittung_warten, l_dienstschleife_loop_2, l_dienstschleife_loop_1, c_dienstschleife, l_faellige_wecken_loop_1, c_faellige_wecken, l_manifest_pruefen_loop_1, c_manifest_pruefen⟩

end GabbroDuty.Duty04Schleifen