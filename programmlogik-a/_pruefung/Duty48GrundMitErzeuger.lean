/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/48-grund-mit-erzeuger.gab  total 2  goals 2  refused 0
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
    names are two different objects (the alias passes carry it); the
    declared `effects` list is complete (`E008`/`E010`, `Frame` in `Program`);
    the initial world satisfies every invariant (a statement about `boot`,
    booked by no register); and everything `Assumed` names.
-/

import Gabbro.Body

set_option autoImplicit false

open Gabbro.Body

namespace GabbroDuty.Duty48GrundMitErzeuger

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  V  aufraeumen :: platz_freigeben requires #1  --  carried by `aufraeumen_meets`
  duty_2  V  nur_unbelegte_zaehlen :: platz_freigeben requires #1  --  carried by `nur_unbelegte_zaehlen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Griffe" _ "zaehler" => some .int
  | .slot "Griffe" _ "belegt" => some .bool
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `buchfuehrung_kaputt` -- a foreign body: its contract is an assumption. -/
def buchfuehrung_kaputt_pre : Expr :=
  (.lit (.bool true))

def buchfuehrung_kaputt_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def buchfuehrung_kaputt_writes : List String := []

def buchfuehrung_kaputt_requires (t : State) : Prop := wellFormed t ∧ eval t buchfuehrung_kaputt_pre = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "buchfuehrung_kaputt" buchfuehrung_kaputt_requires buchfuehrung_kaputt_post
  ∧ Frame ρ "buchfuehrung_kaputt" buchfuehrung_kaputt_writes

/-! ## The routines: body, contract, duty -/

/-! ### `aufraeumen` -/

def aufraeumen_body : List Stmt :=
  [(.locked "GRIFFE" [(.bindCallElse "n" "platz_freigeben" ["g", "s"] [(.name "g"), (.name "s")] (.bin .and (.hasShape "s" .int) (.lit (.bool true))) "e" [(.onReason (.name "e") [("Unbelegt", [(.ret (some (.lit (.int 0))))]), ("Buchfuehrung", [(.call "buchfuehrung_kaputt" [] [] (.lit (.bool true)))])])]), (.ret (some (.name "n")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def aufraeumen_pre : Expr :=
  (.hasShape "s" .int)

def aufraeumen_writes : List String := ["Griffe"]

/-- What a caller of `aufraeumen` has to bring: a well-typed world and the precondition. -/
def aufraeumen_requires (t : State) : Prop := wellFormed t ∧ eval t aufraeumen_pre = some (.bool true)

/-- What `aufraeumen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aufraeumen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `aufraeumen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aufraeumen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aufraeumen_pre = some (.bool true))
    -- the contract of `buchfuehrung_kaputt`
    (c_buchfuehrung_kaputt : Contract ρ "buchfuehrung_kaputt" buchfuehrung_kaputt_requires buchfuehrung_kaputt_post)
    -- the frame of `buchfuehrung_kaputt`
    (fr_buchfuehrung_kaputt : Frame ρ "buchfuehrung_kaputt" buchfuehrung_kaputt_writes)
    -- the contract of `platz_freigeben`
    (c_platz_freigeben : Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post)
    -- the frame of `platz_freigeben`
    (fr_platz_freigeben : Frame ρ "platz_freigeben" platz_freigeben_writes),
    ∃ s', finalState (exec ρ aufraeumen_body s) = some s'
        ∧ aufraeumen_post s s' (finalValue (exec ρ aufraeumen_body s))

theorem aufraeumen_meets : aufraeumen_meets_statement := by
  unfold aufraeumen_meets_statement
  intro ρ s hwf hpre c_buchfuehrung_kaputt fr_buchfuehrung_kaputt c_platz_freigeben fr_platz_freigeben
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" hpre
  gabbro_auto [aufraeumen_body, aufraeumen_pre, aufraeumen_post, wellFormed, buchfuehrung_kaputt_pre, buchfuehrung_kaputt_requires, buchfuehrung_kaputt_post, buchfuehrung_kaputt_writes, Frame_read _ _ _ fr_buchfuehrung_kaputt, platz_freigeben_pre, platz_freigeben_requires, platz_freigeben_post, platz_freigeben_writes, Frame_read _ _ _ fr_platz_freigeben, e_s] using shapeOf

/-! ### `nur_unbelegte_zaehlen` -/

def nur_unbelegte_zaehlen_body : List Stmt :=
  [(.locked "GRIFFE" [(.bindCallElse "n" "platz_freigeben" ["g", "s"] [(.name "g"), (.name "s")] (.bin .and (.hasShape "s" .int) (.lit (.bool true))) "e" [(.ite (.bin .eq (.name "e") (.lit (.reason "Unbelegt"))) [(.ret (some (.lit (.int 1))))] []), (.ret (some (.lit (.int 0))))]), (.ret (some (.name "n")))])]

/-- The precondition: the declared shapes and the `requires`. -/
def nur_unbelegte_zaehlen_pre : Expr :=
  (.hasShape "s" .int)

def nur_unbelegte_zaehlen_writes : List String := ["Griffe"]

/-- What a caller of `nur_unbelegte_zaehlen` has to bring: a well-typed world and the precondition. -/
def nur_unbelegte_zaehlen_requires (t : State) : Prop := wellFormed t ∧ eval t nur_unbelegte_zaehlen_pre = some (.bool true)

/-- What `nur_unbelegte_zaehlen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def nur_unbelegte_zaehlen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `nur_unbelegte_zaehlen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def nur_unbelegte_zaehlen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s nur_unbelegte_zaehlen_pre = some (.bool true))
    -- the contract of `platz_freigeben`
    (c_platz_freigeben : Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post)
    -- the frame of `platz_freigeben`
    (fr_platz_freigeben : Frame ρ "platz_freigeben" platz_freigeben_writes),
    ∃ s', finalState (exec ρ nur_unbelegte_zaehlen_body s) = some s'
        ∧ nur_unbelegte_zaehlen_post s s' (finalValue (exec ρ nur_unbelegte_zaehlen_body s))

theorem nur_unbelegte_zaehlen_meets : nur_unbelegte_zaehlen_meets_statement := by
  unfold nur_unbelegte_zaehlen_meets_statement
  intro ρ s hwf hpre c_platz_freigeben fr_platz_freigeben
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" hpre
  gabbro_auto [nur_unbelegte_zaehlen_body, nur_unbelegte_zaehlen_pre, nur_unbelegte_zaehlen_post, wellFormed, platz_freigeben_pre, platz_freigeben_requires, platz_freigeben_post, platz_freigeben_writes, Frame_read _ _ _ fr_platz_freigeben, e_s] using shapeOf

/-! ### `platz_freigeben` -/

def platz_freigeben_body : List Stmt :=
  [(.ite (.un .not (.place "Griffe" (.name "s") "belegt")) [(.ret (some (.lit (.reason "Unbelegt"))))] []), (.ite (.bin .and (.bin .ge (.place "Griffe" (.name "s") "zaehler") (.lit (.int 1))) (.bin .le (.place "Griffe" (.name "s") "zaehler") (.lit (.int 65534)))) [] [(.ret (some (.lit (.reason "Buchfuehrung"))))]), (.assign "Griffe" (.name "s") "zaehler" (.bin .sub (.place "Griffe" (.name "s") "zaehler") (.lit (.int 1)))), (.ite (.bin .eq (.place "Griffe" (.name "s") "zaehler") (.lit (.int 0))) [(.assign "Griffe" (.name "s") "belegt" (.lit (.bool false)))] []), (.ret (some (.place "Griffe" (.name "s") "zaehler")))]

/-- The precondition: the declared shapes and the `requires`. -/
def platz_freigeben_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.lit (.bool true)))

def platz_freigeben_writes : List String := ["Griffe"]

/-- What a caller of `platz_freigeben` has to bring: a well-typed world and the precondition. -/
def platz_freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t platz_freigeben_pre = some (.bool true)

/-- What `platz_freigeben` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def platz_freigeben_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-- **The duty of `platz_freigeben`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def platz_freigeben_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s platz_freigeben_pre = some (.bool true)),
    ∃ s', finalState (exec ρ platz_freigeben_body s) = some s'
        ∧ platz_freigeben_post s s' (finalValue (exec ρ platz_freigeben_body s))

theorem platz_freigeben_meets : platz_freigeben_meets_statement := by
  unfold platz_freigeben_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" (and_left _ _ _ hpre)
  obtain ⟨n_Griffe_belegt_s, h_Griffe_belegt_s⟩ := WF_bool shapeOf s.world (.slot "Griffe" w_s "belegt") hwf rfl
  obtain ⟨n_Griffe_zaehler_s, h_Griffe_zaehler_s⟩ := WF_int shapeOf s.world (.slot "Griffe" w_s "zaehler") hwf rfl
  gabbro_auto [platz_freigeben_body, platz_freigeben_pre, platz_freigeben_post, wellFormed, e_s, h_Griffe_belegt_s, h_Griffe_zaehler_s] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aufraeumen" aufraeumen_body
  ∧ Frame ρ "aufraeumen" aufraeumen_writes
  ∧ Runs ρ "nur_unbelegte_zaehlen" nur_unbelegte_zaehlen_body
  ∧ Frame ρ "nur_unbelegte_zaehlen" nur_unbelegte_zaehlen_writes
  ∧ Runs ρ "platz_freigeben" platz_freigeben_body
  ∧ Frame ρ "platz_freigeben" platz_freigeben_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_platz_freigeben : platz_freigeben_meets_statement)
    (d_aufraeumen : aufraeumen_meets_statement)
    (d_nur_unbelegte_zaehlen : nur_unbelegte_zaehlen_meets_statement) :
    Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post
    ∧ Contract ρ "aufraeumen" aufraeumen_requires aufraeumen_post
    ∧ Contract ρ "nur_unbelegte_zaehlen" nur_unbelegte_zaehlen_requires nur_unbelegte_zaehlen_post := by
  obtain ⟨r_aufraeumen, fr_aufraeumen, r_nur_unbelegte_zaehlen, fr_nur_unbelegte_zaehlen, r_platz_freigeben, fr_platz_freigeben⟩ := hp
  obtain ⟨c_buchfuehrung_kaputt, fr_buchfuehrung_kaputt⟩ := ha
  have c_platz_freigeben : Contract ρ "platz_freigeben" platz_freigeben_requires platz_freigeben_post :=
    contract_of_duty ρ "platz_freigeben" platz_freigeben_body platz_freigeben_requires platz_freigeben_post r_platz_freigeben
      (fun t ht => d_platz_freigeben ρ t ht.1 ht.2)
  have c_aufraeumen : Contract ρ "aufraeumen" aufraeumen_requires aufraeumen_post :=
    contract_of_duty ρ "aufraeumen" aufraeumen_body aufraeumen_requires aufraeumen_post r_aufraeumen
      (fun t ht => d_aufraeumen ρ t ht.1 ht.2 c_buchfuehrung_kaputt fr_buchfuehrung_kaputt c_platz_freigeben fr_platz_freigeben)
  have c_nur_unbelegte_zaehlen : Contract ρ "nur_unbelegte_zaehlen" nur_unbelegte_zaehlen_requires nur_unbelegte_zaehlen_post :=
    contract_of_duty ρ "nur_unbelegte_zaehlen" nur_unbelegte_zaehlen_body nur_unbelegte_zaehlen_requires nur_unbelegte_zaehlen_post r_nur_unbelegte_zaehlen
      (fun t ht => d_nur_unbelegte_zaehlen ρ t ht.1 ht.2 c_platz_freigeben fr_platz_freigeben)
  exact ⟨c_platz_freigeben, c_aufraeumen, c_nur_unbelegte_zaehlen⟩

end GabbroDuty.Duty48GrundMitErzeuger
