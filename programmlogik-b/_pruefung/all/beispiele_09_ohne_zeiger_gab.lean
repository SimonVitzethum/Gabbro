/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/09-ohne-zeiger.gab  total 8  goals 5  refused 3
        @assumed 3  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty09OhneZeiger

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  device-promise (3): ASSUMED -- a promise at hardware Gabbro does not see: an ASSUMPTION
    duty_3  D  Vtd :: transition wurzel_setzen
    duty_4  D  Vtd :: transition uebersetzung_an requires
    duty_5  D  Vtd :: transition uebersetzung_an

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Kappenraum :: invariant wurzel_ohne_vorgaenger  --  carried by `blatt_loeschen_meets`, `einsammeln_meets`
  duty_2  N  blatt_loeschen :: ensures #1  --  carried by `blatt_loeschen_meets`
  duty_3  D  Vtd :: transition wurzel_setzen  --  ASSUMED (device-promise)
  duty_4  D  Vtd :: transition uebersetzung_an requires  --  ASSUMED (device-promise)
  duty_5  D  Vtd :: transition uebersetzung_an  --  ASSUMED (device-promise)
  duty_6  V  einsammeln :: blatt_loeschen requires #1  --  carried by `einsammeln_meets`
  duty_7  V  einsammeln :: blatt_loeschen requires #2  --  carried by `einsammeln_meets`
  duty_8  V  einsammeln :: blatt_loeschen requires #3  --  carried by `einsammeln_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kappenraum" _ "benutzt" => some .bool
  | .slot "Kappenraum" _ "objekt" => some .int
  | .slot "Kappenraum" _ "elter" => some .opt
  | .slot "Kappenraum" _ "erstes_kind" => some .opt
  | .slot "Kappenraum" _ "naechstes" => some .opt
  | .slot "Objekte" _ "benutzt" => some .bool
  | .slot "Objekte" _ "art" => some (.sum [("Speicher", (some (some (0, 18446744073709551615)))), ("Endpunkt", (some (some (0, 4294967295))))])
  | .slot "Objekte" _ "zaehler" => some (.intIn 0 65535)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `wurzel_ohne_vorgaenger` over `Kappenraum`. -/
def inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `speicher_freigeben` -- a foreign body: its contract is an assumption. -/
def speicher_freigeben_pre : Expr :=
  (.hasShape "p" (.intIn 0 18446744073709551615))

def speicher_freigeben_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def speicher_freigeben_writes : List String := ["halde"]

def speicher_freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t speicher_freigeben_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_wurzel_ohne_vorgaenger = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "speicher_freigeben" speicher_freigeben_requires speicher_freigeben_post
  ∧ Frame ρ "speicher_freigeben" speicher_freigeben_writes

/-! ## The routines: body and contract -/

/-! ### `blatt_loeschen` -/

def blatt_loeschen_body : List Stmt :=
  [(.bindName "obj" (.place "Kappenraum" (.name "s") "objekt")), (.assign "Kappenraum" (.name "s") "benutzt" (.lit (.bool false))), (.assign "Kappenraum" (.name "s") "elter" (.lit .absent)), (.ite (.bin .ge (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 1))) [(.assign "Objekte" (.name "obj") "zaehler" (.bin .sub (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 1))))] []), (.ite (.bin .eq (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 0))) [(.onTag (.place "Objekte" (.name "obj") "art") [("Speicher", some "p", [(.call "speicher_freigeben" ["p"] [(.name "p")] (.hasShape "p" (.intIn 0 18446744073709551615)))]), ("Endpunkt", some "e", [])]), (.assign "Objekte" (.name "obj") "benutzt" (.lit (.bool false)))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def blatt_loeschen_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))))))

/-- `wurzel_ohne_vorgaenger`, as `blatt_loeschen` keeps it. -/
def blatt_loeschen_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))

def blatt_loeschen_writes : List String := ["Kappenraum", "Objekte"]

/-- What a caller of `blatt_loeschen` has to bring: a well-typed world and the precondition. -/
def blatt_loeschen_requires (t : State) : Prop := wellFormed t ∧ eval t blatt_loeschen_pre = some (.bool true)

/-- What `blatt_loeschen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def blatt_loeschen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' blatt_loeschen_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.un .not (.place "Kappenraum" (.name "s") "benutzt")) = some (.bool true))

/-! ### `einsammeln` -/

def einsammeln_body : List Stmt :=
  [(.loop "einsammeln#1" (.bin .and (.hasShape "s" (.intIn 0 80255)) (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))) [(.call "blatt_loeschen" ["s"] [(.name "opfer")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt")))))))])]

/-- The precondition: the declared shapes and the `requires`. -/
def einsammeln_pre : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))))

/-- `wurzel_ohne_vorgaenger`, as `einsammeln` keeps it. -/
def einsammeln_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt"))

def einsammeln_writes : List String := ["Kappenraum", "Objekte"]

/-- What a caller of `einsammeln` has to bring: a well-typed world and the precondition. -/
def einsammeln_requires (t : State) : Prop := wellFormed t ∧ eval t einsammeln_pre = some (.bool true)

/-- What `einsammeln` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einsammeln_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' einsammeln_inv_wurzel_ohne_vorgaenger = some (.bool true)

/-! ### `scharfschalten` -/

-- REFUSED  scharfschalten  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def scharfschalten_pre : Expr :=
  (.bin .and (.hasShape "basis" (.intIn 0 18446744073709551615)) (.bin .and (.hasShape "wurzel" (.intIn 0 18446744073709551615)) (.bin .eq (.bin .rem (.name "wurzel") (.lit (.int 4096))) (.lit (.int 0)))))

def scharfschalten_writes : List String := ["v"]

/-- What a caller of `scharfschalten` has to bring: a well-typed world and the precondition. -/
def scharfschalten_requires (t : State) : Prop := wellFormed t ∧ eval t scharfschalten_pre = some (.bool true)

/-- What `scharfschalten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def scharfschalten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ## The duties: one statement per routine and per loop -/

/-! ### `blatt_loeschen` -/

/-- **The duty of `blatt_loeschen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def blatt_loeschen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s blatt_loeschen_pre = some (.bool true))
    -- the contract of `speicher_freigeben`
    (c_speicher_freigeben : Contract ρ "speicher_freigeben" speicher_freigeben_requires speicher_freigeben_post)
    -- the frame of `speicher_freigeben`
    (fr_speicher_freigeben : Frame ρ "speicher_freigeben" speicher_freigeben_writes),
    ∃ s', finalState (exec ρ blatt_loeschen_body s) = some s'
        ∧ blatt_loeschen_post s s' (finalValue (exec ρ blatt_loeschen_body s))

theorem blatt_loeschen_meets : blatt_loeschen_meets_statement := by
  unfold blatt_loeschen_meets_statement
  intro ρ s hwf hpre c_speicher_freigeben fr_speicher_freigeben
  simp only [wellFormed] at hwf ⊢
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [blatt_loeschen_inv_wurzel_ohne_vorgaenger, blatt_loeschen_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_Kappenraum_objekt_s, h_Kappenraum_objekt_s⟩ := WF_int shapeOf s.world (.slot "Kappenraum" w_s "objekt") hwf rfl
  obtain ⟨n_Kappenraum_benutzt_s, h_Kappenraum_benutzt_s⟩ := WF_bool shapeOf s.world (.slot "Kappenraum" w_s "benutzt") hwf rfl
  have hall := hpre
  gabbro_simp_at hall [blatt_loeschen_pre, e_s, h_Kappenraum_objekt_s, h_Kappenraum_benutzt_s]
  gabbro_auto [blatt_loeschen_body, blatt_loeschen_pre, blatt_loeschen_post, wellFormed, blatt_loeschen_inv_wurzel_ohne_vorgaenger, speicher_freigeben_pre, speicher_freigeben_requires, speicher_freigeben_post, speicher_freigeben_writes, Frame_read _ _ _ fr_speicher_freigeben, e_s, h_Kappenraum_objekt_s, h_Kappenraum_benutzt_s, hall] using shapeOf

/-! ### `einsammeln` -/

/-- Loop `einsammeln#1` of `einsammeln`: its body and its invariant (with the shapes of the locals in scope). -/
def einsammeln_loop_1_inv : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 80255)) (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt")))

def einsammeln_loop_1_body : List Stmt :=
  [(.call "blatt_loeschen" ["s"] [(.name "opfer")] (.bin .and (.hasShape "s" (.intIn 0 80255)) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.forallSlots "s" 80256 (.place "Kappenraum" (.name "s") "benutzt")))))))]

/-- **The loop rule of `einsammeln#1`, as a statement over one pass.** -/
def einsammeln_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 80256)
    (hwf : wellFormed t)
    (hinv : eval t einsammeln_loop_1_inv = some (.bool true))
    (c_blatt_loeschen : Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post)
    (fr_blatt_loeschen : Frame ρ "blatt_loeschen" blatt_loeschen_writes),
    ∃ t', finalState (exec ρ einsammeln_loop_1_body { t with local' := bindLocal t.local' "opfer" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' einsammeln_loop_1_inv = some (.bool true)

theorem einsammeln_loop_1_keeps : einsammeln_loop_1_keeps_statement := by
  unfold einsammeln_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv c_blatt_loeschen fr_blatt_loeschen
  simp only [wellFormed] at hwf ⊢
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ hinv)
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [einsammeln_inv_wurzel_ohne_vorgaenger, einsammeln_loop_1_inv]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn t "s" _ _ (and_left _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [einsammeln_loop_1_inv, e_s]
  gabbro_auto [einsammeln_loop_1_body, einsammeln_loop_1_inv, wellFormed, blatt_loeschen_pre, blatt_loeschen_requires, blatt_loeschen_post, blatt_loeschen_writes, Frame_read _ _ _ fr_blatt_loeschen, e_s, hall] using shapeOf

/-- **The duty of `einsammeln`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def einsammeln_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s einsammeln_pre = some (.bool true))
    -- the contract of `blatt_loeschen`
    (c_blatt_loeschen : Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post)
    -- the frame of `blatt_loeschen`
    (fr_blatt_loeschen : Frame ρ "blatt_loeschen" blatt_loeschen_writes)
    -- the rule of loop `einsammeln#1`
    (l_einsammeln_loop_1 : LoopRule ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv),
    ∃ s', finalState (exec ρ einsammeln_body s) = some s'
        ∧ einsammeln_post s s' (finalValue (exec ρ einsammeln_body s))

theorem einsammeln_meets : einsammeln_meets_statement := by
  unfold einsammeln_meets_statement
  intro ρ s hwf hpre c_blatt_loeschen fr_blatt_loeschen l_einsammeln_loop_1
  simp only [wellFormed] at hwf ⊢
  have hi_wurzel_ohne_vorgaenger := (and_right _ _ _ (and_right _ _ _ hpre))
  gabbro_simp_at hi_wurzel_ohne_vorgaenger [einsammeln_inv_wurzel_ohne_vorgaenger, einsammeln_pre]
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [einsammeln_pre, e_s]
  gabbro_auto [einsammeln_body, einsammeln_pre, einsammeln_post, wellFormed, einsammeln_inv_wurzel_ohne_vorgaenger, blatt_loeschen_pre, blatt_loeschen_requires, blatt_loeschen_post, blatt_loeschen_writes, Frame_read _ _ _ fr_blatt_loeschen, einsammeln_loop_1_inv, e_s, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "blatt_loeschen" blatt_loeschen_body
  ∧ Frame ρ "blatt_loeschen" blatt_loeschen_writes
  ∧ Runs ρ "einsammeln" einsammeln_body
  ∧ Frame ρ "einsammeln" einsammeln_writes
  ∧ RunsLoopIn ρ "einsammeln#1" einsammeln_loop_1_body "opfer" 0 80256

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_blatt_loeschen : blatt_loeschen_meets_statement)
    (d_einsammeln_loop_1 : einsammeln_loop_1_keeps_statement)
    (d_einsammeln : einsammeln_meets_statement) :
    Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post
    ∧ LoopRule ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv
    ∧ Contract ρ "einsammeln" einsammeln_requires einsammeln_post := by
  obtain ⟨r_blatt_loeschen, fr_blatt_loeschen, r_einsammeln, fr_einsammeln, rl_einsammeln_loop_1⟩ := hp
  obtain ⟨c_speicher_freigeben, fr_speicher_freigeben⟩ := ha
  have c_blatt_loeschen : Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post :=
    contract_of_duty ρ "blatt_loeschen" blatt_loeschen_body blatt_loeschen_requires blatt_loeschen_post r_blatt_loeschen
      (fun t ht => d_blatt_loeschen ρ t ht.1 ht.2 c_speicher_freigeben fr_speicher_freigeben)
  have l_einsammeln_loop_1 : LoopRule ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv :=
    looprule_of_body_in ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv einsammeln_loop_1_body "opfer" 0 80256 rl_einsammeln_loop_1
      (fun t k hlo hhi hw hi => d_einsammeln_loop_1 ρ t k hlo hhi hw hi c_blatt_loeschen fr_blatt_loeschen)
  have c_einsammeln : Contract ρ "einsammeln" einsammeln_requires einsammeln_post :=
    contract_of_duty ρ "einsammeln" einsammeln_body einsammeln_requires einsammeln_post r_einsammeln
      (fun t ht => d_einsammeln ρ t ht.1 ht.2 c_blatt_loeschen fr_blatt_loeschen l_einsammeln_loop_1)
  exact ⟨c_blatt_loeschen, l_einsammeln_loop_1, c_einsammeln⟩

end GabbroDuty.Duty09OhneZeiger
