/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/01-tabelle.gab  total 15  goals 15  refused 0
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

namespace GabbroDuty.Duty01Tabelle

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Kappenraum :: invariant wurzel_ohne_vorgaenger  --  carried by `aushaengen_meets`, `blatt_loeschen_meets`, `einsammeln_meets`
  duty_2  W  Kappenraum :: invariant baum_bleibt_baum  --  carried by `aushaengen_meets`, `blatt_loeschen_meets`, `einsammeln_meets`
  duty_3  E  aushaengen :: baum_wohlgeformt  --  carried by `aushaengen_meets`
  duty_4  N  aushaengen :: ensures #1  --  carried by `aushaengen_meets`
  duty_5  N  aushaengen :: ensures #2  --  carried by `aushaengen_meets`
  duty_6  N  aushaengen :: ensures #3  --  carried by `aushaengen_meets`
  duty_7  E  einsammeln :: baum_wohlgeformt  --  carried by `einsammeln_meets`
  duty_8  S  einsammeln :: loop invariant #1  --  carried by `einsammeln_loop_1_keeps`
  duty_9  E  blatt_loeschen :: baum_wohlgeformt  --  carried by `blatt_loeschen_meets`
  duty_10  N  blatt_loeschen :: ensures #1  --  carried by `blatt_loeschen_meets`
  duty_11  V  einsammeln :: blatt_loeschen requires #1  --  carried by `einsammeln_meets`
  duty_12  V  einsammeln :: blatt_loeschen requires #2  --  carried by `einsammeln_meets`
  duty_13  V  einsammeln :: blatt_loeschen requires #3  --  carried by `einsammeln_meets`
  duty_14  V  blatt_loeschen :: aushaengen requires #1  --  carried by `blatt_loeschen_meets`
  duty_15  V  blatt_loeschen :: aushaengen requires #2  --  carried by `blatt_loeschen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Kappenraum" _ "benutzt" => some .bool
  | .slot "Kappenraum" _ "marke" => some .int
  | .slot "Kappenraum" _ "objekt" => some .int
  | .slot "Kappenraum" _ "abzeichen" => some .int
  | .slot "Kappenraum" _ "elter" => some .opt
  | .slot "Kappenraum" _ "erstes_kind" => some .opt
  | .slot "Kappenraum" _ "naechstes" => some .opt
  | .slot "Kappenraum" _ "vorheriges" => some .opt
  | .slot "Objekte" _ "benutzt" => some .bool
  | .slot "Objekte" _ "marke" => some .int
  | .slot "Objekte" _ "art" => some .sum
  | .slot "Objekte" _ "zaehler" => some .int
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `wurzel_ohne_vorgaenger` over `Kappenraum`. -/
def inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent))))

/-- `baum_bleibt_baum` over `Kappenraum`. -/
def inv_baum_bleibt_baum : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `speicher_freigeben` -- a foreign body: its contract is an assumption. -/
def speicher_freigeben_pre : Expr :=
  (.lit (.bool true))

def speicher_freigeben_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'

def speicher_freigeben_writes : List String := ["halde"]

def speicher_freigeben_requires (t : State) : Prop := wellFormed t ∧ eval t speicher_freigeben_pre = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "speicher_freigeben" speicher_freigeben_requires speicher_freigeben_post
  ∧ Frame ρ "speicher_freigeben" speicher_freigeben_writes

/-! ## The routines: body, contract, duty -/

/-! ### `aushaengen` -/

def aushaengen_body : List Stmt :=
  [(.onOption (.place "Kappenraum" (.name "s") "vorheriges") "p" [(.assign "Kappenraum" (.name "p") "naechstes" (.place "Kappenraum" (.name "s") "naechstes"))] [(.onOption (.place "Kappenraum" (.name "s") "elter") "e" [(.assign "Kappenraum" (.name "e") "erstes_kind" (.place "Kappenraum" (.name "s") "naechstes"))] [])]), (.onOption (.place "Kappenraum" (.name "s") "naechstes") "n" [(.assign "Kappenraum" (.name "n") "vorheriges" (.place "Kappenraum" (.name "s") "vorheriges"))] []), (.assign "Kappenraum" (.name "s") "elter" (.lit .absent)), (.assign "Kappenraum" (.name "s") "erstes_kind" (.lit .absent)), (.assign "Kappenraum" (.name "s") "naechstes" (.lit .absent)), (.assign "Kappenraum" (.name "s") "vorheriges" (.lit .absent))]

/-- The precondition: the declared shapes and the `requires`. -/
def aushaengen_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)))))))

/-- `baum_wohlgeformt`, as `aushaengen` keeps it. -/
def aushaengen_inv_baum_wohlgeformt : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

/-- `wurzel_ohne_vorgaenger`, as `aushaengen` keeps it. -/
def aushaengen_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent))))

/-- `baum_bleibt_baum`, as `aushaengen` keeps it. -/
def aushaengen_inv_baum_bleibt_baum : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

def aushaengen_writes : List String := ["Kappenraum"]

/-- What a caller of `aushaengen` has to bring: a well-typed world and the precondition. -/
def aushaengen_requires (t : State) : Prop := wellFormed t ∧ eval t aushaengen_pre = some (.bool true)

/-- What `aushaengen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def aushaengen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' aushaengen_inv_baum_wohlgeformt = some (.bool true)
  ∧ eval s' aushaengen_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ eval s' aushaengen_inv_baum_bleibt_baum = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent)) = some (.bool true))
  ∧ -- ensures #2
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)) = some (.bool true))
  ∧ -- ensures #3
  (eval { world := s'.world, local' := s.local' } (.bin .eq (.place "Kappenraum" (.name "s") "naechstes") (.lit .absent)) = some (.bool true))

/-- **The duty of `aushaengen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def aushaengen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s aushaengen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ aushaengen_body s) = some s'
        ∧ aushaengen_post s s' (finalValue (exec ρ aushaengen_body s))

theorem aushaengen_meets : aushaengen_meets_statement := by
  unfold aushaengen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" (and_left _ _ _ hpre)
  rcases WF_opt shapeOf s.world (.slot "Kappenraum" w_s "vorheriges") hwf rfl with h_Kappenraum_vorheriges_s | ⟨n_Kappenraum_vorheriges_s, h_Kappenraum_vorheriges_s⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "Kappenraum" w_s "naechstes") hwf rfl with h_Kappenraum_naechstes_s | ⟨n_Kappenraum_naechstes_s, h_Kappenraum_naechstes_s⟩ <;>
    rcases WF_opt shapeOf s.world (.slot "Kappenraum" w_s "elter") hwf rfl with h_Kappenraum_elter_s | ⟨n_Kappenraum_elter_s, h_Kappenraum_elter_s⟩
    <;> ((try gabbro_simp [aushaengen_body, aushaengen_pre, aushaengen_post, wellFormed, aushaengen_inv_baum_wohlgeformt, aushaengen_inv_wurzel_ohne_vorgaenger, aushaengen_inv_baum_bleibt_baum, e_s, h_Kappenraum_vorheriges_s, h_Kappenraum_naechstes_s, h_Kappenraum_elter_s]); all_goals (try (repeat' apply And.intro)); all_goals (try (gabbro_wf shapeOf)); trace_state; all_goals sorry)

/-! ### `blatt_loeschen` -/

def blatt_loeschen_body : List Stmt :=
  [(.bindName "obj" (.place "Kappenraum" (.name "s") "objekt")), (.call "aushaengen" ["c", "s"] [(.name "c"), (.name "s")] (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)))))))), (.assign "Kappenraum" (.name "s") "marke" (.wrapTo 32 false (.bin .add (.place "Kappenraum" (.name "s") "marke") (.lit (.int 1))))), (.assign "Kappenraum" (.name "s") "benutzt" (.lit (.bool false))), (.ite (.bin .ge (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 1))) [(.assign "Objekte" (.name "obj") "zaehler" (.bin .sub (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 1))))] []), (.ite (.bin .eq (.place "Objekte" (.name "obj") "zaehler") (.lit (.int 0))) [(.onTag (.place "Objekte" (.name "obj") "art") [("Speicher", some "p", [(.call "speicher_freigeben" ["p"] [(.name "p")] (.lit (.bool true)))]), ("Endpunkt", some "e", []), ("Faden", some "f", []), ("Antwort", some "a", [])]), (.assign "Objekte" (.name "obj") "benutzt" (.lit (.bool false)))] [])]

/-- The precondition: the declared shapes and the `requires`. -/
def blatt_loeschen_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .eq (.place "Kappenraum" (.name "s") "erstes_kind") (.lit .absent))) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))))))))

/-- `baum_wohlgeformt`, as `blatt_loeschen` keeps it. -/
def blatt_loeschen_inv_baum_wohlgeformt : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

/-- `wurzel_ohne_vorgaenger`, as `blatt_loeschen` keeps it. -/
def blatt_loeschen_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent))))

/-- `baum_bleibt_baum`, as `blatt_loeschen` keeps it. -/
def blatt_loeschen_inv_baum_bleibt_baum : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

def blatt_loeschen_writes : List String := ["Kappenraum", "Objekte"]

/-- What a caller of `blatt_loeschen` has to bring: a well-typed world and the precondition. -/
def blatt_loeschen_requires (t : State) : Prop := wellFormed t ∧ eval t blatt_loeschen_pre = some (.bool true)

/-- What `blatt_loeschen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def blatt_loeschen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' blatt_loeschen_inv_baum_wohlgeformt = some (.bool true)
  ∧ eval s' blatt_loeschen_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ eval s' blatt_loeschen_inv_baum_bleibt_baum = some (.bool true)
  ∧ -- ensures #1
  (eval { world := s'.world, local' := s.local' } (.un .not (.place "Kappenraum" (.name "s") "benutzt")) = some (.bool true))

/-- **The duty of `blatt_loeschen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def blatt_loeschen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s blatt_loeschen_pre = some (.bool true))
    -- the contract of `aushaengen`
    (c_aushaengen : Contract ρ "aushaengen" aushaengen_requires aushaengen_post)
    -- the frame of `aushaengen`
    (fr_aushaengen : Frame ρ "aushaengen" aushaengen_writes)
    -- the contract of `speicher_freigeben`
    (c_speicher_freigeben : Contract ρ "speicher_freigeben" speicher_freigeben_requires speicher_freigeben_post)
    -- the frame of `speicher_freigeben`
    (fr_speicher_freigeben : Frame ρ "speicher_freigeben" speicher_freigeben_writes),
    ∃ s', finalState (exec ρ blatt_loeschen_body s) = some s'
        ∧ blatt_loeschen_post s s' (finalValue (exec ρ blatt_loeschen_body s))

theorem blatt_loeschen_meets : blatt_loeschen_meets_statement := by
  unfold blatt_loeschen_meets_statement
  intro ρ s hwf hpre c_aushaengen fr_aushaengen c_speicher_freigeben fr_speicher_freigeben
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int s "s" (and_left _ _ _ hpre)
  obtain ⟨n_Kappenraum_objekt_s, h_Kappenraum_objekt_s⟩ := WF_int shapeOf s.world (.slot "Kappenraum" w_s "objekt") hwf rfl
  obtain ⟨n_Kappenraum_benutzt_s, h_Kappenraum_benutzt_s⟩ := WF_bool shapeOf s.world (.slot "Kappenraum" w_s "benutzt") hwf rfl
  ((try gabbro_simp [blatt_loeschen_body, blatt_loeschen_pre, blatt_loeschen_post, wellFormed, blatt_loeschen_inv_baum_wohlgeformt, blatt_loeschen_inv_wurzel_ohne_vorgaenger, blatt_loeschen_inv_baum_bleibt_baum, e_s, h_Kappenraum_objekt_s, h_Kappenraum_benutzt_s]); all_goals (try (repeat' apply And.intro)); all_goals (try (gabbro_wf shapeOf)); trace_state; all_goals sorry)

/-! ### `einsammeln` -/

def einsammeln_body : List Stmt :=
  [(.loop "einsammeln#1" (.bin .and (.hasShape "s" .int) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.place "Kappenraum" (.name "s") "benutzt"))))) [(.call "blatt_loeschen" ["c", "o", "s"] [(.name "c"), (.name "o"), (.name "opfer")] (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .eq (.place "Kappenraum" (.name "s") "erstes_kind") (.lit .absent))) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)))))))))])]

/-- The precondition: the declared shapes and the `requires`. -/
def einsammeln_pre : Expr :=
  (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)))))))

/-- `baum_wohlgeformt`, as `einsammeln` keeps it. -/
def einsammeln_inv_baum_wohlgeformt : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

/-- `wurzel_ohne_vorgaenger`, as `einsammeln` keeps it. -/
def einsammeln_inv_wurzel_ohne_vorgaenger : Expr :=
  (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent))))

/-- `baum_bleibt_baum`, as `einsammeln` keeps it. -/
def einsammeln_inv_baum_bleibt_baum : Expr :=
  (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096))

def einsammeln_writes : List String := ["Kappenraum", "Objekte"]

/-- What a caller of `einsammeln` has to bring: a well-typed world and the precondition. -/
def einsammeln_requires (t : State) : Prop := wellFormed t ∧ eval t einsammeln_pre = some (.bool true)

/-- What `einsammeln` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def einsammeln_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' einsammeln_inv_baum_wohlgeformt = some (.bool true)
  ∧ eval s' einsammeln_inv_wurzel_ohne_vorgaenger = some (.bool true)
  ∧ eval s' einsammeln_inv_baum_bleibt_baum = some (.bool true)

/-- Loop `einsammeln#1` of `einsammeln`: its body and its invariant (with the shapes of the locals in scope). -/
def einsammeln_loop_1_inv : Expr :=
  (.bin .and (.hasShape "s" .int) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.place "Kappenraum" (.name "s") "benutzt")))))

def einsammeln_loop_1_body : List Stmt :=
  [(.call "blatt_loeschen" ["c", "o", "s"] [(.name "c"), (.name "o"), (.name "opfer")] (.bin .and (.hasShape "s" .int) (.bin .and (.lit (.bool true)) (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .and (.bin .and (.place "Kappenraum" (.name "s") "benutzt") (.bin .eq (.place "Kappenraum" (.name "s") "erstes_kind") (.lit .absent))) (.bin .and (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)) (.bin .and (.forallSlots "s" 4096 (.bin .or (.un .not (.bin .eq (.place "Kappenraum" (.name "s") "elter") (.lit .absent))) (.bin .eq (.place "Kappenraum" (.name "s") "vorheriges") (.lit .absent)))) (.forallSlots "s" 4096 (.reaches "Kappenraum" (.name "s") (.lit (.int 0)) "elter" 4096)))))))))]

/-- **The loop rule of `einsammeln#1`, as a statement over one pass.** -/
def einsammeln_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t einsammeln_loop_1_inv = some (.bool true))
    (c_blatt_loeschen : Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post)
    (fr_blatt_loeschen : Frame ρ "blatt_loeschen" blatt_loeschen_writes),
    ∃ t', finalState (exec ρ einsammeln_loop_1_body { t with local' := bindLocal t.local' "opfer" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' einsammeln_loop_1_inv = some (.bool true)

theorem einsammeln_loop_1_keeps : einsammeln_loop_1_keeps_statement := by
  unfold einsammeln_loop_1_keeps_statement
  intro ρ t k hwf hinv c_blatt_loeschen fr_blatt_loeschen
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s⟩ := shape_int t "s" (and_left _ _ _ hinv)
  ((try gabbro_simp [einsammeln_loop_1_body, einsammeln_loop_1_inv, wellFormed, e_s]); all_goals (try (repeat' apply And.intro)); all_goals (try (gabbro_wf shapeOf)); trace_state; all_goals sorry)

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
  obtain ⟨w_s, e_s⟩ := shape_int s "s" (and_left _ _ _ hpre)
  obtain ⟨n_Kappenraum_benutzt_s, h_Kappenraum_benutzt_s⟩ := WF_bool shapeOf s.world (.slot "Kappenraum" w_s "benutzt") hwf rfl
  ((try gabbro_simp [einsammeln_body, einsammeln_pre, einsammeln_post, wellFormed, einsammeln_inv_baum_wohlgeformt, einsammeln_inv_wurzel_ohne_vorgaenger, einsammeln_inv_baum_bleibt_baum, e_s, h_Kappenraum_benutzt_s]); all_goals (try (repeat' apply And.intro)); all_goals (try (gabbro_wf shapeOf)); trace_state; all_goals sorry)

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "aushaengen" aushaengen_body
  ∧ Frame ρ "aushaengen" aushaengen_writes
  ∧ Runs ρ "blatt_loeschen" blatt_loeschen_body
  ∧ Frame ρ "blatt_loeschen" blatt_loeschen_writes
  ∧ Runs ρ "einsammeln" einsammeln_body
  ∧ Frame ρ "einsammeln" einsammeln_writes
  ∧ RunsLoop ρ "einsammeln#1" einsammeln_loop_1_body "opfer"

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_aushaengen : aushaengen_meets_statement)
    (d_blatt_loeschen : blatt_loeschen_meets_statement)
    (d_einsammeln_loop_1 : einsammeln_loop_1_keeps_statement)
    (d_einsammeln : einsammeln_meets_statement) :
    Contract ρ "aushaengen" aushaengen_requires aushaengen_post
    ∧ Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post
    ∧ LoopRule ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv
    ∧ Contract ρ "einsammeln" einsammeln_requires einsammeln_post := by
  obtain ⟨r_aushaengen, fr_aushaengen, r_blatt_loeschen, fr_blatt_loeschen, r_einsammeln, fr_einsammeln, rl_einsammeln_loop_1⟩ := hp
  obtain ⟨c_speicher_freigeben, fr_speicher_freigeben⟩ := ha
  have c_aushaengen : Contract ρ "aushaengen" aushaengen_requires aushaengen_post :=
    contract_of_duty ρ "aushaengen" aushaengen_body aushaengen_requires aushaengen_post r_aushaengen
      (fun t ht => d_aushaengen ρ t ht.1 ht.2)
  have c_blatt_loeschen : Contract ρ "blatt_loeschen" blatt_loeschen_requires blatt_loeschen_post :=
    contract_of_duty ρ "blatt_loeschen" blatt_loeschen_body blatt_loeschen_requires blatt_loeschen_post r_blatt_loeschen
      (fun t ht => d_blatt_loeschen ρ t ht.1 ht.2 c_aushaengen fr_aushaengen c_speicher_freigeben fr_speicher_freigeben)
  have l_einsammeln_loop_1 : LoopRule ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv :=
    looprule_of_body ρ "einsammeln#1" wellFormed einsammeln_loop_1_inv einsammeln_loop_1_body "opfer" rl_einsammeln_loop_1
      (fun t k hw hi => d_einsammeln_loop_1 ρ t k hw hi c_blatt_loeschen fr_blatt_loeschen)
  have c_einsammeln : Contract ρ "einsammeln" einsammeln_requires einsammeln_post :=
    contract_of_duty ρ "einsammeln" einsammeln_body einsammeln_requires einsammeln_post r_einsammeln
      (fun t ht => d_einsammeln ρ t ht.1 ht.2 c_blatt_loeschen fr_blatt_loeschen l_einsammeln_loop_1)
  exact ⟨c_aushaengen, c_blatt_loeschen, l_einsammeln_loop_1, c_einsammeln⟩

end GabbroDuty.Duty01Tabelle
