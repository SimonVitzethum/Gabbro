/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  beispiele/39-auftragsdienst.gab  total 3  goals 2  refused 1
        @assumed 1  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.Duty39Auftragsdienst

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  foreign-body (1): ASSUMED -- an `ensures` at a body Gabbro never sees: an ASSUMPTION, stated in `Assumed`
    duty_2  F  naechste_menge :: ensures #1

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  W  Auftraege :: invariant rest_bleibt_im_bereich  --  carried by `dienst_meets`
  duty_2  F  naechste_menge :: ensures #1  --  ASSUMED (foreign-body)
  duty_3  V  dienst :: erster_dringender requires #1  --  carried by `dienst_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "Auftraege" _ "belegt" => some .bool
  | .slot "Auftraege" _ "art" => some (.sum [("Lesen", (some (some (0, 4096)))), ("Schreiben", (some none)), ("Ruhe", none)])
  | .slot "Auftraege" _ "prio" => some (.intIn 0 7)
  | .slot "Auftraege" _ "rest" => some (.intIn 0 4096)
  | .slot "Auftraege" _ "buendel" => some .opt
  | .global "RUNDE_FERTIG" => some .bool
  | .global "bericht" => some (.intIn 0 65535)
  | .global "erledigt" => some (.intIn 0 65535)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `rest_bleibt_im_bereich` over `Auftraege`. -/
def inv_rest_bleibt_im_bereich : Expr :=
  (.forallSlots "s" 64 (.bin .le (.place "Auftraege" (.name "s") "rest") (.lit (.int 4096))))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `abschaltung_angefordert` -- a foreign body: its contract is an assumption. -/
def abschaltung_angefordert_pre : Expr :=
  (.lit (.bool true))

def abschaltung_angefordert_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ b, r = some (.bool b))

def abschaltung_angefordert_writes : List String := []

def abschaltung_angefordert_requires (t : State) : Prop := wellFormed t ∧ eval t abschaltung_angefordert_pre = some (.bool true)

/-- `block_uebertragen` -- a foreign body: its contract is an assumption. -/
def block_uebertragen_pre : Expr :=
  (.hasShape "n" (.intIn 0 4096))

def block_uebertragen_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4096)

def block_uebertragen_writes : List String := ["geraet"]

def block_uebertragen_requires (t : State) : Prop := wellFormed t ∧ eval t block_uebertragen_pre = some (.bool true)

/-- `naechste_menge` -- a foreign body: its contract is an assumption. -/
def naechste_menge_pre : Expr :=
  (.lit (.bool true))

def naechste_menge_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4096) ∨ ∃ e, r = some (.reason e))
  ∧ (∃ v, r = some v ∧ eval { world := t'.world, local' := (bindLocal t.local' "result" v) } (.bin .ge (.name "result") (.lit (.int 1))) = some (.bool true))

def naechste_menge_writes : List String := []

def naechste_menge_requires (t : State) : Prop := wellFormed t ∧ eval t naechste_menge_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_rest_bleibt_im_bereich = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post
  ∧ Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes
  ∧ Contract ρ "block_uebertragen" block_uebertragen_requires block_uebertragen_post
  ∧ Frame ρ "block_uebertragen" block_uebertragen_writes
  ∧ Contract ρ "naechste_menge" naechste_menge_requires naechste_menge_post
  ∧ Frame ρ "naechste_menge" naechste_menge_writes

/-! ## The routines: body and contract -/

/-! ### `abarbeiten` -/

def abarbeiten_body : List Stmt :=
  [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "abarbeiten#1" (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 65535))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))) [(.bindCallElse "menge" "naechste_menge" [] [] (.lit (.bool true)) "e" [(.bindName "#ret" (.global "erledigt")), (.bindName "#returned" (.lit (.bool true))), .leave]), (.ite (.bin .and (.bin .ge (.name "menge") (.lit (.int 128))) (.bin .le (.name "menge") (.lit (.int 4096)))) [] [.exit]), (.bindCall "geschafft" "block_uebertragen" ["n"] [(.name "menge")] (.hasShape "n" (.intIn 0 4096))), (.ite (.bin .ge (.name "geschafft") (.lit (.int 1))) [(.assignGlobal "erledigt" (.lit (.int 1)))] [])]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.global "erledigt")))]

/-- The precondition: the declared shapes and the `requires`. -/
def abarbeiten_pre : Expr :=
  (.lit (.bool true))

def abarbeiten_writes : List String := ["erledigt", "geraet"]

/-- What a caller of `abarbeiten` has to bring: a well-typed world and the precondition. -/
def abarbeiten_requires (t : State) : Prop := wellFormed t ∧ eval t abarbeiten_pre = some (.bool true)

/-- What `abarbeiten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def abarbeiten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `bericht_lesen` -/

def bericht_lesen_body : List Stmt :=
  [(.awaitLoad "fertig" "RUNDE_FERTIG" ["bericht"]), (.ite (.name "fertig") [(.ret (some (.global "bericht")))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def bericht_lesen_pre : Expr :=
  (.lit (.bool true))

def bericht_lesen_writes : List String := []

/-- What a caller of `bericht_lesen` has to bring: a well-typed world and the precondition. -/
def bericht_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t bericht_lesen_pre = some (.bool true)

/-- What `bericht_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def bericht_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `buendel_von` -/

def buendel_von_body : List Stmt :=
  [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "buendel_von#1" (.bin .and (.hasShape "i" (.intIn 0 63)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .opt)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))) [(.bindName "#ret" (.someOf (.name "v"))), (.bindName "#returned" (.lit (.bool true))), .leave]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.lit .absent)))]

/-- The precondition: the declared shapes and the `requires`. -/
def buendel_von_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 63)) (.lit (.bool true)))

def buendel_von_writes : List String := []

/-- What a caller of `buendel_von` has to bring: a well-typed world and the precondition. -/
def buendel_von_requires (t : State) : Prop := wellFormed t ∧ eval t buendel_von_pre = some (.bool true)

/-- What `buendel_von` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def buendel_von_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = some .absent ∨ ∃ x, r = some (.present x))

/-! ### `dienst` -/

def dienst_body : List Stmt :=
  [(.loop "dienst#1" (.forallSlots "s" 64 (.bin .le (.place "Auftraege" (.name "s") "rest") (.lit (.int 4096)))) [(.locked "WARTESCHLANGE" [(.bindCall "#m1" "erster_dringender" ["q", "schwelle"] [(.name "q"), (.lit (.int 7))] (.bin .and (.hasShape "schwelle" (.intIn 0 7)) (.lit (.bool true)))), (.onOption (.name "#m1") "i" [(.assign "Auftraege" (.name "i") "belegt" (.lit (.bool false))), (.assign "Auftraege" (.name "i") "rest" (.lit (.int 0))), (.assignGlobal "bericht" (.lit (.int 1)))] [])]), (.publish "RUNDE_FERTIG" (.lit (.bool true)) ["bericht"]), (.bindCall "#m2" "abschaltung_angefordert" [] [] (.lit (.bool true))), (.ite (.name "#m2") [.leave] [])])]

/-- The precondition: the declared shapes and the `requires`. -/
def dienst_pre : Expr :=
  (.forallSlots "s" 64 (.bin .le (.place "Auftraege" (.name "s") "rest") (.lit (.int 4096))))

/-- `rest_bleibt_im_bereich`, as `dienst` keeps it. -/
def dienst_inv_rest_bleibt_im_bereich : Expr :=
  (.forallSlots "s" 64 (.bin .le (.place "Auftraege" (.name "s") "rest") (.lit (.int 4096))))

def dienst_writes : List String := ["Auftraege", "bericht", "RUNDE_FERTIG"]

/-- What a caller of `dienst` has to bring: a well-typed world and the precondition. -/
def dienst_requires (t : State) : Prop := wellFormed t ∧ eval t dienst_pre = some (.bool true)

/-- What `dienst` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def dienst_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' dienst_inv_rest_bleibt_im_bereich = some (.bool true)

/-! ### `erster_dringender` -/

def erster_dringender_body : List Stmt :=
  [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "erster_dringender#1" (.bin .and (.hasShape "schwelle" (.intIn 0 7)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .opt)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))) [(.bindName "p" (.place "Auftraege" (.name "i") "prio")), (.onTag (.place "Auftraege" (.name "i") "art") [("Lesen", some "n", [(.ite (.bin .ge (.name "p") (.name "schwelle")) [(.bindName "#ret" (.someOf (.name "i"))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), ("Schreiben", some "n", [(.ite (.bin .ge (.name "p") (.name "schwelle")) [(.bindName "#ret" (.someOf (.name "i"))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), ("Ruhe", none, [])])]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.lit .absent)))]

/-- The precondition: the declared shapes and the `requires`. -/
def erster_dringender_pre : Expr :=
  (.bin .and (.hasShape "schwelle" (.intIn 0 7)) (.lit (.bool true)))

def erster_dringender_writes : List String := []

/-- What a caller of `erster_dringender` has to bring: a well-typed world and the precondition. -/
def erster_dringender_requires (t : State) : Prop := wellFormed t ∧ eval t erster_dringender_pre = some (.bool true)

/-- What `erster_dringender` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def erster_dringender_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (r = some .absent ∨ ∃ x, r = some (.present x))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `abarbeiten` -/

/-- Loop `abarbeiten#1` of `abarbeiten`: its body and its invariant (with the shapes of the locals in scope). -/
def abarbeiten_loop_1_inv : Expr :=
  (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 65535))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))

def abarbeiten_loop_1_body : List Stmt :=
  [(.bindCallElse "menge" "naechste_menge" [] [] (.lit (.bool true)) "e" [(.bindName "#ret" (.global "erledigt")), (.bindName "#returned" (.lit (.bool true))), .leave]), (.ite (.bin .and (.bin .ge (.name "menge") (.lit (.int 128))) (.bin .le (.name "menge") (.lit (.int 4096)))) [] [.exit]), (.bindCall "geschafft" "block_uebertragen" ["n"] [(.name "menge")] (.hasShape "n" (.intIn 0 4096))), (.ite (.bin .ge (.name "geschafft") (.lit (.int 1))) [(.assignGlobal "erledigt" (.lit (.int 1)))] [])]

/-- **The loop rule of `abarbeiten#1`, as a statement over one pass.** -/
def abarbeiten_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t abarbeiten_loop_1_inv = some (.bool true))
    (c_block_uebertragen : Contract ρ "block_uebertragen" block_uebertragen_requires block_uebertragen_post)
    (fr_block_uebertragen : Frame ρ "block_uebertragen" block_uebertragen_writes)
    (c_naechste_menge : Contract ρ "naechste_menge" naechste_menge_requires naechste_menge_post)
    (fr_naechste_menge : Frame ρ "naechste_menge" naechste_menge_writes),
    ∃ t', finalState (exec ρ abarbeiten_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' abarbeiten_loop_1_inv = some (.bool true)

theorem abarbeiten_loop_1_keeps : abarbeiten_loop_1_keeps_statement := by
  unfold abarbeiten_loop_1_keeps_statement
  intro ρ t k hwf hinv c_block_uebertragen fr_block_uebertragen c_naechste_menge fr_naechste_menge
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ hinv)
  have hall := hinv
  gabbro_simp_at hall [abarbeiten_loop_1_inv, e__returned]
  gabbro_auto [abarbeiten_loop_1_body, abarbeiten_loop_1_inv, wellFormed, block_uebertragen_pre, block_uebertragen_requires, block_uebertragen_post, block_uebertragen_writes, Frame_read _ _ _ fr_block_uebertragen, naechste_menge_pre, naechste_menge_requires, naechste_menge_post, naechste_menge_writes, Frame_read _ _ _ fr_naechste_menge, e__returned, hall] using shapeOf

/-- **The duty of `abarbeiten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def abarbeiten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s abarbeiten_pre = some (.bool true))
    -- the contract of `block_uebertragen`
    (c_block_uebertragen : Contract ρ "block_uebertragen" block_uebertragen_requires block_uebertragen_post)
    -- the frame of `block_uebertragen`
    (fr_block_uebertragen : Frame ρ "block_uebertragen" block_uebertragen_writes)
    -- the contract of `naechste_menge`
    (c_naechste_menge : Contract ρ "naechste_menge" naechste_menge_requires naechste_menge_post)
    -- the frame of `naechste_menge`
    (fr_naechste_menge : Frame ρ "naechste_menge" naechste_menge_writes)
    -- the rule of loop `abarbeiten#1`
    (l_abarbeiten_loop_1 : LoopRule ρ "abarbeiten#1" wellFormed abarbeiten_loop_1_inv),
    ∃ s', finalState (exec ρ abarbeiten_body s) = some s'
        ∧ abarbeiten_post s s' (finalValue (exec ρ abarbeiten_body s))

theorem abarbeiten_meets : abarbeiten_meets_statement := by
  unfold abarbeiten_meets_statement
  intro ρ s hwf hpre c_block_uebertragen fr_block_uebertragen c_naechste_menge fr_naechste_menge l_abarbeiten_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [abarbeiten_pre]
  gabbro_auto [abarbeiten_body, abarbeiten_pre, abarbeiten_post, wellFormed, block_uebertragen_pre, block_uebertragen_requires, block_uebertragen_post, block_uebertragen_writes, Frame_read _ _ _ fr_block_uebertragen, naechste_menge_pre, naechste_menge_requires, naechste_menge_post, naechste_menge_writes, Frame_read _ _ _ fr_naechste_menge, abarbeiten_loop_1_inv, hall] using shapeOf

/-! ### `bericht_lesen` -/

/-- **The duty of `bericht_lesen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def bericht_lesen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s bericht_lesen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ bericht_lesen_body s) = some s'
        ∧ bericht_lesen_post s s' (finalValue (exec ρ bericht_lesen_body s))

theorem bericht_lesen_meets : bericht_lesen_meets_statement := by
  unfold bericht_lesen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [bericht_lesen_pre]
  gabbro_auto [bericht_lesen_body, bericht_lesen_pre, bericht_lesen_post, wellFormed, hall] using shapeOf

/-! ### `buendel_von` -/

/-- Loop `buendel_von#1` of `buendel_von`: its body and its invariant (with the shapes of the locals in scope). -/
def buendel_von_loop_1_inv : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 63)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .opt)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))

def buendel_von_loop_1_body : List Stmt :=
  [(.bindName "#ret" (.someOf (.name "v"))), (.bindName "#returned" (.lit (.bool true))), .leave]

/-- **The loop rule of `buendel_von#1`, as a statement over one pass.** -/
def buendel_von_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 64)
    (hwf : wellFormed t)
    (hinv : eval t buendel_von_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ buendel_von_loop_1_body { t with local' := bindLocal t.local' "v" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' buendel_von_loop_1_inv = some (.bool true)

theorem buendel_von_loop_1_keeps : buendel_von_loop_1_keeps_statement := by
  unfold buendel_von_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn t "i" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  have hall := hinv
  gabbro_simp_at hall [buendel_von_loop_1_inv, e_i, e__returned]
  gabbro_auto [buendel_von_loop_1_body, buendel_von_loop_1_inv, wellFormed, e_i, e__returned, hall] using shapeOf

/-- **The duty of `buendel_von`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def buendel_von_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s buendel_von_pre = some (.bool true))
    -- the rule of loop `buendel_von#1`
    (l_buendel_von_loop_1 : LoopRule ρ "buendel_von#1" wellFormed buendel_von_loop_1_inv),
    ∃ s', finalState (exec ρ buendel_von_body s) = some s'
        ∧ buendel_von_post s s' (finalValue (exec ρ buendel_von_body s))

theorem buendel_von_meets : buendel_von_meets_statement := by
  unfold buendel_von_meets_statement
  intro ρ s hwf hpre l_buendel_von_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [buendel_von_pre, e_i]
  gabbro_auto [buendel_von_body, buendel_von_pre, buendel_von_post, wellFormed, buendel_von_loop_1_inv, e_i, hall] using shapeOf

/-! ### `dienst` -/

/-- Loop `dienst#1` of `dienst`: its body and its invariant (with the shapes of the locals in scope). -/
def dienst_loop_1_inv : Expr :=
  (.forallSlots "s" 64 (.bin .le (.place "Auftraege" (.name "s") "rest") (.lit (.int 4096))))

def dienst_loop_1_body : List Stmt :=
  [(.locked "WARTESCHLANGE" [(.bindCall "#m1" "erster_dringender" ["q", "schwelle"] [(.name "q"), (.lit (.int 7))] (.bin .and (.hasShape "schwelle" (.intIn 0 7)) (.lit (.bool true)))), (.onOption (.name "#m1") "i" [(.assign "Auftraege" (.name "i") "belegt" (.lit (.bool false))), (.assign "Auftraege" (.name "i") "rest" (.lit (.int 0))), (.assignGlobal "bericht" (.lit (.int 1)))] [])]), (.publish "RUNDE_FERTIG" (.lit (.bool true)) ["bericht"]), (.bindCall "#m2" "abschaltung_angefordert" [] [] (.lit (.bool true))), (.ite (.name "#m2") [.leave] [])]

/-- **The loop rule of `dienst#1`, as a statement over one pass.** -/
def dienst_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t dienst_loop_1_inv = some (.bool true))
    (c_abschaltung_angefordert : Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post)
    (fr_abschaltung_angefordert : Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes)
    (c_erster_dringender : Contract ρ "erster_dringender" erster_dringender_requires erster_dringender_post)
    (fr_erster_dringender : Frame ρ "erster_dringender" erster_dringender_writes),
    ∃ t', finalState (exec ρ dienst_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' dienst_loop_1_inv = some (.bool true)

theorem dienst_loop_1_keeps : dienst_loop_1_keeps_statement := by
  unfold dienst_loop_1_keeps_statement
  intro ρ t k hwf hinv c_abschaltung_angefordert fr_abschaltung_angefordert c_erster_dringender fr_erster_dringender
  simp only [wellFormed] at hwf ⊢
  have hi_rest_bleibt_im_bereich := hinv
  gabbro_simp_at hi_rest_bleibt_im_bereich [dienst_inv_rest_bleibt_im_bereich, dienst_loop_1_inv]
  have hall := hinv
  gabbro_simp_at hall [dienst_loop_1_inv]
  gabbro_auto [dienst_loop_1_body, dienst_loop_1_inv, wellFormed, abschaltung_angefordert_pre, abschaltung_angefordert_requires, abschaltung_angefordert_post, abschaltung_angefordert_writes, Frame_read _ _ _ fr_abschaltung_angefordert, erster_dringender_pre, erster_dringender_requires, erster_dringender_post, erster_dringender_writes, Frame_read _ _ _ fr_erster_dringender, hall] using shapeOf

/-- **The duty of `dienst`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def dienst_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s dienst_pre = some (.bool true))
    -- the contract of `abschaltung_angefordert`
    (c_abschaltung_angefordert : Contract ρ "abschaltung_angefordert" abschaltung_angefordert_requires abschaltung_angefordert_post)
    -- the frame of `abschaltung_angefordert`
    (fr_abschaltung_angefordert : Frame ρ "abschaltung_angefordert" abschaltung_angefordert_writes)
    -- the contract of `erster_dringender`
    (c_erster_dringender : Contract ρ "erster_dringender" erster_dringender_requires erster_dringender_post)
    -- the frame of `erster_dringender`
    (fr_erster_dringender : Frame ρ "erster_dringender" erster_dringender_writes)
    -- the rule of loop `dienst#1`
    (l_dienst_loop_1 : LoopRule ρ "dienst#1" wellFormed dienst_loop_1_inv),
    ∃ s', finalState (exec ρ dienst_body s) = some s'
        ∧ dienst_post s s' (finalValue (exec ρ dienst_body s))

theorem dienst_meets : dienst_meets_statement := by
  unfold dienst_meets_statement
  intro ρ s hwf hpre c_abschaltung_angefordert fr_abschaltung_angefordert c_erster_dringender fr_erster_dringender l_dienst_loop_1
  simp only [wellFormed] at hwf ⊢
  have hi_rest_bleibt_im_bereich := hpre
  gabbro_simp_at hi_rest_bleibt_im_bereich [dienst_inv_rest_bleibt_im_bereich, dienst_pre]
  have hall := hpre
  gabbro_simp_at hall [dienst_pre]
  gabbro_auto [dienst_body, dienst_pre, dienst_post, wellFormed, dienst_inv_rest_bleibt_im_bereich, abschaltung_angefordert_pre, abschaltung_angefordert_requires, abschaltung_angefordert_post, abschaltung_angefordert_writes, Frame_read _ _ _ fr_abschaltung_angefordert, erster_dringender_pre, erster_dringender_requires, erster_dringender_post, erster_dringender_writes, Frame_read _ _ _ fr_erster_dringender, dienst_loop_1_inv, hall] using shapeOf

/-! ### `erster_dringender` -/

/-- Loop `erster_dringender#1` of `erster_dringender`: its body and its invariant (with the shapes of the locals in scope). -/
def erster_dringender_loop_1_inv : Expr :=
  (.bin .and (.hasShape "schwelle" (.intIn 0 7)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" .opt)) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))

def erster_dringender_loop_1_body : List Stmt :=
  [(.bindName "p" (.place "Auftraege" (.name "i") "prio")), (.onTag (.place "Auftraege" (.name "i") "art") [("Lesen", some "n", [(.ite (.bin .ge (.name "p") (.name "schwelle")) [(.bindName "#ret" (.someOf (.name "i"))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), ("Schreiben", some "n", [(.ite (.bin .ge (.name "p") (.name "schwelle")) [(.bindName "#ret" (.someOf (.name "i"))), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), ("Ruhe", none, [])])]

/-- **The loop rule of `erster_dringender#1`, as a statement over one pass.** -/
def erster_dringender_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 64)
    (hwf : wellFormed t)
    (hinv : eval t erster_dringender_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ erster_dringender_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' erster_dringender_loop_1_inv = some (.bool true)

theorem erster_dringender_loop_1_keeps : erster_dringender_loop_1_keeps_statement := by
  unfold erster_dringender_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schwelle, e_schwelle, lo_schwelle, hi_schwelle⟩ := shape_intIn t "schwelle" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨n_Auftraege_prio_i, h_Auftraege_prio_i, lo_Auftraege_prio_i, hi_Auftraege_prio_i⟩ := WF_intIn shapeOf t.world (.slot "Auftraege" k "prio") _ _ hwf rfl
  obtain ⟨n_Auftraege_art_i, q_Auftraege_art_i, h_Auftraege_art_i, c_Auftraege_art_i⟩ := WF_sum shapeOf t.world (.slot "Auftraege" k "art") _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [erster_dringender_loop_1_inv, e_schwelle, e__returned, h_Auftraege_prio_i, h_Auftraege_art_i]
  gabbro_auto [erster_dringender_loop_1_body, erster_dringender_loop_1_inv, wellFormed, e_schwelle, e__returned, h_Auftraege_prio_i, h_Auftraege_art_i, hall] using shapeOf

/-- **The duty of `erster_dringender`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def erster_dringender_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s erster_dringender_pre = some (.bool true))
    -- the rule of loop `erster_dringender#1`
    (l_erster_dringender_loop_1 : LoopRule ρ "erster_dringender#1" wellFormed erster_dringender_loop_1_inv),
    ∃ s', finalState (exec ρ erster_dringender_body s) = some s'
        ∧ erster_dringender_post s s' (finalValue (exec ρ erster_dringender_body s))

theorem erster_dringender_meets : erster_dringender_meets_statement := by
  unfold erster_dringender_meets_statement
  intro ρ s hwf hpre l_erster_dringender_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_schwelle, e_schwelle, lo_schwelle, hi_schwelle⟩ := shape_intIn s "schwelle" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [erster_dringender_pre, e_schwelle]
  gabbro_auto [erster_dringender_body, erster_dringender_pre, erster_dringender_post, wellFormed, erster_dringender_loop_1_inv, e_schwelle, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "abarbeiten" abarbeiten_body
  ∧ Frame ρ "abarbeiten" abarbeiten_writes
  ∧ RunsLoop ρ "abarbeiten#1" abarbeiten_loop_1_body "#pass"
  ∧ Runs ρ "bericht_lesen" bericht_lesen_body
  ∧ Frame ρ "bericht_lesen" bericht_lesen_writes
  ∧ Runs ρ "buendel_von" buendel_von_body
  ∧ Frame ρ "buendel_von" buendel_von_writes
  ∧ RunsLoopIn ρ "buendel_von#1" buendel_von_loop_1_body "v" 0 64
  ∧ Runs ρ "dienst" dienst_body
  ∧ Frame ρ "dienst" dienst_writes
  ∧ RunsLoop ρ "dienst#1" dienst_loop_1_body "#pass"
  ∧ Runs ρ "erster_dringender" erster_dringender_body
  ∧ Frame ρ "erster_dringender" erster_dringender_writes
  ∧ RunsLoopIn ρ "erster_dringender#1" erster_dringender_loop_1_body "i" 0 64

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_abarbeiten_loop_1 : abarbeiten_loop_1_keeps_statement)
    (d_abarbeiten : abarbeiten_meets_statement)
    (d_bericht_lesen : bericht_lesen_meets_statement)
    (d_buendel_von_loop_1 : buendel_von_loop_1_keeps_statement)
    (d_buendel_von : buendel_von_meets_statement)
    (d_erster_dringender_loop_1 : erster_dringender_loop_1_keeps_statement)
    (d_erster_dringender : erster_dringender_meets_statement)
    (d_dienst_loop_1 : dienst_loop_1_keeps_statement)
    (d_dienst : dienst_meets_statement) :
    LoopRule ρ "abarbeiten#1" wellFormed abarbeiten_loop_1_inv
    ∧ Contract ρ "abarbeiten" abarbeiten_requires abarbeiten_post
    ∧ Contract ρ "bericht_lesen" bericht_lesen_requires bericht_lesen_post
    ∧ LoopRule ρ "buendel_von#1" wellFormed buendel_von_loop_1_inv
    ∧ Contract ρ "buendel_von" buendel_von_requires buendel_von_post
    ∧ LoopRule ρ "erster_dringender#1" wellFormed erster_dringender_loop_1_inv
    ∧ Contract ρ "erster_dringender" erster_dringender_requires erster_dringender_post
    ∧ LoopRule ρ "dienst#1" wellFormed dienst_loop_1_inv
    ∧ Contract ρ "dienst" dienst_requires dienst_post := by
  obtain ⟨r_abarbeiten, fr_abarbeiten, rl_abarbeiten_loop_1, r_bericht_lesen, fr_bericht_lesen, r_buendel_von, fr_buendel_von, rl_buendel_von_loop_1, r_dienst, fr_dienst, rl_dienst_loop_1, r_erster_dringender, fr_erster_dringender, rl_erster_dringender_loop_1⟩ := hp
  obtain ⟨c_abschaltung_angefordert, fr_abschaltung_angefordert, c_block_uebertragen, fr_block_uebertragen, c_naechste_menge, fr_naechste_menge⟩ := ha
  have l_abarbeiten_loop_1 : LoopRule ρ "abarbeiten#1" wellFormed abarbeiten_loop_1_inv :=
    looprule_of_body ρ "abarbeiten#1" wellFormed abarbeiten_loop_1_inv abarbeiten_loop_1_body "#pass" rl_abarbeiten_loop_1
      (fun t k hw hi => d_abarbeiten_loop_1 ρ t k hw hi c_block_uebertragen fr_block_uebertragen c_naechste_menge fr_naechste_menge)
  have c_abarbeiten : Contract ρ "abarbeiten" abarbeiten_requires abarbeiten_post :=
    contract_of_duty ρ "abarbeiten" abarbeiten_body abarbeiten_requires abarbeiten_post r_abarbeiten
      (fun t ht => d_abarbeiten ρ t ht.1 ht.2 c_block_uebertragen fr_block_uebertragen c_naechste_menge fr_naechste_menge l_abarbeiten_loop_1)
  have c_bericht_lesen : Contract ρ "bericht_lesen" bericht_lesen_requires bericht_lesen_post :=
    contract_of_duty ρ "bericht_lesen" bericht_lesen_body bericht_lesen_requires bericht_lesen_post r_bericht_lesen
      (fun t ht => d_bericht_lesen ρ t ht.1 ht.2)
  have l_buendel_von_loop_1 : LoopRule ρ "buendel_von#1" wellFormed buendel_von_loop_1_inv :=
    looprule_of_body_in ρ "buendel_von#1" wellFormed buendel_von_loop_1_inv buendel_von_loop_1_body "v" 0 64 rl_buendel_von_loop_1
      (fun t k hlo hhi hw hi => d_buendel_von_loop_1 ρ t k hlo hhi hw hi)
  have c_buendel_von : Contract ρ "buendel_von" buendel_von_requires buendel_von_post :=
    contract_of_duty ρ "buendel_von" buendel_von_body buendel_von_requires buendel_von_post r_buendel_von
      (fun t ht => d_buendel_von ρ t ht.1 ht.2 l_buendel_von_loop_1)
  have l_erster_dringender_loop_1 : LoopRule ρ "erster_dringender#1" wellFormed erster_dringender_loop_1_inv :=
    looprule_of_body_in ρ "erster_dringender#1" wellFormed erster_dringender_loop_1_inv erster_dringender_loop_1_body "i" 0 64 rl_erster_dringender_loop_1
      (fun t k hlo hhi hw hi => d_erster_dringender_loop_1 ρ t k hlo hhi hw hi)
  have c_erster_dringender : Contract ρ "erster_dringender" erster_dringender_requires erster_dringender_post :=
    contract_of_duty ρ "erster_dringender" erster_dringender_body erster_dringender_requires erster_dringender_post r_erster_dringender
      (fun t ht => d_erster_dringender ρ t ht.1 ht.2 l_erster_dringender_loop_1)
  have l_dienst_loop_1 : LoopRule ρ "dienst#1" wellFormed dienst_loop_1_inv :=
    looprule_of_body ρ "dienst#1" wellFormed dienst_loop_1_inv dienst_loop_1_body "#pass" rl_dienst_loop_1
      (fun t k hw hi => d_dienst_loop_1 ρ t k hw hi c_abschaltung_angefordert fr_abschaltung_angefordert c_erster_dringender fr_erster_dringender)
  have c_dienst : Contract ρ "dienst" dienst_requires dienst_post :=
    contract_of_duty ρ "dienst" dienst_body dienst_requires dienst_post r_dienst
      (fun t ht => d_dienst ρ t ht.1 ht.2 c_abschaltung_angefordert fr_abschaltung_angefordert c_erster_dringender fr_erster_dringender l_dienst_loop_1)
  exact ⟨l_abarbeiten_loop_1, c_abarbeiten, c_bericht_lesen, l_buendel_von_loop_1, c_buendel_von, l_erster_dringender_loop_1, c_erster_dringender, l_dienst_loop_1, c_dienst⟩

end GabbroDuty.Duty39Auftragsdienst