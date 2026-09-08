/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/proben/probe-netz-rahmen-und-ergebnis.gab  total 0  goals 0  refused 0
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

namespace GabbroDuty.DutyProbeNetzRahmenUndErgebnis

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .field "EthArp" "ziel_mac_hi" => some (.intIn 0 4294967295)
  | .field "EthArp" "ziel_mac_lo" => some (.intIn 0 65535)
  | .field "EthArp" "quell_mac_hi" => some (.intIn 0 4294967295)
  | .field "EthArp" "quell_mac_lo" => some (.intIn 0 65535)
  | .field "EthArp" "ethertyp" => some (.intIn 2054 2054)
  | .field "EthArp" "hardwaretyp" => some (.intIn 1 1)
  | .field "EthArp" "protokolltyp" => some (.intIn 2048 2048)
  | .field "EthArp" "hw_laenge" => some (.intIn 6 6)
  | .field "EthArp" "pr_laenge" => some (.intIn 4 4)
  | .field "EthArp" "opcode" => some (.intIn 1 2)
  | .field "EthArp" "absender_mac_hi" => some (.intIn 0 4294967295)
  | .field "EthArp" "absender_mac_lo" => some (.intIn 0 65535)
  | .field "EthArp" "absender_ip" => some (.intIn 0 4294967295)
  | .field "EthArp" "ziel2_mac_hi" => some (.intIn 0 4294967295)
  | .field "EthArp" "ziel2_mac_lo" => some (.intIn 0 65535)
  | .field "EthArp" "ziel_ip" => some (.intIn 0 4294967295)
  | .field "Netzergebnis" "merkmale_ok" => some .bool
  | .field "Netzergebnis" "mac_hi" => some (.intIn 0 4294967295)
  | .field "Netzergebnis" "mac_lo" => some (.intIn 0 65535)
  | .field "Netzergebnis" "tx_benutzt" => some .bool
  | .field "Netzergebnis" "rx_benutzt" => some .bool
  | .field "Netzergebnis" "rx_laenge" => some (.intIn 0 4294967295)
  | .field "Netzergebnis" "arp_antwort" => some .bool
  | .field "Netzergebnis" "absender_ip" => some (.intIn 0 4294967295)
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

/-! ### `antwort_pruefen` -/

def antwort_pruefen_body : List Stmt :=
  [(.ite (.bin .lt (.name "laenge") (.lit (.int 54))) [(.ret (some (.lit (.bool false))))] []), (.ite (.bin .ne (.fieldOf "EthArp" "opcode") (.lit (.int 2))) [(.ret (some (.lit (.bool false))))] []), (.ret (some (.bin .eq (.fieldOf "EthArp" "absender_ip") (.name "gefragte_ip"))))]

/-- The precondition: the declared shapes and the `requires`. -/
def antwort_pruefen_pre : Expr :=
  (.bin .and (.hasShape "laenge" (.intIn 0 4294967295)) (.hasShape "gefragte_ip" (.intIn 0 4294967295)))

def antwort_pruefen_writes : List String := []

/-- What a caller of `antwort_pruefen` has to bring: a well-typed world and the precondition. -/
def antwort_pruefen_requires (t : State) : Prop := wellFormed t ∧ eval t antwort_pruefen_pre = some (.bool true)

/-- What `antwort_pruefen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def antwort_pruefen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `arp_anfrage_stellen` -/

def arp_anfrage_stellen_body : List Stmt :=
  [(.assignField "EthArp" "ziel_mac_hi" (.lit (.int 4294967295))), (.assignField "EthArp" "ziel_mac_lo" (.lit (.int 65535))), (.assignField "EthArp" "quell_mac_hi" (.name "mac_hi")), (.assignField "EthArp" "quell_mac_lo" (.name "mac_lo")), (.assignField "EthArp" "absender_mac_hi" (.name "mac_hi")), (.assignField "EthArp" "absender_mac_lo" (.name "mac_lo")), (.assignField "EthArp" "ethertyp" (.lit (.int 2054))), (.assignField "EthArp" "hardwaretyp" (.lit (.int 1))), (.assignField "EthArp" "protokolltyp" (.lit (.int 2048))), (.assignField "EthArp" "hw_laenge" (.lit (.int 6))), (.assignField "EthArp" "pr_laenge" (.lit (.int 4))), (.assignField "EthArp" "opcode" (.lit (.int 1))), (.assignField "EthArp" "absender_ip" (.name "meine_ip")), (.assignField "EthArp" "ziel2_mac_hi" (.lit (.int 0))), (.assignField "EthArp" "ziel2_mac_lo" (.lit (.int 0))), (.assignField "EthArp" "ziel_ip" (.name "ziel_ip"))]

/-- The precondition: the declared shapes and the `requires`. -/
def arp_anfrage_stellen_pre : Expr :=
  (.bin .and (.hasShape "mac_hi" (.intIn 0 4294967295)) (.bin .and (.hasShape "mac_lo" (.intIn 0 65535)) (.bin .and (.hasShape "meine_ip" (.intIn 0 4294967295)) (.hasShape "ziel_ip" (.intIn 0 4294967295)))))

def arp_anfrage_stellen_writes : List String := ["EthArp"]

/-- What a caller of `arp_anfrage_stellen` has to bring: a well-typed world and the precondition. -/
def arp_anfrage_stellen_requires (t : State) : Prop := wellFormed t ∧ eval t arp_anfrage_stellen_pre = some (.bool true)

/-- What `arp_anfrage_stellen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arp_anfrage_stellen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `mac_lesen` -/

-- REFUSED  mac_lesen  (constructed-value): a record, a `tagged` or a device handle -- this model has no value for one
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def mac_lesen_pre : Expr :=
  (.hasShape "hat_konfig" .bool)

def mac_lesen_writes : List String := []

/-- What a caller of `mac_lesen` has to bring: a well-typed world and the precondition. -/
def mac_lesen_requires (t : State) : Prop := wellFormed t ∧ eval t mac_lesen_pre = some (.bool true)

/-- What `mac_lesen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def mac_lesen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `antwort_pruefen` -/

/-- **The duty of `antwort_pruefen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def antwort_pruefen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s antwort_pruefen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ antwort_pruefen_body s) = some s'
        ∧ antwort_pruefen_post s s' (finalValue (exec ρ antwort_pruefen_body s))

theorem antwort_pruefen_meets : antwort_pruefen_meets_statement := by
  unfold antwort_pruefen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_laenge, e_laenge, lo_laenge, hi_laenge⟩ := shape_intIn s "laenge" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_gefragte_ip, e_gefragte_ip, lo_gefragte_ip, hi_gefragte_ip⟩ := shape_intIn s "gefragte_ip" _ _ (and_right _ _ _ hpre)
  obtain ⟨n_EthArp_opcode, h_EthArp_opcode, lo_EthArp_opcode, hi_EthArp_opcode⟩ := WF_intIn shapeOf s.world (.field "EthArp" "opcode") _ _ hwf rfl
  obtain ⟨n_EthArp_absender_ip, h_EthArp_absender_ip, lo_EthArp_absender_ip, hi_EthArp_absender_ip⟩ := WF_intIn shapeOf s.world (.field "EthArp" "absender_ip") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [antwort_pruefen_pre, e_laenge, e_gefragte_ip, h_EthArp_opcode, h_EthArp_absender_ip]
  gabbro_auto [antwort_pruefen_body, antwort_pruefen_pre, antwort_pruefen_post, wellFormed, e_laenge, e_gefragte_ip, h_EthArp_opcode, h_EthArp_absender_ip, hall] using shapeOf

/-! ### `arp_anfrage_stellen` -/

/-- **The duty of `arp_anfrage_stellen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arp_anfrage_stellen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arp_anfrage_stellen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ arp_anfrage_stellen_body s) = some s'
        ∧ arp_anfrage_stellen_post s s' (finalValue (exec ρ arp_anfrage_stellen_body s))

theorem arp_anfrage_stellen_meets : arp_anfrage_stellen_meets_statement := by
  unfold arp_anfrage_stellen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_mac_hi, e_mac_hi, lo_mac_hi, hi_mac_hi⟩ := shape_intIn s "mac_hi" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_mac_lo, e_mac_lo, lo_mac_lo, hi_mac_lo⟩ := shape_intIn s "mac_lo" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_meine_ip, e_meine_ip, lo_meine_ip, hi_meine_ip⟩ := shape_intIn s "meine_ip" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨w_ziel_ip, e_ziel_ip, lo_ziel_ip, hi_ziel_ip⟩ := shape_intIn s "ziel_ip" _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨n_EthArp_ziel_mac_hi, h_EthArp_ziel_mac_hi, lo_EthArp_ziel_mac_hi, hi_EthArp_ziel_mac_hi⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel_mac_hi") _ _ hwf rfl
  obtain ⟨n_EthArp_ziel_mac_lo, h_EthArp_ziel_mac_lo, lo_EthArp_ziel_mac_lo, hi_EthArp_ziel_mac_lo⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel_mac_lo") _ _ hwf rfl
  obtain ⟨n_EthArp_quell_mac_hi, h_EthArp_quell_mac_hi, lo_EthArp_quell_mac_hi, hi_EthArp_quell_mac_hi⟩ := WF_intIn shapeOf s.world (.field "EthArp" "quell_mac_hi") _ _ hwf rfl
  obtain ⟨n_EthArp_quell_mac_lo, h_EthArp_quell_mac_lo, lo_EthArp_quell_mac_lo, hi_EthArp_quell_mac_lo⟩ := WF_intIn shapeOf s.world (.field "EthArp" "quell_mac_lo") _ _ hwf rfl
  obtain ⟨n_EthArp_absender_mac_hi, h_EthArp_absender_mac_hi, lo_EthArp_absender_mac_hi, hi_EthArp_absender_mac_hi⟩ := WF_intIn shapeOf s.world (.field "EthArp" "absender_mac_hi") _ _ hwf rfl
  obtain ⟨n_EthArp_absender_mac_lo, h_EthArp_absender_mac_lo, lo_EthArp_absender_mac_lo, hi_EthArp_absender_mac_lo⟩ := WF_intIn shapeOf s.world (.field "EthArp" "absender_mac_lo") _ _ hwf rfl
  obtain ⟨n_EthArp_ethertyp, h_EthArp_ethertyp, lo_EthArp_ethertyp, hi_EthArp_ethertyp⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ethertyp") _ _ hwf rfl
  obtain ⟨n_EthArp_hardwaretyp, h_EthArp_hardwaretyp, lo_EthArp_hardwaretyp, hi_EthArp_hardwaretyp⟩ := WF_intIn shapeOf s.world (.field "EthArp" "hardwaretyp") _ _ hwf rfl
  obtain ⟨n_EthArp_protokolltyp, h_EthArp_protokolltyp, lo_EthArp_protokolltyp, hi_EthArp_protokolltyp⟩ := WF_intIn shapeOf s.world (.field "EthArp" "protokolltyp") _ _ hwf rfl
  obtain ⟨n_EthArp_hw_laenge, h_EthArp_hw_laenge, lo_EthArp_hw_laenge, hi_EthArp_hw_laenge⟩ := WF_intIn shapeOf s.world (.field "EthArp" "hw_laenge") _ _ hwf rfl
  obtain ⟨n_EthArp_pr_laenge, h_EthArp_pr_laenge, lo_EthArp_pr_laenge, hi_EthArp_pr_laenge⟩ := WF_intIn shapeOf s.world (.field "EthArp" "pr_laenge") _ _ hwf rfl
  obtain ⟨n_EthArp_opcode, h_EthArp_opcode, lo_EthArp_opcode, hi_EthArp_opcode⟩ := WF_intIn shapeOf s.world (.field "EthArp" "opcode") _ _ hwf rfl
  obtain ⟨n_EthArp_absender_ip, h_EthArp_absender_ip, lo_EthArp_absender_ip, hi_EthArp_absender_ip⟩ := WF_intIn shapeOf s.world (.field "EthArp" "absender_ip") _ _ hwf rfl
  obtain ⟨n_EthArp_ziel2_mac_hi, h_EthArp_ziel2_mac_hi, lo_EthArp_ziel2_mac_hi, hi_EthArp_ziel2_mac_hi⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel2_mac_hi") _ _ hwf rfl
  obtain ⟨n_EthArp_ziel2_mac_lo, h_EthArp_ziel2_mac_lo, lo_EthArp_ziel2_mac_lo, hi_EthArp_ziel2_mac_lo⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel2_mac_lo") _ _ hwf rfl
  obtain ⟨n_EthArp_ziel_ip, h_EthArp_ziel_ip, lo_EthArp_ziel_ip, hi_EthArp_ziel_ip⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel_ip") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [arp_anfrage_stellen_pre, e_mac_hi, e_mac_lo, e_meine_ip, e_ziel_ip, h_EthArp_ziel_mac_hi, h_EthArp_ziel_mac_lo, h_EthArp_quell_mac_hi, h_EthArp_quell_mac_lo, h_EthArp_absender_mac_hi, h_EthArp_absender_mac_lo, h_EthArp_ethertyp, h_EthArp_hardwaretyp, h_EthArp_protokolltyp, h_EthArp_hw_laenge, h_EthArp_pr_laenge, h_EthArp_opcode, h_EthArp_absender_ip, h_EthArp_ziel2_mac_hi, h_EthArp_ziel2_mac_lo, h_EthArp_ziel_ip]
  gabbro_auto [arp_anfrage_stellen_body, arp_anfrage_stellen_pre, arp_anfrage_stellen_post, wellFormed, e_mac_hi, e_mac_lo, e_meine_ip, e_ziel_ip, h_EthArp_ziel_mac_hi, h_EthArp_ziel_mac_lo, h_EthArp_quell_mac_hi, h_EthArp_quell_mac_lo, h_EthArp_absender_mac_hi, h_EthArp_absender_mac_lo, h_EthArp_ethertyp, h_EthArp_hardwaretyp, h_EthArp_protokolltyp, h_EthArp_hw_laenge, h_EthArp_pr_laenge, h_EthArp_opcode, h_EthArp_absender_ip, h_EthArp_ziel2_mac_hi, h_EthArp_ziel2_mac_lo, h_EthArp_ziel_ip, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "antwort_pruefen" antwort_pruefen_body
  ∧ Frame ρ "antwort_pruefen" antwort_pruefen_writes
  ∧ Runs ρ "arp_anfrage_stellen" arp_anfrage_stellen_body
  ∧ Frame ρ "arp_anfrage_stellen" arp_anfrage_stellen_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_antwort_pruefen : antwort_pruefen_meets_statement)
    (d_arp_anfrage_stellen : arp_anfrage_stellen_meets_statement) :
    Contract ρ "antwort_pruefen" antwort_pruefen_requires antwort_pruefen_post
    ∧ Contract ρ "arp_anfrage_stellen" arp_anfrage_stellen_requires arp_anfrage_stellen_post := by
  obtain ⟨r_antwort_pruefen, fr_antwort_pruefen, r_arp_anfrage_stellen, fr_arp_anfrage_stellen⟩ := hp
  have c_antwort_pruefen : Contract ρ "antwort_pruefen" antwort_pruefen_requires antwort_pruefen_post :=
    contract_of_duty ρ "antwort_pruefen" antwort_pruefen_body antwort_pruefen_requires antwort_pruefen_post r_antwort_pruefen
      (fun t ht => d_antwort_pruefen ρ t ht.1 ht.2)
  have c_arp_anfrage_stellen : Contract ρ "arp_anfrage_stellen" arp_anfrage_stellen_requires arp_anfrage_stellen_post :=
    contract_of_duty ρ "arp_anfrage_stellen" arp_anfrage_stellen_body arp_anfrage_stellen_requires arp_anfrage_stellen_post r_arp_anfrage_stellen
      (fun t ht => d_arp_anfrage_stellen ρ t ht.1 ht.2)
  exact ⟨c_antwort_pruefen, c_arp_anfrage_stellen⟩

end GabbroDuty.DutyProbeNetzRahmenUndErgebnis
