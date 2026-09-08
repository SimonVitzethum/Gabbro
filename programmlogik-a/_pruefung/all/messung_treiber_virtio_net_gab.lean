/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/treiber/virtio-net.gab  total 5  goals 0  refused 5
        @assumed 5  of the refused are ASSUMPTIONS -- hardware, foreign code -- and 0 are refused forms

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

namespace GabbroDuty.DutyVirtioNet

/-! ## What is NOT carried, and why -/

/-
  A duty that vanishes is noticed; one that gets weaker is not -- so each
  stands here with its reason.

  device-promise (5): ASSUMED -- a promise at hardware Gabbro does not see: an ASSUMPTION
    duty_1  D  Gemein :: transition anerkennen
    duty_2  D  Gemein :: transition treiber_da
    duty_3  D  Gemein :: transition merkmale_ok
    duty_4  D  Gemein :: transition treiber_ok requires
    duty_5  D  Gemein :: transition treiber_ok

-/

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  D  Gemein :: transition anerkennen  --  ASSUMED (device-promise)
  duty_2  D  Gemein :: transition treiber_da  --  ASSUMED (device-promise)
  duty_3  D  Gemein :: transition merkmale_ok  --  ASSUMED (device-promise)
  duty_4  D  Gemein :: transition treiber_ok requires  --  ASSUMED (device-promise)
  duty_5  D  Gemein :: transition treiber_ok  --  ASSUMED (device-promise)
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "AvailRing" _ "kopf" => some (.intIn 0 65535)
  | .slot "Deskring" _ "adresse" => some (.intIn 0 18446744073709551615)
  | .slot "Deskring" _ "laenge" => some (.intIn 0 4294967295)
  | .slot "Deskring" _ "merkmale" => some (.intIn 0 65535)
  | .slot "Deskring" _ "naechst" => some (.intIn 0 65535)
  | .slot "UsedRing" _ "kopf" => some (.intIn 0 4294967295)
  | .slot "UsedRing" _ "laenge" => some (.intIn 0 4294967295)
  | .field "Deskriptor" "adresse" => some (.intIn 0 18446744073709551615)
  | .field "Deskriptor" "laenge" => some (.intIn 0 4294967295)
  | .field "Deskriptor" "weiter" => some .bool
  | .field "Deskriptor" "schreibt" => some .bool
  | .field "Deskriptor" "indirekt" => some .bool
  | .field "Deskriptor" "naechst" => some (.intIn 0 65535)
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
  | .field "GebrauchtEintrag" "kopf" => some (.intIn 0 4294967295)
  | .field "GebrauchtEintrag" "laenge" => some (.intIn 0 4294967295)
  | .global "deskring_gesehen" => some (.intIn 0 65535)
  | .global "availring_gesehen" => some (.intIn 0 65535)
  | .global "AVAIL_IDX" => some (.intIn 0 65535)
  | .global "USED_IDX" => some (.intIn 0 65535)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `anerkennen` -- a `transition` of `Gemein`: a register write behind a frame. -/
def anerkennen_pre : Expr :=
  (.lit (.bool true))

def anerkennen_post (_t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'

def anerkennen_writes : List String := ["Gemein"]

def anerkennen_requires (t : State) : Prop := wellFormed t ∧ eval t anerkennen_pre = some (.bool true)

/-- `merkmale_ok` -- a `transition` of `Gemein`: a register write behind a frame. -/
def merkmale_ok_pre : Expr :=
  (.lit (.bool true))

def merkmale_ok_post (_t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'

def merkmale_ok_writes : List String := ["Gemein"]

def merkmale_ok_requires (t : State) : Prop := wellFormed t ∧ eval t merkmale_ok_pre = some (.bool true)

/-- `treiber_da` -- a `transition` of `Gemein`: a register write behind a frame. -/
def treiber_da_pre : Expr :=
  (.lit (.bool true))

def treiber_da_post (_t t' : State) (_r : Option Value) : Prop :=
  wellFormed t'

def treiber_da_writes : List String := ["Gemein"]

def treiber_da_requires (t : State) : Prop := wellFormed t ∧ eval t treiber_da_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "anerkennen" anerkennen_requires anerkennen_post
  ∧ Frame ρ "anerkennen" anerkennen_writes
  ∧ Contract ρ "merkmale_ok" merkmale_ok_requires merkmale_ok_post
  ∧ Frame ρ "merkmale_ok" merkmale_ok_writes
  ∧ Contract ρ "treiber_da" treiber_da_requires treiber_da_post
  ∧ Frame ρ "treiber_da" treiber_da_writes

/-! ## The routines: body and contract -/

/-! ### `armieren` -/

def armieren_body : List Stmt :=
  [(.assign "Deskring" (.name "i") "adresse" (.name "adresse")), (.assign "Deskring" (.name "i") "laenge" (.name "laenge")), (.assign "Deskring" (.name "i") "merkmale" (.lit (.int 0))), (.assign "Deskring" (.name "i") "naechst" (.lit (.int 0))), (.assign "AvailRing" (.name "i") "kopf" (.name "i")), (.publish "AVAIL_IDX" (.name "i") ["deskring_gesehen", "availring_gesehen"])]

/-- The precondition: the declared shapes and the `requires`. -/
def armieren_pre : Expr :=
  (.bin .and (.hasShape "i" (.intIn 0 7)) (.bin .and (.hasShape "adresse" (.intIn 0 18446744073709551615)) (.bin .and (.hasShape "laenge" (.intIn 0 4294967295)) (.hasShape "schreibt" .bool))))

def armieren_writes : List String := ["Deskring", "AvailRing", "AVAIL_IDX"]

/-- What a caller of `armieren` has to bring: a well-typed world and the precondition. -/
def armieren_requires (t : State) : Prop := wellFormed t ∧ eval t armieren_pre = some (.bool true)

/-- What `armieren` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def armieren_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `arp_stellen` -/

def arp_stellen_body : List Stmt :=
  [(.assignField "EthArp" "ethertyp" (.lit (.int 2054))), (.assignField "EthArp" "opcode" (.lit (.int 1))), (.assignField "EthArp" "absender_ip" (.name "meine_ip")), (.assignField "EthArp" "ziel_ip" (.name "ziel_ip"))]

/-- The precondition: the declared shapes and the `requires`. -/
def arp_stellen_pre : Expr :=
  (.bin .and (.hasShape "meine_ip" (.intIn 0 4294967295)) (.hasShape "ziel_ip" (.intIn 0 4294967295)))

def arp_stellen_writes : List String := ["EthArp"]

/-- What a caller of `arp_stellen` has to bring: a well-typed world and the precondition. -/
def arp_stellen_requires (t : State) : Prop := wellFormed t ∧ eval t arp_stellen_pre = some (.bool true)

/-- What `arp_stellen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arp_stellen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'

/-! ### `stufe_anerkennen` -/

def stufe_anerkennen_body : List Stmt :=
  [(.call "anerkennen" ["d"] [(.name "g")] (.lit (.bool true))), (.ret (some (.name "m")))]

/-- The precondition: the declared shapes and the `requires`. -/
def stufe_anerkennen_pre : Expr :=
  (.lit (.bool true))

def stufe_anerkennen_writes : List String := ["m", "g"]

/-- What a caller of `stufe_anerkennen` has to bring: a well-typed world and the precondition. -/
def stufe_anerkennen_requires (t : State) : Prop := wellFormed t ∧ eval t stufe_anerkennen_pre = some (.bool true)

/-- What `stufe_anerkennen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def stufe_anerkennen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `stufe_laeuft` -/

-- REFUSED  stufe_laeuft  (device-transition): a `transition` whose `requires` has no term here
--   Its contract stands below all the same, so that a caller's theorem can name it;
--   what is missing is the theorem that discharges it.

/-- The precondition: the declared shapes and the `requires`. -/
def stufe_laeuft_pre : Expr :=
  (.lit (.bool true))

def stufe_laeuft_writes : List String := ["m", "g"]

/-- What a caller of `stufe_laeuft` has to bring: a well-typed world and the precondition. -/
def stufe_laeuft_requires (t : State) : Prop := wellFormed t ∧ eval t stufe_laeuft_pre = some (.bool true)

/-- What `stufe_laeuft` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def stufe_laeuft_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `stufe_merkmale` -/

def stufe_merkmale_body : List Stmt :=
  [(.call "merkmale_ok" ["d"] [(.name "g")] (.lit (.bool true))), (.loop "stufe_merkmale#1" (.lit (.bool true)) []), (.ret (some (.name "m")))]

/-- The precondition: the declared shapes and the `requires`. -/
def stufe_merkmale_pre : Expr :=
  (.lit (.bool true))

def stufe_merkmale_writes : List String := ["m", "g"]

/-- What a caller of `stufe_merkmale` has to bring: a well-typed world and the precondition. -/
def stufe_merkmale_requires (t : State) : Prop := wellFormed t ∧ eval t stufe_merkmale_pre = some (.bool true)

/-- What `stufe_merkmale` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def stufe_merkmale_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ### `stufe_treiber` -/

def stufe_treiber_body : List Stmt :=
  [(.call "treiber_da" ["d"] [(.name "g")] (.lit (.bool true))), (.ret (some (.name "m")))]

/-- The precondition: the declared shapes and the `requires`. -/
def stufe_treiber_pre : Expr :=
  (.lit (.bool true))

def stufe_treiber_writes : List String := ["m", "g"]

/-- What a caller of `stufe_treiber` has to bring: a well-typed world and the precondition. -/
def stufe_treiber_requires (t : State) : Prop := wellFormed t ∧ eval t stufe_treiber_pre = some (.bool true)

/-- What `stufe_treiber` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def stufe_treiber_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ v, r = some v)

/-! ## The duties: one statement per routine and per loop -/

/-! ### `armieren` -/

/-- **The duty of `armieren`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def armieren_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s armieren_pre = some (.bool true)),
    ∃ s', finalState (exec ρ armieren_body s) = some s'
        ∧ armieren_post s s' (finalValue (exec ρ armieren_body s))

theorem armieren_meets : armieren_meets_statement := by
  unfold armieren_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_adresse, e_adresse, lo_adresse, hi_adresse⟩ := shape_intIn s "adresse" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_laenge, e_laenge, lo_laenge, hi_laenge⟩ := shape_intIn s "laenge" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨w_schreibt, e_schreibt⟩ := shape_bool s "schreibt" (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  have hall := hpre
  gabbro_simp_at hall [armieren_pre, e_i, e_adresse, e_laenge, e_schreibt]
  gabbro_auto [armieren_body, armieren_pre, armieren_post, wellFormed, e_i, e_adresse, e_laenge, e_schreibt, hall] using shapeOf

/-! ### `arp_stellen` -/

/-- **The duty of `arp_stellen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arp_stellen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arp_stellen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ arp_stellen_body s) = some s'
        ∧ arp_stellen_post s s' (finalValue (exec ρ arp_stellen_body s))

theorem arp_stellen_meets : arp_stellen_meets_statement := by
  unfold arp_stellen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_meine_ip, e_meine_ip, lo_meine_ip, hi_meine_ip⟩ := shape_intIn s "meine_ip" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_ziel_ip, e_ziel_ip, lo_ziel_ip, hi_ziel_ip⟩ := shape_intIn s "ziel_ip" _ _ (and_right _ _ _ hpre)
  obtain ⟨n_EthArp_ethertyp, h_EthArp_ethertyp, lo_EthArp_ethertyp, hi_EthArp_ethertyp⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ethertyp") _ _ hwf rfl
  obtain ⟨n_EthArp_opcode, h_EthArp_opcode, lo_EthArp_opcode, hi_EthArp_opcode⟩ := WF_intIn shapeOf s.world (.field "EthArp" "opcode") _ _ hwf rfl
  obtain ⟨n_EthArp_absender_ip, h_EthArp_absender_ip, lo_EthArp_absender_ip, hi_EthArp_absender_ip⟩ := WF_intIn shapeOf s.world (.field "EthArp" "absender_ip") _ _ hwf rfl
  obtain ⟨n_EthArp_ziel_ip, h_EthArp_ziel_ip, lo_EthArp_ziel_ip, hi_EthArp_ziel_ip⟩ := WF_intIn shapeOf s.world (.field "EthArp" "ziel_ip") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [arp_stellen_pre, e_meine_ip, e_ziel_ip, h_EthArp_ethertyp, h_EthArp_opcode, h_EthArp_absender_ip, h_EthArp_ziel_ip]
  gabbro_auto [arp_stellen_body, arp_stellen_pre, arp_stellen_post, wellFormed, e_meine_ip, e_ziel_ip, h_EthArp_ethertyp, h_EthArp_opcode, h_EthArp_absender_ip, h_EthArp_ziel_ip, hall] using shapeOf

/-! ### `stufe_anerkennen` -/

/-- **The duty of `stufe_anerkennen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def stufe_anerkennen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s stufe_anerkennen_pre = some (.bool true))
    -- the contract of `anerkennen`
    (c_anerkennen : Contract ρ "anerkennen" anerkennen_requires anerkennen_post)
    -- the frame of `anerkennen`
    (fr_anerkennen : Frame ρ "anerkennen" anerkennen_writes),
    ∃ s', finalState (exec ρ stufe_anerkennen_body s) = some s'
        ∧ stufe_anerkennen_post s s' (finalValue (exec ρ stufe_anerkennen_body s))

theorem stufe_anerkennen_meets : stufe_anerkennen_meets_statement := by
  unfold stufe_anerkennen_meets_statement
  intro ρ s hwf hpre c_anerkennen fr_anerkennen
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [stufe_anerkennen_pre]
  gabbro_auto [stufe_anerkennen_body, stufe_anerkennen_pre, stufe_anerkennen_post, wellFormed, anerkennen_pre, anerkennen_requires, anerkennen_post, anerkennen_writes, Frame_read _ _ _ fr_anerkennen, hall] using shapeOf

/-! ### `stufe_merkmale` -/

/-- Loop `stufe_merkmale#1` of `stufe_merkmale`: its body and its invariant (with the shapes of the locals in scope). -/
def stufe_merkmale_loop_1_inv : Expr :=
  (.lit (.bool true))

def stufe_merkmale_loop_1_body : List Stmt :=
  []

/-- **The loop rule of `stufe_merkmale#1`, as a statement over one pass.** -/
def stufe_merkmale_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hwf : wellFormed t)
    (hinv : eval t stufe_merkmale_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ stufe_merkmale_loop_1_body { t with local' := bindLocal t.local' "#pass" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' stufe_merkmale_loop_1_inv = some (.bool true)

theorem stufe_merkmale_loop_1_keeps : stufe_merkmale_loop_1_keeps_statement := by
  unfold stufe_merkmale_loop_1_keeps_statement
  intro ρ t k hwf hinv
  simp only [wellFormed] at hwf ⊢
  have hall := hinv
  gabbro_simp_at hall [stufe_merkmale_loop_1_inv]
  gabbro_auto [stufe_merkmale_loop_1_body, stufe_merkmale_loop_1_inv, wellFormed, hall] using shapeOf

/-- **The duty of `stufe_merkmale`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def stufe_merkmale_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s stufe_merkmale_pre = some (.bool true))
    -- the contract of `merkmale_ok`
    (c_merkmale_ok : Contract ρ "merkmale_ok" merkmale_ok_requires merkmale_ok_post)
    -- the frame of `merkmale_ok`
    (fr_merkmale_ok : Frame ρ "merkmale_ok" merkmale_ok_writes)
    -- the rule of loop `stufe_merkmale#1`
    (l_stufe_merkmale_loop_1 : LoopRule ρ "stufe_merkmale#1" wellFormed stufe_merkmale_loop_1_inv),
    ∃ s', finalState (exec ρ stufe_merkmale_body s) = some s'
        ∧ stufe_merkmale_post s s' (finalValue (exec ρ stufe_merkmale_body s))

theorem stufe_merkmale_meets : stufe_merkmale_meets_statement := by
  unfold stufe_merkmale_meets_statement
  intro ρ s hwf hpre c_merkmale_ok fr_merkmale_ok l_stufe_merkmale_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [stufe_merkmale_pre]
  gabbro_auto [stufe_merkmale_body, stufe_merkmale_pre, stufe_merkmale_post, wellFormed, merkmale_ok_pre, merkmale_ok_requires, merkmale_ok_post, merkmale_ok_writes, Frame_read _ _ _ fr_merkmale_ok, stufe_merkmale_loop_1_inv, hall] using shapeOf

/-! ### `stufe_treiber` -/

/-- **The duty of `stufe_treiber`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def stufe_treiber_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s stufe_treiber_pre = some (.bool true))
    -- the contract of `treiber_da`
    (c_treiber_da : Contract ρ "treiber_da" treiber_da_requires treiber_da_post)
    -- the frame of `treiber_da`
    (fr_treiber_da : Frame ρ "treiber_da" treiber_da_writes),
    ∃ s', finalState (exec ρ stufe_treiber_body s) = some s'
        ∧ stufe_treiber_post s s' (finalValue (exec ρ stufe_treiber_body s))

theorem stufe_treiber_meets : stufe_treiber_meets_statement := by
  unfold stufe_treiber_meets_statement
  intro ρ s hwf hpre c_treiber_da fr_treiber_da
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [stufe_treiber_pre]
  gabbro_auto [stufe_treiber_body, stufe_treiber_pre, stufe_treiber_post, wellFormed, treiber_da_pre, treiber_da_requires, treiber_da_post, treiber_da_writes, Frame_read _ _ _ fr_treiber_da, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "armieren" armieren_body
  ∧ Frame ρ "armieren" armieren_writes
  ∧ Runs ρ "arp_stellen" arp_stellen_body
  ∧ Frame ρ "arp_stellen" arp_stellen_writes
  ∧ Runs ρ "stufe_anerkennen" stufe_anerkennen_body
  ∧ Frame ρ "stufe_anerkennen" stufe_anerkennen_writes
  ∧ Runs ρ "stufe_merkmale" stufe_merkmale_body
  ∧ Frame ρ "stufe_merkmale" stufe_merkmale_writes
  ∧ RunsLoop ρ "stufe_merkmale#1" stufe_merkmale_loop_1_body "#pass"
  ∧ Runs ρ "stufe_treiber" stufe_treiber_body
  ∧ Frame ρ "stufe_treiber" stufe_treiber_writes

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_armieren : armieren_meets_statement)
    (d_arp_stellen : arp_stellen_meets_statement)
    (d_stufe_anerkennen : stufe_anerkennen_meets_statement)
    (d_stufe_merkmale_loop_1 : stufe_merkmale_loop_1_keeps_statement)
    (d_stufe_merkmale : stufe_merkmale_meets_statement)
    (d_stufe_treiber : stufe_treiber_meets_statement) :
    Contract ρ "armieren" armieren_requires armieren_post
    ∧ Contract ρ "arp_stellen" arp_stellen_requires arp_stellen_post
    ∧ Contract ρ "stufe_anerkennen" stufe_anerkennen_requires stufe_anerkennen_post
    ∧ LoopRule ρ "stufe_merkmale#1" wellFormed stufe_merkmale_loop_1_inv
    ∧ Contract ρ "stufe_merkmale" stufe_merkmale_requires stufe_merkmale_post
    ∧ Contract ρ "stufe_treiber" stufe_treiber_requires stufe_treiber_post := by
  obtain ⟨r_armieren, fr_armieren, r_arp_stellen, fr_arp_stellen, r_stufe_anerkennen, fr_stufe_anerkennen, r_stufe_merkmale, fr_stufe_merkmale, rl_stufe_merkmale_loop_1, r_stufe_treiber, fr_stufe_treiber⟩ := hp
  obtain ⟨c_anerkennen, fr_anerkennen, c_merkmale_ok, fr_merkmale_ok, c_treiber_da, fr_treiber_da⟩ := ha
  have c_armieren : Contract ρ "armieren" armieren_requires armieren_post :=
    contract_of_duty ρ "armieren" armieren_body armieren_requires armieren_post r_armieren
      (fun t ht => d_armieren ρ t ht.1 ht.2)
  have c_arp_stellen : Contract ρ "arp_stellen" arp_stellen_requires arp_stellen_post :=
    contract_of_duty ρ "arp_stellen" arp_stellen_body arp_stellen_requires arp_stellen_post r_arp_stellen
      (fun t ht => d_arp_stellen ρ t ht.1 ht.2)
  have c_stufe_anerkennen : Contract ρ "stufe_anerkennen" stufe_anerkennen_requires stufe_anerkennen_post :=
    contract_of_duty ρ "stufe_anerkennen" stufe_anerkennen_body stufe_anerkennen_requires stufe_anerkennen_post r_stufe_anerkennen
      (fun t ht => d_stufe_anerkennen ρ t ht.1 ht.2 c_anerkennen fr_anerkennen)
  have l_stufe_merkmale_loop_1 : LoopRule ρ "stufe_merkmale#1" wellFormed stufe_merkmale_loop_1_inv :=
    looprule_of_body ρ "stufe_merkmale#1" wellFormed stufe_merkmale_loop_1_inv stufe_merkmale_loop_1_body "#pass" rl_stufe_merkmale_loop_1
      (fun t k hw hi => d_stufe_merkmale_loop_1 ρ t k hw hi)
  have c_stufe_merkmale : Contract ρ "stufe_merkmale" stufe_merkmale_requires stufe_merkmale_post :=
    contract_of_duty ρ "stufe_merkmale" stufe_merkmale_body stufe_merkmale_requires stufe_merkmale_post r_stufe_merkmale
      (fun t ht => d_stufe_merkmale ρ t ht.1 ht.2 c_merkmale_ok fr_merkmale_ok l_stufe_merkmale_loop_1)
  have c_stufe_treiber : Contract ρ "stufe_treiber" stufe_treiber_requires stufe_treiber_post :=
    contract_of_duty ρ "stufe_treiber" stufe_treiber_body stufe_treiber_requires stufe_treiber_post r_stufe_treiber
      (fun t ht => d_stufe_treiber ρ t ht.1 ht.2 c_treiber_da fr_treiber_da)
  exact ⟨c_armieren, c_arp_stellen, c_stufe_anerkennen, l_stufe_merkmale_loop_1, c_stufe_merkmale, c_stufe_treiber⟩

end GabbroDuty.DutyVirtioNet