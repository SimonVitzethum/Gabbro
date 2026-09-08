/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the
    `.gab`, and a second register over the same thing is the very class this
    folder is written against.

    Every obligation of the register appears below: CARRIED by a theorem of
    this unit, ASSUMED (hardware, foreign code -- named in `Assumed`), or
    REFUSED by name. The line that has to add up:

        @duty 1  messung/netz/udp-echo.gab  total 3  goals 3  refused 0
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

namespace GabbroDuty.DutyUdpEcho

/-! ## What is NOT carried, and why -/

-- Every obligation of this unit is carried by a theorem below.

/-! ## The register, and which theorem carries each line -/

/-
  duty_1  S  summe_1071 :: loop invariant #1  --  carried by `summe_1071_loop_1_keeps`
  duty_2  N  summe_1071 :: ensures #1  --  carried by `summe_1071_meets`
  duty_3  E  arp_lernen :: belegt_hat_adresse  --  carried by `arp_lernen_meets`
-/

/-! ## The well-typed world -- hypothesis `U2`, once for the unit -/

/-- The shape every declared place carries, read from the declarations. -/
def shapeOf : Typing := fun p =>
  match p with
  | .slot "ArpTabelle" _ "belegt" => some .bool
  | .slot "ArpTabelle" _ "ip" => some (.intIn 0 4294967295)
  | .slot "ArpTabelle" _ "mac_hi" => some (.intIn 0 4294967295)
  | .slot "ArpTabelle" _ "mac_lo" => some (.intIn 0 65535)
  | .slot "ArpTabelle" _ "alter" => some (.intIn 0 65535)
  | .slot "Kopfworte.wort" _ "elem" => some (.intIn 0 65535)
  | .field "EthKopf" "ziel_hi" => some (.intIn 0 4294967295)
  | .field "EthKopf" "ziel_lo" => some (.intIn 0 65535)
  | .field "EthKopf" "quell_hi" => some (.intIn 0 4294967295)
  | .field "EthKopf" "quell_lo" => some (.intIn 0 65535)
  | .field "EthKopf" "ethertyp" => some (.intIn 0 65535)
  | .field "IpKopf" "version" => some (.intIn 0 255)
  | .field "IpKopf" "ihl" => some (.intIn 0 255)
  | .field "IpKopf" "dscp" => some (.intIn 0 255)
  | .field "IpKopf" "ecn" => some (.intIn 0 255)
  | .field "IpKopf" "gesamtlaenge" => some (.intIn 0 65535)
  | .field "IpKopf" "kennung" => some (.intIn 0 65535)
  | .field "IpKopf" "flags" => some (.intIn 0 65535)
  | .field "IpKopf" "fragment" => some (.intIn 0 65535)
  | .field "IpKopf" "ttl" => some (.intIn 0 255)
  | .field "IpKopf" "protokoll" => some (.intIn 0 255)
  | .field "IpKopf" "pruefsumme" => some (.intIn 0 65535)
  | .field "IpKopf" "quelle" => some (.intIn 0 4294967295)
  | .field "IpKopf" "ziel" => some (.intIn 0 4294967295)
  | .field "UdpKopf" "quellport" => some (.intIn 0 65535)
  | .field "UdpKopf" "zielport" => some (.intIn 0 65535)
  | .field "UdpKopf" "laenge" => some (.intIn 0 65535)
  | .field "UdpKopf" "summe" => some (.intIn 0 65535)
  | _ => none

def wellFormed (s : State) : Prop := WF shapeOf s.world

/-! ## The invariants of the unit, as expressions -/

/-- `belegt_hat_adresse` over `ArpTabelle`. -/
def inv_belegt_hat_adresse : Expr :=
  (.forallSlots "s" 16 (.bin .or (.un .not (.place "ArpTabelle" (.name "s") "belegt")) (.bin .ne (.place "ArpTabelle" (.name "s") "ip") (.lit (.int 0)))))

/-! ## What is ASSUMED about callees no body of this unit defines -/

/-- `senden` -- a foreign body: its contract is an assumption. -/
def senden_pre : Expr :=
  (.hasShape "laenge" (.intIn 0 65535))

def senden_post (t t' : State) (r : Option Value) : Prop :=
  wellFormed t'
  ∧ ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295) ∨ ∃ e, r = some (.reason e))

def senden_writes : List String := []

def senden_requires (t : State) : Prop := wellFormed t ∧ eval t senden_pre = some (.bool true)

/-- **The initial state** -- what `boot` owes: a well-typed world in which every
    invariant of the unit holds. No register books it; it is named here so that it can
    be assumed BY NAME and not by omission. -/
def Initially (s0 : State) : Prop :=
  wellFormed s0
  ∧ eval s0 inv_belegt_hat_adresse = some (.bool true)

/-- **What is assumed of the environment beyond the bodies of this unit.** -/
def Assumed (ρ : Env) : Prop :=
  Contract ρ "senden" senden_requires senden_post
  ∧ Frame ρ "senden" senden_writes

/-! ## The routines: body and contract -/

/-! ### `arp_lernen` -/

def arp_lernen_body : List Stmt :=
  [(.assign "ArpTabelle" (.name "platz") "belegt" (.lit (.bool true))), (.assign "ArpTabelle" (.name "platz") "ip" (.name "ip")), (.assign "ArpTabelle" (.name "platz") "mac_hi" (.name "hi")), (.assign "ArpTabelle" (.name "platz") "mac_lo" (.name "lo")), (.assign "ArpTabelle" (.name "platz") "alter" (.lit (.int 0)))]

/-- The precondition: the declared shapes and the `requires`. -/
def arp_lernen_pre : Expr :=
  (.bin .and (.hasShape "platz" (.intIn 0 15)) (.bin .and (.hasShape "ip" (.intIn 0 4294967295)) (.bin .and (.hasShape "hi" (.intIn 0 4294967295)) (.bin .and (.hasShape "lo" (.intIn 0 65535)) (.bin .and (.bin .ne (.name "ip") (.lit (.int 0))) (.forallSlots "s" 16 (.bin .or (.un .not (.place "ArpTabelle" (.name "s") "belegt")) (.bin .ne (.place "ArpTabelle" (.name "s") "ip") (.lit (.int 0))))))))))

/-- `belegt_hat_adresse`, as `arp_lernen` keeps it. -/
def arp_lernen_inv_belegt_hat_adresse : Expr :=
  (.forallSlots "s" 16 (.bin .or (.un .not (.place "ArpTabelle" (.name "s") "belegt")) (.bin .ne (.place "ArpTabelle" (.name "s") "ip") (.lit (.int 0)))))

def arp_lernen_writes : List String := ["ArpTabelle"]

/-- What a caller of `arp_lernen` has to bring: a well-typed world and the precondition. -/
def arp_lernen_requires (t : State) : Prop := wellFormed t ∧ eval t arp_lernen_pre = some (.bool true)

/-- What `arp_lernen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arp_lernen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ eval s' arp_lernen_inv_belegt_hat_adresse = some (.bool true)

/-! ### `arp_suchen` -/

def arp_suchen_body : List Stmt :=
  [(.bindName "#returned" (.lit (.bool false))), (.bindName "#ret" (.lit .absent)), (.loop "arp_suchen#1" (.bin .and (.hasShape "ip" (.intIn 0 4294967295)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 4294967295))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true)))))) [(.ite (.bin .and (.place "ArpTabelle" (.name "s") "belegt") (.bin .eq (.place "ArpTabelle" (.name "s") "ip") (.name "ip"))) [(.bindName "#ret" (.place "ArpTabelle" (.name "s") "mac_hi")), (.bindName "#returned" (.lit (.bool true))), .leave] [])]), (.ite (.name "#returned") [(.ret (some (.name "#ret")))] []), (.ret (some (.lit (.int 0))))]

/-- The precondition: the declared shapes and the `requires`. -/
def arp_suchen_pre : Expr :=
  (.hasShape "ip" (.intIn 0 4294967295))

def arp_suchen_writes : List String := []

/-- What a caller of `arp_suchen` has to bring: a well-typed world and the precondition. -/
def arp_suchen_requires (t : State) : Prop := wellFormed t ∧ eval t arp_suchen_pre = some (.bool true)

/-- What `arp_suchen` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def arp_suchen_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)

/-! ### `echo_beantworten` -/

def echo_beantworten_body : List Stmt :=
  [(.ite (.bin .ne (.fieldOf "EthKopf" "ethertyp") (.lit (.int 2048))) [(.ret (some (.lit (.reason "FremderTyp"))))] []), (.bindCall "#m1" "kopf_gueltig" ["k", "w"] [(.name "k"), (.name "w")] (.lit (.bool true))), (.ite (.un .not (.name "#m1")) [(.ret (some (.lit (.reason "Pruefsumme"))))] []), (.ite (.bin .ne (.fieldOf "IpKopf" "ziel") (.name "meine_ip")) [(.ret (some (.lit (.reason "NichtFuerUns"))))] []), (.ite (.bin .ne (.fieldOf "IpKopf" "protokoll") (.lit (.int 17))) [(.ret (some (.lit (.reason "FremderTyp"))))] []), (.bindName "alt_quelle" (.fieldOf "IpKopf" "quelle")), (.assignField "IpKopf" "quelle" (.fieldOf "IpKopf" "ziel")), (.assignField "IpKopf" "ziel" (.name "alt_quelle")), (.assignField "IpKopf" "ttl" (.lit (.int 64))), (.bindCallElse "gesendet" "senden" ["e", "laenge"] [(.name "e"), (.fieldOf "IpKopf" "gesamtlaenge")] (.hasShape "laenge" (.intIn 0 65535)) "grund" [(.ret (some (.lit (.int 0))))]), (.ret (some (.name "gesendet")))]

/-- The precondition: the declared shapes and the `requires`. -/
def echo_beantworten_pre : Expr :=
  (.hasShape "meine_ip" (.intIn 0 4294967295))

def echo_beantworten_writes : List String := ["IpKopf"]

/-- What a caller of `echo_beantworten` has to bring: a well-typed world and the precondition. -/
def echo_beantworten_requires (t : State) : Prop := wellFormed t ∧ eval t echo_beantworten_pre = some (.bool true)

/-- What `echo_beantworten` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def echo_beantworten_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  ((∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295) ∨ ∃ e, r = some (.reason e))

/-! ### `falte` -/

def falte_body : List Stmt :=
  [(.bindName "a" (.bin .add (.bin .band (.name "s") (.lit (.int 65535))) (.bin .shr (.name "s") (.lit (.int 16))))), (.bindName "b" (.bin .add (.bin .band (.name "a") (.lit (.int 65535))) (.bin .shr (.name "a") (.lit (.int 16))))), (.ret (some (.bin .bxor (.bin .band (.name "b") (.lit (.int 65535))) (.lit (.int 65535)))))]

/-- The precondition: the declared shapes and the `requires`. -/
def falte_pre : Expr :=
  (.hasShape "s" (.intIn 0 4294967295))

def falte_writes : List String := []

/-- What a caller of `falte` has to bring: a well-typed world and the precondition. -/
def falte_requires (t : State) : Prop := wellFormed t ∧ eval t falte_pre = some (.bool true)

/-- What `falte` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def falte_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `kopf_gueltig` -/

def kopf_gueltig_body : List Stmt :=
  [(.ite (.bin .ne (.fieldOf "IpKopf" "version") (.lit (.int 4))) [(.ret (some (.lit (.bool false))))] []), (.ite (.bin .lt (.fieldOf "IpKopf" "ihl") (.lit (.int 5))) [(.ret (some (.lit (.bool false))))] []), (.bindCall "#m1" "kopfsumme" ["k"] [(.name "w")] (.lit (.bool true))), (.ite (.bin .ne (.name "#m1") (.lit (.int 0))) [(.ret (some (.lit (.bool false))))] []), (.ret (some (.lit (.bool true))))]

/-- The precondition: the declared shapes and the `requires`. -/
def kopf_gueltig_pre : Expr :=
  (.lit (.bool true))

def kopf_gueltig_writes : List String := []

/-- What a caller of `kopf_gueltig` has to bring: a well-typed world and the precondition. -/
def kopf_gueltig_requires (t : State) : Prop := wellFormed t ∧ eval t kopf_gueltig_pre = some (.bool true)

/-- What `kopf_gueltig` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kopf_gueltig_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ b, r = some (.bool b))

/-! ### `kopfsumme` -/

def kopfsumme_body : List Stmt :=
  [(.bindCall "#m1" "summe_1071" ["k"] [(.name "k")] (.lit (.bool true))), (.retCall "falte" ["s"] [(.name "#m1")] (.hasShape "s" (.intIn 0 4294967295)))]

/-- The precondition: the declared shapes and the `requires`. -/
def kopfsumme_pre : Expr :=
  (.lit (.bool true))

def kopfsumme_writes : List String := []

/-- What a caller of `kopfsumme` has to bring: a well-typed world and the precondition. -/
def kopfsumme_requires (t : State) : Prop := wellFormed t ∧ eval t kopfsumme_pre = some (.bool true)

/-- What `kopfsumme` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def kopfsumme_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 65535)

/-! ### `summe_1071` -/

def summe_1071_body : List Stmt :=
  [(.bindName "s" (.lit (.int 0))), (.loop "summe_1071#1" (.bin .and (.hasShape "s" (.intIn 0 4294967295)) (.bin .le (.name "s") (.lit (.int 4294967295)))) [(.bindName "s" (.bin .add (.name "s") (.place "Kopfworte.wort" (.name "i") "elem")))]), (.ret (some (.name "s")))]

/-- The precondition: the declared shapes and the `requires`. -/
def summe_1071_pre : Expr :=
  (.lit (.bool true))

def summe_1071_writes : List String := []

/-- What a caller of `summe_1071` has to bring: a well-typed world and the precondition. -/
def summe_1071_requires (t : State) : Prop := wellFormed t ∧ eval t summe_1071_pre = some (.bool true)

/-- What `summe_1071` PROMISES: the world stays well-typed, every invariant it maintains
    survives, and its `ensures` hold -- over the entry state (`old`), the exit state
    and the result. -/
def summe_1071_post (s s' : State) (r : Option Value) : Prop :=
  wellFormed s'
  ∧ -- the answer: a value of the declared shape
  (∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)
  ∧ -- ensures #1
  (∃ v, r = some v ∧ eval { world := s'.world, local' := (bindLocal s.local' "result" v) } (.bin .le (.name "result") (.lit (.int 4294967295))) = some (.bool true))

/-! ## The duties: one statement per routine and per loop -/

/-! ### `arp_lernen` -/

/-- **The duty of `arp_lernen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arp_lernen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arp_lernen_pre = some (.bool true)),
    ∃ s', finalState (exec ρ arp_lernen_body s) = some s'
        ∧ arp_lernen_post s s' (finalValue (exec ρ arp_lernen_body s))

theorem arp_lernen_meets : arp_lernen_meets_statement := by
  unfold arp_lernen_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hi_belegt_hat_adresse := (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))))
  gabbro_simp_at hi_belegt_hat_adresse [arp_lernen_inv_belegt_hat_adresse, arp_lernen_pre]
  obtain ⟨w_platz, e_platz, lo_platz, hi_platz⟩ := shape_intIn s "platz" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_ip, e_ip, lo_ip, hi_ip⟩ := shape_intIn s "ip" _ _ (and_left _ _ _ (and_right _ _ _ hpre))
  obtain ⟨w_hi, e_hi, lo_hi, hi_hi⟩ := shape_intIn s "hi" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ hpre)))
  obtain ⟨w_lo, e_lo, lo_lo, hi_lo⟩ := shape_intIn s "lo" _ _ (and_left _ _ _ (and_right _ _ _ (and_right _ _ _ (and_right _ _ _ hpre))))
  have hall := hpre
  gabbro_simp_at hall [arp_lernen_pre, e_platz, e_ip, e_hi, e_lo]
  gabbro_auto [arp_lernen_body, arp_lernen_pre, arp_lernen_post, wellFormed, arp_lernen_inv_belegt_hat_adresse, e_platz, e_ip, e_hi, e_lo, hall] using shapeOf

/-! ### `arp_suchen` -/

/-- Loop `arp_suchen#1` of `arp_suchen`: its body and its invariant (with the shapes of the locals in scope). -/
def arp_suchen_loop_1_inv : Expr :=
  (.bin .and (.hasShape "ip" (.intIn 0 4294967295)) (.bin .and (.hasShape "#returned" .bool) (.bin .or (.bin .and (.name "#returned") (.hasShape "#ret" (.intIn 0 4294967295))) (.bin .and (.un .not (.name "#returned")) (.lit (.bool true))))))

def arp_suchen_loop_1_body : List Stmt :=
  [(.ite (.bin .and (.place "ArpTabelle" (.name "s") "belegt") (.bin .eq (.place "ArpTabelle" (.name "s") "ip") (.name "ip"))) [(.bindName "#ret" (.place "ArpTabelle" (.name "s") "mac_hi")), (.bindName "#returned" (.lit (.bool true))), .leave] [])]

/-- **The loop rule of `arp_suchen#1`, as a statement over one pass.** -/
def arp_suchen_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 16)
    (hwf : wellFormed t)
    (hinv : eval t arp_suchen_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ arp_suchen_loop_1_body { t with local' := bindLocal t.local' "s" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' arp_suchen_loop_1_inv = some (.bool true)

theorem arp_suchen_loop_1_keeps : arp_suchen_loop_1_keeps_statement := by
  unfold arp_suchen_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_ip, e_ip, lo_ip, hi_ip⟩ := shape_intIn t "ip" _ _ (and_left _ _ _ hinv)
  obtain ⟨w__returned, e__returned⟩ := shape_bool t "#returned" (and_left _ _ _ (and_right _ _ _ hinv))
  obtain ⟨n_ArpTabelle_belegt_s, h_ArpTabelle_belegt_s⟩ := WF_bool shapeOf t.world (.slot "ArpTabelle" k "belegt") hwf rfl
  obtain ⟨n_ArpTabelle_ip_s, h_ArpTabelle_ip_s, lo_ArpTabelle_ip_s, hi_ArpTabelle_ip_s⟩ := WF_intIn shapeOf t.world (.slot "ArpTabelle" k "ip") _ _ hwf rfl
  obtain ⟨n_ArpTabelle_mac_hi_s, h_ArpTabelle_mac_hi_s, lo_ArpTabelle_mac_hi_s, hi_ArpTabelle_mac_hi_s⟩ := WF_intIn shapeOf t.world (.slot "ArpTabelle" k "mac_hi") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [arp_suchen_loop_1_inv, e_ip, e__returned, h_ArpTabelle_belegt_s, h_ArpTabelle_ip_s, h_ArpTabelle_mac_hi_s]
  gabbro_auto [arp_suchen_loop_1_body, arp_suchen_loop_1_inv, wellFormed, e_ip, e__returned, h_ArpTabelle_belegt_s, h_ArpTabelle_ip_s, h_ArpTabelle_mac_hi_s, hall] using shapeOf

/-- **The duty of `arp_suchen`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def arp_suchen_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s arp_suchen_pre = some (.bool true))
    -- the rule of loop `arp_suchen#1`
    (l_arp_suchen_loop_1 : LoopRule ρ "arp_suchen#1" wellFormed arp_suchen_loop_1_inv),
    ∃ s', finalState (exec ρ arp_suchen_body s) = some s'
        ∧ arp_suchen_post s s' (finalValue (exec ρ arp_suchen_body s))

theorem arp_suchen_meets : arp_suchen_meets_statement := by
  unfold arp_suchen_meets_statement
  intro ρ s hwf hpre l_arp_suchen_loop_1
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_ip, e_ip, lo_ip, hi_ip⟩ := shape_intIn s "ip" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [arp_suchen_pre, e_ip]
  gabbro_auto [arp_suchen_body, arp_suchen_pre, arp_suchen_post, wellFormed, arp_suchen_loop_1_inv, e_ip, hall] using shapeOf

/-! ### `echo_beantworten` -/

/-- **The duty of `echo_beantworten`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def echo_beantworten_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s echo_beantworten_pre = some (.bool true))
    -- the contract of `kopf_gueltig`
    (c_kopf_gueltig : Contract ρ "kopf_gueltig" kopf_gueltig_requires kopf_gueltig_post)
    -- the frame of `kopf_gueltig`
    (fr_kopf_gueltig : Frame ρ "kopf_gueltig" kopf_gueltig_writes)
    -- the contract of `senden`
    (c_senden : Contract ρ "senden" senden_requires senden_post)
    -- the frame of `senden`
    (fr_senden : Frame ρ "senden" senden_writes),
    ∃ s', finalState (exec ρ echo_beantworten_body s) = some s'
        ∧ echo_beantworten_post s s' (finalValue (exec ρ echo_beantworten_body s))

theorem echo_beantworten_meets : echo_beantworten_meets_statement := by
  unfold echo_beantworten_meets_statement
  intro ρ s hwf hpre c_kopf_gueltig fr_kopf_gueltig c_senden fr_senden
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_meine_ip, e_meine_ip, lo_meine_ip, hi_meine_ip⟩ := shape_intIn s "meine_ip" _ _ hpre
  obtain ⟨n_EthKopf_ethertyp, h_EthKopf_ethertyp, lo_EthKopf_ethertyp, hi_EthKopf_ethertyp⟩ := WF_intIn shapeOf s.world (.field "EthKopf" "ethertyp") _ _ hwf rfl
  obtain ⟨n_IpKopf_ziel, h_IpKopf_ziel, lo_IpKopf_ziel, hi_IpKopf_ziel⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "ziel") _ _ hwf rfl
  obtain ⟨n_IpKopf_protokoll, h_IpKopf_protokoll, lo_IpKopf_protokoll, hi_IpKopf_protokoll⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "protokoll") _ _ hwf rfl
  obtain ⟨n_IpKopf_quelle, h_IpKopf_quelle, lo_IpKopf_quelle, hi_IpKopf_quelle⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "quelle") _ _ hwf rfl
  obtain ⟨n_IpKopf_ttl, h_IpKopf_ttl, lo_IpKopf_ttl, hi_IpKopf_ttl⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "ttl") _ _ hwf rfl
  obtain ⟨n_IpKopf_gesamtlaenge, h_IpKopf_gesamtlaenge, lo_IpKopf_gesamtlaenge, hi_IpKopf_gesamtlaenge⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "gesamtlaenge") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [echo_beantworten_pre, e_meine_ip, h_EthKopf_ethertyp, h_IpKopf_ziel, h_IpKopf_protokoll, h_IpKopf_quelle, h_IpKopf_ttl, h_IpKopf_gesamtlaenge]
  gabbro_auto [echo_beantworten_body, echo_beantworten_pre, echo_beantworten_post, wellFormed, kopf_gueltig_pre, kopf_gueltig_requires, kopf_gueltig_post, kopf_gueltig_writes, Frame_read _ _ _ fr_kopf_gueltig, senden_pre, senden_requires, senden_post, senden_writes, Frame_read _ _ _ fr_senden, e_meine_ip, h_EthKopf_ethertyp, h_IpKopf_ziel, h_IpKopf_protokoll, h_IpKopf_quelle, h_IpKopf_ttl, h_IpKopf_gesamtlaenge, hall] using shapeOf

/-! ### `falte` -/

/-- **The duty of `falte`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def falte_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s falte_pre = some (.bool true)),
    ∃ s', finalState (exec ρ falte_body s) = some s'
        ∧ falte_post s s' (finalValue (exec ρ falte_body s))

theorem falte_meets : falte_meets_statement := by
  unfold falte_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn s "s" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [falte_pre, e_s]
  gabbro_auto [falte_body, falte_pre, falte_post, wellFormed, e_s, hall] using shapeOf

/-! ### `kopf_gueltig` -/

/-- **The duty of `kopf_gueltig`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kopf_gueltig_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kopf_gueltig_pre = some (.bool true))
    -- the contract of `kopfsumme`
    (c_kopfsumme : Contract ρ "kopfsumme" kopfsumme_requires kopfsumme_post)
    -- the frame of `kopfsumme`
    (fr_kopfsumme : Frame ρ "kopfsumme" kopfsumme_writes),
    ∃ s', finalState (exec ρ kopf_gueltig_body s) = some s'
        ∧ kopf_gueltig_post s s' (finalValue (exec ρ kopf_gueltig_body s))

theorem kopf_gueltig_meets : kopf_gueltig_meets_statement := by
  unfold kopf_gueltig_meets_statement
  intro ρ s hwf hpre c_kopfsumme fr_kopfsumme
  simp only [wellFormed] at hwf ⊢
  obtain ⟨n_IpKopf_version, h_IpKopf_version, lo_IpKopf_version, hi_IpKopf_version⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "version") _ _ hwf rfl
  obtain ⟨n_IpKopf_ihl, h_IpKopf_ihl, lo_IpKopf_ihl, hi_IpKopf_ihl⟩ := WF_intIn shapeOf s.world (.field "IpKopf" "ihl") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [kopf_gueltig_pre, h_IpKopf_version, h_IpKopf_ihl]
  gabbro_auto [kopf_gueltig_body, kopf_gueltig_pre, kopf_gueltig_post, wellFormed, kopfsumme_pre, kopfsumme_requires, kopfsumme_post, kopfsumme_writes, Frame_read _ _ _ fr_kopfsumme, h_IpKopf_version, h_IpKopf_ihl, hall] using shapeOf

/-! ### `kopfsumme` -/

/-- **The duty of `kopfsumme`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def kopfsumme_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s kopfsumme_pre = some (.bool true))
    -- the contract of `falte`
    (c_falte : Contract ρ "falte" falte_requires falte_post)
    -- the frame of `falte`
    (fr_falte : Frame ρ "falte" falte_writes)
    -- the contract of `summe_1071`
    (c_summe_1071 : Contract ρ "summe_1071" summe_1071_requires summe_1071_post)
    -- the frame of `summe_1071`
    (fr_summe_1071 : Frame ρ "summe_1071" summe_1071_writes),
    ∃ s', finalState (exec ρ kopfsumme_body s) = some s'
        ∧ kopfsumme_post s s' (finalValue (exec ρ kopfsumme_body s))

theorem kopfsumme_meets : kopfsumme_meets_statement := by
  unfold kopfsumme_meets_statement
  intro ρ s hwf hpre c_falte fr_falte c_summe_1071 fr_summe_1071
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [kopfsumme_pre]
  gabbro_auto [kopfsumme_body, kopfsumme_pre, kopfsumme_post, wellFormed, falte_pre, falte_requires, falte_post, falte_writes, Frame_read _ _ _ fr_falte, summe_1071_pre, summe_1071_requires, summe_1071_post, summe_1071_writes, Frame_read _ _ _ fr_summe_1071, hall] using shapeOf

/-! ### `summe_1071` -/

/-- Loop `summe_1071#1` of `summe_1071`: its body and its invariant (with the shapes of the locals in scope). -/
def summe_1071_loop_1_inv : Expr :=
  (.bin .and (.hasShape "s" (.intIn 0 4294967295)) (.bin .le (.name "s") (.lit (.int 4294967295))))

def summe_1071_loop_1_body : List Stmt :=
  [(.bindName "s" (.bin .add (.name "s") (.place "Kopfworte.wort" (.name "i") "elem")))]

/-- **The loop rule of `summe_1071#1`, as a statement over one pass.** -/
def summe_1071_loop_1_keeps_statement : Prop :=
  ∀ (ρ : Env) (t : State) (k : Int)
    (hlo : 0 ≤ k)
    (hhi : k < 65536)
    (hwf : wellFormed t)
    (hinv : eval t summe_1071_loop_1_inv = some (.bool true)),
    ∃ t', finalState (exec ρ summe_1071_loop_1_body { t with local' := bindLocal t.local' "i" (.int k) }) = some t'
        ∧ wellFormed t' ∧ eval t' summe_1071_loop_1_inv = some (.bool true)

theorem summe_1071_loop_1_keeps : summe_1071_loop_1_keeps_statement := by
  unfold summe_1071_loop_1_keeps_statement
  intro ρ t k hlo hhi hwf hinv
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_s, e_s, lo_s, hi_s⟩ := shape_intIn t "s" _ _ (and_left _ _ _ hinv)
  obtain ⟨n_Kopfworte.wort_elem_i, h_Kopfworte.wort_elem_i, lo_Kopfworte.wort_elem_i, hi_Kopfworte.wort_elem_i⟩ := WF_intIn shapeOf t.world (.slot "Kopfworte.wort" k "elem") _ _ hwf rfl
  have hall := hinv
  gabbro_simp_at hall [summe_1071_loop_1_inv, e_s, h_Kopfworte.wort_elem_i]
  gabbro_auto [summe_1071_loop_1_body, summe_1071_loop_1_inv, wellFormed, e_s, h_Kopfworte.wort_elem_i, hall] using shapeOf

/-- **The duty of `summe_1071`**: under its precondition, the body runs to an end and
    keeps its promise. Every `ensures`, every `V` at its call sites and every
    invariant it maintains is this one theorem. -/
def summe_1071_meets_statement : Prop :=
  ∀ (ρ : Env) (s : State)
    -- the well-formed world (`U2`)
    (hwf : wellFormed s)
    -- the declared shapes, the `requires`, the invariants it maintains
    (hpre : eval s summe_1071_pre = some (.bool true))
    -- the rule of loop `summe_1071#1`
    (l_summe_1071_loop_1 : LoopRule ρ "summe_1071#1" wellFormed summe_1071_loop_1_inv),
    ∃ s', finalState (exec ρ summe_1071_body s) = some s'
        ∧ summe_1071_post s s' (finalValue (exec ρ summe_1071_body s))

theorem summe_1071_meets : summe_1071_meets_statement := by
  unfold summe_1071_meets_statement
  intro ρ s hwf hpre l_summe_1071_loop_1
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [summe_1071_pre]
  gabbro_auto [summe_1071_body, summe_1071_pre, summe_1071_post, wellFormed, summe_1071_loop_1_inv, hall] using shapeOf

/-! ## The wiring -- what the generator owes, and pays

    `Program ρ` says the environment runs the bodies of this unit. From it and
    the duty statements, `unit_closed` yields every contract and every loop rule
    -- in dependency order, so that no person writes the induction over the
    call graph or over the passes of a loop. -/

def Program (ρ : Env) : Prop :=
  Runs ρ "arp_lernen" arp_lernen_body
  ∧ Frame ρ "arp_lernen" arp_lernen_writes
  ∧ Runs ρ "arp_suchen" arp_suchen_body
  ∧ Frame ρ "arp_suchen" arp_suchen_writes
  ∧ RunsLoopIn ρ "arp_suchen#1" arp_suchen_loop_1_body "s" 0 16
  ∧ Runs ρ "echo_beantworten" echo_beantworten_body
  ∧ Frame ρ "echo_beantworten" echo_beantworten_writes
  ∧ Runs ρ "falte" falte_body
  ∧ Frame ρ "falte" falte_writes
  ∧ Runs ρ "kopf_gueltig" kopf_gueltig_body
  ∧ Frame ρ "kopf_gueltig" kopf_gueltig_writes
  ∧ Runs ρ "kopfsumme" kopfsumme_body
  ∧ Frame ρ "kopfsumme" kopfsumme_writes
  ∧ Runs ρ "summe_1071" summe_1071_body
  ∧ Frame ρ "summe_1071" summe_1071_writes
  ∧ RunsLoopIn ρ "summe_1071#1" summe_1071_loop_1_body "i" 0 65536

theorem unit_closed (ρ : Env) (hp : Program ρ) (ha : Assumed ρ)
    (d_arp_lernen : arp_lernen_meets_statement)
    (d_arp_suchen_loop_1 : arp_suchen_loop_1_keeps_statement)
    (d_arp_suchen : arp_suchen_meets_statement)
    (d_falte : falte_meets_statement)
    (d_summe_1071_loop_1 : summe_1071_loop_1_keeps_statement)
    (d_summe_1071 : summe_1071_meets_statement)
    (d_kopfsumme : kopfsumme_meets_statement)
    (d_kopf_gueltig : kopf_gueltig_meets_statement)
    (d_echo_beantworten : echo_beantworten_meets_statement) :
    Contract ρ "arp_lernen" arp_lernen_requires arp_lernen_post
    ∧ LoopRule ρ "arp_suchen#1" wellFormed arp_suchen_loop_1_inv
    ∧ Contract ρ "arp_suchen" arp_suchen_requires arp_suchen_post
    ∧ Contract ρ "falte" falte_requires falte_post
    ∧ LoopRule ρ "summe_1071#1" wellFormed summe_1071_loop_1_inv
    ∧ Contract ρ "summe_1071" summe_1071_requires summe_1071_post
    ∧ Contract ρ "kopfsumme" kopfsumme_requires kopfsumme_post
    ∧ Contract ρ "kopf_gueltig" kopf_gueltig_requires kopf_gueltig_post
    ∧ Contract ρ "echo_beantworten" echo_beantworten_requires echo_beantworten_post := by
  obtain ⟨r_arp_lernen, fr_arp_lernen, r_arp_suchen, fr_arp_suchen, rl_arp_suchen_loop_1, r_echo_beantworten, fr_echo_beantworten, r_falte, fr_falte, r_kopf_gueltig, fr_kopf_gueltig, r_kopfsumme, fr_kopfsumme, r_summe_1071, fr_summe_1071, rl_summe_1071_loop_1⟩ := hp
  obtain ⟨c_senden, fr_senden⟩ := ha
  have c_arp_lernen : Contract ρ "arp_lernen" arp_lernen_requires arp_lernen_post :=
    contract_of_duty ρ "arp_lernen" arp_lernen_body arp_lernen_requires arp_lernen_post r_arp_lernen
      (fun t ht => d_arp_lernen ρ t ht.1 ht.2)
  have l_arp_suchen_loop_1 : LoopRule ρ "arp_suchen#1" wellFormed arp_suchen_loop_1_inv :=
    looprule_of_body_in ρ "arp_suchen#1" wellFormed arp_suchen_loop_1_inv arp_suchen_loop_1_body "s" 0 16 rl_arp_suchen_loop_1
      (fun t k hlo hhi hw hi => d_arp_suchen_loop_1 ρ t k hlo hhi hw hi)
  have c_arp_suchen : Contract ρ "arp_suchen" arp_suchen_requires arp_suchen_post :=
    contract_of_duty ρ "arp_suchen" arp_suchen_body arp_suchen_requires arp_suchen_post r_arp_suchen
      (fun t ht => d_arp_suchen ρ t ht.1 ht.2 l_arp_suchen_loop_1)
  have c_falte : Contract ρ "falte" falte_requires falte_post :=
    contract_of_duty ρ "falte" falte_body falte_requires falte_post r_falte
      (fun t ht => d_falte ρ t ht.1 ht.2)
  have l_summe_1071_loop_1 : LoopRule ρ "summe_1071#1" wellFormed summe_1071_loop_1_inv :=
    looprule_of_body_in ρ "summe_1071#1" wellFormed summe_1071_loop_1_inv summe_1071_loop_1_body "i" 0 65536 rl_summe_1071_loop_1
      (fun t k hlo hhi hw hi => d_summe_1071_loop_1 ρ t k hlo hhi hw hi)
  have c_summe_1071 : Contract ρ "summe_1071" summe_1071_requires summe_1071_post :=
    contract_of_duty ρ "summe_1071" summe_1071_body summe_1071_requires summe_1071_post r_summe_1071
      (fun t ht => d_summe_1071 ρ t ht.1 ht.2 l_summe_1071_loop_1)
  have c_kopfsumme : Contract ρ "kopfsumme" kopfsumme_requires kopfsumme_post :=
    contract_of_duty ρ "kopfsumme" kopfsumme_body kopfsumme_requires kopfsumme_post r_kopfsumme
      (fun t ht => d_kopfsumme ρ t ht.1 ht.2 c_falte fr_falte c_summe_1071 fr_summe_1071)
  have c_kopf_gueltig : Contract ρ "kopf_gueltig" kopf_gueltig_requires kopf_gueltig_post :=
    contract_of_duty ρ "kopf_gueltig" kopf_gueltig_body kopf_gueltig_requires kopf_gueltig_post r_kopf_gueltig
      (fun t ht => d_kopf_gueltig ρ t ht.1 ht.2 c_kopfsumme fr_kopfsumme)
  have c_echo_beantworten : Contract ρ "echo_beantworten" echo_beantworten_requires echo_beantworten_post :=
    contract_of_duty ρ "echo_beantworten" echo_beantworten_body echo_beantworten_requires echo_beantworten_post r_echo_beantworten
      (fun t ht => d_echo_beantworten ρ t ht.1 ht.2 c_kopf_gueltig fr_kopf_gueltig c_senden fr_senden)
  exact ⟨c_arp_lernen, l_arp_suchen_loop_1, c_arp_suchen, c_falte, l_summe_1071_loop_1, c_summe_1071, c_kopfsumme, c_kopf_gueltig, c_echo_beantworten⟩

end GabbroDuty.DutyUdpEcho