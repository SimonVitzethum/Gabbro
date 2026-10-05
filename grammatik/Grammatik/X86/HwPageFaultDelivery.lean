/-
  File:      Grammatik/X86/HwPageFaultDelivery.lean
  Subject:   Page-fault delivery: CR2, error code and the interrupt frame.

  Lane 1309: follow-up of lanes 1283 (`HwPaging`: failing walk is a #PF
  outcome with the faulting address) and 1125/1181 (`HwInterrupts`,
  `HwNestedInterrupts`: checked delivery). Connects ONE family to the
  coherent machine (`HardwareExecution` §11), reusing the accepted
  definitions unchanged (never copied, only lifted).

  Silicon assumptions (ANNAHMEN, provenance per MUSE-REPORT-660, never
  proofs): S1 #PF is vector 14; S2 the error-code bit positions are the
  walk's `PfFehlerCode` order P/W-R/U-S/RSVD/I-D (SDM Vol 3A Table 4-7);
  S3 a #PF gate is an interrupt gate (IF cleared); S4 a fault during
  delivery of a fault escalates to #DF (vector 8, code zero); S5 CR2
  loads the faulting linear address; S6 delivery is not a TSO drain.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwPaging
import Grammatik.X86.HwPreciseFault
import Grammatik.X86.HwNestedInterrupts

namespace Gabbro.Grammatik.X86

/-- Page-fault vector (S1): #PF is vector 14. -/
def pfVektor : Nat := 14

/-- The page-fault vector is 14. -/
theorem pfVektor_vierzehn : pfVektor = 14 := rfl

/-! ## 1. Checked page-fault event and delivery step.

   A failing `seitenGang` walk is a #PF outcome with the faulting
   LINEAR address plus its error code (`HwPaging`). Delivery takes
   that outcome onto the coherent machine: gate 14 from machine
   memory, the accepted check pipeline, stack selection, the
   canonical-pointer check, then the accepted frame push with the
   error code appended. Exceptions take no IF gate (S6 note: IF only
   gates maskable INTR); the new IF follows the gate kind, and the
   witness gate is an interrupt gate (S3: IF cleared). -/

/-- Checked page-fault event: the walk's faulting address and code
    plus the delivery inputs. Gate bytes are NEVER carried: the step
    reads them from machine memory (`liesTorBytes`). -/
structure PfEreignis where
  linear : Nat
  code : PfFehlerCode
  steuer : Steuerstand
  codeOk : Bool
  wechsel : Bool
  neuDpl : Nat
  ssAlt : Wort
  rflags : Wort
  csAlt : Wort
  ripAlt : Wort
  deriving DecidableEq, Repr

/-- Error code as pushed: S2 bit order is the walk's `pfCodeBits`. -/
def pfCodeWort (c : PfFehlerCode) : Wort :=
  BitVec.ofNat 64 (pfCodeBits c)

/-- Build the accepted delivery request: vector 14 (S1), external
    source (no software-INT DPL check), the frame words and the error
    code. The old request is built, never redefined. -/
def pfAnfrage (e : PfEreignis) (t : Wort × Wort)
    (curRsp : Wort) : LieferAnfrage :=
  ⟨pfVektor, t, .extern, e.codeOk, e.wechsel, e.neuDpl, curRsp,
    e.ssAlt, e.rflags, e.csAlt, e.ripAlt, some (pfCodeWort e.code)⟩

/-- The request selects vector 14. -/
theorem pfAnfrage_vektor (e : PfEreignis) (t : Wort × Wort)
    (curRsp : Wort) : (pfAnfrage e t curRsp).vektor = pfVektor := rfl

/-- The request carries the error code. -/
theorem pfAnfrage_code (e : PfEreignis) (t : Wort × Wort)
    (curRsp : Wort) :
    (pfAnfrage e t curRsp).fehlercode = some (pfCodeWort e.code) := rfl

/-- The frame is six words: five frame words plus the error code. -/
theorem pfAnfrage_rahmen_sechs (e : PfEreignis) (t : Wort × Wort)
    (curRsp : Wort) :
    (rahmenWorte (pfAnfrage e t curRsp)).length = 6 := by
  simp [rahmenWorte, pfAnfrage]

/-- Push stage over the accepted frame chain, mirroring
    `schiebeUndStelle`: canonical-pointer check first, then the
    accepted `schiebeRahmen` pushes. The new IF follows the gate
    kind (S3); the switch flag is reported through. -/
def pfFertig (m : HwMaschine) (c : Nat) (e : PfEreignis)
    (g : IdtTor) (q : LieferAnfrage) (rsp : Wort) (gew : Bool) :
    Option (HwMaschine × Bool × Bool) :=
  if !istKanonisch rsp then none
  else match schiebeRahmen m.mem rsp (rahmenWorte q) with
  | none => none
  | some m' => some (asyncMasch m c g q rsp m',
      if g.unterbrechung then false else e.steuer.ifBit, gew)

/-- One page-fault delivery attempt on core `c`. Stage order is
    checks-before-effects: IDT limit, gate-byte read from machine
    memory, the accepted check pipeline, stack selection,
    canonical-pointer check, frame push. The first failure refuses
    with `none` and changes nothing. No IF gate: exceptions are not
    maskable INTR. -/
def pfSchritt (m : HwMaschine) (c : Nat) (e : PfEreignis) :
    Option (HwMaschine × Bool × Bool) :=
  if !torImLimit e.steuer.idtLimit pfVektor then none
  else match liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) with
  | none => none
  | some t =>
    match pruefeTor pfVektor e.steuer.idtLimit t .extern
        e.steuer.cpl e.codeOk with
    | .fehler _ => none
    | .bereit g =>
      match waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel
          ((m.kerne c).register Register.rsp) with
      | .stapelFehler _ => none
      | .behalten rsp => pfFertig m c e g
          (pfAnfrage e t ((m.kerne c).register Register.rsp)) rsp false
      | .wechseln rsp => pfFertig m c e g
          (pfAnfrage e t ((m.kerne c).register Register.rsp)) rsp true

/-- SUCCESS over a switched stack: the frame lands, control follows
    the gate kind, the switch is reported. -/
theorem pfSchritt_zugestellt_wechsel (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2) :
    pfSchritt m c e =
      some (asyncMasch m c g (pfAnfrage e t curRsp) rsp m2,
        if g.unterbrechung then false else e.steuer.ifBit, true) := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hcur, hp, hs, hk, hpush]

/-- SUCCESS over the kept stack: same frame, no switch reported. -/
theorem pfSchritt_zugestellt_behalten (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2) :
    pfSchritt m c e =
      some (asyncMasch m c g (pfAnfrage e t curRsp) rsp m2,
        if g.unterbrechung then false else e.steuer.ifBit, false) := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hcur, hp, hs, hk, hpush]

/-! ## 2. Preservation, agreement, precise fault, handler entry.

   (1) `HwWf` is preserved (profiles untouched); (2) the step
   succeeds exactly where the accepted `liefere` delivers, with the
   same memory, RIP, IF and switch flag; the faulting instruction
   left no architectural effect (the accepted precise-fault
   stillness, `HwPreciseFault`); handler entry runs at the gate
   offset with RSP descended past the six-word frame. -/

/-- Push-stage preservation: the frame changes memory only; the
    successor keeps profiles and all buffers (S6). -/
theorem pfFertig_erhaelt (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (g : IdtTor) (q : LieferAnfrage) (rsp : Wort)
    (gew : Bool) (m' : HwMaschine) (ifNeu gew' : Bool)
    (h : pfFertig m c e g q rsp gew = some (m', ifNeu, gew'))
    (hwf : HwWf m) :
    HwWf m' ∧ ∀ d : Nat, m'.puffer d = m.puffer d := by
  unfold pfFertig at h
  cases hk : istKanonisch rsp with
  | false =>
    rw [hk] at h
    simp at h
  | true =>
    rw [hk] at h
    simp at h
    cases hs : schiebeRahmen m.mem rsp (rahmenWorte q) with
    | none =>
      rw [hs] at h
      simp at h
    | some m2 =>
      rw [hs] at h
      simp at h
      obtain ⟨h1, _, _⟩ := h
      rw [← h1]
      exact ⟨asyncMasch_wf m c g q rsp m2 hwf, fun _ => rfl⟩

/-- Delivery preservation: checks first, effects only through the
    push stage, so profiles and every buffer survive. -/
theorem pfLieferung_erhaelt (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (m' : HwMaschine) (ifNeu gew : Bool)
    (h : pfSchritt m c e = some (m', ifNeu, gew))
    (hwf : HwWf m) :
    HwWf m' ∧ ∀ d : Nat, m'.puffer d = m.puffer d := by
  unfold pfSchritt at h
  cases hl : torImLimit e.steuer.idtLimit pfVektor with
  | false =>
    rw [hl] at h
    simp at h
  | true =>
    rw [hl] at h
    simp at h
    cases hr : liesTorBytes m.mem
        (torAdresse e.steuer.idtBasis pfVektor) with
    | none =>
      rw [hr] at h
      simp at h
    | some t =>
      rw [hr] at h
      simp at h
      cases hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
          e.steuer.cpl e.codeOk with
      | fehler _ =>
        rw [hp] at h
        simp at h
      | bereit g =>
        rw [hp] at h
        simp at h
        cases hs : waehleStapel m.mem e.steuer g.ist e.neuDpl
            e.wechsel ((m.kerne c).register Register.rsp) with
        | stapelFehler _ =>
          rw [hs] at h
          simp at h
        | behalten rsp =>
          rw [hs] at h
          simp at h
          exact pfFertig_erhaelt m c e g _ rsp _ m' ifNeu gew h hwf
        | wechseln rsp =>
          rw [hs] at h
          simp at h
          exact pfFertig_erhaelt m c e g _ rsp _ m' ifNeu gew h hwf

/-- (1) Delivery preserves well-formedness. -/
theorem pfLieferung_wf (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (m' : HwMaschine) (ifNeu gew : Bool)
    (h : pfSchritt m c e = some (m', ifNeu, gew))
    (hwf : HwWf m) : HwWf m' :=
  (pfLieferung_erhaelt m c e m' ifNeu gew h hwf).1

/-- (1) Delivery drains no buffer on any core (S6). -/
theorem pfLieferung_puffer_still (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (m' : HwMaschine) (ifNeu gew : Bool)
    (h : pfSchritt m c e = some (m', ifNeu, gew))
    (hwf : HwWf m) (d : Nat) :
    m'.puffer d = m.puffer d :=
  (pfLieferung_erhaelt m c e m' ifNeu gew h hwf).2 d

/-- (2) AGREEMENT, switched case: the step succeeds exactly where
    the accepted `liefere` delivers, with the same memory, RIP, IF
    and switch flag. The old evaluator is lifted, never redefined. -/
theorem pfSchritt_liefere_wechsel (m : HwMaschine)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2) :
    liefere m.mem e.steuer (pfAnfrage e t curRsp) =
      .zugestellt m2 g.offset
        (if g.unterbrechung then false else e.steuer.ifBit) true :=
  liefere_zugestellt_wechsel m.mem m2 e.steuer (pfAnfrage e t curRsp)
    g rsp hp hs hk hpush

/-- (2) AGREEMENT, kept case. -/
theorem pfSchritt_liefere_behalten (m : HwMaschine)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2) :
    liefere m.mem e.steuer (pfAnfrage e t curRsp) =
      .zugestellt m2 g.offset
        (if g.unterbrechung then false else e.steuer.ifBit) false :=
  liefere_zugestellt_behalten m.mem m2 e.steuer (pfAnfrage e t curRsp)
    g rsp hp hs hk hpush

/-- The faulting instruction left no architectural effect: shared
    memory is still (the accepted precise-fault stillness, reused). -/
theorem pfFehler_speicher_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) :
    m'.mem = m.mem :=
  przFehler_speicher_still m m' c f h

/-- The faulting instruction left no architectural effect: no
    buffered store is dropped on any core. -/
theorem pfFehler_puffer_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) (d : Nat) :
    m'.puffer d = m.puffer d :=
  przFehler_puffer_still m m' c f h d

/-- The faulting instruction left no architectural effect: every
    core view is still. -/
theorem pfFehler_beobachtung_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) (d : Nat)
    (a : Adresse) :
    loadByte (tsoAnsicht m') d a = loadByte (tsoAnsicht m) d a :=
  przFehler_beobachtung_still m m' c f h d a

/-- Handler entry runs at the gate offset. -/
theorem pfEintritt_rip (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher) :
    ((asyncMasch m c g (pfAnfrage e t curRsp) rsp m2).kerne c).rip =
      g.offset :=
  asyncMasch_rip m c g (pfAnfrage e t curRsp) rsp m2

/-- RSP descends past exactly the six-word frame. -/
theorem pfEintritt_rsp (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher) :
    (((asyncMasch m c g (pfAnfrage e t curRsp) rsp m2).kerne c).register
      Register.rsp) =
      rsp - BitVec.ofNat 64
        (8 * (rahmenWorte (pfAnfrage e t curRsp)).length) :=
  asyncMasch_rsp_neu m c g (pfAnfrage e t curRsp) rsp m2

/-- An interrupt gate clears IF on #PF delivery (S3). -/
theorem pfInterrupt_loescht_if (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2)
    (hgate : g.unterbrechung = true) :
    ∃ m' gew, pfSchritt m c e = some (m', false, gew) := by
  have hz := pfSchritt_zugestellt_wechsel m c e t g curRsp rsp m2
    hl hr hcur hp hs hk hpush
  exact ⟨_, _, by simpa [hgate] using hz⟩

/-- A trap gate would keep IF (same stage equations, other kind). -/
theorem pfTrap_behaelt_if (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = some m2)
    (hgate : g.unterbrechung = false) :
    ∃ m' gew, pfSchritt m c e = some (m', e.steuer.ifBit, gew) := by
  have hz := pfSchritt_zugestellt_wechsel m c e t g curRsp rsp m2
    hl hr hcur hp hs hk hpush
  exact ⟨_, _, by simpa [hgate] using hz⟩

/-! ## 3. Extended machine with CR2, adapter plug, refusals, #DF.

   `HwMaschine` stores no IDT/TSS/IF/CR2 state, so the full delivery
   semantics (CR2 load per S5, IF update per S3) lives on the
   extended machine pairing it with per-core control and CR2. The
   `sync` case embeds `HwSchritt` exactly. A fault during delivery
   of the fault escalates to #DF (S4): vector 8, error code zero. -/

/-- Extended machine: coherent machine plus per-core control state
    plus per-core CR2 (S5: the faulting linear address). -/
structure HwPfMaschine where
  hw : HwMaschine
  steuer : Nat → Steuerstand
  cr2 : Nat → Nat

/-- Extended events: synchronous machine steps or page-fault
    delivery. -/
inductive PfMaschEreignis where
  | syncEv : HwEreignis → PfMaschEreignis
  | pfEv : PfEreignis → PfMaschEreignis
  deriving DecidableEq, Repr

/-- Extended step: `HwSchritt` embedded unchanged (control and CR2
    kept), or checked #PF delivery (CR2 loaded with the faulting
    address, control IF updated on the acting core). -/
inductive HwPfSchritt :
    HwPfMaschine → HwPfMaschine → PfMaschEreignis → Prop where
  | sync {s : HwPfMaschine} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.hw m' e) :
      HwPfSchritt s ⟨m', s.steuer, s.cr2⟩ (.syncEv e)
  | pf {s : HwPfMaschine} (c : Nat) (e : PfEreignis)
      {m' : HwMaschine} {ifNeu : Bool} {gew : Bool}
      (hst : e.steuer = s.steuer c)
      (h : pfSchritt s.hw c e = some (m', ifNeu, gew)) :
      HwPfSchritt s ⟨m', fun d =>
        if d = c then { s.steuer c with ifBit := ifNeu }
        else s.steuer d, fun d => if d = c then e.linear else s.cr2 d⟩
        (.pfEv e)

/-- EMBEDDING IN: every coherent step rides along unchanged. -/
theorem hwPfSchritt_sync_einbetten (s : HwPfMaschine)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.hw m' e) :
    HwPfSchritt s ⟨m', s.steuer, s.cr2⟩ (.syncEv e) :=
  .sync h

/-- EMBEDDING ONLY: a sync-labelled extended step IS a coherent step
    with untouched control and CR2. -/
theorem hwPfSchritt_sync_nur (s s' : HwPfMaschine) (e : HwEreignis)
    (h : HwPfSchritt s s' (.syncEv e)) :
    ∃ m', s'.hw = m' ∧ s'.steuer = s.steuer ∧ s'.cr2 = s.cr2 ∧
      HwSchritt s.hw m' e := by
  cases h with
  | sync h => exact ⟨_, rfl, rfl, rfl, h⟩

/-- Every extended step preserves machine well-formedness: old steps
    by the accepted preservation, delivery steps because profiles
    are never touched. -/
theorem hwPfSchritt_wf (s s' : HwPfMaschine)
    (e : PfMaschEreignis) (h : HwPfSchritt s s' e)
    (hwf : HwWf s.hw) : HwWf s'.hw := by
  cases h with
  | sync hstep => exact hwSchritt_wf s.hw _ _ hstep hwf
  | pf c ev hst h => exact pfLieferung_wf s.hw c ev _ _ _ h hwf

/-- CR2 loads the faulting linear address (S5): the delivery step
    is reached and the successor's CR2 on the acting core IS the
    faulting address. -/
theorem hwPfSchritt_cr2 (s : HwPfMaschine) (c : Nat)
    (e : PfEreignis) (m' : HwMaschine) (ifNeu gew : Bool)
    (hst : e.steuer = s.steuer c)
    (h : pfSchritt s.hw c e = some (m', ifNeu, gew)) :
    HwPfSchritt s ⟨m', fun d =>
        if d = c then { s.steuer c with ifBit := ifNeu }
        else s.steuer d, fun d =>
        if d = c then e.linear else s.cr2 d⟩ (.pfEv e) ∧
      (fun d => if d = c then e.linear else s.cr2 d) c = e.linear := by
  refine ⟨HwPfSchritt.pf c e hst h, ?_⟩
  simp

/-- The family adapter: the machine projection of the checked
    delivery step (CR2/IF updates live in the extended relation). -/
def adapterPf : HwAdapter PfEreignis :=
  ⟨fun m c e => (pfSchritt m c e).map (fun r => r.1)⟩

/-- Delivery through the plug is the checked step. -/
theorem adapterPf_treue (m : HwMaschine) (c : Nat) (e : PfEreignis) :
    adapterPf.schritt m c e =
      (pfSchritt m c e).map (fun r => r.1) := rfl

/-- Every admitted plug step preserves well-formedness. -/
theorem adapterPf_wf (m m' : HwMaschine) (c : Nat)
    (e : PfEreignis)
    (h : adapterPf.schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  have h' : (pfSchritt m c e).map (fun r => r.1) = some m' := h
  cases hs : pfSchritt m c e with
  | none =>
    simp [hs] at h'
  | some r =>
    rw [hs] at h'
    simp at h'
    have hs' : pfSchritt m c e = some (r.1, r.2.1, r.2.2) := hs
    rw [← h']
    exact pfLieferung_wf m c e r.1 r.2.1 r.2.2 hs' hwf

/-! ### Planted refusals: every unadmitted shape refuses loudly.

   Each gate fails closed with `none` and changes nothing; the first
   failing stage wins. Exceptions take no IF gate, so there is no
   masked refusal: delivery under IF=false is proved in §5. -/

/-- (3) A vector past the IDT limit refuses before any byte is read. -/
theorem pfSchritt_verweigert_limit (m : HwMaschine) (c : Nat)
    (e : PfEreignis)
    (hl : torImLimit e.steuer.idtLimit pfVektor = false) :
    pfSchritt m c e = none := by
  simp [pfSchritt, hl]

/-- (3) An unreadable gate refuses the whole delivery. -/
theorem pfSchritt_verweigert_torlesung (m : HwMaschine) (c : Nat)
    (e : PfEreignis)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      none) :
    pfSchritt m c e = none := by
  simp [pfSchritt, hl, hr]

/-- (3) A failed descriptor check refuses with no effect. -/
theorem pfSchritt_verweigert_torfehler (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort) (f : TorFehler)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .fehler f) :
    pfSchritt m c e = none := by
  simp [pfSchritt, hl, hr, hp]

/-- (3) STACK FAULT BEFORE PUSH: a failed stack selection refuses and
    pushes nothing. -/
theorem pfSchritt_verweigert_stapel (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp : Wort) (f : TorFehler)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .stapelFehler f) :
    pfSchritt m c e = none := by
  unfold pfSchritt
  simp [hl, hr, hp, hcur, hs]

/-- (3) NONCANONICAL POINTER BEFORE PUSH, switched stack: the loaded
    pointer is checked before the first frame word lands. -/
theorem pfSchritt_verweigert_kanonisch_wechsel (m : HwMaschine)
    (c : Nat) (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = false) :
    pfSchritt m c e = none := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hp, hcur, hs, hk]

/-- (3) NONCANONICAL POINTER BEFORE PUSH, kept stack. -/
theorem pfSchritt_verweigert_kanonisch_behalten (m : HwMaschine)
    (c : Nat) (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = false) :
    pfSchritt m c e = none := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hp, hcur, hs, hk]

/-- (3) DARK STACK, switched case: a refused frame push refuses the
    whole delivery. -/
theorem pfSchritt_verweigert_rahmen_wechsel (m : HwMaschine)
    (c : Nat) (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = none) :
    pfSchritt m c e = none := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hp, hcur, hs, hk, hpush]

/-- (3) DARK STACK, kept case. -/
theorem pfSchritt_verweigert_rahmen_behalten (m : HwMaschine)
    (c : Nat) (e : PfEreignis) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort)
    (hl : torImLimit e.steuer.idtLimit pfVektor = true)
    (hr : liesTorBytes m.mem (torAdresse e.steuer.idtBasis pfVektor) =
      some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor pfVektor e.steuer.idtLimit t .extern
      e.steuer.cpl e.codeOk = .bereit g)
    (hs : waehleStapel m.mem e.steuer g.ist e.neuDpl e.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (pfAnfrage e t curRsp)) = none) :
    pfSchritt m c e = none := by
  unfold pfSchritt pfFertig
  simp [hl, hr, hp, hcur, hs, hk, hpush]

/-- The adapter plug refuses whatever the step refuses: limit case. -/
theorem adapterPf_verweigert_limit (m : HwMaschine) (c : Nat)
    (e : PfEreignis)
    (hl : torImLimit e.steuer.idtLimit pfVektor = false) :
    adapterPf.schritt m c e = none := by
  have h := pfSchritt_verweigert_limit m c e hl
  simp [adapterPf, h]

/-! ### Double fault on a failing delivery (S4).

   A fault during delivery of the fault escalates: the refused
   delivery becomes #DF, vector 8, error code zero (the accepted
   `dfVektor`/`dfCode`, `HwNestedInterrupts`). The full #DF handler
   entry reuses the same push stage and stays downstream. -/

/-- Delivery outcome with escalation: success, or the double fault. -/
inductive PfErgebnis where
  | zugestellt : HwMaschine → Bool → Bool → PfErgebnis
  | doppelFehler : PfErgebnis

/-- Delivery with escalation: success delivers, any refusal is #DF. -/
def pfMitDf (m : HwMaschine) (c : Nat) (e : PfEreignis) : PfErgebnis :=
  match pfSchritt m c e with
  | some (m', ifNeu, gew) => .zugestellt m' ifNeu gew
  | none => .doppelFehler

/-- Fault vector projection: success carries none, #DF is vector 8. -/
def pfVektorVon : PfErgebnis → Option Nat
  | .zugestellt _ _ _ => none
  | .doppelFehler => some dfVektor

/-- Error-code projection: success carries none, #DF carries zero. -/
def pfCodeVon : PfErgebnis → Option Wort
  | .zugestellt _ _ _ => none
  | .doppelFehler => some dfCode

/-- SUCCESS passes through: no escalation. -/
theorem pfMitDf_zugestellt (m : HwMaschine) (c : Nat)
    (e : PfEreignis) (m' : HwMaschine) (ifNeu gew : Bool)
    (h : pfSchritt m c e = some (m', ifNeu, gew)) :
    pfMitDf m c e = .zugestellt m' ifNeu gew := by
  simp [pfMitDf, h]

/-- DOUBLE FAULT (S4): a refused delivery escalates -- vector 8,
    error code zero. -/
theorem pfMitDf_doppelt (m : HwMaschine) (c : Nat)
    (e : PfEreignis)
    (h : pfSchritt m c e = none) :
    pfMitDf m c e = .doppelFehler ∧
      pfVektorVon (pfMitDf m c e) = some dfVektor ∧
      pfCodeVon (pfMitDf m c e) = some dfCode := by
  have hdf : pfMitDf m c e = .doppelFehler := by
    simp [pfMitDf, h]
  refine ⟨hdf, ?_, ?_⟩ <;> rw [hdf] <;> rfl

/-- #DF is vector 8. -/
theorem pfDf_vektor_acht : dfVektor = 8 := rfl

/-- #DF carries error code zero. -/
theorem pfDf_code_null : dfCode = BitVec.ofNat 64 0 := rfl

/-! ## 4. Joint witness: #PF delivery on a two-core machine.

   The walk says the fault (`HwPaging` witness tables: user write
   through the read-only mapping of linear page 2 faults with
   W/R set); delivery loads CR2 with 8192, selects gate 14 from a
   byte-populated IDT, clears IF through the interrupt gate, pushes
   the six-word frame with error code 7, and leaves every buffer
   empty. Reuses the accepted IDT/TSS/stack image shape
   (`loWit`, `witTssByte`) at the vector-14 slot. -/

/-- Witness IDT/TSS/stack bytes: the accepted vector-2 image plus a
    copy of the witness gate at the vector-14 slot (4320), the
    accepted TSS image, zero elsewhere. -/
def pfWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else if a.toNat < 4144 then witIdtByte (a.toNat - 4096)
  else if a.toNat < 4320 then BitVec.ofNat 8 0
  else if a.toNat < 4336 then witIdtByte (a.toNat - 4320 + 32)
  else if a.toNat < 12288 then BitVec.ofNat 8 0
  else if a.toNat < 12336 then witTssByte (a.toNat - 12288)
  else BitVec.ofNat 8 0

/-- Witness readability: both IDT windows, the TSS window and the
    stack window (16320-16384: the six-word frame plus a clear data
    cell at 16328). -/
def pfWitLesbar (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4144) ||
    decide (4320 ≤ a.toNat ∧ a.toNat < 4336) ||
    decide (12288 ≤ a.toNat ∧ a.toNat < 12336) ||
    decide (16320 ≤ a.toNat ∧ a.toNat < 16384)

/-- Witness writability: the stack window only. -/
def pfWitSchreibbar (a : Adresse) : Bool :=
  decide (16320 ≤ a.toNat ∧ a.toNat < 16384)

/-- Witness memory: gate-14 image readable, stack writable. -/
def pfWitMem : Speicher :=
  { bytes := pfWitBytes
    lesbar := pfWitLesbar
    schreibbar := pfWitSchreibbar
    ausfuehrbar := fun _ => false }

/-- Witness control: IDT limit 255 (vector 14 needs 239), TSS limit
    103, CPL 0, IF set -- exceptions take no IF gate. -/
def pfWitSteuer : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 255, BitVec.ofNat 64 12288, 103, 0, true⟩

/-- Witness error code: the RO-write protection fault. -/
def pfWitCode : PfFehlerCode := ⟨true, true, true, false, false⟩

/-- Witness event: faulting address 8192 with the RO-write code and
    the accepted nonzero frame words. -/
def pfWitEv : PfEreignis :=
  ⟨8192, pfWitCode, pfWitSteuer, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660⟩

/-- Witness cores: core 0 runs with the IST-switch RSP, core 1 idles. -/
def pfWitKern : Nat → HwKern
  | 0 => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 20480
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 8192,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: gate-14 IDT/TSS/stack memory, empty
    buffers, full silicon. -/
def pfWitStart : HwMaschine :=
  ⟨pfWitMem, pfWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem pfWitStart_wf : HwWf pfWitStart := by
  intro c f h
  exact (merkmalZugelassen_heisst_beide pfWitStart.hw
    (pfWitStart.bereit c) f h).1

/-- The walk says the fault: user write through the read-only
    mapping faults with W/R set (the accepted `HwPaging` witness,
    lifted unchanged). -/
theorem pfWit_gang :
    (seitenGang witSeitenSteuer witTab ⟨8192, true, true, false⟩).1 =
      .seitenFehler 8192 ⟨true, true, true, false, false⟩ :=
  wit_schreibe_ro_pf

/-- The pushed error code is 7. -/
theorem pfWit_code_sieben :
    pfCodeBits ⟨true, true, true, false, false⟩ = 7 :=
  wit_code_ro

/-- The error-code word is 7. -/
theorem pfWitCode_wort :
    pfCodeWort pfWitCode = BitVec.ofNat 64 7 := by
  decide

/-- Gate address of vector 14 is 4320. -/
theorem pfWit_torAdresse :
    torAdresse (BitVec.ofNat 64 4096) 14 = BitVec.ofNat 64 4320 := by
  decide

/-- Vector 14 fits the witness IDT limit. -/
theorem pfWit_imLimit : torImLimit 255 14 = true := by
  decide

/-- The gate bytes read back as the two witness words. -/
theorem pfWit_liest :
    liesTorBytes pfWitMem (torAdresse pfWitSteuer.idtBasis pfVektor) =
      some (loWit, 0) := by
  decide

/-- The vector-14 gate is admitted: the accepted interrupt gate. -/
theorem pfWit_gate_bereit :
    pruefeTor pfVektor 255 (loWit, (0 : Wort)) .extern 0 true =
      .bereit ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ := by
  decide

/-- The witness TSS slot loads the IST stack. -/
theorem pfWit_stapel :
    waehleStapel pfWitMem pfWitSteuer 1 0 false
      (BitVec.ofNat 64 20480) =
      .wechseln (BitVec.ofNat 64 16384) := by
  decide

/-- The selected stack pointer is canonical. -/
theorem pfWit_kanonisch :
    istKanonisch (BitVec.ofNat 64 16384) = true := by
  decide

/-! ## 5. Delivery outcome, refusals, TSO stage.

   The delivery attempt on core 0, projected the accepted way. -/

/-- The delivery attempt on core 0. -/
def pfWitSchritt : Option (HwMaschine × Bool × Bool) :=
  pfSchritt pfWitStart 0 pfWitEv

/-- Project the delivered memory (witness memory on refusal). -/
def pfMemOut (o : Option (HwMaschine × Bool × Bool)) : Speicher :=
  match o with
  | some (m, _, _) => m.mem
  | none => pfWitMem

/-- Read the handler RIP out of a delivery outcome. -/
def pfRipOut (o : Option (HwMaschine × Bool × Bool))
    (c : Nat) : Option Wort :=
  match o with
  | some (m, _, _) => some (m.kerne c).rip
  | _ => none

/-- Read the new RSP out of a delivery outcome. -/
def pfRspOut (o : Option (HwMaschine × Bool × Bool))
    (c : Nat) : Option Wort :=
  match o with
  | some (m, _, _) => some ((m.kerne c).register Register.rsp)
  | _ => none

/-- Read the new IF out of a delivery outcome. -/
def pfIfOut (o : Option (HwMaschine × Bool × Bool)) : Option Bool :=
  match o with
  | some (_, b, _) => some b
  | _ => none

/-- Read the switch flag out of a delivery outcome. -/
def pfGewOut (o : Option (HwMaschine × Bool × Bool)) : Option Bool :=
  match o with
  | some (_, _, g) => some g
  | _ => none

/-- Read a buffer length out of a delivery outcome. -/
def pfBufOut (o : Option (HwMaschine × Bool × Bool))
    (c : Nat) : Option Nat :=
  match o with
  | some (m, _, _) => some (m.puffer c).length
  | _ => none

/-- Delivery reaches the witness handler offset. -/
theorem pfWit_liefert_rip :
    pfRipOut pfWitSchritt 0 = some (BitVec.ofNat 64 8192) := by
  decide

/-- RSP descends past the six-word frame: 16384 - 48 = 16336. -/
theorem pfWit_liefert_rsp :
    pfRspOut pfWitSchritt 0 = some (BitVec.ofNat 64 16336) := by
  decide

/-- The interrupt gate clears IF (the snapshot had it set). -/
theorem pfWit_liefert_if :
    pfIfOut pfWitSchritt = some false := by
  decide

/-- Delivery reports the IST switch. -/
theorem pfWit_liefert_gew :
    pfGewOut pfWitSchritt = some true := by
  decide

/-- S6 witnessed: no buffer grew on the acting core. -/
theorem pfWit_puffer_0 : pfBufOut pfWitSchritt 0 = some 0 := by
  decide

/-- S6 witnessed: no buffer grew on the other core either. -/
theorem pfWit_puffer_1 : pfBufOut pfWitSchritt 1 = some 0 := by
  decide

/-- Frame word 1 (SS) reads back. -/
theorem pfWit_rahmen_ss :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16376) =
      some (BitVec.ofNat 64 16) := by
  decide

/-- Frame word 2 (old RSP) reads back. -/
theorem pfWit_rahmen_rsp :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16368) =
      some (BitVec.ofNat 64 20480) := by
  decide

/-- Frame word 3 (RFLAGS) reads back. -/
theorem pfWit_rahmen_rflags :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16360) =
      some (BitVec.ofNat 64 514) := by
  decide

/-- Frame word 4 (CS) reads back. -/
theorem pfWit_rahmen_cs :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16352) =
      some (BitVec.ofNat 64 8) := by
  decide

/-- Frame word 5 (RIP) reads back. -/
theorem pfWit_rahmen_rip :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16344) =
      some (BitVec.ofNat 64 4660) := by
  decide

/-- Frame word 6 (error code 7) reads back. -/
theorem pfWit_rahmen_code :
    read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16336) =
      some (BitVec.ofNat 64 7) := by
  decide

/-- The frame observably changes memory. -/
theorem pfWit_aendert_ss :
    pfWitMem.bytes (BitVec.ofNat 64 16376) ≠
      (pfMemOut pfWitSchritt).bytes (BitVec.ofNat 64 16376) := by
  decide

/-- No IF gate: delivery succeeds under IF=false too. -/
theorem pfWit_klar_liefert :
    (pfSchritt pfWitStart 0
      { pfWitEv with steuer := { pfWitSteuer with ifBit := false } }).isSome =
      true := by
  decide

/-- Short IDT limit refuses: vector 14 needs 239, limit is 47. -/
def pfWitSteuerKurz : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 47, BitVec.ofNat 64 12288, 103, 0, true⟩

theorem pfWit_limit_verweigert :
    pfSchritt pfWitStart 0
      { pfWitEv with steuer := pfWitSteuerKurz } = none := by
  decide

/-- Unreadable gate refuses the whole delivery. -/
def pfWitMemTorDunkel : Speicher :=
  { pfWitMem with lesbar := fun _ => false }

def pfWitStartTorDunkel : HwMaschine :=
  { pfWitStart with mem := pfWitMemTorDunkel }

theorem pfWit_tor_verweigert :
    pfSchritt pfWitStartTorDunkel 0 pfWitEv = none := by
  decide

/-- Dark stack refuses: the frame has nowhere to land. -/
def pfWitMemDunkel : Speicher :=
  { pfWitMem with schreibbar := fun _ => false }

def pfWitStartDunkel : HwMaschine :=
  { pfWitStart with mem := pfWitMemDunkel }

theorem pfWit_dunkel_verweigert :
    pfSchritt pfWitStartDunkel 0 pfWitEv = none := by
  decide

/-- Dark-stack delivery escalates to #DF: vector 8. -/
theorem pfWit_dunkel_df_vektor :
    pfVektorVon (pfMitDf pfWitStartDunkel 0 pfWitEv) = some 8 := by
  decide

/-- Dark-stack delivery escalates to #DF: error code zero. -/
theorem pfWit_dunkel_df_code :
    pfCodeVon (pfMitDf pfWitStartDunkel 0 pfWitEv) =
      some (BitVec.ofNat 64 0) := by
  decide

/-! ## 6. Joint TSO stage: issue, forwarding, foreign view, drain.

   Chained onto the delivery successor: core 1 issues byte 42 at a
   writable cell clear of the six-word frame, observes it by
   forwarding, core 0 still reads the old byte (no foreign
   forwarding), and after the drain both cores read 42. Delivery
   left every buffer empty, so the issue starts from the exact
   post-delivery state. -/

/-- Witness data cell: writable in the witness memory, clear of the
    six frame words (lowest frame word covers 16336-16343). -/
def pfWitZelle : Adresse := BitVec.ofNat 64 16328

/-- The machine after delivery, if reached. -/
def pfWitM2 : Option HwMaschine :=
  match pfWitSchritt with
  | some (m, _, _) => some m
  | none => none

/-- Core 1 issues byte 42 at the data cell. -/
def pfWitTso1 : Option TSOZustand :=
  match pfWitM2 with
  | some m2 => issueByte (tsoAnsicht m2) 1 pfWitZelle (BitVec.ofNat 8 42)
  | none => none

/-- Core 1 observes its own byte (forwarding). -/
def pfWitLoadEigen : Option (Option Byte) :=
  match pfWitTso1 with
  | some s => some (loadByte s 1 pfWitZelle)
  | none => none

/-- Core 0 observes the old byte (no foreign forwarding). -/
def pfWitLoadFremd : Option (Option Byte) :=
  match pfWitTso1 with
  | some s => some (loadByte s 0 pfWitZelle)
  | none => none

/-- Core 1 drains its oldest entry. -/
def pfWitTso2 : Option TSOZustand :=
  match pfWitTso1 with
  | some s => flushKern s 1
  | none => none

/-- The shared byte after the drain. -/
def pfWitNachFlush : Option (Option Byte) :=
  match pfWitTso2 with
  | some s => some (some (s.mem.bytes pfWitZelle))
  | none => none

/-- Core 0 reads the drained byte from shared memory. -/
def pfWitFremdNachFlush : Option (Option Byte) :=
  match pfWitTso2 with
  | some s => some (loadByte s 0 pfWitZelle)
  | none => none

/-- The data cell starts zeroed. -/
theorem pfWit_anfang_null :
    pfWitMem.bytes pfWitZelle = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 1 reads its own unflushed byte. -/
theorem pfWit_weiterleitung :
    pfWitLoadEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 0 still reads zero. -/
theorem pfWit_fremd_alt :
    pfWitLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem pfWit_spuelung_aendert :
    pfWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 0 observes the new byte. -/
theorem pfWit_fremd_neu :
    pfWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-! ## 7. Extended-relation witness and the joint `_zeuge`.

   The #PF delivery is a reached `HwPfSchritt.pf` step with CR2
   loaded and the IF update stored on the acting core. -/

/-- Witness control for every core. -/
def pfWitSteuerAlle : Nat → Steuerstand := fun _ => pfWitSteuer

/-- Witness CR2 start: zero everywhere. -/
def pfWitCr2Alle : Nat → Nat := fun _ => 0

/-- The delivery attempt succeeds (as a Boolean observation). -/
theorem pfWit_erfolg_ex : ∃ r, pfWitSchritt = some r := by
  cases h0 : pfWitSchritt with
  | none =>
    have hc := pfWit_liefert_rip
    simp [pfRipOut, h0] at hc
  | some r => exact ⟨r, rfl⟩

/-- The event snapshot agrees with the stored control. -/
theorem pfWit_hst : pfWitEv.steuer = pfWitSteuerAlle 0 := rfl

/-- The #PF delivery is a reached extended step with CR2 loaded. -/
theorem pfWit_relation : ∃ m' : HwMaschine,
    ∃ st' : Nat → Steuerstand, ∃ cr' : Nat → Nat,
    HwPfSchritt ⟨pfWitStart, pfWitSteuerAlle, pfWitCr2Alle⟩
      ⟨m', st', cr'⟩ (.pfEv pfWitEv) ∧ cr' 0 = 8192 := by
  obtain ⟨⟨m', ifNeu, gew⟩, h⟩ := pfWit_erfolg_ex
  refine ⟨m', _, _, HwPfSchritt.pf 0 pfWitEv pfWit_hst h, ?_⟩
  have hev : pfWitEv.linear = 8192 := rfl
  simp [hev]

/-- JOINT WITNESS: the walk's RO-write fault (address 8192, code 7)
    delivered on core 0 over byte-populated canonical memory --
    handler reached, RSP past the six-word frame, IF cleared from a
    set snapshot, IST switch reported, CR2 loaded, buffers still
    empty, six-word frame read back, memory observably changed --
    beside the limit/gate-dark/stack-dark refusals and the #DF
    escalation (vector 8, code zero), a core-1 buffered store with
    owner-only forwarding, its drain observed from both cores,
    well-formedness and the reached extended step. Non-degenerate:
    two cores touch memory, two steps change actual shared-memory
    bytes. -/
theorem pfLiefer_zeuge :
    (seitenGang witSeitenSteuer witTab ⟨8192, true, true, false⟩).1 =
        .seitenFehler 8192 ⟨true, true, true, false, false⟩ ∧
      pfCodeWort pfWitCode = BitVec.ofNat 64 7 ∧
      pfRipOut pfWitSchritt 0 = some (BitVec.ofNat 64 8192) ∧
      pfRspOut pfWitSchritt 0 = some (BitVec.ofNat 64 16336) ∧
      pfIfOut pfWitSchritt = some false ∧
      pfGewOut pfWitSchritt = some true ∧
      pfBufOut pfWitSchritt 0 = some 0 ∧
      pfBufOut pfWitSchritt 1 = some 0 ∧
      read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16376) =
        some (BitVec.ofNat 64 16) ∧
      read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16344) =
        some (BitVec.ofNat 64 4660) ∧
      read64 (pfMemOut pfWitSchritt) (BitVec.ofNat 64 16336) =
        some (BitVec.ofNat 64 7) ∧
      pfWitMem.bytes (BitVec.ofNat 64 16376) ≠
        (pfMemOut pfWitSchritt).bytes (BitVec.ofNat 64 16376) ∧
      (pfSchritt pfWitStart 0
        { pfWitEv with steuer := { pfWitSteuer with ifBit := false } }).isSome =
        true ∧
      pfSchritt pfWitStart 0
        { pfWitEv with steuer := pfWitSteuerKurz } = none ∧
      pfSchritt pfWitStartTorDunkel 0 pfWitEv = none ∧
      pfSchritt pfWitStartDunkel 0 pfWitEv = none ∧
      pfVektorVon (pfMitDf pfWitStartDunkel 0 pfWitEv) = some 8 ∧
      pfCodeVon (pfMitDf pfWitStartDunkel 0 pfWitEv) =
        some (BitVec.ofNat 64 0) ∧
      pfWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      pfWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      pfWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      pfWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      HwWf pfWitStart ∧
      (∃ m' : HwMaschine, ∃ st' : Nat → Steuerstand,
        ∃ cr' : Nat → Nat,
        HwPfSchritt ⟨pfWitStart, pfWitSteuerAlle, pfWitCr2Alle⟩
          ⟨m', st', cr'⟩ (.pfEv pfWitEv) ∧ cr' 0 = 8192) := by
  refine ⟨pfWit_gang, pfWitCode_wort, pfWit_liefert_rip,
    pfWit_liefert_rsp, pfWit_liefert_if, pfWit_liefert_gew,
    pfWit_puffer_0, pfWit_puffer_1, pfWit_rahmen_ss,
    pfWit_rahmen_rip, pfWit_rahmen_code, pfWit_aendert_ss,
    pfWit_klar_liefert, pfWit_limit_verweigert, pfWit_tor_verweigert,
    pfWit_dunkel_verweigert, pfWit_dunkel_df_vektor,
    pfWit_dunkel_df_code, pfWit_weiterleitung, pfWit_fremd_alt,
    pfWit_spuelung_aendert, pfWit_fremd_neu, pfWitStart_wf,
    pfWit_relation⟩

/- CUTS:
   Proved here, over the accepted coherent machine (HardwareExecution
   §11: `HwMaschine`/`HwSchritt`/`HwAdapter`/`HwWf`), the accepted
   page-walk fault (`seitenGang`, `PfFehlerCode`, `pfCodeBits` in
   `HwPaging`, lifted unchanged), the accepted descriptor-layer
   evaluator (`liefere` and its stage lemmas in
   `InterruptDescriptorHardware`) and the accepted precise-fault
   stillness (`przFehler_*` in `HwPreciseFault`), all lifted unchanged:
   - checked page-fault event (`PfEreignis`: walk address and code
     plus delivery inputs; gate bytes read from machine memory, never
     carried) with vector-14 selection (S1) and the error code in S2
     bit order (`pfCodeWort`);
   - delivery step (`pfSchritt`/`pfFertig`) in checks-before-effects
     order with the six-word frame (five frame words plus error
     code), the `HwAdapter` plug (`adapterPf`, replacing the `Unit`
     default for this producer) and the extended machine/relation
     with CR2 (`HwPfMaschine`, `PfMaschEreignis`, `HwPfSchritt`) with
     the exact sync embedding (`hwPfSchritt_sync_einbetten`,
     `hwPfSchritt_sync_nur`);
   - (1) `HwWf` preservation and no TSO drain (S6) for every
     successful delivery;
   - (2) exact agreement with `liefere` (same memory, handler RIP,
     new IF, switch flag), both stack paths;
   - the faulting instruction left no architectural effect
     (memory, buffers, core views still);
   - handler entry: gate offset in RIP, RSP past the six-word frame,
     CR2 loaded with the faulting address (S5);
   - IF behaviour: interrupt gate clears, trap gate keeps (S3);
     exceptions take no IF gate (witnessed under IF set and clear);
   - (3) planted refusals at every stage: over-limit vector,
     unreadable gate, failed descriptor check, failed stack
     selection, noncanonical pointer, failed frame push (both stack
     paths), projected to the adapter plug;
   - #DF escalation (S4): a refused delivery is the double fault,
     vector 8, error code zero (the accepted `dfVektor`/`dfCode`;
     the full #DF handler entry reuses the same push stage and stays
     downstream);
   - (4) joint non-degenerate witness (`pfLiefer_zeuge`): the
     walk's RO-write fault delivered on core 0 (handler 8192, RSP
     16336, IF cleared, IST switch, CR2 8192, empty buffers,
     six-word frame read-back, changed cells) beside three refusals
     and the #DF escalation, a core-1 buffered store with
     owner-only forwarding, its drain observed from both cores,
     well-formedness and the reached extended step.
   NOT proved here, and not claimed:
   - No hardware correspondence: S1-S6 cite the Intel SDM extracts
     as provenance; the proofs show self-consistency of the lifted
     model only.
   - No nested #PF delivery and no handler execution: what runs
     after delivery stays downstream (entry lane).
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the accepted guards; the TSO stage reuses the
     accepted byte equations only.
   - No timing, TLB behaviour, access/dirty write-back interaction
     (the walk's own update lives in `HwPaging`), SMEP/SMAP handling
     (refused by the walk), large-page or noncanonical walk shapes
     (no delivery step is admitted for them), large interrupt frames
     beyond the six-word form, or supervisor-shadow-stack behaviour.
   - `gabbro_ziel` axioms are untouched.
-/

#print axioms pfVektor_vierzehn
#print axioms pfAnfrage_vektor
#print axioms pfAnfrage_code
#print axioms pfAnfrage_rahmen_sechs
#print axioms pfSchritt_zugestellt_wechsel
#print axioms pfSchritt_zugestellt_behalten
#print axioms pfFertig_erhaelt
#print axioms pfLieferung_erhaelt
#print axioms pfLieferung_wf
#print axioms pfLieferung_puffer_still
#print axioms pfSchritt_liefere_wechsel
#print axioms pfSchritt_liefere_behalten
#print axioms pfFehler_speicher_still
#print axioms pfFehler_puffer_still
#print axioms pfFehler_beobachtung_still
#print axioms pfEintritt_rip
#print axioms pfEintritt_rsp
#print axioms pfInterrupt_loescht_if
#print axioms pfTrap_behaelt_if
#print axioms hwPfSchritt_sync_einbetten
#print axioms hwPfSchritt_sync_nur
#print axioms hwPfSchritt_wf
#print axioms hwPfSchritt_cr2
#print axioms adapterPf_treue
#print axioms adapterPf_wf
#print axioms pfSchritt_verweigert_limit
#print axioms pfSchritt_verweigert_torlesung
#print axioms pfSchritt_verweigert_torfehler
#print axioms pfSchritt_verweigert_stapel
#print axioms pfSchritt_verweigert_kanonisch_wechsel
#print axioms pfSchritt_verweigert_kanonisch_behalten
#print axioms pfSchritt_verweigert_rahmen_wechsel
#print axioms pfSchritt_verweigert_rahmen_behalten
#print axioms adapterPf_verweigert_limit
#print axioms pfMitDf_zugestellt
#print axioms pfMitDf_doppelt
#print axioms pfDf_vektor_acht
#print axioms pfDf_code_null
#print axioms pfWitStart_wf
#print axioms pfWit_gang
#print axioms pfWit_code_sieben
#print axioms pfWitCode_wort
#print axioms pfWit_torAdresse
#print axioms pfWit_imLimit
#print axioms pfWit_liest
#print axioms pfWit_gate_bereit
#print axioms pfWit_stapel
#print axioms pfWit_kanonisch
#print axioms pfWit_liefert_rip
#print axioms pfWit_liefert_rsp
#print axioms pfWit_liefert_if
#print axioms pfWit_liefert_gew
#print axioms pfWit_puffer_0
#print axioms pfWit_puffer_1
#print axioms pfWit_rahmen_ss
#print axioms pfWit_rahmen_rsp
#print axioms pfWit_rahmen_rflags
#print axioms pfWit_rahmen_cs
#print axioms pfWit_rahmen_rip
#print axioms pfWit_rahmen_code
#print axioms pfWit_aendert_ss
#print axioms pfWit_klar_liefert
#print axioms pfWit_limit_verweigert
#print axioms pfWit_tor_verweigert
#print axioms pfWit_dunkel_verweigert
#print axioms pfWit_dunkel_df_vektor
#print axioms pfWit_dunkel_df_code
#print axioms pfWit_anfang_null
#print axioms pfWit_weiterleitung
#print axioms pfWit_fremd_alt
#print axioms pfWit_spuelung_aendert
#print axioms pfWit_fremd_neu
#print axioms pfWit_erfolg_ex
#print axioms pfWit_hst
#print axioms pfWit_relation
#print axioms pfLiefer_zeuge

end Gabbro.Grammatik.X86
