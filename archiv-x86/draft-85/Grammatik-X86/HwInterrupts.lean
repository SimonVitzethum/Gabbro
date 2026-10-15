/-
  File:      Grammatik/X86/HwInterrupts.lean
  Subject:   Asynchronous interrupt delivery on the coherent multicore machine.

  Lane 1125: the interrupt672 family producer. The checked asynchronous
  event type (`AsyncEreignis`) and its `HwAdapter` plug
  (`adapterInterrupt1125`) over the accepted `HwMaschine`/`HwSchritt`
  (HardwareExecution.lean §11), lifting the accepted descriptor-layer
  evaluator `liefere` (InterruptDescriptorHardware.lean) unchanged.
  Delivery never drains the per-core TSO store buffer; IF/mask gating
  follows the SDM; every silicon fact beyond self-consistency is named
  in the ANNAHMEN block in §1 and the CUTS block at the end.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.InterruptDescriptorHardware

namespace Gabbro.Grammatik.X86

/-! ## 1. Checked asynchronous event type and admission gates.

   Silicon assumptions (ANNAHMEN, checked against the clone-local Intel
   SDM extracts; provenance, never proofs):
   - S1: maskable external interrupts (INTR) are gated by IF; NMI
     bypasses IF (Vol. 3 interrupt delivery; Table 6-1).
   - S2: NMI arrives on vector 2; maskable external vectors are
     32-255 (vectors 0-31 are synchronous exceptions, Table 6-1).
   - S3: delivery is NOT a serialising drain of the per-core store
     buffer (memory-ordering chapter: only stated serialising forms
     drain; delivery alone leaves pending stores buffered).
-/

/-- Delivery kind: maskable INTR (IF-gated) or NMI (bypasses IF). -/
inductive AsyncArt where
  | maskierbar : AsyncArt
  | nichtMaskierbar : AsyncArt
  deriving DecidableEq, Repr

/-- Checked asynchronous event: vector, kind, control snapshot, code-row
    input, privilege-change data and frame words. Gate bytes are NEVER
    carried: the step reads them from machine memory (`liesTorBytes`). -/
structure AsyncEreignis where
  vektor : Nat
  art : AsyncArt
  steuer : Steuerstand
  codeOk : Bool
  wechsel : Bool
  neuDpl : Nat
  ssAlt : Wort
  rflags : Wort
  csAlt : Wort
  ripAlt : Wort
  fehlercode : Option Wort
  deriving DecidableEq, Repr

/-- Vector admission (S2): NMI is vector 2; maskable external vectors
    are 32-255 (0-31 are synchronous exceptions, never async). -/
def asyncVektorOk (ev : AsyncEreignis) : Bool :=
  match ev.art with
  | .nichtMaskierbar => decide (ev.vektor = 2)
  | .maskierbar => decide (32 ≤ ev.vektor ∧ ev.vektor ≤ 255)

/-- IF gate (S1): maskable delivery needs IF; NMI always passes. -/
def asyncBereit (ev : AsyncEreignis) : Bool :=
  match ev.art with
  | .nichtMaskierbar => true
  | .maskierbar => ev.steuer.ifBit

/-- Equation: the NMI vector check. -/
theorem asyncVektorOk_nmi (ev : AsyncEreignis) :
    asyncVektorOk { ev with art := .nichtMaskierbar } =
      decide (ev.vektor = 2) := rfl

/-- Equation: the maskable range check. -/
theorem asyncVektorOk_maskierbar (ev : AsyncEreignis) :
    asyncVektorOk { ev with art := .maskierbar } =
      decide (32 ≤ ev.vektor ∧ ev.vektor ≤ 255) := rfl

/-- Equation: the maskable IF read. -/
theorem asyncBereit_maskierbar (ev : AsyncEreignis) :
    asyncBereit { ev with art := .maskierbar } = ev.steuer.ifBit := rfl

/-- NMI bypasses the IF gate, whatever IF says. -/
theorem asyncBereit_nmi (ev : AsyncEreignis) :
    asyncBereit { ev with art := .nichtMaskierbar } = true := rfl

/-- A masked maskable event is refused. -/
theorem asyncBereit_maskiert (ev : AsyncEreignis)
    (h : ev.steuer.ifBit = false) :
    asyncBereit { ev with art := .maskierbar } = false := by
  rw [asyncBereit_maskierbar, h]

/-- A non-2 vector is no NMI. -/
theorem asyncVektor_nmi_falsch (ev : AsyncEreignis)
    (h : ev.vektor ≠ 2) :
    asyncVektorOk { ev with art := .nichtMaskierbar } = false := by
  rw [asyncVektorOk_nmi, decide_eq_false_iff_not]
  exact h

/-- An exception-range vector is no maskable external interrupt. -/
theorem asyncVektor_maskierbar_klein (ev : AsyncEreignis)
    (h : ev.vektor < 32) :
    asyncVektorOk { ev with art := .maskierbar } = false := by
  rw [asyncVektorOk_maskierbar, decide_eq_false_iff_not]
  omega

/-! ## 2. Request builder and delivery successor on the machine.

   The accepted request is built, never redefined: external source,
   gate bytes READ from machine memory (the caller passes the read
   words), current RSP from the acting core's registers. The successor
   installs new memory, the handler RIP and the frame-descended RSP;
   buffers, profiles and all other core data are untouched. -/

/-- Build the accepted delivery request over read gate words `t` and
    the acting core's current RSP. -/
def asyncAnfrage (ev : AsyncEreignis) (t : Wort × Wort)
    (curRsp : Wort) : LieferAnfrage :=
  ⟨ev.vektor, t, .extern, ev.codeOk, ev.wechsel, ev.neuDpl, curRsp,
    ev.ssAlt, ev.rflags, ev.csAlt, ev.ripAlt, ev.fehlercode⟩

/-- Delivery successor: new memory `m2`, handler RIP, RSP descended
    past the pushed frame; everything else (buffers, profiles, flags,
    XMM, FP, other cores) is copied. -/
def asyncMasch (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) : HwMaschine :=
  { m with mem := m2, kerne := fun d =>
    if d = c then
      ⟨fun q' => if q' = Register.rsp then
          rsp - BitVec.ofNat 64 (8 * (rahmenWorte q).length)
        else (m.kerne c).register q',
        (m.kerne c).flags, g.offset, (m.kerne c).xmm, (m.kerne c).fp⟩
    else m.kerne d }

/-- The successor runs the handler: RIP is the gate offset. -/
theorem asyncMasch_rip (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) :
    ((asyncMasch m c g q rsp m2).kerne c).rip = g.offset := by
  simp [asyncMasch]

/-- The stack effect: RSP descends past exactly the pushed frame. -/
theorem asyncMasch_rsp_neu (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) :
    (((asyncMasch m c g q rsp m2).kerne c).register Register.rsp) =
      rsp - BitVec.ofNat 64 (8 * (rahmenWorte q).length) := by
  simp [asyncMasch]

/-- The successor carries the pushed memory. -/
theorem asyncMasch_mem (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) :
    (asyncMasch m c g q rsp m2).mem = m2 := rfl

/-- S3, machine form: delivery never touches any store buffer. -/
theorem asyncMasch_puffer_still (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher) (d : Nat) :
    (asyncMasch m c g q rsp m2).puffer d = m.puffer d := rfl

/-- Profiles are untouched, so well-formedness survives by itself. -/
theorem asyncMasch_wf (m : HwMaschine) (c : Nat) (g : IdtTor)
    (q : LieferAnfrage) (rsp : Wort) (m2 : Speicher)
    (hwf : HwWf m) : HwWf (asyncMasch m c g q rsp m2) := hwf

/-! ## 3. The checked delivery step and its `HwAdapter` plug.

   Stage order is checks-before-effects: vector admission, IF gate,
   IDT limit, gate-byte read from machine memory, the accepted check
   pipeline, stack selection, canonical-pointer check, frame push.
   The first failure refuses with `none` and changes nothing. -/

/-- Push stage over the accepted frame chain, mirroring
    `schiebeUndStelle`: canonical-pointer check first, then the
    accepted `write64` pushes. Returns the machine, the new IF and
    the switch flag. -/
def asyncFertig (m : HwMaschine) (c : Nat) (st : Steuerstand)
    (g : IdtTor) (q : LieferAnfrage) (rsp : Wort) (gew : Bool) :
    Option (HwMaschine × Bool × Bool) :=
  if !istKanonisch rsp then none
  else match schiebeRahmen m.mem rsp (rahmenWorte q) with
  | none => none
  | some m' => some (asyncMasch m c g q rsp m',
      if g.unterbrechung then false else st.ifBit, gew)

/-- One async delivery attempt on core `c` under control snapshot `st`.
    Gate bytes come from machine memory; nothing is trusted parsed. -/
def asyncSchritt (m : HwMaschine) (c : Nat) (ev : AsyncEreignis)
    (st : Steuerstand) : Option (HwMaschine × Bool × Bool) :=
  if !asyncVektorOk ev then none
  else if !asyncBereit ev then none
  else if !torImLimit st.idtLimit ev.vektor then none
  else match liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) with
  | none => none
  | some t =>
    match pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk with
    | .fehler _ => none
    | .bereit g =>
      match waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel
          ((m.kerne c).register Register.rsp) with
      | .stapelFehler _ => none
      | .behalten rsp => asyncFertig m c st g
          (asyncAnfrage ev t ((m.kerne c).register Register.rsp)) rsp false
      | .wechseln rsp => asyncFertig m c st g
          (asyncAnfrage ev t ((m.kerne c).register Register.rsp)) rsp true

/-- The interrupt672 producer plug: the event carries its control
    snapshot; the machine projection is the first component. -/
def adapterInterrupt1125 : HwAdapter AsyncEreignis :=
  ⟨fun m c ev => (asyncSchritt m c ev ev.steuer).map (fun r => r.1)⟩

/-! ## 4. Extended machine and step relation; exact sync embedding.

   `HwMaschine` stores no IDT/TSS/IF state, so the full async
   semantics (including the IF update) lives on the extended machine
   pairing it with per-core control. The `sync` case embeds
   `HwSchritt` exactly; the `async` case requires the event's control
   snapshot to agree with the stored one. -/

/-- Extended machine: coherent machine plus per-core control state. -/
structure HwIntMaschine where
  hw : HwMaschine
  steuer : Nat → Steuerstand

/-- Extended events: synchronous machine steps or async delivery. -/
inductive IntEreignis where
  | syncEv : HwEreignis → IntEreignis
  | asyncEv : AsyncEreignis → IntEreignis
  deriving DecidableEq, Repr

/-- Extended step: `HwSchritt` embedded unchanged (control kept), or
    checked delivery (control IF updated on the acting core). -/
inductive HwIntSchritt :
    HwIntMaschine → HwIntMaschine → IntEreignis → Prop where
  | sync {s : HwIntMaschine} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.hw m' e) :
      HwIntSchritt s ⟨m', s.steuer⟩ (.syncEv e)
  | async {s : HwIntMaschine} (c : Nat) (ev : AsyncEreignis)
      {m' : HwMaschine} {ifNeu : Bool} {gew : Bool}
      (hst : ev.steuer = s.steuer c)
      (h : asyncSchritt s.hw c ev (s.steuer c) = some (m', ifNeu, gew)) :
      HwIntSchritt s ⟨m', fun d =>
        if d = c then { s.steuer c with ifBit := ifNeu }
        else s.steuer d⟩ (.asyncEv ev)

/-- EMBEDDING IN: every coherent step rides along unchanged. -/
theorem hwIntSchritt_sync_einbetten (s : HwIntMaschine)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.hw m' e) :
    HwIntSchritt s ⟨m', s.steuer⟩ (.syncEv e) :=
  .sync h

/-- EMBEDDING ONLY: a sync-labelled extended step IS a coherent step
    with untouched control. -/
theorem hwIntSchritt_sync_nur (s s' : HwIntMaschine) (e : HwEreignis)
    (h : HwIntSchritt s s' (.syncEv e)) :
    ∃ m', s'.hw = m' ∧ s'.steuer = s.steuer ∧ HwSchritt s.hw m' e := by
  cases h with
  | sync h => exact ⟨_, rfl, rfl, h⟩

/-! ## 5. Success equations, preservation and accepted agreement.

   Stated in the accepted `liefere_zugestellt_*` style: every stage
   equation as a premise, the machine result as the conclusion. -/

/-- SUCCESS over a switched stack: the frame lands, control follows
    the gate kind, the switch is reported. -/
theorem asyncSchritt_zugestellt_wechsel (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2) :
    asyncSchritt m c ev st =
      some (asyncMasch m c g (asyncAnfrage ev t curRsp) rsp m2,
        if g.unterbrechung then false else st.ifBit, true) := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk, hpush]

/-- SUCCESS over the kept stack: same frame, no switch reported. -/
theorem asyncSchritt_zugestellt_behalten (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2) :
    asyncSchritt m c ev st =
      some (asyncMasch m c g (asyncAnfrage ev t curRsp) rsp m2,
        if g.unterbrechung then false else st.ifBit, false) := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk, hpush]

/-- (1) WELL-FORMEDNESS, switched case: every successful delivery
    preserves `HwWf` (profiles are never touched). -/
theorem asyncSchritt_zugestellt_wechsel_wf (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2)
    (hwf : HwWf m) :
    ∀ r, asyncSchritt m c ev st = some r → HwWf r.1 := by
  intro r hres
  have hz := asyncSchritt_zugestellt_wechsel m c ev st t g curRsp rsp m2
    hv hb hl hr hcur hp hs hk hpush
  rw [hz] at hres
  cases hres
  exact asyncMasch_wf m c g (asyncAnfrage ev t curRsp) rsp m2 hwf

/-- (1) WELL-FORMEDNESS, kept case. -/
theorem asyncSchritt_zugestellt_behalten_wf (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2)
    (hwf : HwWf m) :
    ∀ r, asyncSchritt m c ev st = some r → HwWf r.1 := by
  intro r hres
  have hz := asyncSchritt_zugestellt_behalten m c ev st t g curRsp rsp m2
    hv hb hl hr hcur hp hs hk hpush
  rw [hz] at hres
  cases hres
  exact asyncMasch_wf m c g (asyncAnfrage ev t curRsp) rsp m2 hwf

/-- (2) AGREEMENT, switched case: the step succeeds exactly where the
    accepted `liefere` delivers, with the same memory, RIP, IF and
    switch flag. The old evaluator is lifted, never redefined. -/
theorem asyncSchritt_liefere_wechsel (m : HwMaschine)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2) :
    liefere m.mem st (asyncAnfrage ev t curRsp) =
      .zugestellt m2 g.offset
        (if g.unterbrechung then false else st.ifBit) true :=
  liefere_zugestellt_wechsel m.mem m2 st (asyncAnfrage ev t curRsp) g rsp
    hp hs hk hpush

/-- (2) AGREEMENT, kept case. -/
theorem asyncSchritt_liefere_behalten (m : HwMaschine)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2) :
    liefere m.mem st (asyncAnfrage ev t curRsp) =
      .zugestellt m2 g.offset
        (if g.unterbrechung then false else st.ifBit) false :=
  liefere_zugestellt_behalten m.mem m2 st (asyncAnfrage ev t curRsp) g rsp
    hp hs hk hpush

/-! ## 6. Planted refusals: every unadmitted shape refuses loudly.

   Each gate fails closed with `none` and changes nothing; the first
   failing stage wins. -/

/-- (3) A vector outside the admitted range refuses. -/
theorem asyncSchritt_verweigert_vektor (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (hv : asyncVektorOk ev = false) :
    asyncSchritt m c ev st = none := by
  simp [asyncSchritt, hv]

/-- (3) A masked maskable event refuses before any memory is read. -/
theorem asyncSchritt_verweigert_maskiert (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = false) :
    asyncSchritt m c ev st = none := by
  simp [asyncSchritt, hv, hb]

/-- (3) A vector past the IDT limit refuses before any byte is read. -/
theorem asyncSchritt_verweigert_limit (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = false) :
    asyncSchritt m c ev st = none := by
  simp [asyncSchritt, hv, hb, hl]

/-- (3) An unreadable gate refuses the whole delivery. -/
theorem asyncSchritt_verweigert_torlesung (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = none) :
    asyncSchritt m c ev st = none := by
  simp [asyncSchritt, hv, hb, hl, hr]

/-- (3) A failed descriptor check refuses with no effect. -/
theorem asyncSchritt_verweigert_torfehler (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (f : TorFehler)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .fehler f) :
    asyncSchritt m c ev st = none := by
  simp [asyncSchritt, hv, hb, hl, hr, hp]

/-- (3) STACK FAULT BEFORE PUSH: a failed stack selection refuses and
    pushes nothing. -/
theorem asyncSchritt_verweigert_stapel (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp : Wort) (f : TorFehler)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .stapelFehler f) :
    asyncSchritt m c ev st = none := by
  unfold asyncSchritt
  simp [hv, hb, hl, hr, hcur, hp, hs]

/-- (3) NONCANONICAL POINTER BEFORE PUSH, switched stack: the
    loaded pointer is checked before the first frame word lands. -/
theorem asyncSchritt_verweigert_kanonisch_wechsel (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis) (st : Steuerstand)
    (t : Wort × Wort) (g : IdtTor) (curRsp rsp : Wort)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = false) :
    asyncSchritt m c ev st = none := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk]

/-- (3) NONCANONICAL POINTER BEFORE PUSH, kept stack. -/
theorem asyncSchritt_verweigert_kanonisch_behalten (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis) (st : Steuerstand)
    (t : Wort × Wort) (g : IdtTor) (curRsp rsp : Wort)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = false) :
    asyncSchritt m c ev st = none := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk]

/-- (3) DARK STACK, switched case: a refused frame push refuses the
    whole delivery. -/
theorem asyncSchritt_verweigert_rahmen_wechsel (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis) (st : Steuerstand)
    (t : Wort × Wort) (g : IdtTor) (curRsp rsp : Wort)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = none) :
    asyncSchritt m c ev st = none := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk, hpush]

/-- (3) DARK STACK, kept case. -/
theorem asyncSchritt_verweigert_rahmen_behalten (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis) (st : Steuerstand)
    (t : Wort × Wort) (g : IdtTor) (curRsp rsp : Wort)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = none) :
    asyncSchritt m c ev st = none := by
  unfold asyncSchritt asyncFertig
  simp [hv, hb, hl, hr, hcur, hp, hs, hk, hpush]

/-- An interrupt gate clears IF on delivery (S5, first half). -/
theorem asyncSchritt_interrupt_loescht_if (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2)
    (hgate : g.unterbrechung = true) :
    ∃ m' gew, asyncSchritt m c ev st = some (m', false, gew) := by
  have hz := asyncSchritt_zugestellt_wechsel m c ev st t g curRsp rsp m2
    hv hb hl hr hcur hp hs hk hpush
  exact ⟨_, _, by simpa [hgate] using hz⟩

/-- A trap gate keeps IF on delivery (S5, second half). -/
theorem asyncSchritt_trap_behaelt_if (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (t : Wort × Wort)
    (g : IdtTor) (curRsp rsp : Wort) (m2 : Speicher)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = true)
    (hl : torImLimit st.idtLimit ev.vektor = true)
    (hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) = some t)
    (hcur : (m.kerne c).register Register.rsp = curRsp)
    (hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl ev.codeOk =
      .bereit g)
    (hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m.mem rsp
      (rahmenWorte (asyncAnfrage ev t curRsp)) = some m2)
    (hgate : g.unterbrechung = false) :
    ∃ m' gew, asyncSchritt m c ev st = some (m', st.ifBit, gew) := by
  have hz := asyncSchritt_zugestellt_wechsel m c ev st t g curRsp rsp m2
    hv hb hl hr hcur hp hs hk hpush
  exact ⟨_, _, by simpa [hgate] using hz⟩

/-- The adapter plug refuses whatever the step refuses: masked case. -/
theorem adapterInterrupt1125_verweigert_maskiert (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = false) :
    adapterInterrupt1125.schritt m c ev = none := by
  have h := asyncSchritt_verweigert_maskiert m c ev ev.steuer hv hb
  simp [adapterInterrupt1125, h]

/-- The adapter plug refuses whatever the step refuses: vector case. -/
theorem adapterInterrupt1125_verweigert_vektor (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis)
    (hv : asyncVektorOk ev = false) :
    adapterInterrupt1125.schritt m c ev = none := by
  have h := asyncSchritt_verweigert_vektor m c ev ev.steuer hv
  simp [adapterInterrupt1125, h]

/-! ## 7. Joint witness: NMI delivery on a two-core machine.

   Reuses the accepted byte-populated IDT/TSS (`witMem`,
   `idtWitSteuer`, `loWit`, the `witAnfrage` frame words). The NMI
   event carries IF=false in its snapshot and still delivers (the S1
   bypass); the masked, misranged, over-limit and dark-stack probes
   refuse. Every claim below is a closed decidable observation. -/

/-- Witness control snapshot: accepted IDT/TSS windows at CPL 0 with
    IF clear. -/
def witSteuerNmi : Steuerstand := { idtWitSteuer with ifBit := false }

/-- Witness event: NMI (vector 2) with the accepted frame words. -/
def witNmi : AsyncEreignis :=
  ⟨2, .nichtMaskierbar, witSteuerNmi, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Witness masked event: maskable vector 35 under IF=false. -/
def witMaskiert : AsyncEreignis :=
  ⟨35, .maskierbar, witSteuerNmi, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Witness range refusal: an exception-range vector as maskable. -/
def witFalschVektor : AsyncEreignis :=
  ⟨2, .maskierbar, idtWitSteuer, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Witness limit control: IF set, so the check reaches the limit. -/
def witLimitSteuer : Steuerstand := { idtWitSteuer with ifBit := true }

/-- Witness limit refusal: vector 35 past the witness IDT limit. -/
def witLimit : AsyncEreignis :=
  ⟨35, .maskierbar, witLimitSteuer, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Witness cores: core 0 runs with the IST-switch RSP, core 1 idles. -/
def intWitKern : Nat → HwKern
  | 0 => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 20480
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 8192,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: accepted IDT/TSS/stack memory, empty
    buffers, full silicon. -/
def intWitStart : HwMaschine :=
  ⟨witMem, intWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Dark machine: no writable frame cell (poison probe). -/
def intWitDunkel : HwMaschine := { intWitStart with mem := witMemDunkel }

/-- The witness machine is well-formed: admission implies silicon
    (the accepted profile lemma, lifted). -/
theorem intWitStart_wf : HwWf intWitStart := by
  intro c f h
  exact (merkmalZugelassen_heisst_beide intWitStart.hw
    (intWitStart.bereit c) f h).1

/-- The delivery attempt on core 0. -/
def witSchritt : Option (HwMaschine × Bool × Bool) :=
  asyncSchritt intWitStart 0 witNmi witSteuerNmi

/-- Project the delivered memory (witness memory on refusal). -/
def asyncMemOut (o : Option (HwMaschine × Bool × Bool)) : Speicher :=
  match o with
  | some (m, _, _) => m.mem
  | none => witMem

/-- Read the handler RIP out of a delivery outcome. -/
def asyncRipOut (o : Option (HwMaschine × Bool × Bool))
    (c : Nat) : Option Wort :=
  match o with
  | some (m, _, _) => some (m.kerne c).rip
  | _ => none

/-- Read the new IF out of a delivery outcome. -/
def asyncIfOut (o : Option (HwMaschine × Bool × Bool)) : Option Bool :=
  match o with
  | some (_, b, _) => some b
  | _ => none

/-- Read the switch flag out of a delivery outcome. -/
def asyncGewOut (o : Option (HwMaschine × Bool × Bool)) : Option Bool :=
  match o with
  | some (_, _, g) => some g
  | _ => none

/-- Read a buffer length out of a delivery outcome. -/
def asyncBufOut (o : Option (HwMaschine × Bool × Bool))
    (c : Nat) : Option Nat :=
  match o with
  | some (m, _, _) => some (m.puffer c).length
  | _ => none

/-- The NMI vector is admitted. -/
theorem witNmi_vektor_ok : asyncVektorOk witNmi = true := by
  decide

/-- The NMI passes the gate despite IF=false. -/
theorem witNmi_bereit : asyncBereit witNmi = true := by
  decide

/-- Vector 2 fits the witness IDT limit. -/
theorem witNmi_limit : torImLimit witSteuerNmi.idtLimit witNmi.vektor = true := by
  decide

/-- The gate bytes read back as the two witness words. -/
theorem witNmi_liest :
    liesTorBytes witMem (torAdresse witSteuerNmi.idtBasis witNmi.vektor) =
      some (loWit, 0) := by
  decide

/-- The witness gate is admitted (the accepted admission, lifted). -/
theorem witNmi_gate_bereit :
    pruefeTor witNmi.vektor witSteuerNmi.idtLimit (loWit, (0 : Wort))
      .extern witSteuerNmi.cpl witNmi.codeOk =
      .bereit ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ :=
  wit_bereit

/-- The witness TSS slot loads the IST stack. -/
theorem witNmi_stapel :
    waehleStapel witMem witSteuerNmi 1 0 false
      (BitVec.ofNat 64 20480) =
      .wechseln (BitVec.ofNat 64 16384) := by
  decide

/-- The selected stack pointer is canonical. -/
theorem witNmi_kanonisch :
    istKanonisch (BitVec.ofNat 64 16384) = true := by
  decide

/-- Delivery reaches the witness handler offset. -/
theorem witNmi_liefert_rip :
    asyncRipOut witSchritt 0 = some (BitVec.ofNat 64 8192) := by
  decide

/-- The interrupt gate clears IF (snapshot had it clear; the abstract
    clear/keep contrast is proved in §6 for every gate kind). -/
theorem witNmi_liefert_if :
    asyncIfOut witSchritt = some false := by
  decide

/-- Delivery reports the IST switch. -/
theorem witNmi_liefert_gew :
    asyncGewOut witSchritt = some true := by
  decide

/-- S3 witnessed: no buffer grew on the acting core. -/
theorem witNmi_puffer_0 : asyncBufOut witSchritt 0 = some 0 := by
  decide

/-- S3 witnessed: no buffer grew on the other core either. -/
theorem witNmi_puffer_1 : asyncBufOut witSchritt 1 = some 0 := by
  decide

/-- First frame word reads back. -/
theorem witNmi_rahmen_ss :
    read64 (asyncMemOut witSchritt) (BitVec.ofNat 64 16376) =
      some (BitVec.ofNat 64 16) := by
  decide

/-- Last frame word reads back. -/
theorem witNmi_rahmen_rip :
    read64 (asyncMemOut witSchritt) (BitVec.ofNat 64 16344) =
      some (BitVec.ofNat 64 4660) := by
  decide

/-- The frame observably changes memory. -/
theorem witNmi_aendert_ss :
    witMem.bytes (BitVec.ofNat 64 16376) ≠
      (asyncMemOut witSchritt).bytes (BitVec.ofNat 64 16376) := by
  decide

/-- Masked maskable delivery refuses. -/
theorem witNmi_maskiert_verweigert :
    asyncSchritt intWitStart 1 witMaskiert witSteuerNmi = none := by
  decide

/-- Exception-range vector as maskable refuses. -/
theorem witNmi_bereich_verweigert :
    asyncSchritt intWitStart 1 witFalschVektor idtWitSteuer = none := by
  decide

/-- Over-limit vector refuses. -/
theorem witNmi_limit_verweigert :
    asyncSchritt intWitStart 1 witLimit witLimitSteuer = none := by
  decide

/-- Dark-stack delivery refuses with #SS shape (vector 12 downstream). -/
theorem witNmi_dunkel_verweigert :
    asyncSchritt intWitDunkel 0 witNmi witSteuerNmi = none := by
  decide

/-! ## 8. Joint TSO stage: issue, forwarding, foreign view, drain.

   Chained onto the delivery successor: core 1 issues byte 42 at a
   writable cell clear of the frame, observes it by forwarding, core
   0 still reads the old byte (no foreign forwarding), and after the
   drain both cores read 42. Delivery left every buffer empty, so the
   issue starts from the exact post-delivery state. -/

/-- Witness data cell: writable in the witness memory, clear of the
    five frame words (lowest frame word covers 16344-16351). -/
def witIntZelle : Adresse := BitVec.ofNat 64 16336

/-- The machine after delivery, if reached. -/
def witIntM2 : Option HwMaschine :=
  match witSchritt with
  | some (m, _, _) => some m
  | none => none

/-- Core 1 issues byte 42 at the data cell. -/
def witIntTso1 : Option TSOZustand :=
  match witIntM2 with
  | some m2 => issueByte (tsoAnsicht m2) 1 witIntZelle (BitVec.ofNat 8 42)
  | none => none

/-- Core 1 observes its own byte (forwarding). -/
def witIntLoadEigen : Option (Option Byte) :=
  match witIntTso1 with
  | some s => some (loadByte s 1 witIntZelle)
  | none => none

/-- Core 0 observes the old byte (no foreign forwarding). -/
def witIntLoadFremd : Option (Option Byte) :=
  match witIntTso1 with
  | some s => some (loadByte s 0 witIntZelle)
  | none => none

/-- Core 1 drains its oldest entry. -/
def witIntTso2 : Option TSOZustand :=
  match witIntTso1 with
  | some s => flushKern s 1
  | none => none

/-- The shared byte after the drain. -/
def witIntNachFlush : Option (Option Byte) :=
  match witIntTso2 with
  | some s => some (some (s.mem.bytes witIntZelle))
  | none => none

/-- Core 0 reads the drained byte from shared memory. -/
def witIntFremdNachFlush : Option (Option Byte) :=
  match witIntTso2 with
  | some s => some (loadByte s 0 witIntZelle)
  | none => none

/-- The data cell starts zeroed. -/
theorem witInt_anfang_null :
    witMem.bytes witIntZelle = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 1 reads its own unflushed byte. -/
theorem witInt_weiterleitung :
    witIntLoadEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 0 still reads zero. -/
theorem witInt_fremd_alt :
    witIntLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem witInt_spuelung_aendert :
    witIntNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 0 observes the new byte. -/
theorem witInt_fremd_neu :
    witIntFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-! ## 9. Extended-relation witness and the joint `_zeuge`.

   The NMI delivery is also a reached `HwIntSchritt.async` step with
   the IF update stored on the acting core. -/

/-- Witness control for every core. -/
def witIntSteuerAlle : Nat → Steuerstand := fun _ => witSteuerNmi

/-- The delivery attempt succeeds (as a Boolean observation). -/
theorem witNmi_erfolg_ex : ∃ r, witSchritt = some r := by
  cases h0 : witSchritt with
  | none =>
    have hc := witNmi_liefert_rip
    simp [asyncRipOut, h0] at hc
  | some r => exact ⟨r, rfl⟩

/-- The NMI delivery is a reached extended async step. -/
theorem witNmi_relation : ∃ m' : HwMaschine, ∃ st' : Nat → Steuerstand,
    HwIntSchritt ⟨intWitStart, witIntSteuerAlle⟩ ⟨m', st'⟩
      (.asyncEv witNmi) := by
  obtain ⟨⟨m', ifNeu, gew⟩, h⟩ := witNmi_erfolg_ex
  exact ⟨m', _, HwIntSchritt.async 0 witNmi rfl h⟩

/-- JOINT WITNESS: NMI delivery over byte-populated canonical memory
    (handler reached, IF cleared, IST switch reported, buffers still
    empty, five-word frame read back, memory observably changed) with
    the masked/range/limit/dark refusals beside it, a buffered store
    visible by forwarding to its owner only, its drain observed from
    both cores, well-formedness, and the reached extended async step.
    Non-degenerate: two cores touch memory, two steps change actual
    shared-memory bytes. -/
theorem asyncLiefer_zeuge :
    asyncRipOut witSchritt 0 = some (BitVec.ofNat 64 8192) ∧
      asyncIfOut witSchritt = some false ∧
      asyncGewOut witSchritt = some true ∧
      asyncBufOut witSchritt 0 = some 0 ∧
      asyncBufOut witSchritt 1 = some 0 ∧
      read64 (asyncMemOut witSchritt) (BitVec.ofNat 64 16376) =
        some (BitVec.ofNat 64 16) ∧
      read64 (asyncMemOut witSchritt) (BitVec.ofNat 64 16344) =
        some (BitVec.ofNat 64 4660) ∧
      witMem.bytes (BitVec.ofNat 64 16376) ≠
        (asyncMemOut witSchritt).bytes (BitVec.ofNat 64 16376) ∧
      asyncSchritt intWitStart 1 witMaskiert witSteuerNmi = none ∧
      asyncSchritt intWitStart 1 witFalschVektor idtWitSteuer = none ∧
      asyncSchritt intWitStart 1 witLimit witLimitSteuer = none ∧
      asyncSchritt intWitDunkel 0 witNmi witSteuerNmi = none ∧
      witIntLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      witIntLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      witIntNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      witIntFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      HwWf intWitStart ∧
      (∃ m' : HwMaschine, ∃ st' : Nat → Steuerstand,
        HwIntSchritt ⟨intWitStart, witIntSteuerAlle⟩ ⟨m', st'⟩
          (.asyncEv witNmi)) := by
  refine ⟨witNmi_liefert_rip, witNmi_liefert_if, witNmi_liefert_gew,
    witNmi_puffer_0, witNmi_puffer_1, witNmi_rahmen_ss, witNmi_rahmen_rip,
    witNmi_aendert_ss, witNmi_maskiert_verweigert,
    witNmi_bereich_verweigert, witNmi_limit_verweigert,
    witNmi_dunkel_verweigert, witInt_weiterleitung, witInt_fremd_alt,
    witInt_spuelung_aendert, witInt_fremd_neu, intWitStart_wf,
    witNmi_relation⟩

/- CUTS:
   Proved here, over the accepted coherent machine (HardwareExecution
   §11: `HwMaschine`/`HwSchritt`/`HwAdapter`/`HwWf`) and the accepted
   descriptor-layer evaluator (`liefere` and its stage lemmas in
   InterruptDescriptorHardware.lean), both lifted unchanged:
   - checked async event type (`AsyncArt`, `AsyncEreignis`: vector,
     kind, control snapshot, code-row input, privilege-change data,
     frame words; gate bytes are read from machine memory, never
     carried) with vector admission (S2: NMI is vector 2, maskable
     32-255) and the IF gate (S1: maskable needs IF, NMI bypasses);
   - delivery step (`asyncSchritt`/`asyncFertig`) in
     checks-before-effects order with the `HwAdapter` plug
     (`adapterInterrupt1125`, replacing the `Unit` default for this
     producer) and the extended machine/relation (`HwIntMaschine`,
     `IntEreignis`, `HwIntSchritt`) with the exact sync embedding
     (`hwIntSchritt_sync_einbetten`, `hwIntSchritt_sync_nur`);
   - (1) `HwWf` preservation for every successful delivery;
   - (2) exact agreement with `liefere` (same memory, handler RIP,
     new IF, switch flag), both stack paths;
   - S3 in machine form and witnessed: delivery never touches any
     per-core TSO buffer (no drain, no issue; `asyncMasch_puffer_still`,
     both buffer lengths still zero after delivery);
   - the stack effect: RSP descends past exactly the pushed frame
     (`asyncMasch_rsp_neu`), RIP is the gate offset;
   - IF behaviour: interrupt gate clears, trap gate keeps (abstract,
     for every successful delivery);
   - (3) planted refusals at every stage: bad vector, masked event,
     over-limit vector, unreadable gate, failed descriptor check,
     failed stack selection, noncanonical pointer, failed frame push
     (both stack paths), projected to the adapter plug;
   - (4) joint non-degenerate witness (`asyncLiefer_zeuge`): NMI
     delivery on core 0 under IF=false over byte-populated IDT/TSS
     (handler 8192, IF cleared, IST switch, empty buffers, frame
     read-back, changed cells) beside four refusals, a core-1
     buffered store with owner-only forwarding, its drain observed
     from both cores, well-formedness and the reached extended step.
   NOT proved here, and not claimed:
   - No hardware correspondence: S1-S3 plus the S5 gate-kind rule
     cite the Intel SDM extracts as provenance; the proofs show
     self-consistency of the lifted model only.
   - No concrete maskable-success witness: the reused IDT image
     carries one gate (vector 2); maskable admission is proved
     abstractly through the same stage equations.
   - No nested delivery, no #DF escalation, no handler execution:
     what runs after delivery stays downstream (entry lane).
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the accepted guards; the TSO stage reuses the
     accepted byte equations only.
   - No timing, priority arbitration (APIC), power or SMI paths;
     the event's control snapshot must agree with stored control
     (`hst`), which the adapter reads from the event itself.
   - `gabbro_ziel` axioms are untouched.
-/

#print axioms asyncBereit_nmi
#print axioms asyncBereit_maskiert
#print axioms asyncVektorOk_nmi
#print axioms asyncVektorOk_maskierbar
#print axioms asyncBereit_maskierbar
#print axioms asyncVektor_nmi_falsch
#print axioms asyncVektor_maskierbar_klein
#print axioms asyncMasch_rip
#print axioms asyncMasch_rsp_neu
#print axioms asyncMasch_mem
#print axioms asyncMasch_puffer_still
#print axioms asyncMasch_wf
#print axioms asyncSchritt_zugestellt_wechsel
#print axioms asyncSchritt_zugestellt_behalten
#print axioms asyncSchritt_zugestellt_wechsel_wf
#print axioms asyncSchritt_zugestellt_behalten_wf
#print axioms asyncSchritt_liefere_wechsel
#print axioms asyncSchritt_liefere_behalten
#print axioms asyncSchritt_verweigert_vektor
#print axioms asyncSchritt_verweigert_maskiert
#print axioms asyncSchritt_verweigert_limit
#print axioms asyncSchritt_verweigert_torlesung
#print axioms asyncSchritt_verweigert_torfehler
#print axioms asyncSchritt_verweigert_stapel
#print axioms asyncSchritt_verweigert_kanonisch_wechsel
#print axioms asyncSchritt_verweigert_kanonisch_behalten
#print axioms asyncSchritt_verweigert_rahmen_wechsel
#print axioms asyncSchritt_verweigert_rahmen_behalten
#print axioms asyncSchritt_interrupt_loescht_if
#print axioms asyncSchritt_trap_behaelt_if
#print axioms adapterInterrupt1125_verweigert_maskiert
#print axioms adapterInterrupt1125_verweigert_vektor
#print axioms hwIntSchritt_sync_einbetten
#print axioms hwIntSchritt_sync_nur
#print axioms intWitStart_wf
#print axioms witNmi_vektor_ok
#print axioms witNmi_bereit
#print axioms witNmi_limit
#print axioms witNmi_liest
#print axioms witNmi_gate_bereit
#print axioms witNmi_stapel
#print axioms witNmi_kanonisch
#print axioms witNmi_liefert_rip
#print axioms witNmi_liefert_if
#print axioms witNmi_liefert_gew
#print axioms witNmi_puffer_0
#print axioms witNmi_puffer_1
#print axioms witNmi_rahmen_ss
#print axioms witNmi_rahmen_rip
#print axioms witNmi_aendert_ss
#print axioms witNmi_maskiert_verweigert
#print axioms witNmi_bereich_verweigert
#print axioms witNmi_limit_verweigert
#print axioms witNmi_dunkel_verweigert
#print axioms witInt_anfang_null
#print axioms witInt_weiterleitung
#print axioms witInt_fremd_alt
#print axioms witInt_spuelung_aendert
#print axioms witInt_fremd_neu
#print axioms witNmi_erfolg_ex
#print axioms witNmi_relation
#print axioms asyncLiefer_zeuge

end Gabbro.Grammatik.X86
