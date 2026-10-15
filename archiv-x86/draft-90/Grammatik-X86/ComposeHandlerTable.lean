/-
  Composition closing: handler-table closing (lane 850).

  Producer/consumer interface closed here: the declared handler table
  (a `List HandlerDekl` mapping vectors to handler RIPs) is closed to
  the accepted IDT producer (`InterruptDescriptorHardware`: gate bytes
  read from actual canonical memory at `torAdresse`, `pruefeTor`,
  `waehleStapel`, `liefere` with `torFehlerCode`/`torVektor`). This file
  only composes already-accepted definitions and theorems; it re-proves
  no descriptor, stack or delivery fact and defines no second
  interpreter or executor.
-/
import Grammatik.X86.InterruptDescriptorHardware

namespace Gabbro.Grammatik.X86

/-- Declared interrupt handler: vector closed to its IDT handler RIP. -/
structure HandlerDekl where
  vektor : Nat
  handlerRip : Adresse
  deriving DecidableEq, Repr

/-- Lookup of a declared handler by vector. -/
def handlerFuer : List HandlerDekl → Nat → Option HandlerDekl
  | [], _ => none
  | h :: t, v => if h.vektor == v then some h else handlerFuer t v

/-- Closing refusal: undeclared vector, unreadable gate, binding
    mismatch (IDT entry names another RIP), or the accepted fault. -/
inductive HandlerWeigerung where
  | undeclariert : Nat → HandlerWeigerung
  | unlesbar : Nat → HandlerWeigerung
  | fehlbindung : Adresse → Adresse → HandlerWeigerung
  | torFehler : TorFehler → Wort → HandlerWeigerung
  deriving DecidableEq, Repr

/-- Closing outcome: admitted delivery or the precise refusal. -/
inductive HandlerErgebnis where
  | zugelassen : Speicher → Adresse → Bool → Bool → HandlerErgebnis
  | verweigert : HandlerWeigerung → HandlerErgebnis

/-- The one checked closing step: declared lookup, gate bytes from
    actual IDT memory, accepted gate check, binding check, accepted
    delivery. Undeclared vectors refuse before any byte is read. -/
def handlerEintritt (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage) : HandlerErgebnis :=
  match handlerFuer tab q.vektor with
  | none => .verweigert (.undeclariert q.vektor)
  | some h =>
    match liesTorBytes m (torAdresse s.idtBasis q.vektor) with
    | none => .verweigert (.unlesbar q.vektor)
    | some t =>
      match pruefeTor q.vektor s.idtLimit t q.herkunft s.cpl q.codeOk with
      | .fehler f => .verweigert (.torFehler f (torFehlerCode f q.herkunft))
      | .bereit g =>
        if g.offset == h.handlerRip then
          match liefere m s { q with tor := t } with
          | .zugestellt m' rip ifNeu gew => .zugelassen m' rip ifNeu gew
          | .lieferFehler f c => .verweigert (.torFehler f c)
        else .verweigert (.fehlbindung g.offset h.handlerRip)

/-! ## 1. Projections (decidable refusal view, delivered memory). -/

/-- Decidable refusal view: admitted delivery projects to `none`. -/
def handlerWeigerung : HandlerErgebnis → Option HandlerWeigerung
  | .zugelassen _ _ _ _ => none
  | .verweigert w => some w

/-- Project the delivered memory (witness memory on refusal, as in
    `ergebnisSpeicher`). -/
def handlerSpeicher : HandlerErgebnis → Speicher
  | .zugelassen m _ _ _ => m
  | .verweigert _ => witMem

/-- Frame words do not mention the gate words: updating `tor` keeps them. -/
theorem rahmenWorte_mit_tor (q : LieferAnfrage) (t : Wort × Wort) :
    rahmenWorte { q with tor := t } = rahmenWorte q := rfl

/-! ## 2. Success closing: declared handler reaches accepted delivery. -/

/-- HANDLER-TABLE CLOSING (generic, arbitrary admitted inputs): a
    declared vector whose IDT bytes read from actual canonical memory
    pass the accepted gate check, whose gate names the declared handler
    RIP, whose accepted stack selection switches, whose pointer is
    canonical and whose accepted frame push succeeds, is admitted
    through the composed step -- and the composed step coincides with
    the accepted delivery `liefere`. Composes only accepted producer
    facts (`liefere_zugestellt_wechsel`); no producer fact is re-proved. -/
theorem ComposeHandlerTable_verbindung (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage) (h : HandlerDekl)
    (t : Wort × Wort) (g : IdtTor) (rsp : Wort) (m' : Speicher)
    (hdecl : handlerFuer tab q.vektor = some h)
    (htor : liesTorBytes m (torAdresse s.idtBasis q.vektor) = some t)
    (hpruef : pruefeTor q.vektor s.idtLimit t q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hbind : g.offset = h.handlerRip)
    (hstapel : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .wechseln rsp)
    (hkanon : istKanonisch rsp = true)
    (hpush : schiebeRahmen m rsp (rahmenWorte q) = some m') :
    handlerEintritt m s tab q = .zugelassen m' g.offset
      (if g.unterbrechung then false else s.ifBit) true ∧
    liefere m s { q with tor := t } = .zugestellt m' g.offset
      (if g.unterbrechung then false else s.ifBit) true := by
  have hpruef' : pruefeTor ({ q with tor := t }).vektor s.idtLimit
      ({ q with tor := t }).tor ({ q with tor := t }).herkunft s.cpl
      ({ q with tor := t }).codeOk = .bereit g := hpruef
  have hpush' : schiebeRahmen m rsp
      (rahmenWorte { q with tor := t }) = some m' := by
    rw [rahmenWorte_mit_tor]
    exact hpush
  have hL := liefere_zugestellt_wechsel m m' s { q with tor := t } g rsp
    hpruef' hstapel hkanon hpush'
  refine ⟨?_, hL⟩
  unfold handlerEintritt
  simp only [hdecl, htor, hpruef]
  have heq : ((g.offset == h.handlerRip) = true) := by simp [hbind]
  simp only [if_pos heq, hL]

/-- KEPT-STACK CLOSING: the same declared handler over the kept stack
    (no IST switch, no privilege change) is admitted with the switch
    flag clear. Composes `liefere_zugestellt_behalten`. -/
theorem ComposeHandlerTable_verbindung_behalten (m : Speicher)
    (s : Steuerstand) (tab : List HandlerDekl) (q : LieferAnfrage)
    (h : HandlerDekl) (t : Wort × Wort) (g : IdtTor) (rsp : Wort)
    (m' : Speicher)
    (hdecl : handlerFuer tab q.vektor = some h)
    (htor : liesTorBytes m (torAdresse s.idtBasis q.vektor) = some t)
    (hpruef : pruefeTor q.vektor s.idtLimit t q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hbind : g.offset = h.handlerRip)
    (hstapel : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .behalten rsp)
    (hkanon : istKanonisch rsp = true)
    (hpush : schiebeRahmen m rsp (rahmenWorte q) = some m') :
    handlerEintritt m s tab q = .zugelassen m' g.offset
      (if g.unterbrechung then false else s.ifBit) false ∧
    liefere m s { q with tor := t } = .zugestellt m' g.offset
      (if g.unterbrechung then false else s.ifBit) false := by
  have hpruef' : pruefeTor ({ q with tor := t }).vektor s.idtLimit
      ({ q with tor := t }).tor ({ q with tor := t }).herkunft s.cpl
      ({ q with tor := t }).codeOk = .bereit g := hpruef
  have hpush' : schiebeRahmen m rsp
      (rahmenWorte { q with tor := t }) = some m' := by
    rw [rahmenWorte_mit_tor]
    exact hpush
  have hL := liefere_zugestellt_behalten m m' s { q with tor := t } g rsp
    hpruef' hstapel hkanon hpush'
  refine ⟨?_, hL⟩
  unfold handlerEintritt
  simp only [hdecl, htor, hpruef]
  have heq : ((g.offset == h.handlerRip) = true) := by simp [hbind]
  simp only [if_pos heq, hL]

/-! ## 3. Refusals: undeclared vectors refuse at entry. -/

/-- UNDECLARED REFUSAL: a vector with no declared handler refuses at
    entry, before any IDT byte is read. Uses the missing declaration. -/
theorem handler_undeclariert_verweigert (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage)
    (h : handlerFuer tab q.vektor = none) :
    handlerEintritt m s tab q =
      .verweigert (.undeclariert q.vektor) := by
  unfold handlerEintritt
  simp [h]

/-- UNREADABLE REFUSAL: a declared vector whose gate halves do not both
    read from actual IDT memory refuses. Uses the declaration and the
    refused read. -/
theorem handler_unlesbar_verweigert (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage) (h : HandlerDekl)
    (hdecl : handlerFuer tab q.vektor = some h)
    (hread : liesTorBytes m (torAdresse s.idtBasis q.vektor) = none) :
    handlerEintritt m s tab q =
      .verweigert (.unlesbar q.vektor) := by
  unfold handlerEintritt
  simp [hdecl, hread]

/-- GATE REFUSAL: a declared vector whose IDT entry fails the accepted
    gate check refuses with the accepted fault and its code. Uses the
    declaration, the gate bytes and the accepted refusal. -/
theorem handler_torfehler_verweigert (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage) (h : HandlerDekl)
    (t : Wort × Wort) (f : TorFehler)
    (hdecl : handlerFuer tab q.vektor = some h)
    (htor : liesTorBytes m (torAdresse s.idtBasis q.vektor) = some t)
    (herr : pruefeTor q.vektor s.idtLimit t q.herkunft s.cpl q.codeOk =
      .fehler f) :
    handlerEintritt m s tab q =
      .verweigert (.torFehler f (torFehlerCode f q.herkunft)) := by
  unfold handlerEintritt
  simp [hdecl, htor, herr]

/-- BINDING REFUSAL: a declared vector whose IDT entry names another
    RIP refuses with the mismatch. Uses the declaration, the gate
    bytes, the accepted admission and the mismatch. -/
theorem handler_fehlbindung_verweigert (m : Speicher) (s : Steuerstand)
    (tab : List HandlerDekl) (q : LieferAnfrage) (h : HandlerDekl)
    (t : Wort × Wort) (g : IdtTor)
    (hdecl : handlerFuer tab q.vektor = some h)
    (htor : liesTorBytes m (torAdresse s.idtBasis q.vektor) = some t)
    (hpruef : pruefeTor q.vektor s.idtLimit t q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hne : g.offset ≠ h.handlerRip) :
    handlerEintritt m s tab q =
      .verweigert (.fehlbindung g.offset h.handlerRip) := by
  unfold handlerEintritt
  simp only [hdecl, htor, hpruef]
  have heq : ((g.offset == h.handlerRip) = true) = False := by
    cases he : (g.offset == h.handlerRip) with
    | true =>
      simp [beq_iff_eq] at he
      exact absurd he hne
    | false => simp
  simp [heq]

/-! ## 4. Joint witness: declared vector over byte-populated IDT/TSS.

  Vector 2 is declared with handler `0x2000`: the witness IDT/TSS
  images of `InterruptDescriptorHardware` (three entries, IST1 holding
  `0x4000`) deliver through the interrupt gate, switch stacks, clear
  IF and push five nonzero frame words that read back and observably
  change two cells. -/

/-- Witness declared handler: vector 2 closed to handler `0x2000`. -/
def witHandler : HandlerDekl := ⟨2, BitVec.ofNat 64 0x2000⟩

/-- Witness declared table: vector 2 only. -/
def witHandlers : List HandlerDekl := [witHandler]

/-- Witness gate: the accepted vector-2 gate of the IDT witness. -/
def witGate : IdtTor := ⟨BitVec.ofNat 64 0x2000, 8, 1, 0, true⟩

/-- Witness table with a renamed handler: vector 2 bound to `0x3000`. -/
def witHandlersFalsch : List HandlerDekl :=
  [⟨2, BitVec.ofNat 64 0x3000⟩]

/-- JOINT WITNESS for `ComposeHandlerTable_verbindung`: every premise
    is instantiated jointly on the byte-populated IDT/TSS witness
    (declared vector 2, gate bytes from actual memory, accepted gate,
    binding, IST switch, canonical pointer), with a reached
    memory-changing run through the composed step (five-word frame,
    two observably changed cells) and planted refusal cases
    (undeclared vector, renamed handler, dark stack). -/
theorem ComposeHandlerTable_verbindung_zeuge :
    handlerFuer witHandlers 2 = some witHandler ∧
    liesTorBytes witMem (torAdresse idtWitSteuer.idtBasis 2) =
      some (loWit, (0 : Wort)) ∧
    pruefeTor 2 47 (loWit, (0 : Wort)) .extern 0 true =
      .bereit witGate ∧
    witGate.offset = witHandler.handlerRip ∧
    waehleStapel witMem idtWitSteuer witGate.ist witAnfrage.neuDpl
        witAnfrage.wechsel witAnfrage.curRsp =
      .wechseln (BitVec.ofNat 64 16384) ∧
    istKanonisch (BitVec.ofNat 64 16384) = true ∧
    (∃ m', schiebeRahmen witMem (BitVec.ofNat 64 16384)
        (rahmenWorte witAnfrage) = some m' ∧
      handlerEintritt witMem idtWitSteuer witHandlers witAnfrage =
        .zugelassen m' witGate.offset false true ∧
      read64 m' (BitVec.ofNat 64 16376) = some (BitVec.ofNat 64 16) ∧
      read64 m' (BitVec.ofNat 64 16344) = some (BitVec.ofNat 64 4660) ∧
      witMem.bytes (BitVec.ofNat 64 16376) ≠
        m'.bytes (BitVec.ofNat 64 16376) ∧
      witMem.bytes (BitVec.ofNat 64 16344) ≠
        m'.bytes (BitVec.ofNat 64 16344)) ∧
    handlerWeigerung
        (handlerEintritt witMem idtWitSteuer [] witAnfrage) =
      some (.undeclariert 2) ∧
    handlerWeigerung
        (handlerEintritt witMem idtWitSteuer witHandlersFalsch
          witAnfrage) =
      some (.fehlbindung (BitVec.ofNat 64 0x2000)
        (BitVec.ofNat 64 0x3000)) ∧
    handlerWeigerung
        (handlerEintritt witMemDunkel idtWitSteuer witHandlers
          witAnfrage) =
      some (.torFehler .stapelFehler 0) := by
  have hdecl : handlerFuer witHandlers witAnfrage.vektor =
      some witHandler := by decide
  have htor : liesTorBytes witMem
      (torAdresse idtWitSteuer.idtBasis witAnfrage.vektor) =
      some witAnfrage.tor := by decide
  have hpruef : pruefeTor witAnfrage.vektor idtWitSteuer.idtLimit
      witAnfrage.tor witAnfrage.herkunft idtWitSteuer.cpl
      witAnfrage.codeOk = .bereit witGate := by decide
  have hbind : witGate.offset = witHandler.handlerRip := rfl
  have hstapel : waehleStapel witMem idtWitSteuer witGate.ist
      witAnfrage.neuDpl witAnfrage.wechsel witAnfrage.curRsp =
      .wechseln (BitVec.ofNat 64 16384) := by decide
  have hkanon : istKanonisch (BitVec.ofNat 64 16384) = true := by decide
  have hsome : (schiebeRahmen witMem (BitVec.ofNat 64 16384)
      (rahmenWorte witAnfrage)).isSome = true := by decide
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨mX, hpush⟩ := hsome
  have hif : (if witGate.unterbrechung then false
      else idtWitSteuer.ifBit) = false := by decide
  have hmain := ComposeHandlerTable_verbindung witMem idtWitSteuer
    witHandlers witAnfrage witHandler witAnfrage.tor witGate
    (BitVec.ofNat 64 16384) mX hdecl htor hpruef hbind hstapel hkanon
    hpush
  rw [hif] at hmain
  have hupd : ({ witAnfrage with tor := witAnfrage.tor }) =
      witAnfrage := rfl
  have hL : liefere witMem idtWitSteuer witAnfrage =
      .zugestellt mX witGate.offset false true := by
    have h2 := hmain.2
    rw [hupd] at h2
    exact h2
  have hss : read64 mX (BitVec.ofNat 64 16376) =
      some (BitVec.ofNat 64 16) := by
    have h0 := wit_rahmen_ss
    rw [hL] at h0
    simpa [ergebnisSpeicher] using h0
  have hss2 : read64 mX (BitVec.ofNat 64 16344) =
      some (BitVec.ofNat 64 4660) := by
    have h0 := wit_rahmen_rip
    rw [hL] at h0
    simpa [ergebnisSpeicher] using h0
  have hch := wit_rahmen_aendert
  rw [hL] at hch
  simp only [ergebnisSpeicher] at hch
  refine ⟨by decide, by decide, by decide, rfl, by decide, by decide,
    ⟨mX, hpush, hmain.1, hss, hss2, hch.1, hch.2⟩,
    by decide, by decide, by decide⟩

/- CUTS:
   Proved here, by composing only the accepted producer modules (no
   producer fact re-proved, no second loader/decoder/executor/ISA):
   - the declared handler table (`HandlerDekl`, `handlerFuer`) and the
     one checked closing step (`handlerEintritt`: declared lookup,
     gate bytes from actual IDT memory at `torAdresse`, accepted
     `pruefeTor`, binding check against the declared RIP, accepted
     `liefere`);
   - the generic success closing over arbitrary admitted inputs
     (`ComposeHandlerTable_verbindung`: switched stack, with producer
     agreement to `liefere`; `..._behalten`: kept stack);
   - four refusal directions (`handler_undeclariert_verweigert`:
     undeclared vectors refuse at entry before any byte is read;
     `handler_unlesbar_verweigert`, `handler_torfehler_verweigert`,
     `handler_fehlbindung_verweigert`);
   - one joint non-degenerate witness
     (`ComposeHandlerTable_verbindung_zeuge`): declared vector 2 over
     the byte-populated IDT/TSS images, IST switch taken, interrupt
     gate clears IF, five-word frame reads back, two cells observably
     change, plus planted refusals (undeclared vector, renamed
     handler, dark stack).
   NOT proved here, and not claimed:
   - No GDT/code-segment ownership: `codeOk` arrives as an explicit
     checked input; selector table walks and conforming checks stay
     downstream (lane 672 per the producer CUTS).
   - No async completion: nested delivery, #DF escalation and
     TSO/store-buffer interaction stay with lanes 672/708 and the
     concurrency lanes; handler execution past delivery (fetch at the
     delivered RIP through the checked loaded mapping) is OPEN.
   - No full 256-vector table: the declared table is an explicit
     input; only reached faults carry vectors and codes.
   - No source correspondence: nothing here claims the declared table
     is the lowering of any source declaration; the shared IR
     (lane 287) and the QUELLBRUECKE bridge are the named open
     dependencies; no substitute IR or executor is invented here.
   - No hardware claim: refusal shapes are validator admission, never
     invented hardware faults; an unreadable gate half refuses as
     `unlesbar` (the accepted producer has no distinct
     in-limit-unreadable member); silicon, caches, TLBs and timing are
     untouched; `gabbro_ziel` axioms are untouched.
-/

#print axioms handlerFuer
#print axioms handlerEintritt
#print axioms handlerWeigerung
#print axioms handlerSpeicher
#print axioms rahmenWorte_mit_tor
#print axioms ComposeHandlerTable_verbindung
#print axioms ComposeHandlerTable_verbindung_behalten
#print axioms handler_undeclariert_verweigert
#print axioms handler_unlesbar_verweigert
#print axioms handler_torfehler_verweigert
#print axioms handler_fehlbindung_verweigert
#print axioms ComposeHandlerTable_verbindung_zeuge

end Gabbro.Grammatik.X86
