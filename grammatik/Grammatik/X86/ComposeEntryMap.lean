/-
  Entry-to-mapping closing (lane 827).

  Producer/consumer interface closed here, over already-accepted modules
  (nothing re-proved, no second decoder, no new executor):
  - producers: `Bild.wohlgeformt`/`geladen` (checked loaded mapping),
    `EntryState.eintrittOk` (listed executable entry, stack, guard,
    MXCSR, IF), `ValidatorSkeleton.valX86` (mapping AND whole-image
    decode coverage) with `GateStub.valTore`, `Byteschritt.fetchDekodiert`
    (the entry RIP as an actual decoded start in executable memory);
  - consumer: `Byteschritt.byteschritt` (the composed step runs).
  The closing predicate `composeEntryMap` conjoins the joint entry
  admission (`EntryExecution.eintrittZulassung`), the skeleton
  (`valX86`) and the decoded-start check; anything else refuses.
-/
import Grammatik.X86.EntryExecution
import Grammatik.X86.ValidatorSkeleton

namespace Gabbro.Grammatik.X86

/-- Closed entry-to-mapping admission: joint entry admission AND
    skeleton (checked mapping plus decode coverage) AND a decoded
    start at the entry RIP. A `Bool`, never a fault claim. -/
def composeEntryMap (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) : Bool :=
  eintrittZulassung p bild bias art z tore && valX86 p bild &&
    (fetchDekodiert z.zustand).isSome

/-- Admission implies the joint entry admission. -/
theorem composeEntryMap_zulassung (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : composeEntryMap p bild bias art z tore = true) :
    eintrittZulassung p bild bias art z tore = true := by
  unfold composeEntryMap at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- Admission implies the skeleton (checked mapping and decode coverage). -/
theorem composeEntryMap_skelett (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : composeEntryMap p bild bias art z tore = true) :
    valX86 p bild = true := by
  unfold composeEntryMap at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- Admission implies a decoded start at the entry RIP. -/
theorem composeEntryMap_startDekodiert (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl)
    (h : composeEntryMap p bild bias art z tore = true) :
    (fetchDekodiert z.zustand).isSome = true := by
  unfold composeEntryMap at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- Admission implies the checked image mapping. -/
theorem composeEntryMap_wohlgeformt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : composeEntryMap p bild bias art z tore = true) :
    wohlgeformt p bild = true :=
  valX86_wohlgeformt p bild
    (composeEntryMap_skelett p bild bias art z tore h)

/-- Admission makes the entry RIP executable through the CHECKED loaded
    mapping (the shared `Speicher` built from the image, not the state's
    own permission function). -/
theorem composeEntryMap_rip_ausfuehrbar (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl)
    (h : composeEntryMap p bild bias art z tore = true) :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true :=
  zulassung_rip_ausfuehrbar p bild bias art z tore
    (composeEntryMap_zulassung p bild bias art z tore h)

/-- CLOSING (entry-to-mapping): from the closed admission, a fetched
    instruction at the entry RIP runs as a real byte step, and the RIP
    is executable through the checked loaded mapping. Generic over
    arbitrary admitted inputs; the mapping leg reuses
    `zulassung_rip_ausfuehrbar`, the step leg `byteschritt_weiter`. -/
theorem ComposeEntryMap_verbindung (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hcomp : composeEntryMap p bild bias art z tore = true)
    (hf : fetchDekodiert z.zustand = some (d, rest))
    (hs : schritt d z.zustand = some s') :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      byteschritt z.zustand = .weiter s' :=
  ⟨composeEntryMap_rip_ausfuehrbar p bild bias art z tore hcomp,
    byteschritt_weiter z.zustand s' d rest hf hs⟩

/-- REFUSAL: an unlisted RIP admits no closed entry. -/
theorem composeEntryMap_verweigert_unlisted (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl)
    (h : eintragGelisted bild z.zustand.rip.toNat = false) :
    composeEntryMap p bild bias art z tore = false := by
  unfold composeEntryMap
  rw [zulassung_verweigert_unlisted p bild bias art z tore h]
  simp

/-- REFUSAL: a gate list with a refused member admits no closed entry. -/
theorem composeEntryMap_verweigert_tor (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (t : TorDekl) (hmem : t ∈ tore)
    (h : torOkB t = false) :
    composeEntryMap p bild bias art z tore = false := by
  unfold composeEntryMap
  rw [zulassung_verweigert_tor p bild bias art z tore t hmem h]
  simp

/-- REFUSAL: no decoded start at the entry RIP admits no closed entry,
    however clean the mapping and entry state are. -/
theorem composeEntryMap_verweigert_ohne_start (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl)
    (h : fetchDekodiert z.zustand = none) :
    composeEntryMap p bild bias art z tore = false := by
  unfold composeEntryMap
  rw [h]
  simp

/-- ACCEPTANCE: the witness entry (listed `ret` entry, aligned stack,
    admitted gate) closes with the skeleton and a decoded start. -/
theorem composeEntryMap_zeuge_ok :
    composeEntryMap .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [schreibTor] = true := by
  decide

/-- PLANTED REFUSAL: the same entry moved to an unlisted RIP closes
    nothing, although image, stack, skeleton and gate are unchanged. -/
theorem composeEntryMap_fremd_verweigert :
    composeEntryMap .p48 valZeuge 0 .hostedMain
      { zeugenEintrittAusf with zustand :=
        { zeugenEintrittAusf.zustand with
          rip := BitVec.ofNat 64 0x5000 } } [schreibTor] = false := by
  decide

/-- PLANTED REFUSAL: the closed entry with a clobbered-out gate closes
    nothing, although image, entry state and skeleton are unchanged. -/
theorem composeEntryMap_abi_verweigert :
    composeEntryMap .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [torAusClobber] = false := by
  decide

/-- PLANTED REFUSAL (W^X): a writable-and-executable section closes
    nothing at the mapping leg, although entry state and gate are
    unchanged. -/
theorem composeEntryMap_wx_verweigert :
    composeEntryMap .p48 valWx 0 .hostedMain zeugenEintrittAusf
      [schreibTor] = false := by
  decide

/-- Witness entry state whose own memory grants no execute permission:
    the checked mapping and entry discipline still hold (they read the
    image, not this memory), but no byte can be fetched there. -/
def zeugenEintrittOhneAusfuehrbar : EintrittZustand :=
  { zeugenEintrittAusf with zustand :=
    { zeugenEintrittAusf.zustand with speicher :=
      { zulassungSpeicher with ausfuehrbar := fun _ => false } } }

/-- The no-execute witness keeps the joint entry admission: mapping and
    entry discipline read the image, not this memory. -/
theorem zeugenOhneAusfuehrbar_zulassung :
    eintrittZulassung .p48 valZeuge 0 .hostedMain
      zeugenEintrittOhneAusfuehrbar [schreibTor] = true := by
  decide

/-- No fetch without execute permission: the decoded-start leg sees
    nothing at this entry RIP. -/
theorem zeugenOhneAusfuehrbar_ohne_start :
    fetchDekodiert zeugenEintrittOhneAusfuehrbar.zustand = none := by
  decide

/-- PLANTED REFUSAL (decoded start): mapping, entry state, skeleton and
    gate hold, yet the closed entry refuses -- the RIP is no decoded
    start in the memory the machine fetches. -/
theorem composeEntryMap_start_verweigert :
    composeEntryMap .p48 valZeuge 0 .hostedMain
      zeugenEintrittOhneAusfuehrbar [schreibTor] = false := by
  decide

/-- JOINT WITNESS (closed entry runs, source duties hold): the witness
    entry closes (checked mapping, skeleton, decoded start, admitted
    gate), its fetched `ret` steps through the composed closing, and on
    a reached non-degenerate source run (a table-writing call with a
    `0 -> 5` memory change) the entry contract holds at its actual
    place -- plus a real eight-byte x86 memory change. Every premise of
    `ComposeEntryMap_verbindung` is jointly instantiated; neither side
    is assumed from the other. -/
theorem ComposeEntryMap_verbindung_zeuge :
    ∃ (M : RufMaschineG eD) (rhoP : Env eD (eD.params ePruefe))
      (wP : World eD) (s' : Zustand) (m m' : Speicher) (a : Adresse)
      (v : Wort),
      composeEntryMap .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
        [schreibTor] = true ∧
      fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) ∧
      schritt ⟨.ret, 1⟩ zeugenEintrittAusf.zustand = some s' ∧
      (geladen valZeuge 0).ausfuehrbar
        zeugenEintrittAusf.zustand.rip = true ∧
      byteschritt zeugenEintrittAusf.zustand = .weiter s' ∧
      ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
        some (BitVec.ofNat 64 0) ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ReqAmEintritt eP ePruefe wP rhoP ∧
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  obtain ⟨M, hr, _, hschr, rhoP, wP, _, _, _, _, _, _, _,
    _, _, hreq, _⟩ := vertragStandort_lauf_zeuge
  obtain ⟨m, m', a, v, hne, hwr, hrd64, hchg⟩ := write_read_zeuge
  have hok : laengeOk 1 = true := by decide
  have hrdSt : read64 zeugenEintrittAusf.zustand.speicher
      (zeugenEintrittAusf.zustand.register Register.rsp) =
      some (BitVec.ofNat 64 0) := by decide
  have hs : schritt ⟨.ret, 1⟩ zeugenEintrittAusf.zustand =
      some (schrittRet zeugenEintrittAusf.zustand Register.rsp
        (zeugenEintrittAusf.zustand.register Register.rsp +
          BitVec.ofNat 64 8) (BitVec.ofNat 64 0)) :=
    schritt_ret_erfolg _ _ _ hok rfl hrdSt
  have hverb := ComposeEntryMap_verbindung .p48 valZeuge 0 .hostedMain
    zeugenEintrittAusf [schreibTor] ⟨.ret, 1⟩ [] _
    composeEntryMap_zeuge_ok zulassung_fetch_ret hs
  exact ⟨M, rhoP, wP, _, m, m', a, v, composeEntryMap_zeuge_ok,
    zulassung_fetch_ret, hs, hverb.1, hverb.2, zulassung_schritt_ret,
    hr, hschr, hreq, hne, hwr, hrd64, hchg⟩

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Bild.wohlgeformt`/
   `geladen`, `EntryState.eintrittOk`, `EntryExecution.eintrittZulassung`
   with its witness `zeugenEintrittAusf`/`zulassungSpeicher`,
   `GateStub.torOkB`/`schreibTor`/`torAusClobber`,
   `ValidatorSkeleton.valX86`/`valZeuge`/`valWx`/`valTore`,
   `Byteschritt.fetchDekodiert`/`byteschritt`/`byteschritt_weiter`,
   `Ausfuehrung.schritt`/`schritt_ret_erfolg`,
   `ContractSites.vertragStandort_lauf_zeuge`,
   `Speicher.write_read_zeuge`): the closed admission predicate
   (`composeEntryMap`: joint entry admission AND skeleton AND a decoded
   start at the entry RIP), its joint-admission/skeleton/decoded-start/
   mapping projections, RIP executability through the CHECKED loaded
   mapping, the closing step (`ComposeEntryMap_verbindung`), generic
   unlisted-RIP / refused-gate / missing-start refusals, planted
   `decide` refusals (unlisted RIP, clobbered gate, W^X section,
   no-decoded-start with mapping and entry intact), the acceptance
   witness, and the joint witness (closed entry, fetched `ret`,
   executed step, reached non-degenerate table-writing source run with
   the entry contract at its place, real x86 memory change).
   OPEN, stated here as obligation and never as an assumed premise of
   any delivered theorem:
   - Source-to-entry lowering: no claim that the admitted bytes are the
     emitted form of any source program. The shared IR (lane 287) and
     the QUELLBRUECKE bridge stay the named open dependencies; no
     substitute IR or executor is invented here.
   - No TSO/GX bridge: every step here is sequential over one
     `Speicher`; per-access target-to-W/GX simulation stays with its
     owner (lanes 567/573-574).
   - No whole-binary/multi-step claim: single composed first step only;
     control-flow legality beyond containment, relocation re-decoding
     correspondence and callee-side template proofs stay with theirs.
   - No hardware claim: refusal `Bool`s are validator admission, never
     a fault claim; silicon, caches, TLBs, store buffers, interrupts,
     faults beyond the decoded refusal and timing are untouched.
     Binding/kernel behaviour stays user logic.
   - No cost/time claim: no budget, cycle or bound is transferred.
-/

#print axioms composeEntryMap
#print axioms composeEntryMap_zulassung
#print axioms composeEntryMap_skelett
#print axioms composeEntryMap_startDekodiert
#print axioms composeEntryMap_wohlgeformt
#print axioms composeEntryMap_rip_ausfuehrbar
#print axioms ComposeEntryMap_verbindung
#print axioms composeEntryMap_verweigert_unlisted
#print axioms composeEntryMap_verweigert_tor
#print axioms composeEntryMap_verweigert_ohne_start
#print axioms composeEntryMap_zeuge_ok
#print axioms composeEntryMap_fremd_verweigert
#print axioms composeEntryMap_abi_verweigert
#print axioms composeEntryMap_wx_verweigert
#print axioms zeugenOhneAusfuehrbar_zulassung
#print axioms zeugenOhneAusfuehrbar_ohne_start
#print axioms composeEntryMap_start_verweigert
#print axioms ComposeEntryMap_verbindung_zeuge

end Gabbro.Grammatik.X86
