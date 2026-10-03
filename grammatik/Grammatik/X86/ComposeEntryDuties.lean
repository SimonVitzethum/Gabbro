/-
  Composition closing: entry duties to one checked conjunction per image
  (lane 858).

  Producer/consumer interface closed here: the producers are the accepted
  joint entry admission (`EntryExecution.eintrittZulassung`: checked image
  mapping AND entry state AND caller gates), the accepted validator
  skeleton (`ValidatorSkeleton.valX86`: mapping AND decode coverage,
  `valTore`, `valLayout`, `externOk`), the accepted computed layout
  (`TableLayout.layoutOk`) and the accepted byte-step execution
  (`Byteschritt.byteschritt` through `zulassung_erster_schritt`). The
  consumer is the per-image duty conjunction (`pflichtSchluss`) and the
  source binding duties at their actual place (`ReqAmEintritt` through the
  accepted reached run, the gate channel link through
  `tor_grund_im_kanal`). Nothing is re-proved here: no second loader,
  decoder, executor, layout or ISA model.
-/
import Grammatik.X86.EntryExecution
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

/-- One checked duty conjunction per image: joint entry admission AND
    decode coverage of every executable section AND the computed table
    layout AND every extern site's proved correspondence. A `Bool`, never
    a fault claim; any unresolved obligation refuses. -/
def pflichtSchluss (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (es : List TabLayout) (xs : List ExternStelle) : Bool :=
  eintrittZulassung p bild bias art z tore && bildDeckung bild &&
    valLayout es && externOk xs

/-- Admission implies the joint entry admission (checked mapping AND
    entry state AND gates). Composes the accepted conjunction shape;
    no producer fact is re-proved. -/
theorem pflicht_eintritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (es : List TabLayout) (xs : List ExternStelle)
    (h : pflichtSchluss p bild bias art z tore es xs = true) :
    eintrittZulassung p bild bias art z tore = true := by
  unfold pflichtSchluss at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.1

/-- Admission implies the full image skeleton (checked mapping AND
    decode coverage of every executable section). The mapping half comes
    from the accepted entry projection (`zulassung_wohlgeformt`), the
    coverage half is the conjunction's own; neither is re-proved. -/
theorem pflicht_valX86 (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (es : List TabLayout) (xs : List ExternStelle)
    (h : pflichtSchluss p bild bias art z tore es xs = true) :
    valX86 p bild = true := by
  have hzul := pflicht_eintritt p bild bias art z tore es xs h
  have hmap := zulassung_wohlgeformt p bild bias art z tore hzul
  unfold pflichtSchluss at h
  simp only [Bool.and_eq_true_iff] at h
  unfold valX86
  rw [hmap, h.1.1.2]
  rfl

/-- DUTY CLOSING through the one checked conjunction, generic over
    arbitrary admitted inputs: one admission yields the joint entry
    admission, the full image skeleton, the layout and extern duties,
    the checked mapping, and RIP executability through the CHECKED
    loaded mapping (not the state's own permission function). Composes
    the accepted projections by name; no producer fact is re-proved. -/
theorem ComposeEntryDuties_verbindung (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (es : List TabLayout) (xs : List ExternStelle)
    (h : pflichtSchluss p bild bias art z tore es xs = true) :
    eintrittZulassung p bild bias art z tore = true ∧
      valX86 p bild = true ∧
      valLayout es = true ∧
      externOk xs = true ∧
      wohlgeformt p bild = true ∧
      (geladen bild bias).ausfuehrbar z.zustand.rip = true := by
  have hzul := pflicht_eintritt p bild bias art z tore es xs h
  have hval := pflicht_valX86 p bild bias art z tore es xs h
  have hmap := zulassung_wohlgeformt p bild bias art z tore hzul
  have hexe := zulassung_rip_ausfuehrbar p bild bias art z tore hzul
  unfold pflichtSchluss at h
  simp only [Bool.and_eq_true_iff] at h
  exact ⟨hzul, hval, h.1.2, h.2, hmap, hexe⟩

/-- FIRST STEP RUNS through the composed admission: the closing is
    execution, not a conjunction of checks. From one admission, a
    fetched instruction with an execution outcome steps the actual byte
    machine, and the RIP is executable through the checked loaded
    mapping. Reuses the accepted `zulassung_erster_schritt`; no second
    fetch, no new executor. -/
theorem pflicht_erster_schritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (es : List TabLayout) (xs : List ExternStelle)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (h : pflichtSchluss p bild bias art z tore es xs = true)
    (hf : fetchDekodiert z.zustand = some (d, rest))
    (hs : schritt d z.zustand = some s') :
    byteschritt z.zustand = .weiter s' ∧
      (geladen bild bias).ausfuehrbar z.zustand.rip = true := by
  have hzul := pflicht_eintritt p bild bias art z tore es xs h
  have hstep := zulassung_erster_schritt p bild bias art z tore d rest s'
    hzul hf hs
  exact ⟨hstep.2, hstep.1⟩

/-- REFUSAL: a refused joint entry admission admits no duty closing.
    Uses the missing admission; composes the accepted unlisted-RIP and
    refused-gate legs (`zulassung_verweigert_unlisted`,
    `zulassung_verweigert_tor`) upstream of this lemma. -/
theorem pflicht_verweigert_eintritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (es : List TabLayout) (xs : List ExternStelle)
    (h : eintrittZulassung p bild bias art z tore = false) :
    pflichtSchluss p bild bias art z tore es xs = false := by
  unfold pflichtSchluss
  rw [h]
  simp

/-- REFUSAL: an image whose executable sections do not fully decode
    admits no duty closing, even where the mapping checks. Uses the
    missing coverage. -/
theorem pflicht_verweigert_ohne_deckung (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (es : List TabLayout) (xs : List ExternStelle)
    (h : bildDeckung bild = false) :
    pflichtSchluss p bild bias art z tore es xs = false := by
  unfold pflichtSchluss
  rw [h]
  simp

/-- REFUSAL: a refused computed table layout admits no duty closing.
    Uses the missing layout; the overlap and alignment shapes are the
    accepted `ueberlapp_verweigert` / `unausgerichtet_verweigert`. -/
theorem pflicht_verweigert_ohne_layout (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (es : List TabLayout) (xs : List ExternStelle)
    (h : valLayout es = false) :
    pflichtSchluss p bild bias art z tore es xs = false := by
  unfold pflichtSchluss
  rw [h]
  simp

/-- REFUSAL: an extern site without proved correspondence admits no
    duty closing; the declaration alone admits nothing. Uses the
    missing bookkeeping bit; the shape is the accepted
    `valFremd_verweigert`. -/
theorem pflicht_verweigert_ohne_extern (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (es : List TabLayout) (xs : List ExternStelle)
    (h : externOk xs = false) :
    pflichtSchluss p bild bias art z tore es xs = false := by
  unfold pflichtSchluss
  rw [h]
  simp

/-- ACCEPTANCE: the one checked conjunction holds on the minimal
    accepted image with the admitted entry, the admitted gate, the
    empty layout and no extern sites. Checked by reduction. -/
theorem pflicht_zeuge_ok :
    pflichtSchluss .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [schreibTor] [] [] = true := by
  decide

/-- PLANTED REFUSAL (altered byte): flipping the single `ret` opcode to
    0 refuses the whole duty closing through decode coverage, although
    the mapping still checks (the accepted
    `valZeuge_mutiert_mapping_bleibt`). Checked by reduction. -/
theorem pflicht_mutiert_verweigert :
    pflichtSchluss .p48 { valZeuge with datei := [natByte 0] } 0
      .hostedMain zeugenEintrittAusf [schreibTor] [] [] = false := by
  decide

/-- PLANTED REFUSAL (overlap): two table extents sharing bytes refuse
    the whole duty closing, although image, entry and gates are
    unchanged. The layout shape is the accepted `ueberlapp_verweigert`. -/
theorem pflicht_layout_verweigert :
    pflichtSchluss .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [schreibTor]
      [{ tab := 0, basis := 4096, len := 16, ausr := 8 },
       { tab := 1, basis := 4104, len := 16, ausr := 8 }] [] = false := by
  decide

/-- PLANTED REFUSAL (unchecked foreign body): one extern site without
    proved correspondence refuses the whole duty closing, although
    image, entry, gates and layout are unchanged. The shape is the
    accepted `valFremd_verweigert`. -/
theorem pflicht_extern_verweigert :
    pflichtSchluss .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [schreibTor] [] [{ ort := 0, bewiesen := false }] = false := by
  decide

/-- JOINT WITNESS for `ComposeEntryDuties_verbindung`: every premise
    jointly instantiated on the minimal accepted image with the admitted
    hosted entry, the admitted gate, the empty layout and no extern
    sites; the admitted `ret` is fetched from the checked bytes and
    steps; a reached non-degenerate source run (a table-writing call
    with a `0 -> 5` memory change) carries the entry contract at its
    actual place; a real eight-byte x86 memory change; and three planted
    refusals (unlisted RIP, clobbered-out gate, mutated opcode byte).
    Neither side is assumed from the other. -/
theorem ComposeEntryDuties_verbindung_zeuge :
    ∃ (M : RufMaschineG eD) (rhoP : Env eD (eD.params ePruefe))
      (wP : World eD),
      pflichtSchluss .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
        [schreibTor] [] [] = true ∧
      valX86 .p48 valZeuge = true ∧
      fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) ∧
      ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
        some (BitVec.ofNat 64 0) ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      ReqAmEintritt eP ePruefe wP rhoP ∧
      (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a) ∧
      pflichtSchluss .p48 valZeuge 0 .hostedMain
        { zeugenEintrittAusf with zustand :=
          { zeugenEintrittAusf.zustand with
            rip := BitVec.ofNat 64 0x5000 } }
        [schreibTor] [] [] = false ∧
      pflichtSchluss .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
        [torAusClobber] [] [] = false ∧
      pflichtSchluss .p48 { valZeuge with datei := [natByte 0] } 0
        .hostedMain zeugenEintrittAusf [schreibTor] [] [] = false := by
  obtain ⟨M, rhoP, wP, _, hfetch, hstep, hr, hreq, hmem⟩ :=
    eintrittAusf_zeuge
  exact ⟨M, rhoP, wP, pflicht_zeuge_ok, valZeuge_akzeptiert, hfetch,
    hstep, hr, hreq, hmem, by decide, by decide,
    pflicht_mutiert_verweigert⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second loader/decoder/executor/layout/ISA): the
    one checked closing step `pflichtSchluss` (joint entry admission AND
    decode coverage AND computed layout AND extern-site bookkeeping),
    its entry/image projections (`pflicht_eintritt`, `pflicht_valX86`),
    the generic duty closing for arbitrary admitted inputs
    (`ComposeEntryDuties_verbindung`: admission, image skeleton, layout
    and extern duties, checked mapping, RIP executability through the
    CHECKED loaded mapping), the first-step execution leg
    (`pflicht_erster_schritt`: the closing is execution, not a conjunction
    of checks), one generic refusal per unresolved obligation
    (`pflicht_verweigert_eintritt` / `_ohne_deckung` / `_ohne_layout` /
    `_ohne_extern`), one checked acceptance (`pflicht_zeuge_ok`), three
    planted refusals pinning each half (`pflicht_mutiert_verweigert` is
    a coverage refusal with the mapping intact,
    `pflicht_layout_verweigert` an overlap, `pflicht_extern_verweigert`
    an unproved foreign body), and the joint non-degenerate witness with
    a reached memory-changing run and planted refusals
    (`ComposeEntryDuties_verbindung_zeuge`).
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the admitted bytes
      are the emitted form of any source program, or that any source
      start lowers to this entry. The shared IR (lane 287) and the
      QUELLBRUECKE bridge are the named open dependencies; no substitute
      IR or executor is invented here.
    - No hardware correspondence: bytes are model `Byte` lists, memory
      the model `Speicher`; silicon, caches, TLBs, store buffers,
      interrupts, faults beyond the decoded refusal and timing are OPEN.
      The refusal `Bool`s are validator admission, never a hardware
      fault claim. Gate/OS contracts stay user logic, never assumptions.
    - No per-access target-to-W/GX simulation: the existing source
      `schwach_ist_gX` result is reused, never re-proved or assumed for
      the target. Owner: the TSO bridge lane.
    - No budget/work transfer and no `valX86_sound`: OPEN. Owners are
      the budget lane and the validator-soundness follow-up.
    - No multi-step control-flow claim: the witness `ret` pops to RIP
      zero (unlisted); entry legality beyond containment and callee-side
      template proofs stay with their owners.
-/

#print axioms ComposeEntryDuties_verbindung
#print axioms ComposeEntryDuties_verbindung_zeuge
#print axioms pflicht_erster_schritt
#print axioms pflicht_verweigert_eintritt
#print axioms pflicht_verweigert_ohne_deckung
#print axioms pflicht_verweigert_ohne_layout
#print axioms pflicht_verweigert_ohne_extern
#print axioms pflicht_zeuge_ok
#print axioms pflicht_mutiert_verweigert
#print axioms pflicht_layout_verweigert
#print axioms pflicht_extern_verweigert
#print axioms pflichtSchluss
#print axioms pflicht_eintritt
#print axioms pflicht_valX86

end Gabbro.Grammatik.X86
