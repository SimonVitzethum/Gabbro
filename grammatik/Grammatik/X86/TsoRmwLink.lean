/-
  File:      Grammatik/X86/TsoRmwLink.lean
  Subject:   LOCK words to W history: timestamp and value link.

  Lane 1213 (follow-up of lane 1145, `TsoRmwBridge.lean`): the
  timestamp/value link from LOCK event words to W history messages
  (`wahl`/`neu`, `Frisch`, the lowering certificate's value link) that
  lane 1145 left OPEN. Proved here, for the accepted locked steps: the
  read-write pairing's value equals the history message's value,
  timestamps strictly increase per location along chained locked steps,
  and the `rmw` adjacency (`neu = wahl.ts + 1`) is discharged for a
  step with no intervening buffered store. CMPXCHG failure is a
  read-only step (word written back unchanged) with the same link.
  No fairness or retry bound.

  SCOPE (honest): the link is proved over the generic history shape
  (`Nachricht`/`Lesbar`/`Frisch` at `Adresse`/`Wort`) that the W
  `wahl`/`neu` fields instantiate -- NOT over a concrete Gabbro
  program's carriers, because no accepted mapping from x86 addresses
  to Gabbro carriers exists yet (owned by the source/table-write
  consumer lanes). The full per-access target-to-W/GX simulation stays
  OPEN (see CUTS).

  Manual provenance: none new -- Intel SDM 325462-093US Sep 2026 via
  the accepted 662 module and lane 1145 (LOCK Vol. 2A 3-565/3-566,
  XADD Vol. 2D 6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194). This lane adds
  no new silicon claim beyond reusing those rows. Aligned whole-word
  atomicity stays a selected-profile contract (`ausgerichtet8` plus
  the empty own buffer), never a hardware proof.
-/
import Grammatik.X86.TsoRmwBridge
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

/-- History vocabulary reused for the link: histories over LOCK word
    addresses with word values -- the generic shape the W histories
    instantiate. -/
abbrev LockHist := Adresse → List (Speichermodell.Nachricht Adresse Wort)

/-- View vocabulary reused for the link. -/
abbrev LockBlick := Speichermodell.Sicht Adresse

/-- The timestamp/value link of one locked step at address `a`: the
    read pairing carries the history message's value (`liesWert`), that
    message is readable at the view (`lesbar`), the write stamp is
    fresh (`frisch`), directly above the read stamp (`angrenzend` --
    exactly the `SchrittW.rmw` shape), and the write pairing carries
    the installed value (`schreibtWert`). -/
structure RmwLink (ev : LockEreignis) (hist : LockHist) (v : LockBlick)
    (a : Adresse) (wahl : Speichermodell.Nachricht Adresse Wort)
    (neu : Nat) (wneu : Wort) : Prop where
  liesWert : ev.gelesen = some wahl.wert
  lesbar : Speichermodell.Lesbar hist v a wahl
  frisch : Speichermodell.Frisch hist v a neu
  angrenzend : neu = wahl.ts + 1
  schreibtWert : ev.geschrieben = some wneu

/-! ## 1. Plug reuse: well-formedness and refusals.

  The bridge plug `tsoRmwAdapter` (lane 1145, reusing `adapterLockRmw`
  unchanged) is lifted, never redefined. -/

/-- The link plug preserves well-formedness: exactly the accepted plug
    lemma, lifted. -/
theorem rmwLink_adapter_wf (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (m' : HwMaschine)
    (h : tsoRmwAdapter.schritt m c a = some m') (hwf : HwWf m) :
    HwWf m' :=
  tsoRmwAdapter_wf m c a m' h hwf

/-- A pending own store refuses the locked word step, so no link event
    exists through the plug. -/
theorem rmwLink_puffer_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest)
    (hok : laengeOk len = true) :
    tsoRmwAdapter.schritt m c (.ok (.xadd64 src base d) len) = none :=
  tsoRmw_puffer_bleibt_verweigert m c src base d len e rest hbuf hok

/-- A misaligned word refuses the locked step, so no link event exists
    through the plug. -/
theorem rmwLink_unaligned_verweigert (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true)
    (hfehl : ausgerichtet8 (effAddr (projZustand m c) base d) = false) :
    tsoRmwAdapter.schritt m c (.ok (.xadd64 src base d) len) = none :=
  tsoRmw_unaligned_bleibt_verweigert m c src base d len hbuf hok hfehl

/-! ## 2. Value link: event words equal history message values.

  Each admitted form is pinned by its accepted step equation with the
  SAME guards (lane 1145 lemmas); the history side is the generic
  `Lesbar`/`Frisch` shape the W `wahl`/`neu` fields instantiate. Every
  premise below feeds either the accepted step equation or one link
  field. -/

/-- XADD value link: the admitted step's read pairing equals the
    history message value, its write pairing the installed word, and
    the link discharges the `rmw` adjacency `neu = wahl.ts + 1`. -/
theorem rmwLink_xadd (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (alt sval : Wort) (mem' : Speicher)
    (hist : LockHist) (v : LockBlick)
    (wahl : Speichermodell.Nachricht Adresse Wort)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some alt)
    (hreg : (m.kerne c).register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d)
      (alt + sval) = some mem')
    (hles : lesbar8 m.mem (effAddr (projZustand m c) base d) = true)
    (hwahl : wahl.wert = alt)
    (hmem : wahl ∈ hist (effAddr (projZustand m c) base d))
    (hle : v (effAddr (projZustand m c) base d) ≤ wahl.ts)
    (hlt : v (effAddr (projZustand m c) base d) < wahl.ts + 1)
    (hne : ∀ msg ∈ hist (effAddr (projZustand m c) base d),
      msg.ts ≠ wahl.ts + 1) :
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.xadd64 src base d) len) = some (m2, ev) ∧
      ev.istRmw = true ∧ ev.istZaun = false ∧
      ev.lesen = Fuss (effAddr (projZustand m c) base d) ∧
      ev.schreiben = Fuss (effAddr (projZustand m c) base d) ∧
      ev.gelesen = some wahl.wert ∧
      ev.geschrieben = some (alt + sval) ∧
      RmwLink ev hist v (effAddr (projZustand m c) base d) wahl
        (wahl.ts + 1) (alt + sval) := by
  obtain ⟨m2, ev, hEv, hRmw, hZaun, hLesen, hSchreiben, hGelesen,
    hGeschrieben, _, _, _⟩ :=
    tsoRmw_xadd_einzel_rmw m c src base d len alt sval mem'
      hbuf hali hrd hreg hok hwr hles
  refine ⟨m2, ev, hEv, hRmw, hZaun, hLesen, hSchreiben, ?_,
    hGeschrieben, ?_⟩
  · rw [hwahl]
    exact hGelesen
  · exact ⟨by rw [hwahl]; exact hGelesen, ⟨hmem, hle⟩, ⟨hlt, hne⟩,
      rfl, hGeschrieben⟩

/-- CMPXCHG-success value link: the read pairing equals the history
    message value, the installed source word the written value. -/
theorem rmwLink_cmpxchg_erfolg (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest sval : Wort) (mem' : Speicher)
    (hist : LockHist) (v : LockBlick)
    (wahl : Speichermodell.Nachricht Adresse Wort)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some dest)
    (hgleich : (dest == (m.kerne c).register .rax) = true)
    (hsrc : (m.kerne c).register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d) sval =
      some mem')
    (hles : lesbar8 m.mem (effAddr (projZustand m c) base d) = true)
    (hwahl : wahl.wert = dest)
    (hmem : wahl ∈ hist (effAddr (projZustand m c) base d))
    (hle : v (effAddr (projZustand m c) base d) ≤ wahl.ts)
    (hlt : v (effAddr (projZustand m c) base d) < wahl.ts + 1)
    (hne : ∀ msg ∈ hist (effAddr (projZustand m c) base d),
      msg.ts ≠ wahl.ts + 1) :
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
        some (m2, ev) ∧
      ev.istRmw = true ∧ ev.istZaun = false ∧
      ev.lesen = Fuss (effAddr (projZustand m c) base d) ∧
      ev.schreiben = Fuss (effAddr (projZustand m c) base d) ∧
      ev.gelesen = some wahl.wert ∧
      ev.geschrieben = some sval ∧
      RmwLink ev hist v (effAddr (projZustand m c) base d) wahl
        (wahl.ts + 1) sval := by
  obtain ⟨m2, ev, hEv, hForm, _, _, _⟩ :=
    tsoRmw_cmpxchg_erfolg_einzel_rmw m c src base d len dest sval mem'
      hbuf hali hrd hgleich hsrc hok hwr hles
  obtain ⟨hRmw, hZaun, hLesen, hSchreiben, hGelesen, hGeschrieben⟩ :=
    hForm
  refine ⟨m2, ev, hEv, hRmw, hZaun, hLesen, hSchreiben, ?_,
    hGeschrieben, ?_⟩
  · rw [hwahl]
    exact hGelesen
  · exact ⟨by rw [hwahl]; exact hGelesen, ⟨hmem, hle⟩, ⟨hlt, hne⟩,
      rfl, hGeschrieben⟩

/-- CMPXCHG-failure link: the failed comparison is a read-only step --
    the word is written back unchanged, so the written pairing equals
    the read pairing -- with the same value link and `rmw` adjacency. -/
theorem rmwLink_cmpxchg_fehlschlag_nur_liest (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest : Wort) (mem' : Speicher)
    (hist : LockHist) (v : LockBlick)
    (wahl : Speichermodell.Nachricht Adresse Wort)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr (projZustand m c) base d) = true)
    (hrd : read64 m.mem (effAddr (projZustand m c) base d) = some dest)
    (hfehl : (dest == (m.kerne c).register .rax) = false)
    (hok : laengeOk len = true)
    (hwr : write64 m.mem (effAddr (projZustand m c) base d) dest =
      some mem')
    (hwahl : wahl.wert = dest)
    (hmem : wahl ∈ hist (effAddr (projZustand m c) base d))
    (hle : v (effAddr (projZustand m c) base d) ≤ wahl.ts)
    (hlt : v (effAddr (projZustand m c) base d) < wahl.ts + 1)
    (hne : ∀ msg ∈ hist (effAddr (projZustand m c) base d),
      msg.ts ≠ wahl.ts + 1) :
    ∃ (m2 : HwMaschine) (ev : LockEreignis),
      hwLockSchrittEv m c (.ok (.cmpxchg64 src base d) len) =
        some (m2, ev) ∧
      ev.istRmw = true ∧ ev.istZaun = false ∧
      ev.lesen = Fuss (effAddr (projZustand m c) base d) ∧
      ev.schreiben = Fuss (effAddr (projZustand m c) base d) ∧
      ev.gelesen = some wahl.wert ∧
      ev.geschrieben = ev.gelesen ∧
      RmwLink ev hist v (effAddr (projZustand m c) base d) wahl
        (wahl.ts + 1) dest := by
  obtain ⟨m2, ev, hEv, hRmw, hZaun, hLesen, hSchreiben, hGelesen,
    hGeschrieben, _, _, _⟩ :=
    tsoRmw_cmpxchg_fehlschlag_rmw m c src base d len dest mem'
      hbuf hali hrd hfehl hok hwr
  refine ⟨m2, ev, hEv, hRmw, hZaun, hLesen, hSchreiben, ?_, ?_, ?_⟩
  · rw [hwahl]
    exact hGelesen
  · rw [hGeschrieben, hGelesen]
  · exact ⟨by rw [hwahl]; exact hGelesen, ⟨hmem, hle⟩, ⟨hlt, hne⟩,
      rfl, hGeschrieben⟩

/-! ## 3. Timestamp link: chained RMWs strictly increase per location.

  The history form of `tsoRmw_kette_ohne_verlust`: the second step
  reads the first step's write, so both the read timestamps and the
  write timestamps strictly increase at the shared address. -/

/-- Chained links strictly increase: the second read pairing equals the
    first write pairing, and both stamps grow. Every premise feeds the
    conclusion: `h1` the write pairing and the first adjacency, `h2`
    the read pairing, the second adjacency and the written value. -/
theorem rmwLink_kette (ev1 ev2 : LockEreignis)
    (hist1 hist2 : LockHist) (v1 v2 : LockBlick) (a : Adresse)
    (w1 w2 : Speichermodell.Nachricht Adresse Wort)
    (neu1 neu2 : Nat) (wneu1 wneu2 : Wort)
    (h1 : RmwLink ev1 hist1 v1 a w1 neu1 wneu1)
    (h2 : RmwLink ev2 hist2 v2 a w2 neu2 wneu2)
    (hkette_ts : w2.ts = neu1)
    (hkette_wert : w2.wert = wneu1) :
    ev2.gelesen = ev1.geschrieben ∧ w1.ts < w2.ts ∧ neu1 < neu2 ∧
      ev2.geschrieben = some wneu2 := by
  refine ⟨?_, ?_, ?_, h2.schreibtWert⟩
  · rw [h2.liesWert, hkette_wert, ← h1.schreibtWert]
  · have hadj1 := h1.angrenzend
    omega
  · have hadj1 := h1.angrenzend
    have hadj2 := h2.angrenzend
    omega

/-- The `rmw` field is discharged for a step with no intervening
    buffered store: two admitted locked adds on one target -- each
    gated on its own empty buffer (`hbuf1`/`hbuf2`), so no buffered
    store sits between read and write -- serialize with the second
    reading the first one's write. Exactly the accepted chain lemma,
    lifted. -/
theorem rmwLink_kette_ohne_puffer (m1 m2 m3 : HwMaschine) (c1 c2 : Nat)
    (ev1 ev2 : LockEreignis)
    (src1 base1 : Register) (d1 : BitVec 32) (len1 : Nat)
    (alt1 sval1 : Wort) (mem2 : Speicher)
    (hbuf1 : m1.puffer c1 = [])
    (hali1 : ausgerichtet8 (effAddr (projZustand m1 c1) base1 d1) = true)
    (hrd1 : read64 m1.mem (effAddr (projZustand m1 c1) base1 d1) =
      some alt1)
    (hreg1 : (m1.kerne c1).register src1 = sval1)
    (hok1 : laengeOk len1 = true)
    (hwr1 : write64 m1.mem (effAddr (projZustand m1 c1) base1 d1)
      (alt1 + sval1) = some mem2)
    (hles1 : lesbar8 m1.mem (effAddr (projZustand m1 c1) base1 d1) = true)
    (src2 base2 : Register) (d2 : BitVec 32) (len2 : Nat)
    (alt2 sval2 : Wort) (mem3 : Speicher)
    (hbuf2 : m2.puffer c2 = [])
    (hali2 : ausgerichtet8 (effAddr (projZustand m2 c2) base2 d2) = true)
    (hrd2 : read64 m2.mem (effAddr (projZustand m2 c2) base2 d2) =
      some alt2)
    (hreg2 : (m2.kerne c2).register src2 = sval2)
    (hok2 : laengeOk len2 = true)
    (hwr2 : write64 m2.mem (effAddr (projZustand m2 c2) base2 d2)
      (alt2 + sval2) = some mem3)
    (hles2 : lesbar8 m2.mem (effAddr (projZustand m2 c2) base2 d2) = true)
    (hstep1 : hwLockSchrittEv m1 c1 (.ok (.xadd64 src1 base1 d1) len1) =
      some (m2, ev1))
    (hstep2 : hwLockSchrittEv m2 c2 (.ok (.xadd64 src2 base2 d2) len2) =
      some (m3, ev2))
    (htgt : effAddr (projZustand m2 c2) base2 d2 =
      effAddr (projZustand m1 c1) base1 d1) :
    ev2.gelesen = ev1.geschrieben :=
  tsoRmw_kette_ohne_verlust m1 m2 m3 c1 c2 ev1 ev2
    src1 base1 d1 len1 alt1 sval1 mem2
    hbuf1 hali1 hrd1 hreg1 hok1 hwr1 hles1
    src2 base2 d2 len2 alt2 sval2 mem3
    hbuf2 hali2 hrd2 hreg2 hok2 hwr2 hles2
    hstep1 hstep2 htgt

/-! ## 4. Joint witness: reached two-core run with the history link.

  Reuses the accepted reached run (`hwLockWitStart`: word 10 at the
  witness address, core 1 holding one pending buffered byte outside the
  footprint): core 0 locked-adds 10 to 15, core 1 drains its byte and
  locked-adds 15 to 22. The history carries the read word 10 at
  timestamp 1 with timestamp 2 fresh -- the `rmw` adjacency shape --
  and the buffered byte is forwarded to its owner only. -/

/-- Witness history: the locked word address carries the initial
    message and the read word 10 at timestamp 1; every other address
    its initial message. -/
def witHist : LockHist :=
  fun a => if a = hwLockWitAdr then
    [⟨0, 0, Speichermodell.Sicht.null⟩,
     ⟨1, 10, Speichermodell.Sicht.null⟩]
    else [⟨0, 0, Speichermodell.Sicht.null⟩]

/-- Witness view: every address known at timestamp 1. -/
def witBlick : LockBlick := fun _ => 1

/-- Witness read message: word 10 at timestamp 1. -/
def witWahl : Speichermodell.Nachricht Adresse Wort :=
  ⟨1, 10, Speichermodell.Sicht.null⟩

/-- The read message is in the witness history. -/
theorem witWahl_mem : witWahl ∈ witHist hwLockWitAdr := by
  simp [witHist, witWahl]

/-- The read message is readable at the witness view. -/
theorem witWahl_lesbar :
    Speichermodell.Lesbar witHist witBlick hwLockWitAdr witWahl :=
  ⟨witWahl_mem, by decide⟩

/-- Timestamp 2 is fresh at the witness address: the `rmw` adjacency
    shape (`neu = wahl.ts + 1` with no intervening message). -/
theorem witNeu_frisch :
    Speichermodell.Frisch witHist witBlick hwLockWitAdr 2 := by
  refine ⟨by decide, ?_⟩
  intro msg hmsg
  have heq : witHist hwLockWitAdr =
      [⟨0, 0, Speichermodell.Sicht.null⟩,
       ⟨1, 10, Speichermodell.Sicht.null⟩] := by
    simp [witHist]
  rw [heq] at hmsg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmsg
  rcases hmsg with rfl | rfl
  · decide
  · decide

/-- The witness read value equals the first event's read word. -/
theorem witWahl_wert : witWahl.wert = 10 := rfl

/-- The witness write stamp is the read stamp plus one. -/
theorem witNeu_adj : witWahl.ts + 1 = 2 := rfl

/-- Joint timestamp/value witness: a reached two-core run whose chained
    locked adds move the word 10 to 15 to 22 -- the second event reads
    exactly what the first one wrote -- with the history value link
    (event words equal the history message value), the `rmw` adjacency
    (timestamp 2 fresh above the read timestamp 1), owner-only
    forwarding, well-formedness, and the planted refusals beside the
    run. Non-degenerate: both steps change ACTUAL shared memory on
    different cores. -/
theorem rmwLink_zeuge :
    tsoRmwEvGelesen tsoRmwWitEv1 = some (some witWahl.wert) ∧
    tsoRmwEvGeschrieben tsoRmwWitEv1 = some (some 15) ∧
    tsoRmwEvGelesen tsoRmwWitEv2 = some (some 15) ∧
    Speichermodell.Lesbar witHist witBlick hwLockWitAdr witWahl ∧
    Speichermodell.Frisch witHist witBlick hwLockWitAdr (witWahl.ts + 1) ∧
    HwWf hwLockWitStart ∧
    hwLockSicht hwLockWitNach1 1 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) ∧
    hwLockSicht hwLockWitNach1 0 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 0)) ∧
    tsoRmwAdapter.schritt hwLockWitStart 1
      (.ok (.xadd64 .rax .rbp 0) 9) = none ∧
    tsoRmwAdapter.schritt hwLockWitUnaligned 0
      (.ok (.xadd64 .rax .rbp 0) 9) = none := by
  refine ⟨?_, tsoRmwWit_ev1_geschrieben, tsoRmwWit_ev2_gelesen,
    witWahl_lesbar, ?_, hwLockWitStart_wf,
    hwLockWit_nach1_eigen_sicht, hwLockWit_nach1_fremd_sicht,
    hwLockWit_puffer, hwLockWit_unaligned⟩
  · rw [witWahl_wert]
    exact tsoRmwWit_ev1_gelesen
  · rw [witNeu_adj]
    exact witNeu_frisch

/- CUTS:
    Proved here: the timestamp/value link from LOCK event words to W
    history messages for the accepted locked steps -- the XADD,
    CMPXCHG-success and CMPXCHG-failure value links (`rmwLink_xadd`,
    `rmwLink_cmpxchg_erfolg`,
    `rmwLink_cmpxchg_fehlschlag_nur_liest`: read pairing equals the
    history message value, write pairing the installed word, `rmw`
    adjacency `neu = wahl.ts + 1` with `Frisch`; failure is read-only
    with the same link) (§2); strict timestamp increase per location
    along chained locked steps, at history level (`rmwLink_kette`)
    and at machine level with no intervening buffered store
    (`rmwLink_kette_ohne_puffer`, lifting the accepted chain lemma;
    `hbuf1`/`hbuf2` are the no-intervening-store guards) (§3); plug
    reuse (`rmwLink_adapter_wf`) with planted refusals beside the run
    (`rmwLink_puffer_verweigert`, `rmwLink_unaligned_verweigert`) (§1);
    the reached non-degenerate two-core joint witness
    `rmwLink_zeuge` (word 10 to 15 to 22 across two cores, event words
    equal to the history message value, `rmw` adjacency discharged on
    the reached run, owner-only forwarding, all refusals) (§4).
    Silicon provenance: Intel SDM 325462-093US Sep 2026 via the
    accepted 662 module and lane 1145 -- this lane adds no new silicon
    claim beyond reusing those rows. Aligned whole-word atomicity
    stays a selected-profile contract (`ausgerichtet8` plus the empty
    own buffer), never a hardware proof.
    NOT proved here, and not claimed:
    - No per-access target-to-W/GX simulation: the link is proved over
      the generic history shape (`Nachricht`/`Lesbar`/`Frisch` at
      `Adresse`/`Wort`), not over a concrete Gabbro program's
      carriers -- no accepted mapping from x86 addresses to Gabbro
      carriers exists yet (source/table-write consumer lanes own it).
      The `rmw` field of a full `SchrittW` is therefore shaped, not
      discharged.
    - No hardware correspondence beyond self-consistency: encodings,
      flag effects and ordering rules are the accepted 662 rows.
    - No fetched-byte dispatch on `HwMaschine`: the link takes parsed
      `LockAnweisung` events; fetch stays with 662 `lockByteschritt`.
    - Narrower widths (8/16/32-bit), other addressing modes and
      split-lock detection stay open with 662/HwLockRmw.
    - No fairness, progress, retry bound or cycle claim; no source,
      checker, contract, budget, duty or goal change: nothing here
      speaks about `Vertrag`, `Stmt`, duties or `gabbro_ziel`.
-/

#print axioms rmwLink_adapter_wf
#print axioms rmwLink_puffer_verweigert
#print axioms rmwLink_unaligned_verweigert
#print axioms rmwLink_xadd
#print axioms rmwLink_cmpxchg_erfolg
#print axioms rmwLink_cmpxchg_fehlschlag_nur_liest
#print axioms rmwLink_kette
#print axioms rmwLink_kette_ohne_puffer
#print axioms witWahl_mem
#print axioms witWahl_lesbar
#print axioms witNeu_frisch
#print axioms witWahl_wert
#print axioms witNeu_adj
#print axioms rmwLink_zeuge

end Gabbro.Grammatik.X86
