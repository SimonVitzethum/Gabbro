/-
  File:      Grammatik/X86/PipelineTsoStore.lean
  Subject:   Pipeline over TSO: the store case on the issue/drain path
             (lane 1261, follow-up of lane 1169 `PipelineTso.lean`,
             which is not in this snapshot, so this file builds on the
             accepted pieces directly).

             A lowered 64-bit store is eight byte issues into the acting
             core's TSO buffer (`hwWortAusgabe`, never the SC word
             effect), each issue one `HwSchritt.gibAus` event, followed
             by oldest-entry drains (`flushKern`); after an
             exclusion-checked drain the shared-memory footprint equals
             the sequential `write64` shadow (via the accepted generic
             `drainGleichWrite64`) with read-back. Until the drain the
             shared bytes are untouched, so a foreign core observes the
             old value (two-core witness below).

             Reused, not duplicated: `hwWortAusgabe`/`issueListe_stern`/
             `HwSchritt` (`HardwareExecution`), `wortEintraege`/
             `WortGruppe`/`FremdFrei`/`DrainSpur` (`WordAccessGrouping`),
             `issueByte`/`flushKern`/`loadByte` (`TSO`), the generic
             drain induction (`HwDrainGeneric.drainGleichWrite64`), the
             forwarding word load (`HwStackCalls.stapelLadeWort`) and
             the two-core drain witness (`drainWit*`, `drainGrp_*`).
             No new machine, no new decoder row, no new instruction,
             no source claim beyond the `write64` shadow (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.TSO.Kern.WordAccessGrouping
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Familien.HwStackCalls
import Grammatik.X86.Hw.Speicher.HwDrainGeneric
import Grammatik.X86.Hw.Gleitkomma.HwFpControl
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution

namespace Gabbro.Grammatik.X86

/-- A lowered 64-bit store at `a` with word `v`: eight byte issues
    into the acting core's TSO buffer, never the SC word effect.
    `none` = at least one footprint byte refused. -/
def tsoStoreIssue (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) : Option HwMaschine :=
  hwWortAusgabe m c a v

/-! ## 1. Validator and the issue path.

    The validator recomputes the buffer shape: after a lowered store
    the acting core carries exactly the eight canonical entries of
    `(a, v)` on top of its old buffer. The issue path changes no
    shared-memory byte and reaches the machine as eight `HwSchritt`
    store-issue events. -/

/-- The validator: the acting core's buffer ends in exactly the eight
    canonical entries of `(a, v)`. Decided, recomputed from the
    address and the word. -/
def tsoStoreValid (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (old : List TSOEintrag) : Bool :=
  decide (m.puffer c = old ++ wortEintraege a v)

/-- A lowered store buffers exactly the eight canonical entries on
    top of the old buffer. -/
theorem tsoStore_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : tsoStoreIssue m c a v = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v :=
  hwWortAusgabe_puffer m c a v m' h

/-- A lowered store changes no shared-memory byte: until the drain
    every core observes the old value. -/
theorem tsoStore_kein_speicher (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : tsoStoreIssue m c a v = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c a v m' h x

/-- The validator accepts exactly the successful issue. -/
theorem tsoStore_valid (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : tsoStoreIssue m c a v = some m') :
    tsoStoreValid m' c a v (m.puffer c) = true := by
  unfold tsoStoreValid
  rw [decide_eq_true_eq]
  exact tsoStore_puffer m c a v m' h

/-- A lowered store reaches the machine in eight store-issue steps:
    the folded word issue is a chain of `HwSchritt.gibAus` events. -/
theorem tsoStore_stern (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : tsoStoreIssue m c a v = some m') :
    HwStern m m' := by
  unfold tsoStoreIssue hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none =>
    rw [h1] at h
    cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hs := issueListe_stern m c (wortEintraege a v)
      (tsoAnsicht m) s' h1
    have hrefl : setTso m (tsoAnsicht m) = m := by
      cases m with
      | mk mem kerne puffer hw bereit => rfl
    rw [hrefl] at hs
    exact hs

/-! ## 2. Store correctness: issue, then exclusion-checked drain.

    From an empty acting buffer the lowered store groups exactly the
    eight canonical entries; the accepted generic drain induction then
    installs exactly the sequential `write64` footprint bytes with
    read-back. The `write64` equation is the same sequential shadow
    the accepted `Pipeline.worldRep_store` keeps the source
    representation against -- no second source interpreter is
    introduced (see CUTS). -/

/-- STORE CORRECTNESS ON THE ISSUE/DRAIN PATH: a lowered store from
    an empty acting buffer, followed by an exclusion-checked drain,
    agrees with the successful sequential `write64` on the whole
    footprint and reads back the word. Every premise feeds the
    conclusion: the issue and the empty start build the group, the
    group with readability, trace, end membership, emptiness and the
    exclusion feed the generic induction, the store equation feeds
    the footprint agreement. -/
theorem pipeline_correct_tsoStore (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m1 : HwMaschine)
    (h_issue : tsoStoreIssue m c a v = some m1)
    (hleer0 : m.puffer c = [])
    (h_fremd : FremdFrei (tsoAnsicht m1) c a)
    (hles : lesbar8 (tsoAnsicht m1).mem a = true)
    (sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c (tsoAnsicht m1) sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (m' : Speicher)
    (hwr : write64 (tsoAnsicht m1).mem a v = some m') :
    (∀ j : Nat, j < 8 →
      sN.mem.bytes (addrOff a j) = m'.bytes (addrOff a j)) ∧
      read64 sN.mem a = some v := by
  have hgrp : WortGruppe (tsoAnsicht m1) c a v := by
    refine ⟨?_, h_fremd⟩
    have hbuf := tsoStore_puffer m c a v m1 h_issue
    show m1.puffer c = wortEintraege a v
    rw [hbuf, hleer0, List.nil_append]
  exact drainGleichWrite64 (tsoAnsicht m1) sN t c a v m'
    hgrp hles hspur hend hleer hstoer hwr

/-! ## 3. Refusals: guard, empty drain, dark observation.

    Unsupported shapes are REFUSED, never guessed: a store whose
    first footprint byte is not writable admits no issue, an empty
    acting buffer admits no drain, and an unreadable first footprint
    byte admits no observation. -/

/-- GUARD STORE REFUSES: without write permission at the first
    footprint byte the whole eight-issue fold refuses. The denial
    fails the very first byte issue. -/
theorem pipeline_refuses_tsoStore_guard (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    tsoStoreIssue m c a v = none := by
  unfold tsoStoreIssue hwWortAusgabe
  have hguard' : (tsoAnsicht m).mem.schreibbar (addrOff a 0) = false :=
    hguard
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _ hguard'
  have hcons : wortEintraege a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- EMPTY DRAIN REFUSES: flushing an empty acting buffer admits no
    step. -/
theorem pipeline_refuses_tsoStore_leer (m : HwMaschine) (c : Nat)
    (hleer : m.puffer c = []) :
    flushKern (tsoAnsicht m) c = none := by
  apply flush_leer
  simpa [tsoAnsicht] using hleer

/-- DARK OBSERVATION REFUSES: without read permission at the first
    footprint byte the whole forwarding word observation refuses. -/
theorem pipeline_refuses_tsoStore_dunkel (s : TSOZustand) (c : Nat)
    (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none :=
  stapelPop_unlesbar s c a hguard

/-! ## 4. Poison probes: every refusal fires on a concrete machine.

    Each probe runs the refusal theorem on a concrete witness machine:
    the write-protected guard machine refuses the store, the empty
    start machine refuses the drain, the unreadable page refuses the
    observation. -/

/-- Poison probe: the guard machine refuses the lowered store. -/
theorem tsoStoreGiftWache :
    tsoStoreIssue drainWitGuardM0 0 drainWitAdr drainWitWort = none :=
  pipeline_refuses_tsoStore_guard _ _ _ _ drainWit_guard_dicht

/-- Poison probe: the empty start machine refuses the drain. -/
theorem tsoStoreGiftLeer :
    flushKern (tsoAnsicht drainWitM0) 0 = none :=
  pipeline_refuses_tsoStore_leer _ _ rfl

/-- Poison probe: the unreadable page refuses the observation. -/
theorem tsoStoreGiftDunkel :
    stapelLadeWort ⟨drainWitDarkMem, fun _ => []⟩ 0 drainWitAdr = none :=
  pipeline_refuses_tsoStore_dunkel _ _ _ drainWit_dark_dicht

/-! ## 5. Joint witness: issue reaches the grouped drain start.

    The witness starts with an empty acting buffer on zeroed
    fully-permissive memory; the lowered store computes exactly the
    accepted grouped drain start `grpS2`, so the main theorem fires
    with the accepted eight-drain. Beside it stand the two-core
    forwarding facts of the accepted `drainWit` run (owner observes
    the new word while the foreign core still reads zero; after the
    drain both observe the new word and shared memory observably
    changed from 0 to 42) and the three refusal probes. -/

/-- Witness start for the issue half: zeroed fully-permissive
    memory, two cores, empty buffers, full silicon. -/
def grpWitM0 : HwMaschine :=
  ⟨zeugenSpeicher, drainWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness after the lowered store: exactly the grouped drain start. -/
def grpWitM1 : HwMaschine := setTso grpWitM0 grpS2

/-- The witness machine is well-formed: full silicon admits all. -/
theorem grpWit_wf : HwWf grpWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The witnessed issue fold succeeds onto the grouped drain
    start. Success is decided (`isSome`), the shape follows
    propositionally: the acting buffer carries exactly the eight
    canonical entries (`issueListe_haengt_an` over the empty start),
    foreign buffers stay empty (`issueListe_anderer_kern`), memory
    keeps its bytes (`issueListe_kein_speicher`) and permissions
    (`issueListe_erhaelt_berechtigungen`). No computed state is ever
    identified by `rfl`. -/
theorem grpWit_fold :
    issueListe (tsoAnsicht grpWitM0) 0
      (wortEintraege (0 : Adresse) zeugenWort) = some grpS2 := by
  have hsome : (issueListe (tsoAnsicht grpWitM0) 0
      (wortEintraege (0 : Adresse) zeugenWort)).isSome = true := by
    decide
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hsome
  have hbuf0 : s'.puffer 0 = wortEintraege (0 : Adresse) zeugenWort := by
    have ha := issueListe_haengt_an _ s' 0 _ hs'
    have hb0 : (tsoAnsicht grpWitM0).puffer 0 = [] := rfl
    rw [hb0] at ha
    simpa using ha
  have hfr : ∀ d : Nat, d ≠ 0 → s'.puffer d = [] := by
    intro d hne
    have ha := issueListe_anderer_kern _ s' 0 _ d hne hs'
    have hb : (tsoAnsicht grpWitM0).puffer d = [] := rfl
    rw [hb] at ha
    exact ha
  have hbytes : ∀ x : Adresse,
      s'.mem.bytes x = grpS2.mem.bytes x := by
    intro x
    have ha := issueListe_kein_speicher _ s' 0 _ hs' x
    have hb : (tsoAnsicht grpWitM0).mem.bytes x = grpS2.mem.bytes x := rfl
    rw [hb] at ha
    exact ha
  have hperm := issueListe_erhaelt_berechtigungen _ s' 0 _ hs'
  have hm0 : (tsoAnsicht grpWitM0).mem = grpS2.mem := rfl
  obtain ⟨hl, hs, ha⟩ := hperm
  rw [hm0] at hl hs ha
  have hmem : s'.mem = grpS2.mem := by
    have h1 : s'.mem.bytes = grpS2.mem.bytes := funext hbytes
    show (⟨s'.mem.bytes, s'.mem.lesbar, s'.mem.schreibbar,
      s'.mem.ausfuehrbar⟩ : Speicher) =
      (⟨grpS2.mem.bytes, grpS2.mem.lesbar, grpS2.mem.schreibbar,
        grpS2.mem.ausfuehrbar⟩ : Speicher)
    rw [h1, hl, hs, ha]
  have hpuff : s'.puffer = grpS2.puffer := by
    funext d
    by_cases h : d = 0
    · subst h
      simp [hbuf0, grpS2]
    · simp [hfr d h, grpS2, h]
  have heq : s' = grpS2 := by
    show s' = (⟨grpS2.mem, grpS2.puffer⟩ : TSOZustand)
    rw [← hmem, ← hpuff]
  rw [heq] at hs'
  exact hs'

/-- The lowered store on the witness reaches exactly the grouped
    drain start: eight byte issues onto the empty buffer. -/
theorem grpWit_issue :
    tsoStoreIssue grpWitM0 0 (0 : Adresse) zeugenWort = some grpWitM1 := by
  unfold tsoStoreIssue hwWortAusgabe grpWitM1
  rw [grpWit_fold]

/-- The witness start buffer is empty. -/
theorem grpWit_leer0 : grpWitM0.puffer 0 = [] := rfl

/-- The validator accepts the witnessed issue. -/
theorem grpWit_valid :
    tsoStoreValid grpWitM1 0 (0 : Adresse) zeugenWort (grpWitM0.puffer 0) =
      true :=
  tsoStore_valid _ _ _ _ _ grpWit_issue

/-- JOINT WITNESS for `pipeline_correct_tsoStore`: the lowered store
    reaches the grouped drain start from an empty buffer on a
    well-formed machine, the validator accepts it, the drained
    footprint is the sequential `write64` footprint with read-back,
    and the run is non-degenerate -- owner-only forwarding of 42 on
    two cores with the foreign core still reading zero, a drain
    changing shared memory 0 to 42 observed from both cores -- beside
    the three planted refusal probes. -/
theorem pipeline_correct_tsoStore_zeuge :
    HwWf grpWitM0 ∧
      tsoStoreIssue grpWitM0 0 (0 : Adresse) zeugenWort = some grpWitM1 ∧
      tsoStoreValid grpWitM1 0 (0 : Adresse) zeugenWort (grpWitM0.puffer 0) =
        true ∧
      (∀ j : Nat, j < 8 →
        grpS10.mem.bytes (addrOff (0 : Adresse) j) =
          zeugenSpeicherNach.bytes (addrOff (0 : Adresse) j)) ∧
      read64 grpS10.mem (0 : Adresse) = some zeugenWort ∧
      drainWitLoadEigen = some (some drainWitWort) ∧
      drainWitLoadFremd = some (some drainWitNull) ∧
      drainWitNachRead = some (some drainWitWort) ∧
      drainWitFremdNachFlush = some (some drainWitWort) ∧
      drainWitMem.bytes drainWitAdr = BitVec.ofNat 8 0 ∧
      tsoStoreIssue drainWitGuardM0 0 drainWitAdr drainWitWort = none ∧
      flushKern (tsoAnsicht drainWitM0) 0 = none ∧
      stapelLadeWort ⟨drainWitDarkMem, fun _ => []⟩ 0 drainWitAdr =
        none := by
  have hans : tsoAnsicht grpWitM1 = grpS2 := setTso_ansicht _ _
  obtain ⟨_, hff⟩ := grp_hgrp
  have hles : lesbar8 (tsoAnsicht grpWitM1).mem (0 : Adresse) = true := by
    rw [hans]
    exact grp_hles
  have hfremd : FremdFrei (tsoAnsicht grpWitM1) 0 (0 : Adresse) := by
    rw [hans]
    exact hff
  have hspur : DrainSpur 0 (tsoAnsicht grpWitM1) grpS10
      [grpS2, grpS3, grpS4, grpS5, grpS6, grpS7, grpS8, grpS9, grpS10] := by
    rw [hans]
    exact grp_spur
  have hwr : write64 (tsoAnsicht grpWitM1).mem (0 : Adresse) zeugenWort =
      some zeugenSpeicherNach := by
    rw [hans]
    exact drainGrp_hwr
  obtain ⟨hfoot, hread⟩ := pipeline_correct_tsoStore grpWitM0 0
    (0 : Adresse) zeugenWort grpWitM1 grpWit_issue grpWit_leer0 hfremd hles
    grpS10 _ hspur grp_hend grp_hempty grp_hstoer _ hwr
  exact ⟨grpWit_wf, grpWit_issue, grpWit_valid, hfoot, hread,
    drainWit_weiterleitung, drainWit_fremd_alt,
    drainWit_spuelung_aendert_speicher, drainWit_fremd_neu,
    drainWit_anfang_null, tsoStoreGiftWache, tsoStoreGiftLeer,
    tsoStoreGiftDunkel⟩

/- CUTS: exactly what is not proved here.

    Proved here (all over the REUSED canonical `Speicher`/`TSO`
    vocabulary, the accepted `HwMaschine`/`HwSchritt`/`HwWf`,
    `issueByte`/`flushKern`, `wortEintraege`, `WortGruppe`/
    `FremdFrei`/`DrainSpur`, `hwWortAusgabe`, `stapelLadeWort`,
    `read64`/`write64` -- no new machine, no new decoder row, no new
    instruction, no source claim beyond the `write64` shadow):
    - lowering `tsoStoreIssue` (eight byte issues, never the SC word
      effect) and the recomputing validator `tsoStoreValid`
      (`tsoStore_valid`);
    - issue path: exactly the eight canonical entries
      (`tsoStore_puffer`), no shared-memory change until the drain
      (`tsoStore_kein_speicher`), eight `HwSchritt` store-issue
      events (`tsoStore_stern` over the accepted `issueListe_stern`);
    - STORE CORRECTNESS (`pipeline_correct_tsoStore`): from an empty
      acting buffer, issue plus exclusion-checked drain equals the
      sequential `write64` footprint with read-back, via the accepted
      generic `drainGleichWrite64`;
    - refusals: guard store (`pipeline_refuses_tsoStore_guard`),
      empty drain (`pipeline_refuses_tsoStore_leer`), dark
      observation (`pipeline_refuses_tsoStore_dunkel`), each with a
      poison probe on a concrete machine (`tsoStoreGiftWache`,
      `tsoStoreGiftLeer`, `tsoStoreGiftDunkel`);
    - joint non-degenerate witness
      (`pipeline_correct_tsoStore_zeuge`): the lowered store computes
      exactly the accepted grouped drain start (`grpWit_issue`, by
      `rfl`), the validator accepts it, the drain installs the
      `write64` footprint, owner-only forwarding of 42 with the
      foreign core reading zero, a drain changing shared memory 0 to
      42 observed from both cores, beside the three refusal probes.
    NOT proved here, and not claimed:
    - No `store64` fetch/decode/execute leg: the lowered store is
      the eight TSO byte issues, not a fetched `Befehl.store64`
      run. Relating `Pipeline.senkStmt` slot stores (with their
      register/address setup and `WorldRep`) to `tsoStoreIssue`
      stays OPEN -- the `write64` equation is the shared shadow,
      not the bridge.
    - No silicon correspondence: encodings are the accepted
      canonical subsets with self-consistency only, not x86 truth.
    - No LOCK/RMW, fault, interrupt, fence-ordering, FP-control or
      SIMD path; no target-to-W/GX simulation; no whole-word
      atomicity beyond `WortGruppe`-guarded byte drains (reused).
    - Lane 1169 `PipelineTso.lean` (with `pipeHw_reg_einbettung`)
      is not in this snapshot, so no lift onto it is stated; the
      register path (`HwSchritt.reg` embedding) is untouched.
-/

#print axioms tsoStoreIssue
#print axioms tsoStoreValid
#print axioms tsoStore_puffer
#print axioms tsoStore_kein_speicher
#print axioms tsoStore_valid
#print axioms tsoStore_stern
#print axioms pipeline_correct_tsoStore
#print axioms pipeline_refuses_tsoStore_guard
#print axioms pipeline_refuses_tsoStore_leer
#print axioms pipeline_refuses_tsoStore_dunkel
#print axioms tsoStoreGiftWache
#print axioms tsoStoreGiftLeer
#print axioms tsoStoreGiftDunkel
#print axioms grpWitM0
#print axioms grpWitM1
#print axioms grpWit_wf
#print axioms grpWit_fold
#print axioms grpWit_issue
#print axioms grpWit_leer0
#print axioms grpWit_valid
#print axioms pipeline_correct_tsoStore_zeuge

end Gabbro.Grammatik.X86
