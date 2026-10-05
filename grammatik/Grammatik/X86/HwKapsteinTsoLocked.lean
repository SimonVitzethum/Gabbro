/-
  File:      Grammatik/X86/HwKapsteinTsoLocked.lean
  Subject:   Capstone: TSO projection of the locked and direct-memory tags.

  Lane 1325: follow-up of lane 1295 (`HwKapsteinTso.lean`). Classifies the
  union tags 1295 left open where this lane owns them (lockRmw, lockFetch,
  system): locked XADD steps equal the accepted TSO locked event
  (`lockSchritt` over `LockedOps`, footprint `Fuss` named, own buffer
  drained first, foreign buffers untouched); MFENCE and the nine
  memory-unchanged system legs are silent on the projection; INT n
  delivery installs memory directly (FINDING, no single TSO event).
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.HwKapsteinTso
import Grammatik.X86.HwKapsteinSteps

namespace Gabbro.Grammatik.X86

/-- A memory-unchanged snapshot leg is silent on the TSO projection:
    the plug installs core data and the same memory while every buffer
    is kept by construction. -/
theorem kap_system_still_of_mem (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis) (k' : HwKern)
    (st' : SysSteuer)
    (h : sysSnapSchritt m c st ev = .ok k' st' m.mem)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  have hplug := adapterSystem_ok m c (st, ev) k' st' m.mem h
  rw [hplug] at had
  cases had
  rfl

/-! ## 1. LOCK XADD: the admitted plug step is the accepted TSO locked
    event.

    `lockSchritt` (`LockedOps`, over `TSOZustand`) is the accepted
    TSO-level locked event. The coherent plug (`hwLockSchritt`, via
    `lockSchrittVoll`) fires it on the projection: the own buffer is
    drained first (the empty-own-buffer guard, extracted as a separate
    leg below), one atomic read-modify-write installs on canonical
    memory with the word footprint `Fuss tgt` named, and foreign
    buffers are untouched (the re-embedding keeps every buffer). -/

/-- An admitted LOCK XADD plug step IS the accepted TSO locked event
    on the projection, with the footprint named and foreign buffers
    untouched. Every premise of the accepted equations is extracted
    from the admitted step; nothing is assumed. -/
theorem kapLockTso_xadd_geerbt (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (m' : HwMaschine)
    (h : hwLockSchritt m c (.ok (.xadd64 src base d) len) =
      some m') :
    ∃ tgt : Adresse, ∃ delta : Wort, ∃ ev : LockEreignis,
      tgt = effAddr (projZustand m c) base d ∧
      delta = (m.kerne c).register src ∧
      m.puffer c = [] ∧
      lockSchritt (.xadd64 tgt delta) c (kapTso m) =
        some (kapTso m', ev) ∧
      ev.lesen = Fuss tgt ∧ ev.schreiben = Fuss tgt ∧
      ev.istRmw = true ∧
      (∀ dd, dd ≠ c → (kapTso m').puffer dd = (kapTso m).puffer dd) ∧
      (kapTso m').puffer c = [] := by
  unfold hwLockSchritt at h
  cases hvoll : lockSchrittVoll (.ok (.xadd64 src base d) len) c
      (lockMaschineVonHw m c) m.hw (m.bereit c) with
  | ok lm' evL =>
    rw [hvoll] at h
    cases h
    unfold lockSchrittVoll at hvoll
    cases hlen : laengeOk len with
    | false =>
      simp [hlen] at hvoll
    | true =>
      simp [hlen] at hvoll
      cases hbuf : (lockMaschineVonHw m c).puffer c with
      | cons e rest =>
        simp [hbuf] at hvoll
      | nil =>
        simp [hbuf] at hvoll
        cases hali : ausgerichtet8
            (effAddr (lockMaschineVonHw m c).zu base d) with
        | false =>
          simp [hali] at hvoll
        | true =>
          simp [hali] at hvoll
          cases hrd : read64 (lockMaschineVonHw m c).zu.speicher
              (effAddr (lockMaschineVonHw m c).zu base d) with
          | none =>
            simp [hrd] at hvoll
          | some alt =>
            simp [hrd] at hvoll
            cases hwr : write64 (lockMaschineVonHw m c).zu.speicher
                (effAddr (lockMaschineVonHw m c).zu base d)
                (alt + (lockMaschineVonHw m c).zu.register src) with
            | none =>
              simp [hwr] at hvoll
            | some mem'0 =>
              simp [hwr] at hvoll
              have hLM := hvoll.1
              subst hLM
              refine ⟨effAddr (projZustand m c) base d,
                (m.kerne c).register src,
                ⟨c, Fuss (effAddr (projZustand m c) base d),
                  Fuss (effAddr (projZustand m c) base d),
                  some alt,
                  some (alt + (m.kerne c).register src),
                  true, false⟩,
                rfl, rfl, hbuf, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · have hbufT : (kapTso m).puffer c = [] := hbuf
                have hrdT : read64 (kapTso m).mem
                    (effAddr (projZustand m c) base d) = some alt := hrd
                have haliT : ausgerichtet8
                    (effAddr (projZustand m c) base d) = true := hali
                have hwrT : write64 (kapTso m).mem
                    (effAddr (projZustand m c) base d)
                    (alt + (m.kerne c).register src) = some mem'0 := hwr
                have hlock := lockSchritt_xadd_erfolg (kapTso m) c
                  (effAddr (projZustand m c) base d)
                  ((m.kerne c).register src) alt mem'0
                  hbufT hrdT haliT hwrT
                exact hlock
              · intro dd _
                rfl
              · exact hbuf
  | speicherFehler =>
    simp [hvoll] at h
  | udFehler g =>
    simp [hvoll] at h
  | verweigert =>
    simp [hvoll] at h

/-- An admitted MFENCE plug step is silent on the TSO projection:
    only RIP advances; canonical memory and every buffer are kept,
    exactly as the accepted fence equation states. Category (a). -/
theorem kapLockTso_mfence_still (m : HwMaschine) (c : Nat)
    (len : Nat) (m' : HwMaschine)
    (h : hwLockSchritt m c (.ok .mfence len) = some m') :
    kapTso m' = kapTso m := by
  unfold hwLockSchritt at h
  cases hvoll : lockSchrittVoll (.ok .mfence len) c
      (lockMaschineVonHw m c) m.hw (m.bereit c) with
  | ok lm' evL =>
    rw [hvoll] at h
    cases h
    unfold lockSchrittVoll at hvoll
    cases hlen : laengeOk len with
    | false =>
      simp [hlen] at hvoll
    | true =>
      simp [hlen] at hvoll
      cases hss : merkmalZugelassen m.hw (m.bereit c) .sseDoppel with
      | false =>
        simp [hss] at hvoll
      | true =>
        simp [hss] at hvoll
        cases hbuf : (lockMaschineVonHw m c).puffer c with
        | cons e rest =>
          simp [hbuf] at hvoll
        | nil =>
          simp [hbuf] at hvoll
          have hLM := hvoll.1
          subst hLM
          rfl
  | speicherFehler =>
    simp [hvoll] at h
  | udFehler g =>
    simp [hvoll] at h
  | verweigert =>
    simp [hvoll] at h

/-- CMPXCHG FINDING (category (c)): no single accepted TSO locked
    event matches the coherent compare-exchange step. On a failing
    comparison the coherent step still performs the manual's write
    cycle (the write-back needs full write permission,
    `lockSchrittVoll_cmpxchg_fehlschlag`), while the accepted TSO CAS
    (`casSchritt_fehlschlag`) stutters with the projection unchanged
    and needs no write at all: the successors already disagree, so
    neither `lockSchritt` (which has no cmpxchg arm) nor `casSchritt`
    is the step's projection. -/
theorem kapLockTso_cmpxchg_befund (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (dest : Wort) (mem' : Speicher)
    (hbuf : (lockMaschineVonHw m c).puffer c = [])
    (hali : ausgerichtet8 (effAddr (lockMaschineVonHw m c).zu base d) =
      true)
    (hrd : read64 (lockMaschineVonHw m c).zu.speicher
      (effAddr (lockMaschineVonHw m c).zu base d) = some dest)
    (hfehl : (dest == (lockMaschineVonHw m c).zu.register .rax) =
      false)
    (hok : laengeOk len = true)
    (hwr : write64 (lockMaschineVonHw m c).zu.speicher
      (effAddr (lockMaschineVonHw m c).zu base d) dest = some mem') :
    (∃ lm' : LockMaschine, ∃ ev : LockEreignis,
      lockSchrittVoll (.ok (.cmpxchg64 src base d) len) c
        (lockMaschineVonHw m c) m.hw (m.bereit c) = .ok lm' ev ∧
      lm'.zu.speicher = mem') ∧
    casSchritt (effAddr (projZustand m c) base d)
      ((m.kerne c).register .rax) ((m.kerne c).register src) c
      (kapTso m) =
      some (kapTso m, false) := by
  have hokStep := lockSchrittVoll_cmpxchg_fehlschlag
    (lockMaschineVonHw m c) c src base d len m.hw (m.bereit c) dest
    mem' hbuf hali hrd hfehl hok hwr
  have hbufT : (kapTso m).puffer c = [] := hbuf
  have haliT : ausgerichtet8 (effAddr (projZustand m c) base d) =
      true := hali
  have hrdT : read64 (kapTso m).mem
      (effAddr (projZustand m c) base d) = some dest := hrd
  have hcas := casSchritt_fehlschlag (kapTso m) c
    (effAddr (projZustand m c) base d)
    ((m.kerne c).register .rax) ((m.kerne c).register src) dest
    hbufT hrdT haliT hfehl
  refine ⟨⟨_, _, hokStep, rfl⟩, hcas⟩

/-! ## 2. Fetched LOCK: off-split, the fetch inherits the plug.

    `hwLockFetchSchritt_ohne_split` (accepted) identifies the fetched
    step with the parsed plug step on the fetched instruction. The TSO
    classification is therefore inherited: fetched XADD is the
    accepted TSO locked event, fetched MFENCE is silent. Split words,
    parsed #UD and absent fetches refuse (accepted refusal pins,
    joined in the witness). -/

/-- A fetched, non-split LOCK XADD step IS the accepted TSO locked
    event on the projection: the fetch decides, the parsed plug runs,
    the footprint is named and foreign buffers are untouched. -/
theorem kap_lockFetch_xadd_geerbt (m : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (rest : List Byte) (m' : HwMaschine)
    (hfetch : hwLockFetch m c =
      some (.ok (.xadd64 src base d) len, rest))
    (hs : match lockFuss m c (.xadd64 src base d) with
      | some tgt => splitSperre tgt = false
      | none => True)
    (h : hwLockFetchSchritt m c = some m') :
    ∃ tgt : Adresse, ∃ delta : Wort, ∃ ev : LockEreignis,
      tgt = effAddr (projZustand m c) base d ∧
      delta = (m.kerne c).register src ∧
      m.puffer c = [] ∧
      lockSchritt (.xadd64 tgt delta) c (kapTso m) =
        some (kapTso m', ev) ∧
      ev.lesen = Fuss tgt ∧ ev.schreiben = Fuss tgt ∧
      ev.istRmw = true ∧
      (∀ dd, dd ≠ c → (kapTso m').puffer dd = (kapTso m).puffer dd) ∧
      (kapTso m').puffer c = [] := by
  have hpar := hwLockFetchSchritt_ohne_split m c
    (.xadd64 src base d) len rest hfetch hs
  rw [hpar] at h
  exact kapLockTso_xadd_geerbt m c src base d len m' h

/-- A fetched, non-split MFENCE step is silent on the TSO
    projection. -/
theorem kap_lockFetch_mfence_still (m : HwMaschine) (c : Nat)
    (len : Nat) (rest : List Byte) (m' : HwMaschine)
    (hfetch : hwLockFetch m c = some (.ok .mfence len, rest))
    (h : hwLockFetchSchritt m c = some m') :
    kapTso m' = kapTso m := by
  have hpar := hwLockFetchSchritt_ohne_split m c .mfence len rest
    hfetch (by simp only [lockFuss])
  rw [hpar] at h
  exact kapLockTso_mfence_still m c len m' h

/-! ## 3. System forms: nine legs are silent, INT n writes directly.

    Accepted leg equations (`HwSystemForms`): HLT, CLI/STI, PAUSE,
    CPUID, RDTSC, SYSCALL, SYSRET and IRET all return `m.mem` on
    success -- core data and control move, canonical memory does not,
    and the plug keeps every buffer by construction. Each is category
    (a) on the projection. SYSCALL/SYSRET in particular perform no
    drain: the buffers-kept equation is proved generally below
    (`kap_system_puffer_bleibt`) and holds for every admitted plug
    step, named assumption S-SYSCALL-KEIN-DRAIN/S-INT-KEIN-DRAIN of the
    family file. INT n pushes its delivery frame through
    `schiebeRahmen` -- a direct multi-byte memory install, category
    (c), high priority. -/

/-- HLT at CPL 0 is silent on the TSO projection. -/
theorem kap_system_hlt_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .hlt) (h0 : st.steuer.cpl = 0)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ := schrittHlt_ok m c st h0
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- CLI where admitted is silent on the TSO projection. -/
theorem kap_system_cli_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .cli)
    (hpriv : st.steuer.cpl ≤ st.steuer.iopl)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ := schrittIf_cli_ok m c st hpriv
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- STI where admitted is silent on the TSO projection. -/
theorem kap_system_sti_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .sti)
    (hpriv : st.steuer.cpl ≤ st.steuer.iopl)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ := schrittIf_sti_ok m c st hpriv
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- PAUSE is silent on the TSO projection. -/
theorem kap_system_pause_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .pause)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', mem0, hrest⟩ := schrittPause_still m c st
  have hleg := hrest.1
  have hmem := hrest.2.2.2.1
  subst hmem
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- CPUID is silent on the TSO projection. -/
theorem kap_system_cpuid_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .cpuid)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ :=
    schrittCpuid_rax m c st ev.eingaben.cpuidOut
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- RDTSC without TSD is silent on the TSO projection. -/
theorem kap_system_rdtsc_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .rdtsc)
    (htsd : ev.eingaben.tsd = false)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ :=
    schrittRdtsc_ok m c st ev.eingaben.tsc
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, htsd, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- SYSCALL where enabled is silent on the TSO projection: in
    particular it performs no drain (S-SYSCALL-KEIN-DRAIN, via
    `kap_system_puffer_bleibt` below). -/
theorem kap_system_syscall_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .syscall)
    (hsce : ev.eingaben.sceLang = true)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ :=
    schrittSyscall_ok m c st ev.eingaben hsce
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- SYSRET where enabled is silent on the TSO projection: in
    particular it performs no drain. -/
theorem kap_system_sysret_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .sysret)
    (hsce : ev.eingaben.sceLang = true)
    (h0 : st.steuer.cpl = 0)
    (hk : ev.eingaben.op64 = true →
      istKanonisch ((m.kerne c).register .rcx) = true)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ :=
    schrittSysret_ok m c st ev.eingaben hsce h0 hk
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- IRET over a readable frame with a canonical target RIP is silent
    on the TSO projection: the frame is only read back, never
    written. -/
theorem kap_system_iret_still (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis)
    (hform : ev.form = .iret)
    (ss rspNeu rflagsGesp cs ripNeu : Wort)
    (h0 : read64 m.mem ((m.kerne c).register .rsp) = some ss)
    (h1 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 8) = some rspNeu)
    (h2 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 16) = some rflagsGesp)
    (h3 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 24) = some cs)
    (h4 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 32) = some ripNeu)
    (hk : istKanonisch ripNeu = true)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  obtain ⟨k', st', hrest⟩ :=
    schrittIret_ok m c st ss rspNeu rflagsGesp cs ripNeu
      h0 h1 h2 h3 h4 hk
  have hleg := hrest.1
  have h : sysSnapSchritt m c st ev = .ok k' st' m.mem := by
    simp [sysSnapSchritt, hform, hleg]
  exact kap_system_still_of_mem m c st ev k' st' h m' had

/-- Every admitted system plug step keeps every buffer: no system leg
    drains the TSO store buffer. This is the plug-level form of the
    named assumptions S-SYSCALL-KEIN-DRAIN and S-INT-KEIN-DRAIN of the
    family file: SYSCALL, SYSRET and INT delivery change no buffer. -/
theorem kap_system_puffer_bleibt (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysEreignis) (m' : HwMaschine) (d : Nat)
    (had : adapterSystem.schritt m c p = some m') :
    m'.puffer d = m.puffer d := by
  cases hs : sysSnapSchritt m c p.1 p.2 with
  | ok k' st' mem' =>
    have hplug := adapterSystem_ok m c p k' st' mem' hs
    rw [hplug] at had
    cases had
    rfl
  | fehler f =>
    have hnone := adapterSystem_fehler m c p f hs
    rw [hnone] at had
    cases had
  | verweigert =>
    have hnone : adapterSystem.schritt m c p = none := by
      simp [adapterSystem, hs]
    rw [hnone] at had
    cases had

/-- INT n FINDING, structural half (category (c)): an admitted INT
    delivery installs its pushed-frame memory directly while every
    buffer is kept. Memory moves by the accepted frame push
    (`schiebeRahmen` through `schrittInt_liefert`), never through a
    TSO issue or flush. -/
theorem kap_system_intN_schreibt_direkt (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis) (k' : HwKern)
    (st' : SysSteuer) (mem' : Speicher)
    (hform : ev.form = .intN)
    (hleg : schrittInt m c st ev.eingaben = .ok k' st' mem')
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    m'.mem = mem' ∧ ∀ d, m'.puffer d = m.puffer d := by
  have h : sysSnapSchritt m c st ev = .ok k' st' mem' := by
    simp [sysSnapSchritt, hform, hleg]
  have hplug := adapterSystem_ok m c (st, ev) k' st' mem' h
  rw [hplug] at had
  cases had
  exact ⟨rfl, fun d => rfl⟩

/-- INT n FINDING, event half (category (c), high priority): a
    delivery that changes two distinct canonical bytes is no single
    accepted TSO event. An issue keeps canonical memory
    (`issue_kein_speicher`); a flush changes exactly its head address
    (`flush_rahmen`) -- one of the two changed bytes differs from it.
    The delivery frame is five words, so every real delivery meets
    the two-byte premise; the byte pair is taken as premise here so
    the obstruction, not a witness shape, is what this leg states. -/
theorem kap_system_intN_kein_tso_ereignis (m m' : HwMaschine)
    (c : Nat) (st : SysSteuer) (ev : SysEreignis)
    (k' : HwKern) (st' : SysSteuer) (mem' : Speicher)
    (hform : ev.form = .intN)
    (hleg : schrittInt m c st ev.eingaben = .ok k' st' mem')
    (had : adapterSystem.schritt m c (st, ev) = some m')
    (x y : Adresse)
    (hx : mem'.bytes x ≠ m.mem.bytes x)
    (hy : mem'.bytes y ≠ m.mem.bytes y)
    (hxy : x ≠ y) :
    ¬ TSOSchritt (kapTso m) (kapTso m') := by
  have hdir := kap_system_intN_schreibt_direkt m c st ev k' st'
    mem' hform hleg m' had
  have hmem : m'.mem = mem' := hdir.1
  have e1x : (kapTso m').mem.bytes x = mem'.bytes x :=
    congrArg (fun mm => mm.bytes x) hmem
  have e1y : (kapTso m').mem.bytes y = mem'.bytes y :=
    congrArg (fun mm => mm.bytes y) hmem
  have e0x : (kapTso m).mem.bytes x = m.mem.bytes x := rfl
  have e0y : (kapTso m).mem.bytes y = m.mem.bytes y := rfl
  intro hstep
  cases hstep with
  | issue cc a v hi =>
    have hkeep := issue_kein_speicher (kapTso m) (kapTso m') cc a v hi x
    rw [e1x, e0x] at hkeep
    exact hx hkeep
  | flush cc hf =>
    cases hpb : (kapTso m).puffer cc with
    | nil =>
      have hleer := flush_leer (kapTso m) cc hpb
      rw [hleer] at hf
      cases hf
    | cons e rest =>
      by_cases he : x = e.addr
      · have hne : y ≠ e.addr := by
          intro hye
          exact hxy (he.trans hye.symm)
        have hfr := flush_rahmen (kapTso m) (kapTso m') cc hf e rest hpb y hne
        rw [e1y, e0y] at hfr
        exact hy hfr
      · have hfr := flush_rahmen (kapTso m) (kapTso m') cc hf e rest hpb x he
        rw [e1x, e0x] at hfr
        exact hx hfr

/- CUTS:
    Skeleton only: the generic silent-leg transport
    `kap_system_still_of_mem`. Per-form legs, the locked-RMW event,
    lockFetch inheritance, the INT n FINDING, union lifts and the
    joint witness follow.
-/

#print axioms kap_system_still_of_mem

end Gabbro.Grammatik.X86
