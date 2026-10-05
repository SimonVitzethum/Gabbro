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

/-! ## 4. Union lifts: the classified tags reach the TSO level.

    Each lift inverts its union constructor (the 1295 pattern) and
    applies the plug-level classification. LOCK XADD reaches the
    accepted TSO locked event; MFENCE and the memory-unchanged system
    legs are silent; fetched XADD inherits the locked event
    off-split. -/

/-- A classified LOCK XADD union step is the accepted TSO locked
    event on the projection. -/
theorem kap_union_lockRmw_xadd_tso (m m' : HwMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (h : HwVollSchritt m m'
      (KapEreignis.lockRmw c (.ok (.xadd64 src base d) len))) :
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
  cases h with
  | lockRmw _ _ heq =>
    have h2 : hwLockSchritt m c (.ok (.xadd64 src base d) len) =
        some m' := heq
    exact kapLockTso_xadd_geerbt m c src base d len m' h2

/-- A classified LOCK MFENCE union step is silent on the
    projection. -/
theorem kap_union_lockRmw_mfence_still (m m' : HwMaschine) (c : Nat)
    (len : Nat)
    (h : HwVollSchritt m m'
      (KapEreignis.lockRmw c (.ok .mfence len))) :
    kapTso m' = kapTso m := by
  cases h with
  | lockRmw _ _ heq =>
    have h2 : hwLockSchritt m c (.ok .mfence len) = some m' := heq
    exact kapLockTso_mfence_still m c len m' h2

/-- A classified fetched LOCK XADD union step is the accepted TSO
    locked event on the projection. -/
theorem kap_union_lockFetch_xadd_tso (m m' : HwMaschine) (c : Nat)
    (u : Unit) (src base : Register) (d : BitVec 32) (len : Nat)
    (rest : List Byte)
    (hfetch : hwLockFetch m c =
      some (.ok (.xadd64 src base d) len, rest))
    (hs : match lockFuss m c (.xadd64 src base d) with
      | some tgt => splitSperre tgt = false
      | none => True)
    (h : HwVollSchritt m m' (KapEreignis.lockFetch c u)) :
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
  cases h with
  | lockFetch _ _ heq =>
    have h2 : hwLockFetchSchritt m c = some m' := heq
    exact kap_lockFetch_xadd_geerbt m c src base d len rest m'
      hfetch hs h2

/-- A classified system union step over a memory-unchanged leg is
    silent on the projection. -/
theorem kap_union_system_still (m m' : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis) (k' : HwKern)
    (st' : SysSteuer)
    (hsnap : sysSnapSchritt m c st ev = .ok k' st' m.mem)
    (h : HwVollSchritt m m' (KapEreignis.system c st ev)) :
    kapTso m' = kapTso m := by
  cases h with
  | system _ _ _ heq =>
    exact kap_system_still_of_mem m c st ev k' st' hsnap m' heq

/-! ## 5. IRET witness machine and the joint silent-system witness.

    `sysWitStart` parks RSP at 20480, where `witMem` is unreadable,
    so no admitted IRET leg exists on it. The variant below parks
    core 0 RSP at 16336 -- five readable zero words inside the
    accepted stack window -- and is otherwise the witness start. -/

/-- IRET witness registers: RSP parked at 16336, rest as the system
    witness. -/
def kapIretReg : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 16336 else sysWitReg q

/-- IRET witness machine: the witness memory, parked RSP on core 0,
    empty buffers, full silicon. -/
def kapIretHw : HwMaschine :=
  ⟨witMem, fun _ => ⟨kapIretReg, zeugeFlags,
    BitVec.ofNat 64 0x1000, fun _ => BitVec.ofNat 128 0,
    kontextReset⟩,
    fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The parked RSP reads back. -/
theorem kapIret_rsp :
    (kapIretHw.kerne 0).register .rsp =
      BitVec.ofNat 64 16336 := by
  decide

/-- The parked machine carries the witness memory. -/
theorem kapIret_mem : kapIretHw.mem = witMem := rfl

/-- The five frame words read back as zero. -/
theorem kapIret_liest0 :
    read64 witMem (BitVec.ofNat 64 16336) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- The five frame words read back as zero. -/
theorem kapIret_liest1 :
    read64 witMem (BitVec.ofNat 64 16344) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- The five frame words read back as zero. -/
theorem kapIret_liest2 :
    read64 witMem (BitVec.ofNat 64 16352) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- The five frame words read back as zero. -/
theorem kapIret_liest3 :
    read64 witMem (BitVec.ofNat 64 16360) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- The five frame words read back as zero. -/
theorem kapIret_liest4 :
    read64 witMem (BitVec.ofNat 64 16368) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- The popped zero RIP is canonical. -/
theorem kapIret_kanonisch :
    istKanonisch (BitVec.ofNat 64 0) = true := by
  decide

/-- The IRET witness machine is well-formed. -/
theorem kapIretHw_wf : HwWf kapIretHw := by
  apply hwWf_aus_zugelassen
  intro c f
  cases f with
  | skalar64 => rfl
  | skalar32 => rfl
  | sseDoppel =>
    show merkmalZugelassen basisHw basisBereit .sseDoppel = true
    decide
  | paketInt128 => rfl

/-- Joint silent-system witness: all nine memory-unchanged legs as
    reached union steps silent on the projection. Eight run on the
    witness start machine, IRET on the parked-RSP variant; the CLI
    leg additionally keeps every buffer. -/
theorem kapLocked_sys_alle_still :
    (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw ∧
      ∀ d, m1.puffer d = sysWitStart.hw.puffer d)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.hlt, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.sti, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.pause, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.cpuid, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.rdtsc, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer
          ⟨.syscall, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer
          ⟨.sysret, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt kapIretHw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.iret, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso kapIretHw) := by
  have hpriv : sysWitSteuer.steuer.cpl ≤ sysWitSteuer.steuer.iopl := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨mCli, hplugCli⟩ := kapPlug_system
    exact ⟨mCli, (kap_system_embedded _ _ _ _ _).mp hplugCli,
      kap_system_cli_still _ _ _ _ rfl hpriv _ hplugCli,
      fun d => kap_system_puffer_bleibt _ _ _ _ d hplugCli⟩
  · obtain ⟨kH, stH, hrestH⟩ :=
      schrittHlt_ok sysWitStart.hw 0 sysWitSteuer rfl
    have hsnapH : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.hlt, sysWitEingaben⟩ = .ok kH stH sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestH.1]
    have hplugH := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.hlt, sysWitEingaben⟩) kH stH _ hsnapH
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugH,
      kap_system_hlt_still _ _ _ _ rfl rfl _ hplugH⟩
  · obtain ⟨kS, stS, hrestS⟩ :=
      schrittIf_sti_ok sysWitStart.hw 0 sysWitSteuer hpriv
    have hsnapS : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.sti, sysWitEingaben⟩ = .ok kS stS sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestS.1]
    have hplugS := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.sti, sysWitEingaben⟩) kS stS _ hsnapS
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugS,
      kap_system_sti_still _ _ _ _ rfl hpriv _ hplugS⟩
  · obtain ⟨kP, stP, memP, hrestP⟩ :=
      schrittPause_still sysWitStart.hw 0 sysWitSteuer
    have hmemP := hrestP.2.2.2.1
    subst hmemP
    have hsnapP : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.pause, sysWitEingaben⟩ = .ok kP stP sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestP.1]
    have hplugP := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.pause, sysWitEingaben⟩) kP stP _ hsnapP
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugP,
      kap_system_pause_still _ _ _ _ rfl _ hplugP⟩
  · obtain ⟨kC, stC, hrestC⟩ := schrittCpuid_rax sysWitStart.hw 0
      sysWitSteuer sysWitEingaben.cpuidOut
    have hsnapC : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.cpuid, sysWitEingaben⟩ = .ok kC stC sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestC.1]
    have hplugC := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.cpuid, sysWitEingaben⟩) kC stC _ hsnapC
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugC,
      kap_system_cpuid_still _ _ _ _ rfl _ hplugC⟩
  · obtain ⟨kR, stR, hrestR⟩ := schrittRdtsc_ok sysWitStart.hw 0
      sysWitSteuer sysWitEingaben.tsc
    have htsd : sysWitEingaben.tsd = false := rfl
    have hsnapR : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.rdtsc, sysWitEingaben⟩ = .ok kR stR sysWitStart.hw.mem := by
      simp [sysSnapSchritt, htsd, hrestR.1]
    have hplugR := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.rdtsc, sysWitEingaben⟩) kR stR _ hsnapR
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugR,
      kap_system_rdtsc_still _ _ _ _ rfl htsd _ hplugR⟩
  · obtain ⟨kY, stY, hrestY⟩ := schrittSyscall_ok sysWitStart.hw 0
      sysWitSteuer sysWitEingaben rfl
    have hsnapY : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.syscall, sysWitEingaben⟩ =
        .ok kY stY sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestY.1]
    have hplugY := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.syscall, sysWitEingaben⟩) kY stY _ hsnapY
    have hsce : sysWitEingaben.sceLang = true := rfl
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugY,
      kap_system_syscall_still _ _ _ _ rfl hsce _ hplugY⟩
  · have hcanon : istKanonisch
        ((sysWitStart.hw.kerne 0).register .rcx) = true := by
      decide
    have hk (h64 : sysWitEingaben.op64 = true) :
        istKanonisch ((sysWitStart.hw.kerne 0).register .rcx) =
          true := hcanon
    obtain ⟨kT, stT, hrestT⟩ := schrittSysret_ok sysWitStart.hw 0
      sysWitSteuer sysWitEingaben rfl rfl hk
    have hsnapT : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.sysret, sysWitEingaben⟩ =
        .ok kT stT sysWitStart.hw.mem := by
      simp [sysSnapSchritt, hrestT.1]
    have hplugT := adapterSystem_ok sysWitStart.hw 0
      (sysWitSteuer, ⟨.sysret, sysWitEingaben⟩) kT stT _ hsnapT
    have hsce : sysWitEingaben.sceLang = true := rfl
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugT,
      kap_system_sysret_still _ _ _ _ rfl hsce rfl hk _ hplugT⟩
  · have h0 : read64 kapIretHw.mem
        ((kapIretHw.kerne 0).register .rsp) =
        some (BitVec.ofNat 64 0) := by
      rw [kapIret_mem, kapIret_rsp]
      exact kapIret_liest0
    have h1 : read64 kapIretHw.mem
        (addrOff ((kapIretHw.kerne 0).register .rsp) 8) =
        some (BitVec.ofNat 64 0) := by
      rw [kapIret_mem, kapIret_rsp]
      exact kapIret_liest1
    have h2 : read64 kapIretHw.mem
        (addrOff ((kapIretHw.kerne 0).register .rsp) 16) =
        some (BitVec.ofNat 64 0) := by
      rw [kapIret_mem, kapIret_rsp]
      exact kapIret_liest2
    have h3 : read64 kapIretHw.mem
        (addrOff ((kapIretHw.kerne 0).register .rsp) 24) =
        some (BitVec.ofNat 64 0) := by
      rw [kapIret_mem, kapIret_rsp]
      exact kapIret_liest3
    have h4 : read64 kapIretHw.mem
        (addrOff ((kapIretHw.kerne 0).register .rsp) 32) =
        some (BitVec.ofNat 64 0) := by
      rw [kapIret_mem, kapIret_rsp]
      exact kapIret_liest4
    have hk : istKanonisch (BitVec.ofNat 64 0) = true :=
      kapIret_kanonisch
    obtain ⟨kI, stI, hrestI⟩ := schrittIret_ok kapIretHw 0
      sysWitSteuer 0 0 0 0 0 h0 h1 h2 h3 h4 hk
    have hsnapI : sysSnapSchritt kapIretHw 0 sysWitSteuer
        ⟨.iret, sysWitEingaben⟩ = .ok kI stI kapIretHw.mem := by
      simp [sysSnapSchritt, hrestI.1]
    have hplugI := adapterSystem_ok kapIretHw 0
      (sysWitSteuer, ⟨.iret, sysWitEingaben⟩) kI stI _ hsnapI
    exact ⟨_, (kap_system_embedded _ _ _ _ _).mp hplugI,
      kap_system_iret_still _ _ _ _ rfl 0 0 0 0 0
        h0 h1 h2 h3 h4 hk _ hplugI⟩

/-! ## 6. Joint witness: locked events, silent legs, the INT n
    obstruction, refusals and two-core non-degeneracy, together. -/

/-- Joint TSO witness for the locked and direct-memory tags: an
    exhibited LOCK XADD union step equals the accepted TSO locked
    event with the footprint named (word 10 to 15, own buffer
    drained); MFENCE and the fetched XADD join it; all nine silent
    system legs stand beside them (the helper); the core-1 INT
    delivery is exhibited and is no single TSO event; the failing
    comparison is admitted while a readable-but-not-writable word
    refuses it; the own-buffer, split-lock, register-#UD and
    freestanding-syscall refusals stand beside the run; both cores
    locked-add 10 to 15 to 22 with owner-only forwarding. -/
theorem kapLocked_zeuge :
    (∃ m1 : HwMaschine, ∃ ev : LockEreignis,
      HwVollSchritt hwLockWitStart m1
        (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9)) ∧
      lockSchritt
        (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
          ((hwLockWitStart.kerne 0).register .rax)) 0
        (kapTso hwLockWitStart) = some (kapTso m1, ev) ∧
      ev.lesen = Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) ∧
      ev.schreiben =
        Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) ∧
      ev.istRmw = true ∧
      (∀ dd, dd ≠ 0 → (kapTso m1).puffer dd =
        (kapTso hwLockWitStart).puffer dd) ∧
      hwLockWitStart.puffer 0 = [] ∧
      read64 hwLockWitStart.mem hwLockWitAdr = some 10 ∧
      read64 m1.mem hwLockWitAdr = some 15)
    ∧ (∃ mF : HwMaschine,
      HwVollSchritt hwLockWitStart mF
        (KapEreignis.lockRmw 0 (.ok .mfence 3)) ∧
      kapTso mF = kapTso hwLockWitStart)
    ∧ (∃ m1 : HwMaschine, ∃ ev : LockEreignis,
      HwVollSchritt hwLockWitStart m1 (KapEreignis.lockFetch 0 ()) ∧
      lockSchritt
        (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
          ((hwLockWitStart.kerne 0).register .rax)) 0
        (kapTso hwLockWitStart) = some (kapTso m1, ev) ∧
      ev.istRmw = true)
    ∧ (∃ mI : HwMaschine,
      HwVollSchritt sysWitStart.hw mI
        (KapEreignis.system 1 sysWitSteuer ⟨.intN, sysWitEingaben⟩) ∧
      ¬ TSOSchritt (kapTso sysWitStart.hw) (kapTso mI))
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw ∧
      ∀ d, m1.puffer d = sysWitStart.hw.puffer d)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.hlt, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.sti, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.pause, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.cpuid, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.rdtsc, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer
          ⟨.syscall, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt sysWitStart.hw m1
        (KapEreignis.system 0 sysWitSteuer
          ⟨.sysret, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso sysWitStart.hw)
    ∧ (∃ m1 : HwMaschine,
      HwVollSchritt kapIretHw m1
        (KapEreignis.system 0 sysWitSteuer ⟨.iret, sysWitEingaben⟩) ∧
      kapTso m1 = kapTso kapIretHw)
    ∧ (hwLockWort hwLockWitAdr
        (hwLockSchritt hwLockWitCmpxchgNein 0
          (.ok (.cmpxchg64 .rcx .rbp 0) 9)) = some 10 ∧
      hwLockReg 0 .rax
        (hwLockSchritt hwLockWitCmpxchgNein 0
          (.ok (.cmpxchg64 .rcx .rbp 0) 9)) = some 10 ∧
      hwLockSchritt hwLockWitOhneSchreiben 0
        (.ok (.cmpxchg64 .rcx .rbp 0) 9) = none)
    ∧ (hwLockSicht hwLockWitNach1 1 hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 99)) ∧
      hwLockSicht hwLockWitNach1 0 hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 0)) ∧
      hwLockWort hwLockWitAdr hwLockWitNach2 = some 22)
    ∧ (hwLockSchritt hwLockWitStart 1
        (.ok (.xadd64 .rax .rbp 0) 9) = none ∧
      hwLockFetchSchritt hwLockFetchSplit 0 = none ∧
      hwLockSchritt hwLockWitStart 0 (.ud .lockAufRegister 5) = none ∧
      adapterSystem.schritt sysWitStart.hw 0
        (sysWitSteuer,
          ⟨.syscall, { sysWitEingaben with sceLang := false }⟩) =
        none)
    ∧ (HwWf hwLockWitStart ∧ HwWf sysWitStart.hw ∧ HwWf kapIretHw) := by
  have legLock : (∃ m1 : HwMaschine, ∃ ev : LockEreignis,
      HwVollSchritt hwLockWitStart m1
        (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9)) ∧
      lockSchritt
        (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
          ((hwLockWitStart.kerne 0).register .rax)) 0
        (kapTso hwLockWitStart) = some (kapTso m1, ev) ∧
      ev.lesen = Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) ∧
      ev.schreiben =
        Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) ∧
      ev.istRmw = true ∧
      (∀ dd, dd ≠ 0 → (kapTso m1).puffer dd =
        (kapTso hwLockWitStart).puffer dd) ∧
      hwLockWitStart.puffer 0 = [] ∧
      read64 hwLockWitStart.mem hwLockWitAdr = some 10 ∧
      read64 m1.mem hwLockWitAdr = some 15) := by
    obtain ⟨mL, hUL⟩ := kap_step_lock
    have hplugL : hwLockSchritt hwLockWitStart 0
        (.ok (.xadd64 .rax .rbp 0) 9) = some mL :=
      (kap_lock_embedded _ _ _ _).mpr hUL
    obtain ⟨tgtL, deltaL, evL, htgtL, hdeltaL, hbufL, hTsoL,
        hfussLL, hfussSL, hrmwL, hforeignL, hownL⟩ :=
      kapLockTso_xadd_geerbt _ _ _ _ _ _ _ hplugL
    have hTsoL' : lockSchritt
        (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
          ((hwLockWitStart.kerne 0).register .rax)) 0
        (kapTso hwLockWitStart) = some (kapTso mL, evL) := by
      rw [← htgtL, ← hdeltaL]
      exact hTsoL
    have hfussLL' : evL.lesen =
        Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) := by
      rw [← htgtL]
      exact hfussLL
    have hfussSL' : evL.schreiben =
        Fuss (effAddr (projZustand hwLockWitStart 0) .rbp 0) := by
      rw [← htgtL]
      exact hfussSL
    have hN1 : hwLockWitNach1 = some mL := hplugL
    have hnach1 : read64 mL.mem hwLockWitAdr = some 15 := by
      have hw15 := hwLockWit_nach1_wort
      rw [hN1] at hw15
      exact hw15
    exact ⟨mL, evL, hUL, hTsoL', hfussLL', hfussSL', hrmwL,
      hforeignL, hbufL, hwLockWit_anfang, hnach1⟩
  have legFence : (∃ mF : HwMaschine,
      HwVollSchritt hwLockWitStart mF
        (KapEreignis.lockRmw 0 (.ok .mfence 3)) ∧
      kapTso mF = kapTso hwLockWitStart) := by
    cases hMF : hwLockSchritt hwLockWitStart 0 (.ok .mfence 3) with
    | none =>
      have hnein := hwLockWit_mfence_ok.1
      rw [hMF] at hnein
      simp only [hwLockRip] at hnein
      cases hnein
    | some mF =>
      have hMFplug : adapterLockRmw.schritt hwLockWitStart 0
          (.ok .mfence 3) = some mF := hMF
      have hUF := (kap_lock_embedded _ _ _ _).mp hMFplug
      have hstillF := kapLockTso_mfence_still _ _ _ _ hMF
      exact ⟨mF, hUF, hstillF⟩
  have legFetch : (∃ m1 : HwMaschine, ∃ ev : LockEreignis,
      HwVollSchritt hwLockWitStart m1 (KapEreignis.lockFetch 0 ()) ∧
      lockSchritt
        (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
          ((hwLockWitStart.kerne 0).register .rax)) 0
        (kapTso hwLockWitStart) = some (kapTso m1, ev) ∧
      ev.istRmw = true) := by
    cases hN : hwLockWitNach1 with
    | none =>
      have hw10 := hwLockWit_nach1_wort
      rw [hN] at hw10
      simp only [hwLockWort] at hw10
      cases hw10
    | some mFL =>
      have hF : hwLockFetchSchritt hwLockWitStart 0 = some mFL := by
        rw [hwLockFetchWit_nach1, hN]
      obtain ⟨tgtF, deltaF, evF, htgtF, hdeltaF, _, hTsoF, _, _,
          hrmwF, _, _⟩ :=
        kap_lockFetch_xadd_geerbt hwLockWitStart 0 .rax .rbp 0 9
          (List.replicate 6 (BitVec.ofNat 8 0)) mFL
          hwLockFetchWit_start0
          (by simp only [hwLockFetchWit_start_fuss,
            hwLockFetchWit_kein_split]) hF
      have hTsoF' : lockSchritt
          (.xadd64 (effAddr (projZustand hwLockWitStart 0) .rbp 0)
            ((hwLockWitStart.kerne 0).register .rax)) 0
          (kapTso hwLockWitStart) = some (kapTso mFL, evF) := by
        rw [← htgtF, ← hdeltaF]
        exact hTsoF
      have hFplug : adapterLockFetch.schritt hwLockWitStart 0 () =
          some mFL := hF
      have hUFfetch : HwVollSchritt hwLockWitStart mFL
          (KapEreignis.lockFetch 0 ()) :=
        (kap_lockFetch_embedded _ _ _ _).mp hFplug
      exact ⟨mFL, evF, hUFfetch, hTsoF', hrmwF⟩
  have legIntN : (∃ mI : HwMaschine,
      HwVollSchritt sysWitStart.hw mI
        (KapEreignis.system 1 sysWitSteuer ⟨.intN, sysWitEingaben⟩) ∧
      ¬ TSOSchritt (kapTso sysWitStart.hw) (kapTso mI)) := by
    cases hS : sysSnapSchritt sysWitStart.hw 1 (sysWitStart.sys 1)
        ⟨.intN, sysWitEingaben⟩ with
    | ok k1 st1 mem1 =>
      have hsys1 : sysWitStart.sys 1 = sysWitSteuer := rfl
      rw [hsys1] at hS
      have hleg : schrittInt sysWitStart.hw 1 sysWitSteuer
          sysWitEingaben = .ok k1 st1 mem1 := by
        have hred : sysSnapSchritt sysWitStart.hw 1 sysWitSteuer
            ⟨.intN, sysWitEingaben⟩ =
            schrittInt sysWitStart.hw 1 sysWitSteuer sysWitEingaben := by
          simp [sysSnapSchritt]
        have hS' := hS
        rw [hred] at hS'
        exact hS'
      obtain ⟨mI, hplugI⟩ : ∃ mI, adapterSystem.schritt sysWitStart.hw 1
          (sysWitSteuer, ⟨.intN, sysWitEingaben⟩) = some mI :=
        ⟨_, adapterSystem_ok sysWitStart.hw 1
          (sysWitSteuer, ⟨.intN, sysWitEingaben⟩) k1 st1 mem1 hS⟩
      have hUI := (kap_system_embedded _ _ _ _ _).mp hplugI
      have hcond : formFrei
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).eingaben.profil
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).form = true :=
        formFrei_gehostet _
      have hAusOk : sysAusfuehren sysWitStart 1 ⟨.intN, sysWitEingaben⟩ =
          .ok (sysInstalliert sysWitStart 1 k1 st1 mem1) := by
        simp [sysAusfuehren, hcond, hsys1, hS]
      have hT1 : sysWitT1 =
          sysInstalliert sysWitStart 1 k1 st1 mem1 := by
        simp [sysWitT1, sysWitO_int1, hAusOk]
      have hT1mem : sysWitT1.hw.mem = mem1 := by
        rw [hT1]
        rfl
      have hx0 : sysWitT1.hw.mem.bytes (BitVec.ofNat 64 16344) ≠
          sysWitStart.hw.mem.bytes (BitVec.ofNat 64 16344) := by
        decide
      have hy0 : sysWitT1.hw.mem.bytes (BitVec.ofNat 64 16369) ≠
          sysWitStart.hw.mem.bytes (BitVec.ofNat 64 16369) := by
        decide
      have hx : mem1.bytes (BitVec.ofNat 64 16344) ≠
          sysWitStart.hw.mem.bytes (BitVec.ofNat 64 16344) := by
        rw [← hT1mem]
        exact hx0
      have hy : mem1.bytes (BitVec.ofNat 64 16369) ≠
          sysWitStart.hw.mem.bytes (BitVec.ofNat 64 16369) := by
        rw [← hT1mem]
        exact hy0
      have hxy : (BitVec.ofNat 64 16344) ≠
          (BitVec.ofNat 64 16369) := by
        decide
      have hkein := kap_system_intN_kein_tso_ereignis sysWitStart.hw mI 1
        sysWitSteuer ⟨.intN, sysWitEingaben⟩ k1 st1 mem1 rfl hleg hplugI
        _ _ hx hy hxy
      exact ⟨mI, hUI, hkein⟩
    | fehler f =>
      have hcond : formFrei
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).eingaben.profil
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).form = true :=
        formFrei_gehostet _
      have hfee : sysAusfuehren sysWitStart 1 ⟨.intN, sysWitEingaben⟩ =
          .fehler f := by
        simp [sysAusfuehren, hcond, hS]
      have hrip := sysWit_int1_rip
      rw [show sysWitO_int1 =
          sysAusfuehren sysWitStart 1 ⟨.intN, sysWitEingaben⟩ from rfl,
        hfee] at hrip
      simp only [sysRipOut] at hrip
      cases hrip
    | verweigert =>
      have hcond : formFrei
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).eingaben.profil
          (⟨.intN, sysWitEingaben⟩ : SysEreignis).form = true :=
        formFrei_gehostet _
      have hverw : sysAusfuehren sysWitStart 1 ⟨.intN, sysWitEingaben⟩ =
          .verweigert := by
        simp [sysAusfuehren, hcond, hS]
      have hrip := sysWit_int1_rip
      rw [show sysWitO_int1 =
          sysAusfuehren sysWitStart 1 ⟨.intN, sysWitEingaben⟩ from rfl,
        hverw] at hrip
      simp only [sysRipOut] at hrip
      cases hrip
  have legUD : adapterSystem.schritt sysWitStart.hw 0
      (sysWitSteuer,
        ⟨.syscall, { sysWitEingaben with sceLang := false }⟩) =
      none := by
    have hudLeg : schrittSyscall sysWitStart.hw 0 sysWitSteuer
        { sysWitEingaben with sceLang := false } = .fehler .ud :=
      schrittSyscall_ud _ _ _ _ rfl
    have hsnapUD : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
        ⟨.syscall, { sysWitEingaben with sceLang := false }⟩ =
        .fehler .ud := by
      simp [sysSnapSchritt, hudLeg]
    exact adapterSystem_fehler _ _ _ _ hsnapUD
  obtain ⟨sCli, sHlt, sSti, sPause, sCpuid, sRdtsc, sSyscall, sSysret,
      sIret⟩ := kapLocked_sys_alle_still
  exact ⟨legLock, legFence, legFetch, legIntN, sCli, sHlt, sSti, sPause,
    sCpuid, sRdtsc, sSyscall, sSysret, sIret,
    ⟨hwLockWit_cmpxchg_nein_ok.1, hwLockWit_cmpxchg_nein_ok.2,
      hwLockWit_schreibfehler⟩,
    ⟨hwLockWit_nach1_eigen_sicht, hwLockWit_nach1_fremd_sicht,
      hwLockWit_nach2_wort⟩,
    ⟨hwLockWit_puffer, hwLockFetchWit_split, hwLockWit_reg_ud, legUD⟩,
    ⟨hwLockWitStart_wf, sysWitStart_wf, kapIretHw_wf⟩⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    definition lifted, never redefined):
    - LOCK XADD is the accepted TSO locked event
      (`kapLockTso_xadd_geerbt`): an admitted `hwLockSchritt` XADD
      step equals `lockSchritt` (`LockedOps`, over `TSOZustand`) on
      the projection `kapTso`, with the word footprint `Fuss tgt`
      named on both sides, old/new words named, `istRmw` set, the
      own buffer drained (`m.puffer c = []` as a separate leg) and
      foreign buffers untouched. The union lift is
      `kap_union_lockRmw_xadd_tso`;
    - MFENCE is silent (`kapLockTso_mfence_still`, union lift
      `kap_union_lockRmw_mfence_still`): only RIP advances;
    - fetched LOCK inherits the classification off-split
      (`kap_lockFetch_xadd_geerbt`, `kap_lockFetch_mfence_still`,
      union lift `kap_union_lockFetch_xadd_tso`); split words,
      parsed #UD and absent fetches refuse (accepted pins, joined
      in the witness);
    - the nine memory-unchanged system legs are silent
      (`kap_system_hlt/cli/sti/pause/cpuid/rdtsc/syscall/sysret/iret_still`
      via the generic transport `kap_system_still_of_mem`, union
      lift `kap_union_system_still`); every admitted plug step keeps
      every buffer (`kap_system_puffer_bleibt`: SYSCALL/SYSRET/INT
      perform no drain, the plug-level form of S-SYSCALL-KEIN-DRAIN
      and S-INT-KEIN-DRAIN);
    - joint witnesses `kapLocked_sys_alle_still` (all nine legs as
      reached union steps silent on the projection; IRET runs on the
      parked-RSP variant `kapIretHw` since the start RSP points at
      unreadable memory) and `kapLocked_zeuge` (LOCK XADD union step
      with its TSO event and footprint, MFENCE, fetched XADD,
      exhibited core-1 INT delivery with its two changed frame bytes,
      the failing-comparison twin with the write-permission refusal,
      own-buffer/split/#UD/freestanding-syscall refusals,
      well-formedness, two-core non-degeneracy 10 to 15 to 22 with
      owner-only forwarding).
    NOT proved here, and not claimed (FINDINGs):
    - CMPXCHG (`kapLockTso_cmpxchg_befund`): no single accepted TSO
      locked event matches the coherent compare-exchange step. On a
      failing comparison the coherent step still performs the
      manual's write cycle (needs `write64`, refused on a
      readable-but-not-writable word) while the accepted TSO CAS
      (`casSchritt_fehlschlag`) stutters with the projection
      unchanged and needs no write; `lockSchritt` has no cmpxchg
      arm at all. Success-only correspondence with `casSchritt`
      (plus flags/RAX effects, which have no TSO-level form) stays
      open;
    - INT n delivery (`kap_system_intN_schreibt_direkt`,
      `kap_system_intN_kein_tso_ereignis`, high priority): an
      admitted delivery installs its pushed-frame memory directly
      (accepted `schiebeRahmen` path) while every buffer is kept; a
      delivery changing two distinct canonical bytes is no single
      accepted TSO event (issue keeps memory, flush touches exactly
      its head address). The exhibited core-1 delivery changes
      bytes 16344 and 16369. A multi-step `TSOErreichbar`
      characterisation of the frame push is not attempted;
    - the remaining 13 union tags (isa, addr, muldiv, uc, port, fp,
      fehler, tor, vec, nested, int, bild, instanzen) are NOT
      classified here;
    - no W/GX bridge (target-only reachability; `tso_last_lesbar`
      is cited, not re-proved); no whole-word atomicity beyond the
      guarded drains; no source, checker, contract, entry, ABI,
      loader, budget or liveness claim; no hardware correspondence
      beyond self-consistency (silicon and timing assumptions live
      in the family files, not re-checked here; cache-line size 64
      for the split-lock refusal is the accepted 1209 assumption).
-/

#print axioms kap_system_still_of_mem
#print axioms kapLockTso_xadd_geerbt
#print axioms kapLockTso_mfence_still
#print axioms kapLockTso_cmpxchg_befund
#print axioms kap_lockFetch_xadd_geerbt
#print axioms kap_lockFetch_mfence_still
#print axioms kap_system_hlt_still
#print axioms kap_system_cli_still
#print axioms kap_system_sti_still
#print axioms kap_system_pause_still
#print axioms kap_system_cpuid_still
#print axioms kap_system_rdtsc_still
#print axioms kap_system_syscall_still
#print axioms kap_system_sysret_still
#print axioms kap_system_iret_still
#print axioms kap_system_puffer_bleibt
#print axioms kap_system_intN_schreibt_direkt
#print axioms kap_system_intN_kein_tso_ereignis
#print axioms kap_union_lockRmw_xadd_tso
#print axioms kap_union_lockRmw_mfence_still
#print axioms kap_union_lockFetch_xadd_tso
#print axioms kap_union_system_still
#print axioms kapIretReg
#print axioms kapIretHw
#print axioms kapIret_rsp
#print axioms kapIret_mem
#print axioms kapIret_liest0
#print axioms kapIret_liest1
#print axioms kapIret_liest2
#print axioms kapIret_liest3
#print axioms kapIret_liest4
#print axioms kapIret_kanonisch
#print axioms kapIretHw_wf
#print axioms kapLocked_sys_alle_still
#print axioms kapLocked_zeuge

end Gabbro.Grammatik.X86
