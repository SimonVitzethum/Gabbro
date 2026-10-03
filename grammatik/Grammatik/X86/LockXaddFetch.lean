/-
  File:      Grammatik/X86/LockXaddFetch.lean
  Subject:   LOCK XADD fetch-add connection: constant-cost word fetch-add
              preferred over CAS loops, full barrier, single atomicity unit,
              pinned bytes, through the accepted LOCK vocabulary.

  Lane 778: thin connection over the accepted canonical vocabulary
  (`Zustand`, `read64`/`write64`, `Fuss`, `TSOZustand`, `lockSchritt`,
  `lockKosten`/`casKosten` from `LockedOps`; `LockForm`, `encodeLock`,
  `decodeLock`/`decodeLockExt`, `LockMaschine`, `lockSchrittVoll`,
  `lockFetch`/`lockByteschritt`, observers and pins from
  `LockedInstructionExecution`; `decodeExt` from `ExtendedExecution`).
  Nothing is redefined here: no new register, memory, decoder or
  source model.

  Manual provenance (clone-local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined volumes 1-4, edition 325462-093US, September 2026
  (`REFERENCES.json`, verified 2026-10-02). Instruction entries used:
  LOCK prefix (Intel SDM Vol. 2A 3-565/3-566: locked bus operation,
  full barrier ordering of the locked access), XADD (Intel SDM Vol. 2D
  6-27/6-28: exchange source with destination then load sum, flags set
  per the addition, LOCK form is atomic). Only these named entries are
  used; no vendor difference, silicon timing or cycle bound is claimed.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.TSO
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Fetch-add shape cost is one unit: reuse of the accepted locked cost. -/
def xaddKosten (a : Adresse) (delta : Wort) : Nat :=
  lockKosten (.xadd64 a delta)

/-! ## 1. Constant cost: fetch-add is one unit, preferred over CAS loops. -/

/-- One fetch-add counts one shape unit. -/
theorem xadd_kosten_eins (a : Adresse) (delta : Wort) :
    xaddKosten a delta = 1 := by
  simp [xaddKosten, lockKosten]

/-- One fetch-add never costs more than any CAS retry count: the CAS
    loop shape (`casKosten n = n + 1`) is unbounded
    (`cas_schleife_unbeschraenkt`), the fetch-add is constant. -/
theorem xadd_guenstiger_als_cas (a : Adresse) (delta : Wort) (n : Nat) :
    xaddKosten a delta ≤ casKosten n := by
  simp [xaddKosten, lockKosten, casKosten]

/-! ## 2. Connection: fetched LOCK XADD is a constant-cost fetch-add.

    Manual grounds (Intel SDM 325462-093US, local snapshot):
    XADD Vol. 2D 6-27/6-28 (exchange source with destination, then load
    the sum; flags per the addition; LOCK makes it atomic), LOCK
    Vol. 2A 3-565/3-566 (locked bus operation with full barrier order).
    Every premise pins one guard of the accepted `lockSchrittVoll`. -/

/-- CONNECTION: a LOCK XADD word step from the accepted byte machine is
    a constant-cost fetch-add with full local barrier, one atomicity
    unit and pinned bytes: the word grows by the source register, the
    source takes the old word, flags follow the addition, RIP advances
    by the parsed length, buffers are untouched, the event is a single
    RMW over the full word footprint, the TSO projection agrees on the
    same words, and the shape cost stays one below every CAS retry. -/
theorem LockXaddFetch_verbindung (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (alt sval : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some alt)
    (hreg : m.zu.register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) (alt + sval) =
      some mem') :
    ∃ (m' : LockMaschine) (ev : LockEreignis),
      lockSchrittVoll (.ok (.xadd64 src base d) len) c m hw bp =
        LockAusgang.ok m' ev ∧
      ev.istRmw = true ∧
      ev.lesen = Fuss (effAddr m.zu base d) ∧
      ev.schreiben = Fuss (effAddr m.zu base d) ∧
      ev.gelesen = some alt ∧
      ev.geschrieben = some (alt + sval) ∧
      xaddKosten (effAddr m.zu base d) sval = 1 ∧
      (∀ n, xaddKosten (effAddr m.zu base d) sval ≤ casKosten n) ∧
      m'.puffer = m.puffer ∧
      m'.zu.speicher = mem' ∧
      m'.zu.register src = alt ∧
      m'.zu.flags = (add64 alt sval).2 ∧
      m'.zu.rip = ripNach m.zu.rip len ∧
      (ev.lesen.length = 8 ∧ ev.schreiben.length = 8) ∧
      ∃ ev0 : LockEreignis,
        lockSchritt (.xadd64 (effAddr m.zu base d) sval) c (toTSO m) =
          some (⟨mem', m.puffer⟩, ev0) ∧
        ev0.gelesen = some alt ∧ ev0.istRmw = true := by
  have hstep := lockSchrittVoll_xadd_erfolg m c src base d len hw bp
    alt sval mem' hbuf hali hrd hreg hok hwr
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d)
      (alt + m.zu.register src) = some mem' := by
    rw [hreg]; exact hwr
  have had := lockVoll_xadd_adapter m c src base d alt mem'
    hbuf hrd hali hwr'
  rw [hreg] at had
  refine ⟨_, _, hstep, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_,
    ?_, rfl, ?_, had⟩
  · simp [xaddKosten, lockKosten]
  · intro n; simp [xaddKosten, lockKosten, casKosten]
  · show (schrittRegister m.zu (ripNach m.zu.rip len) (add64 alt sval).2 src alt).register src = alt
    simp [schrittRegister, regSet]
  · rfl
  · simp [Fuss]

/-! ## 3. Fetched bytes and planted refusals through the common path.

    Admitted LOCK XADD bytes run through the combined decoder
    (`decodeLockExt`: the accepted `decodeExt` first, the lock rows only
    where it refuses); unsupported neighbours refuse explicitly. All
    facts reuse the accepted pins, never re-decided here. -/

/-- The common dispatcher refuses the LOCK XADD bytes: no older row
    shadows the fetch-add form (reused pin). -/
theorem xadd_gemeinsam_verweigert :
    decodeExt pinXadd = none :=
  pin_lock_ext_verweigert_xadd

/-- Where every older decoder refuses, the combined decode takes the
    LOCK XADD row whole: admitted final bytes enter through the common
    architecture (reused pins). -/
theorem xadd_kombiniert_nimmt :
    decodeLockExt pinXadd =
      some (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9, []) :=
  decodeLockExt_lock pinXadd _ [] pin_lock_ext_verweigert_xadd
    pin_lock_xadd_decodiert

/-- UNSUPPORTED NEIGHBOURS REFUSE: a pending own store, a misaligned
    word, a LOCK on a register destination (architectural #UD) and an
    unreadable word each admit no silent fetch-add (reused pins). -/
theorem xadd_nachbarn_verweigern :
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeExec lockDataRW lockDataRW 5 8192 0
        einEintrag)
      0 basisHw basisBereit) = .verweigert ∧
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeExec lockDataRW lockDataRW 5 8193 0 [])
      0 basisHw basisBereit) = .verweigert ∧
    lockArt (lockByteschritt
      (lockZeug pinRegUd 0 lockCodeExec lockDataRW lockDataRW 0 8192 0 [])
      0 basisHw basisBereit) = .udFehler ∧
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeNie lockDataRW lockDataRW 5 8192 0 [])
      0 basisHw basisBereit) = .verweigert :=
  ⟨zeug_puffer_verweigert, zeug_unaligned_verweigert,
    zeug_reg_ud_fetched, zeug_ohne_exec_verweigert⟩

/-! ## 4. Joint witness: every premise together on one fetched run.

    All guards of `LockXaddFetch_verbindung` hold jointly on the
    accepted fetched XADD machine (`zeugXadd`: word 10 at 8192, delta 5
    in rax, base rbp, empty buffer, 9 checked bytes); the fetched run
    moves the word 10 to 15, returns the old 10 through rax, and the
    start word observably differs from the fetched word. -/

/-- JOINT WITNESS for `LockXaddFetch_verbindung`: every premise holds
    jointly on concrete values, the connection fires, and the reached
    fetched run changes memory (10 to 15) with the old value returned
    through the register. Non-degenerate: a reached memory-changing
    execution, not an empty run. -/
theorem LockXaddFetch_verbindung_zeuge :
    ∃ (m : LockMaschine) (mem' : Speicher),
      m.puffer 0 = [] ∧
      ausgerichtet8 (effAddr m.zu .rbp 0) = true ∧
      read64 m.zu.speicher (effAddr m.zu .rbp 0) = some 10 ∧
      m.zu.register .rax = 5 ∧
      laengeOk 9 = true ∧
      write64 m.zu.speicher (effAddr m.zu .rbp 0) (10 + 5) =
        some mem' ∧
      (∃ (m' : LockMaschine) (ev : LockEreignis),
        lockSchrittVoll (.ok (.xadd64 .rax .rbp 0) 9) 0 m basisHw
            basisBereit = LockAusgang.ok m' ev ∧
          ev.istRmw = true ∧
          m'.zu.register .rax = 10 ∧
          m'.zu.speicher = mem') ∧
      lockArt (lockByteschritt m 0 basisHw basisBereit) = .ok ∧
      lockWort (BitVec.ofNat 64 8192)
        (lockByteschritt m 0 basisHw basisBereit) = some 15 ∧
      read64 m.zu.speicher (BitVec.ofNat 64 8192) ≠
        lockWort (BitVec.ofNat 64 8192)
          (lockByteschritt m 0 basisHw basisBereit) := by
  obtain ⟨m, mem', hbuf, heff, hali, hrd, hreg, hwr, hok, hwort,
    hrax, hne⟩ := lockSchrittVoll_xadd_erfolg_zeuge
  have hali' : ausgerichtet8 (effAddr m.zu .rbp 0) = true := by
    rw [heff]; exact hali
  have hrd' : read64 m.zu.speicher (effAddr m.zu .rbp 0) =
      some 10 := by
    rw [heff]; exact hrd
  have hwr' : write64 m.zu.speicher (effAddr m.zu .rbp 0) (10 + 5) =
      some mem' := by
    rw [heff]; exact hwr
  have hconn := LockXaddFetch_verbindung m 0 .rax .rbp 0 9 basisHw
    basisBereit 10 5 mem' hbuf hali' hrd' hreg rfl hwr'
  obtain ⟨m', ev, hstep, hrmw, _, _, _, _, _, _, _, hspeicher, hraxalt,
    _, _, _, _⟩ := hconn
  refine ⟨m, mem', hbuf, hali', hrd', hreg, rfl, hwr',
    ⟨m', ev, hstep, hrmw, hraxalt, hspeicher⟩, hok, hwort, hne⟩

/- CUTS:
    Proved here (all over the REUSED accepted vocabulary -- `lockKosten`/
    `casKosten`, `lockSchrittVoll`/`lockSchritt`, `decodeLockExt`,
    `lockByteschritt` and the pins of `LockedOps`/
    `LockedInstructionExecution`/`ExtendedExecution` -- no new register,
    memory, decoder, arithmetic or source model):
    - constant fetch-add cost (`xaddKosten` is one unit) preferred over
      CAS loops (`xadd_guenstiger_als_cas`: below every `casKosten n`;
      retry unboundedness itself stays with `cas_schleife_unbeschraenkt`);
    - the `LockXaddFetch_verbindung` connection (word grows by the source
      register, source takes the old word, addition flags, RIP advance,
      untouched buffers, single RMW over the pinned 8-byte footprint,
      TSO projection on the same words, cost one below every CAS retry);
    - fetched bytes through the common path (`xadd_kombiniert_nimmt`:
      the combined decoder takes the LOCK XADD row where `decodeExt`
      refuses it, so no older row is shadowed);
    - planted refusals (`xadd_nachbarn_verweigern`: pending own store,
      misaligned word, LOCK on a register destination as #UD, and
      execute-denied bytes refuse explicitly);
    - the joint `LockXaddFetch_verbindung_zeuge` witness: every premise
      jointly on the fetched `zeugXadd` run (word 10 to 15, old 10 back
      through rax, start word observably changed).
    NOT proved here, and not claimed:
    - No silicon correspondence: the LOCK/XADD entries (Vol. 2A
      3-565/3-566, Vol. 2D 6-27/6-28, edition 325462-093US Sep 2026)
      are the named contracts against the local official snapshot;
      faults are the accepted permission-checked outcomes, not silicon.
    - No new codec rows: all bytes, forms and steps are the accepted
      `LockedInstructionExecution` ones; narrower widths, other LOCK
      forms (CMPXCHG stays with its owner), other addressing modes and
      unlocked XADD stay open.
    - No W/GX refinement and no cycle/latency/progress claim: the bridge
      owns refinement; `xaddKosten` is a shape count and CAS retry stays
      unbounded here.
    - No source, checker, contract, budget, duty or goal change:
      nothing here speaks about `Vertrag`, `Stmt`, duties or
      `gabbro_ziel`.
-/

#print axioms xaddKosten
#print axioms xadd_kosten_eins
#print axioms xadd_guenstiger_als_cas
#print axioms LockXaddFetch_verbindung
#print axioms LockXaddFetch_verbindung_zeuge
#print axioms xadd_gemeinsam_verweigert
#print axioms xadd_kombiniert_nimmt
#print axioms xadd_nachbarn_verweigern

end Gabbro.Grammatik.X86
