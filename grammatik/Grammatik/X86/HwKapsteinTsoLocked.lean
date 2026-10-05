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

/- CUTS:
    Skeleton only: the generic silent-leg transport
    `kap_system_still_of_mem`. Per-form legs, the locked-RMW event,
    lockFetch inheritance, the INT n FINDING, union lifts and the
    joint witness follow.
-/

#print axioms kap_system_still_of_mem

end Gabbro.Grammatik.X86
