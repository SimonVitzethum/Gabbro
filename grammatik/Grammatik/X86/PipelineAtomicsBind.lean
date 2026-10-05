/-
  File:      Grammatik/X86/PipelineAtomicsBind.lean
  Subject:   Pipeline atomics: register-address binding for RMW/fence byte
             forms, SFENCE/LFENCE lowering, and the 8-issue word-install
             proof.

  Lane 1203 (follow-up of lane 1163 `PipelineAtomics.lean`): the three
  open gaps named in its CUTS -- (a) which (base, disp) names which
  address for the locked byte forms, (b) SFENCE/LFENCE lowering, (c) the
  whole-word store install from bytes -- closed over REUSED accepted
  definitions only. No new machine, no new decoder row, no second IR,
  no source/checker/goal change. Unsupported shapes are REFUSED.
-/
import Grammatik.X86.PipelineAtomics
import Grammatik.X86.SfenceStoreNarrow
import Grammatik.X86.LfenceLoadNarrow
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86.PipelineAtomicsBind

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineAtomics

/-- Fence kind: full MFENCE plus the two narrow forms. -/
inductive ZaunArt where
  | mfence
  | sfence
  | lfence
  deriving DecidableEq, Repr

/-- Canonical bytes of one fence kind (all reused, never redefined). -/
def zaunBytes : ZaunArt → List Byte
  | .mfence => pinMfence
  | .sfence => pinSfence
  | .lfence => lfenceBytes

/-- MFENCE bytes are the accepted locked fence pin. -/
theorem zaunBytes_mfence : zaunBytes .mfence = pinMfence := rfl

/-- SFENCE bytes are the accepted narrow-store pin. -/
theorem zaunBytes_sfence : zaunBytes .sfence = pinSfence := rfl

/-- LFENCE bytes are the accepted narrow-load pin. -/
theorem zaunBytes_lfence : zaunBytes .lfence = lfenceBytes := rfl

/-! ## 1. Register-address binding for the locked byte forms.

    The accepted locked steps speak about ADDRESSES (`lockSchritt`,
    `casSchritt`), the byte forms about REGISTERS (`LockForm.xadd64 src
    base disp`). The link is the register file: `effAddr m.zu base d`
    names the address the locked step runs at. Each theorem below states
    the lane-1163 lowering together with the accepted projection at the
    BOUND address -- the lowering and the address agree by the single
    `heff` equation. Fences need no address: the MFENCE projection is
    register-free. -/

/-- **XADD BINDING.** The lowered LOCK XADD runs the accepted locked
    add at exactly the address the register pair names. -/
theorem bind_xadd (m : LockMaschine) (c : Nat) (a : Adresse)
    (src base : Register) (d : BitVec 32)
    (alt : Wort) (mem' : Speicher)
    (heff : effAddr m.zu base d = a)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 m.zu.speicher a (alt + m.zu.register src) = some mem') :
    PipelineAtomics.senkAtom (PipelineAtomics.AtomQuelle.xadd src base d) =
      some [PipelineAtomics.ZielOp.lock (.xadd64 src base d)] ∧
    ∃ ev : LockEreignis,
      lockSchritt (.xadd64 a (m.zu.register src)) c (toTSO m) =
        some (⟨mem', m.puffer⟩, ev) ∧
      ev.gelesen = some alt ∧ ev.istRmw = true := by
  have hrd' : read64 m.zu.speicher (effAddr m.zu base d) = some alt := by
    rw [heff]; exact hrd
  have hali' : ausgerichtet8 (effAddr m.zu base d) = true := by
    rw [heff]; exact hali
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d)
      (alt + m.zu.register src) = some mem' := by
    rw [heff]; exact hwr
  have h := lockVoll_xadd_adapter m c src base d alt mem' hbuf hrd' hali' hwr'
  rw [heff] at h
  exact ⟨PipelineAtomics.senk_xadd src base d, h⟩

/-- **CAS BINDING.** The lowered LOCK CMPXCHG success runs the accepted
    CAS success at exactly the address the register pair names
    (comparison against rax, install of the src word). -/
theorem bind_cas_erfolg (m : LockMaschine) (c : Nat) (a : Adresse)
    (src base : Register) (d : BitVec 32)
    (dest : Wort) (mem' : Speicher)
    (heff : effAddr m.zu base d = a)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher a = some dest)
    (hali : ausgerichtet8 a = true)
    (hgleich : (dest == m.zu.register .rax) = true)
    (hwr : write64 m.zu.speicher a (m.zu.register src) = some mem') :
    PipelineAtomics.senkAtom (PipelineAtomics.AtomQuelle.cas src base d) =
      some [PipelineAtomics.ZielOp.lock (.cmpxchg64 src base d)] ∧
    casSchritt a (m.zu.register .rax) (m.zu.register src) c (toTSO m) =
      some (⟨mem', m.puffer⟩, true) := by
  have hrd' : read64 m.zu.speicher (effAddr m.zu base d) = some dest := by
    rw [heff]; exact hrd
  have hali' : ausgerichtet8 (effAddr m.zu base d) = true := by
    rw [heff]; exact hali
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d)
      (m.zu.register src) = some mem' := by
    rw [heff]; exact hwr
  have h := lockVoll_cmpxchg_erfolg_adapter m c src base d dest mem'
    hbuf hrd' hali' hgleich hwr'
  rw [heff] at h
  exact ⟨PipelineAtomics.senk_cas src base d, h⟩

/-- **FENCE NEEDS NO BINDING.** The lowered fence is the accepted fence
    gate with no register or address premise at all. -/
theorem bind_mfence (m : LockMaschine) (c : Nat)
    (hbuf : m.puffer c = []) :
    PipelineAtomics.senkAtom PipelineAtomics.AtomQuelle.zaun =
      some [PipelineAtomics.ZielOp.lock .mfence] ∧
    lockSchritt .mfence c (toTSO m) =
      some (toTSO m, ⟨c, [], [], none, none, false, true⟩) :=
  ⟨PipelineAtomics.senk_zaun, lockVoll_mfence_adapter m c hbuf⟩

/-! ## 2. SFENCE/LFENCE lowering: canonical bytes with decode facts.

    Lane 1163 lowered only the full MFENCE fence. Each narrow form
    lowers to its own accepted pin: SFENCE to `pinSfence` (decoded by
    `decodeSfence`, never by the pilot or locked decoders), LFENCE to
    `lfenceBytes` (decoded by `decodeLfence`, refused by both older
    decoders). MFENCE keeps its lane-1163 lowering; its byte fact is
    restated here through `zaunBytes` so all three fences share one
    validator. -/

/-- MFENCE bytes decode to the fence form (reused round trip). -/
theorem zaun_mfence_dekodiert (suffix : List Byte) :
    decodeLock (zaunBytes .mfence ++ suffix) =
      some (LockAnweisung.ok .mfence 3, suffix) :=
  roundtrip_lock_mfence suffix

/-- SFENCE bytes decode to the narrow-store fence form. -/
theorem zaun_sfence_dekodiert (suffix : List Byte) :
    decodeSfence (zaunBytes .sfence ++ suffix) =
      some (SfenceAnweisung.ok .sfence 3, suffix) :=
  roundtrip_sfence suffix

/-- LFENCE bytes decode to the narrow-load fence form. -/
theorem zaun_lfence_dekodiert (suffix : List Byte) :
    decodeLfence (zaunBytes .lfence ++ suffix) = some ((), suffix) :=
  roundtrip_lfence suffix

/-- Decided validator: `bs` is accepted for `z` exactly when it is the
    canonical pin. Bytes are checked data, never trusted. -/
def valZaun (z : ZaunArt) (bs : List Byte) : Bool :=
  decide (zaunBytes z = bs)

/-- The validator accepts exactly the canonical pins. -/
theorem valZaun_korrekt (z : ZaunArt) (bs : List Byte) :
    valZaun z bs = true ↔ zaunBytes z = bs := by
  unfold valZaun
  simp [decide_eq_true_eq]

/- CUTS: what is not proved here (skeleton; extended with each piece)
    NOT proved here, and not claimed:
    - No seq_cst total order, no fairness, no CAS retry bound.
    - No full source `execBlock` correspondence for atomics.
-/

#print axioms zaunBytes_mfence
#print axioms zaunBytes_sfence
#print axioms zaunBytes_lfence
#print axioms zaun_mfence_dekodiert
#print axioms zaun_sfence_dekodiert
#print axioms zaun_lfence_dekodiert
#print axioms valZaun_korrekt
#print axioms bind_xadd
#print axioms bind_cas_erfolg
#print axioms bind_mfence

end Gabbro.Grammatik.X86.PipelineAtomicsBind
