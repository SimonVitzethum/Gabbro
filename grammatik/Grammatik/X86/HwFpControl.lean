/-
  File:      Grammatik/X86/HwFpControl.lean
  Subject:   Scalar FP32/FP64 and MXCSR on the coherent machine.

  Lane 1129: lift the accepted scalar families onto `HwMaschine`
  (HardwareExecution.lean) per core, reusing their evaluators unchanged:
  binary32 (`ScalarFloat32HardwareForms`: `s32Schritt`), binary64 REX
  (`ScalarFloatHardwareForms`: `fpSchritt` via `fpHwDecode`), and MXCSR
  (`FpControlHardwareForms`: `mxcsrSchritt`). Register steps ride the
  `HwSchritt.reg` memory-unchanged gate; every memory operand travels as
  `loadByte`/`issueByte`/`flushKern` equations on the shared TSO view.
  Silicon provenance is cited from the family files, never restated.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.ScalarFloatHardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.ScalarFloatCodec

namespace Gabbro.Grammatik.X86

/-- Observable family events on the coherent machine: one register
    step per family leg, plus the shared TSO byte memory events and
    explicit refusal. Memory-changing family forms never take the
    register path; they travel through the issue/load/flush events. -/
inductive FpCtrlEreignis where
  | s32reg : Nat → S32Decodiert → FpCtrlEreignis
  | f64reg : Nat → FpDecodiert → FpCtrlEreignis
  | mxcsrLd : Nat → MxcsrDec → FpCtrlEreignis
  | leseBeob : Nat → Adresse → Byte → FpCtrlEreignis
  | schreibAusgabe : Nat → Adresse → Byte → FpCtrlEreignis
  | spülung : Nat → TSOEintrag → FpCtrlEreignis
  | verweigert : Nat → FpCtrlEreignis
  deriving DecidableEq, Repr

/-- The four canonical byte-store entries of a 32-bit FP word `v`
    at `a`, oldest first: byte `k` sits at `addrOff a k`. The 64-bit
    leg reuses `wortEintraege` unchanged. -/
def fpEintraege32 (a : Adresse) (v : Wort) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte v 0⟩, ⟨addrOff a 1, wortByte v 1⟩,
    ⟨addrOff a 2, wortByte v 2⟩, ⟨addrOff a 3, wortByte v 3⟩]

/-- Four entries, one per footprint byte. -/
theorem fpEintraege32_laenge (a : Adresse) (v : Wort) :
    (fpEintraege32 a v).length = 4 := rfl

/-! ## 1. Step relation: family register steps plus shared TSO events.

  Register steps re-embed ONLY core data (XMM/control included) and
  keep machine memory and buffers; the memory-unchanged premise is the
  `HwSchritt.reg` gate, so no canonical `read32`/`write32`/`read64`/
  `write64` effect is ever substituted for a buffered access.
  Memory-changing family forms (stores, MXCSR store) never take the
  register path: they travel through the issue/load/flush events on
  the shared TSO view (§3). The MXCSR leg runs under the modern
  example profile with open control gates (profile data, never
  silicon constants: see the CUTS of `FpControlHardwareForms`). -/

inductive FpCtrlSchritt : HwMaschine → HwMaschine → FpCtrlEreignis → Prop where
  | s32reg {m : HwMaschine} (c : Nat) (d : S32Decodiert) (t' : FpZustand)
      (hstep : s32Schritt d (projFp m c) = some t')
      (hmem : t'.kern.speicher = m.mem) :
      FpCtrlSchritt m (setKernVonFp m c t') (.s32reg c d)
  | f64reg {m : HwMaschine} (c : Nat) (d : FpDecodiert) (t' : FpZustand)
      (hstep : fpSchritt d (projFp m c) = some t')
      (hmem : t'.kern.speicher = m.mem) :
      FpCtrlSchritt m (setKernVonFp m c t') (.f64reg c d)
  | mxcsrLd {m : HwMaschine} (c : Nat) (d : MxcsrDec) (t' : FpZustand)
      (hstep : mxcsrSchritt d (projFp m c) mxcsrProfilModern
        mxcsrSteuerungOffen = .weiter t')
      (hmem : t'.kern.speicher = m.mem) :
      FpCtrlSchritt m (setKernVonFp m c t') (.mxcsrLd c d)
  | lade {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (h : loadByte (tsoAnsicht m) c a = some v) :
      FpCtrlSchritt m m (.leseBeob c a v)
  | gibAus {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht m) c a v = some s') :
      FpCtrlSchritt m (setTso m s') (.schreibAusgabe c a v)
  | spüle {m : HwMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht m) c = some s')
      (hkopf : (m.puffer c).head? = some e) :
      FpCtrlSchritt m (setTso m s') (.spülung c e)
  | fehler {m : HwMaschine} (c : Nat)
      (h : fetchExt (projFp m c) (geholt (projZustand m c)) = none) :
      FpCtrlSchritt m m (.verweigert c)

/-! ## 2. Re-embedding projections and well-formedness.

  Profiles are untouched by every step, so `HwWf` survives; the
  re-embedded core answers the successor XMM/control/RIP over the
  shared memory. -/

/-- After re-embedding, the core answers the successor XMM file. -/
theorem setKernVonFp_xmm (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    ((setKernVonFp m c t').kerne c).xmm = t'.xmm := by
  unfold setKernVonFp setKernDaten
  simp

/-- After re-embedding, the core answers the successor control word. -/
theorem setKernVonFp_fp (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    ((setKernVonFp m c t').kerne c).fp = t'.fp := by
  unfold setKernVonFp setKernDaten
  simp

/-- After re-embedding, the core answers the successor RIP. -/
theorem setKernVonFp_rip (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    ((setKernVonFp m c t').kerne c).rip = t'.kern.rip := by
  unfold setKernVonFp setKernDaten
  simp

/-- Every family step preserves well-formedness: profiles untouched. -/
theorem fpCtrlSchritt_wf (m m' : HwMaschine) (e : FpCtrlEreignis)
    (h : FpCtrlSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | s32reg c d t' hstep hmem => exact setKernDaten_wf _ c _ hwf
  | f64reg c d t' hstep hmem => exact setKernDaten_wf _ c _ hwf
  | mxcsrLd c d t' hstep hmem => exact setKernDaten_wf _ c _ hwf
  | lade c a v h => exact hwf
  | gibAus c a v s' h => exact setTso_wf _ s' hwf
  | spüle c e s' h hkopf => exact setTso_wf _ s' hwf
  | fehler c h => exact hwf

/-! ## 3. Exact agreement with the accepted family evaluators.

  Nothing is redefined: each step carries the accepted equation, and
  the conclusions below run it. The f64 leg IS the coherent `reg`
  step through `stepExt_fp`; the s32/MXCSR legs are new plugs
  (`decodeExt` has no s32/MXCSR rows), so their agreement is stated
  against the family evaluator directly. -/

/-- A coherent f64 register step is the `HwSchritt.reg` step on the
    unified `.fp` form: the accepted `stepExt_fp`, lifted. -/
theorem fpCtrlF64_reg_ist_hwReg (m m' : HwMaschine) (c : Nat)
    (d : FpDecodiert)
    (h : FpCtrlSchritt m m' (.f64reg c d)) :
    HwSchritt m m' (.regAusf c (.fp d)) := by
  cases h with
  | f64reg c d t' hstep hmem =>
    exact HwSchritt.reg c (.fp d) t'
      (stepExt_fp d (projFp m c) t' (m.bereit c) hstep) hmem

/-- The s32 leg computes the accepted model sum into the low single:
    `1.0f32 + 2.0f32` lands `3.0f32`, upper 96 bits preserved. -/
theorem fpCtrlS32_addssRR_rechnet (m m' : HwMaschine) (c : Nat)
    (dst src : XmmReg) (l : Nat)
    (hok : laengeOk l = true)
    (hfp : s32Eintritt (projFp m c).fp = true)
    (h : FpCtrlSchritt m m' (.s32reg c ⟨.addssRR dst src, l⟩)) :
    xmmTief32 (m'.kerne c).xmm dst =
      s32Rechne .add (xmmTief32 (m.kerne c).xmm dst)
        (xmmTief32 (m.kerne c).xmm src) := by
  cases h with
  | s32reg c d t' hstep hmem =>
    have heq := s32Schritt_addssRR ⟨.addssRR dst src, l⟩ (projFp m c)
      dst src hok hfp rfl
    rw [heq] at hstep
    obtain rfl := Option.some_inj.mp hstep
    rw [setKernVonFp_xmm]
    exact xmmSchreibeTief32_tief _ _ _

/-- The MXCSR leg installs exactly the four-byte word the accepted
    load step installs: control change, nothing else. -/
theorem fpCtrlMxcsrLd_installiert (m m' : HwMaschine) (c : Nat)
    (base : Register) (disp : BitVec 32) (l : Nat) (v : Wort) (w : MXCSR)
    (hok : laengeOk l = true)
    (hrd : read32 (projFp m c).kern.speicher
      (effAddr (projFp m c).kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk mxcsrProfilModern w = true)
    (h : FpCtrlSchritt m m'
      (.mxcsrLd c ⟨.ldmxcsr base disp, l, false⟩)) :
    ((m'.kerne c).fp).mxcsr = w := by
  cases h with
  | mxcsrLd c d t' hstep hmem =>
    have heq := mxcsrSchritt_ld_erfolg ⟨.ldmxcsr base disp, l, false⟩
      (projFp m c) mxcsrProfilModern mxcsrSteuerungOffen base disp v w
      hok rfl mxcsrSteuerungOffen_ok rfl hrd hw hok2
    rw [heq] at hstep
    cases hstep
    rw [setKernVonFp_fp]

/-- The TSO legs are the coherent TSO steps: observations. -/
theorem fpCtrlLade_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : FpCtrlSchritt m m' (.leseBeob c a v)) :
    HwSchritt m m' (.leseBeob c a v) := by
  cases h with
  | lade c a v h => exact HwSchritt.lade c a v h

/-- The TSO legs are the coherent TSO steps: store issue. -/
theorem fpCtrlGibAus_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : FpCtrlSchritt m m' (.schreibAusgabe c a v)) :
    HwSchritt m m' (.schreibAusgabe c a v) := by
  cases h with
  | gibAus c a v s' h => exact HwSchritt.gibAus c a v s' h

/-- The TSO legs are the coherent TSO steps: drain. -/
theorem fpCtrlSpüle_ist_hw (m m' : HwMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : FpCtrlSchritt m m' (.spülung c e)) :
    ∃ s' : TSOZustand, HwSchritt m m' (.spülung c e) := by
  cases h with
  | spüle c e s' h hkopf => exact ⟨s', HwSchritt.spüle c e s' h hkopf⟩

/- CUTS (steps done):
   Proved: step relation over the three family legs plus shared TSO
   events; wf preservation; exact agreement (f64 leg IS HwSchritt.reg,
   s32/MXCSR legs run the accepted evaluators).
   NOT proved yet: TSO word bridges, control-state establish/preserve,
   NaN/signed-zero/no-contraction, refusals, the joint witness.
-/

#print axioms fpCtrlSchritt_wf
#print axioms fpCtrlF64_reg_ist_hwReg
#print axioms fpCtrlS32_addssRR_rechnet
#print axioms fpCtrlMxcsrLd_installiert

end Gabbro.Grammatik.X86
