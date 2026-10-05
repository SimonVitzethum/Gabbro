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
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat32HardwareForms
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloatHardwareForms
import Grammatik.X86.Befehle.Gleitkomma.FpControlHardwareForms
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloatCodec

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

/-! ## 4. TSO word bridges: FP words travel as byte issues.

  A 32-bit FP store is NEVER the canonical `write32` effect: it is
  four `issueByte` steps over `fpEintraege32` (the 64-bit leg reuses
  `hwWortAusgabe` unchanged). Loads observe through `loadByte`
  (forwarding included); a load with no pending entry reads canonical
  memory. The word assembly itself stays the accepted
  `read32`/`write32` definition, cited, never redone. -/

/-- A 32-bit FP store on the machine: four buffered byte issues over
    `fpEintraege32`, never the canonical word effect. -/
def fpCtrlAusgabe32 (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) : Option HwMaschine :=
  match issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => none
  | some s' => some (setTso m s')

/-- A successful 32-bit FP store appends exactly the four canonical
    entries to the acting core's buffer. -/
theorem fpCtrlAusgabe32_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : fpCtrlAusgabe32 m c a v = some m') :
    m'.puffer c = m.puffer c ++ fpEintraege32 a v := by
  unfold fpCtrlAusgabe32 at h
  cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact issueListe_haengt_an (tsoAnsicht m) s' c _ h1

/-- A 32-bit FP store changes no canonical byte. -/
theorem fpCtrlAusgabe32_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fpCtrlAusgabe32 m c a v = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold fpCtrlAusgabe32 at h
  cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact issueListe_kein_speicher (tsoAnsicht m) s' c _ h1 x

/-- A word fold preserves every permission: only buffers grow. -/
theorem issueListe_erhaelt_berechtigungen (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    s'.mem.lesbar = s.mem.lesbar ∧
      s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      obtain ⟨hl1, hs1, ha1⟩ :=
        issue_erhaelt_berechtigungen s s1 c e.addr e.wert h1
      obtain ⟨hl2, hs2, ha2⟩ := ih s1 s' h
      exact ⟨by rw [hl2, hl1], by rw [hs2, hs1], by rw [ha2, ha1]⟩

/-- A 32-bit FP store changes no permission. -/
theorem fpCtrlAusgabe32_berechtigungen (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (h : fpCtrlAusgabe32 m c a v = some m') :
    m'.mem.lesbar = m.mem.lesbar ∧
      m'.mem.schreibbar = m.mem.schreibbar ∧
      m'.mem.ausfuehrbar = m.mem.ausfuehrbar := by
  unfold fpCtrlAusgabe32 at h
  cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact issueListe_erhaelt_berechtigungen (tsoAnsicht m) s' c _ h1

/-- A 32-bit FP store preserves well-formedness. -/
theorem fpCtrlAusgabe32_wf (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort)
    (h : fpCtrlAusgabe32 m c a v = some m') (hwf : HwWf m) :
    HwWf m' := by
  unfold fpCtrlAusgabe32 at h
  cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact setTso_wf _ s' hwf

/-- Youngest match at footprint byte 0 is the first entry. -/
theorem neuestens_fp32_0 (a : Adresse) (v : Wort) :
    neuestens (fpEintraege32 a v) (addrOff a 0) =
      some (wortByte v 0) := by
  have h10 : addrOff a 1 ≠ addrOff a 0 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  have h20 : addrOff a 2 ≠ addrOff a 0 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  have h30 : addrOff a 3 ≠ addrOff a 0 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  simp [fpEintraege32, neuestens, h10, h20, h30]

/-- Youngest match at footprint byte 1 is the second entry. -/
theorem neuestens_fp32_1 (a : Adresse) (v : Wort) :
    neuestens (fpEintraege32 a v) (addrOff a 1) =
      some (wortByte v 1) := by
  have h21 : addrOff a 2 ≠ addrOff a 1 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  have h31 : addrOff a 3 ≠ addrOff a 1 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  simp [fpEintraege32, neuestens, h21, h31]

/-- Youngest match at footprint byte 2 is the third entry. -/
theorem neuestens_fp32_2 (a : Adresse) (v : Wort) :
    neuestens (fpEintraege32 a v) (addrOff a 2) =
      some (wortByte v 2) := by
  have h32 : addrOff a 3 ≠ addrOff a 2 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  simp [fpEintraege32, neuestens, h32]

/-- Youngest match at footprint byte 3 is the fourth entry. -/
theorem neuestens_fp32_3 (a : Adresse) (v : Wort) :
    neuestens (fpEintraege32 a v) (addrOff a 3) =
      some (wortByte v 3) := by
  simp [fpEintraege32, neuestens]

/-- Forwarding, all four bytes: after core `c` stores word `v` at
    readable `a` from an empty own buffer, core `c` observes every
    stored byte -- the accepted single-byte `load_nach_issue`,
    lifted per footprint byte. -/
theorem fpCtrlWeiterleitung32 (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort)
    (hempty : m.puffer c = [])
    (hrd0 : m.mem.lesbar (addrOff a 0) = true)
    (hrd1 : m.mem.lesbar (addrOff a 1) = true)
    (hrd2 : m.mem.lesbar (addrOff a 2) = true)
    (hrd3 : m.mem.lesbar (addrOff a 3) = true)
    (h : fpCtrlAusgabe32 m c a v = some m') :
    loadByte (tsoAnsicht m') c (addrOff a 0) = some (wortByte v 0) ∧
    loadByte (tsoAnsicht m') c (addrOff a 1) = some (wortByte v 1) ∧
    loadByte (tsoAnsicht m') c (addrOff a 2) = some (wortByte v 2) ∧
    loadByte (tsoAnsicht m') c (addrOff a 3) = some (wortByte v 3) := by
  have hbuf := fpCtrlAusgabe32_puffer m c a v m' h
  have hperm := fpCtrlAusgabe32_berechtigungen m m' c a v h
  have hbuf' : (tsoAnsicht m').puffer c = fpEintraege32 a v := by
    show m'.puffer c = fpEintraege32 a v
    rw [hbuf, hempty, List.nil_append]
  have hrd0' : (tsoAnsicht m').mem.lesbar (addrOff a 0) = true := by
    show m'.mem.lesbar (addrOff a 0) = true
    rw [hperm.1]
    exact hrd0
  have hrd1' : (tsoAnsicht m').mem.lesbar (addrOff a 1) = true := by
    show m'.mem.lesbar (addrOff a 1) = true
    rw [hperm.1]
    exact hrd1
  have hrd2' : (tsoAnsicht m').mem.lesbar (addrOff a 2) = true := by
    show m'.mem.lesbar (addrOff a 2) = true
    rw [hperm.1]
    exact hrd2
  have hrd3' : (tsoAnsicht m').mem.lesbar (addrOff a 3) = true := by
    show m'.mem.lesbar (addrOff a 3) = true
    rw [hperm.1]
    exact hrd3
  have e0 : loadByte (tsoAnsicht m') c (addrOff a 0) =
      some (wortByte v 0) := by
    simp [loadByte, hbuf', neuestens_fp32_0, hrd0']
  have e1 : loadByte (tsoAnsicht m') c (addrOff a 1) =
      some (wortByte v 1) := by
    simp [loadByte, hbuf', neuestens_fp32_1, hrd1']
  have e2 : loadByte (tsoAnsicht m') c (addrOff a 2) =
      some (wortByte v 2) := by
    simp [loadByte, hbuf', neuestens_fp32_2, hrd2']
  have e3 : loadByte (tsoAnsicht m') c (addrOff a 3) =
      some (wortByte v 3) := by
    simp [loadByte, hbuf', neuestens_fp32_3, hrd3']
  exact ⟨e0, e1, e2, e3⟩

/-- Observation without a pending entry reads canonical memory: the
    accepted `load_ohne_eintrag`, lifted to the machine view. -/
theorem fpCtrlLade_beobachtet (m : HwMaschine) (c : Nat) (a : Adresse)
    (hmiss : neuestens (m.puffer c) a = none)
    (hrd : m.mem.lesbar a = true) :
    loadByte (tsoAnsicht m) c a = some (m.mem.bytes a) :=
  load_ohne_eintrag (tsoAnsicht m) c a hmiss hrd

/-! ## 5. Control state: RNE established and preserved.

  No admitted scalar step touches the control word: the f64 leg
  keeps it by the accepted `fpSchritt_erhaelt_fp` (all fifteen
  forms), the s32 leg by the same case analysis below (all
  seventeen forms, proved here since the family states only
  per-form frames). Hence rounding mode (RNE) survives every
  register step. Establishment is the MXCSR load leg: the reset
  word installs admission, while the FTZ word stays
  source-inadmissible although architecturally loadable. -/

/-- The s32 admission gate is the f64 admission gate. -/
theorem s32Eintritt_ist_fpEintritt (k : FPKontext) :
    s32Eintritt k = fpEintritt k := rfl

/-- No s32 step touches the control word: all seventeen forms write
    only `kern`/`xmm`. -/
theorem s32Schritt_erhaelt_fp (d : S32Decodiert) (t t' : FpZustand)
    (hstep : s32Schritt d t = some t') : t'.fp = t.fp := by
  cases hok : laengeOk d.laenge with
  | false =>
    rw [s32Schritt_laenge_verweigert d t hok] at hstep
    cases hstep
  | true =>
    cases hfp : s32Eintritt t.fp with
    | false =>
      rw [s32Schritt_profil_verweigert d t hok hfp] at hstep
      cases hstep
    | true =>
      cases hbef : d.befehl with
      | addssRR dst src =>
        rw [s32Schritt_addssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | subssRR dst src =>
        rw [s32Schritt_subssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | mulssRR dst src =>
        rw [s32Schritt_mulssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | divssRR dst src =>
        rw [s32Schritt_divssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | addssRM dst base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_addssRM_verweigert d t dst base disp hok hfp hbef
            hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_addssRM_erfolg d t dst base disp v hok hfp hbef
            hrd] at hstep
          cases hstep
          rfl
      | subssRM dst base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_subssRM_verweigert d t dst base disp hok hfp hbef
            hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_subssRM_erfolg d t dst base disp v hok hfp hbef
            hrd] at hstep
          cases hstep
          rfl
      | mulssRM dst base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_mulssRM_verweigert d t dst base disp hok hfp hbef
            hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_mulssRM_erfolg d t dst base disp v hok hfp hbef
            hrd] at hstep
          cases hstep
          rfl
      | divssRM dst base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_divssRM_verweigert d t dst base disp hok hfp hbef
            hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_divssRM_erfolg d t dst base disp v hok hfp hbef
            hrd] at hstep
          cases hstep
          rfl
      | ucomissRR lhs rhs =>
        rw [s32Schritt_ucomissRR d t lhs rhs hok hfp hbef] at hstep
        cases hstep
        rfl
      | ucomissRM lhs base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_ucomissRM_verweigert d t lhs base disp hok hfp
            hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_ucomissRM_erfolg d t lhs base disp v hok hfp
            hbef hrd] at hstep
          cases hstep
          rfl
      | movssRR dst src =>
        rw [s32Schritt_movssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | movssLade dst base disp =>
        cases hrd : read32 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [s32Schritt_movssLade_verweigert d t dst base disp hok hfp
            hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [s32Schritt_movssLade_erfolg d t dst base disp v hok hfp
            hbef hrd] at hstep
          cases hstep
          rfl
      | movssSpeichere base src disp =>
        cases hwr : write32 t.kern.speicher (effAddr t.kern base disp)
            (BitVec.setWidth 64 (xmmTief32 t.xmm src)) with
        | none =>
          rw [s32Schritt_movssSpeichere_verweigert d t base src disp hok
            hfp hbef hwr] at hstep
          cases hstep
        | some m =>
          rw [s32Schritt_movssSpeichere_erfolg d t base src disp m hok
            hfp hbef hwr] at hstep
          cases hstep
          rfl
      | cvtss2sdRR dst src =>
        rw [s32Schritt_cvtss2sdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | cvtsd2ssRR dst src =>
        rw [s32Schritt_cvtsd2ssRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      | cvtsi2ss dst src is64 =>
        rw [s32Schritt_cvtsi2ss d t dst src is64 hok hfp hbef] at hstep
        cases hstep
        rfl
      | cvttss2si dst src is64 =>
        rw [s32Schritt_cvttss2si d t dst src is64 hok hfp hbef] at hstep
        cases hstep
        rfl

/-- Admission is preserved across s32 steps. -/
theorem s32Schritt_erhaelt_Eintritt (d : S32Decodiert) (t t' : FpZustand)
    (hstep : s32Schritt d t = some t') :
    s32Eintritt t'.fp = s32Eintritt t.fp := by
  rw [s32Schritt_erhaelt_fp d t t' hstep]

/-- Every s32 step keeps the rounding mode. -/
theorem fpCtrlS32_erhaelt_rne (d : S32Decodiert) (t t' : FpZustand)
    (hstep : s32Schritt d t = some t') :
    mxcsrRundungRNE t'.fp.mxcsr = mxcsrRundungRNE t.fp.mxcsr := by
  rw [s32Schritt_erhaelt_fp d t t' hstep]

/-- Every f64 step keeps the rounding mode. -/
theorem fpCtrlF64_erhaelt_rne (d : FpDecodiert) (t t' : FpZustand)
    (hstep : fpSchritt d t = some t') :
    mxcsrRundungRNE t'.fp.mxcsr = mxcsrRundungRNE t.fp.mxcsr := by
  rw [fpSchritt_erhaelt_fp d t t' hstep]

/-- A coherent s32 register step keeps the core rounding mode. -/
theorem fpCtrlS32_erhaelt_rneMaschine (m m' : HwMaschine) (c : Nat)
    (d : S32Decodiert)
    (h : FpCtrlSchritt m m' (.s32reg c d)) :
    mxcsrRundungRNE ((m'.kerne c).fp).mxcsr =
      mxcsrRundungRNE ((m.kerne c).fp).mxcsr := by
  cases h with
  | s32reg c d t' hstep hmem =>
    have hfp : t'.fp = (m.kerne c).fp :=
      s32Schritt_erhaelt_fp d (projFp m c) t' hstep
    rw [setKernVonFp_fp, hfp]

/-- A coherent f64 register step keeps the core rounding mode. -/
theorem fpCtrlF64_erhaelt_rneMaschine (m m' : HwMaschine) (c : Nat)
    (d : FpDecodiert)
    (h : FpCtrlSchritt m m' (.f64reg c d)) :
    mxcsrRundungRNE ((m'.kerne c).fp).mxcsr =
      mxcsrRundungRNE ((m.kerne c).fp).mxcsr := by
  cases h with
  | f64reg c d t' hstep hmem =>
    have hfp : t'.fp = (m.kerne c).fp :=
      fpSchritt_erhaelt_fp d (projFp m c) t' hstep
    rw [setKernVonFp_fp, hfp]

/-- The reset word is round-to-nearest. -/
theorem fpCtrlReset_rne : mxcsrRundungRNE (0x1F80 : MXCSR) = true := by
  decide

/-- The reset word is admitted. -/
theorem fpCtrlReset_einlass : fpEintritt (⟨0x1F80⟩ : FPKontext) = true :=
  kontextReset_gueltig

/-- The FTZ word is architecturally loadable but source-inadmissible:
    hardware `#GP` and source refusal apart, on the machine. -/
theorem fpCtrlFtz_spalt :
    ldmxcsrArchOk mxcsrProfilModern 0x9F80 = true ∧
      fpEintritt (⟨0x9F80⟩ : FPKontext) = false :=
  ⟨ldmxcsrArchOk_ftz_modern, mxcsr_ftz_verweigert⟩

/-- A coherent reset-word MXCSR load establishes admission on the
    core: the installed word is admitted. -/
theorem fpCtrlMxcsrReset_stellt_her (m m' : HwMaschine) (c : Nat)
    (base : Register) (disp : BitVec 32) (l : Nat) (v : Wort)
    (hok : laengeOk l = true)
    (hrd : read32 (projFp m c).kern.speicher
      (effAddr (projFp m c).kern base disp) = some v)
    (hwv : v = BitVec.ofNat 64 0x1F80)
    (h : FpCtrlSchritt m m'
      (.mxcsrLd c ⟨.ldmxcsr base disp, l, false⟩)) :
    fpEintritt (m'.kerne c).fp = true := by
  have hw : (BitVec.ofNat 32 (v.toNat % 4294967296) : MXCSR) = 0x1F80 := by
    rw [hwv]
    decide
  have hok2 : ldmxcsrArchOk mxcsrProfilModern
      (BitVec.ofNat 32 (v.toNat % 4294967296)) = true := by
    rw [hw]
    exact ldmxcsrArchOk_reset_modern
  have hinst := fpCtrlMxcsrLd_installiert m m' c base disp l v
    (BitVec.ofNat 32 (v.toNat % 4294967296)) hok hrd rfl hok2 h
  have hfin : mxcsrGueltig ((m'.kerne c).fp.mxcsr) = true := by
    rw [hinst, hw]
    exact mxcsr_standard
  exact hfin

/-! ## 6. IEEE observations: NaN, signed zero, no contraction.

  All arithmetic is the accepted kernel, cited, never recomputed:
  masked `0/0` classifies NaN (both widths), `+0 + -0 = +0` (both
  widths), and binary32 is never silently promoted to binary64
  (the `2^24` stall where binary64 advances). -/

/-- Masked binary32 `0/0` classifies NaN. -/
theorem fpCtrlS32_nan : Gleitkomma.klasse Gleitkomma.f32
    (bites32 (s32Rechne .div 0 0)) = .nan :=
  s32_null_durch_null_nan

/-- Two distinct binary64 NaN payloads take the unordered row. -/
theorem fpCtrlF64_nan_ungeordnet : ucomiFlags
    (bites64 0x7FF0000000000001)
    (bites64 0x7FF0000000000002) =
    ⟨true, true, some false, true, false, false⟩ :=
  fpHwNan_ungeordnet

/-- Binary32 signed zero: `+0 + -0 = +0`. -/
theorem fpCtrlS32_plusnull :
    s32Rechne .add 0x00000000 0x80000000 = 0x00000000 :=
  s32_plusnull_minusnull

/-- Binary64 signed zero: `+0.0 + -0.0 = +0.0`. -/
theorem fpCtrlF64_plusnull : fpRechne .add 0 0x8000000000000000 = 0 :=
  add_plusnull_minusnull

/-- NO CONTRACTION: binary32 stalls at `2^24` while binary64
    advances -- a promoted implementation would agree with f64. -/
theorem fpCtrlKeineKontraktion :
    s32Rechne .add 0x4B800000 0x3F800000 = 0x4B800000 ∧
      muster64 (fadd64 (bites64 0x4330000000000000)
        (bites64 0x3FF0000000000000)) ≠ 0x4330000000000000 :=
  ⟨s32_stallt_bei_2hoch24, s32_f64_steigt_weiter⟩

/-! ## 7. Refusals and the 32-bit group discipline.

  Bad lengths, refused profiles, LOCK-prefixed MXCSR (`#UD` in the
  family, hence no `.weiter` and no machine step), unreadable loads
  and unwritable issues all refuse explicitly. The 32-bit group
  predicate pins coherence the other way: a partial buffer is no
  group, a foreign footprint entry breaks it, and a successful
  `fpCtrlAusgabe32` from an empty foreign-free buffer establishes
  it. The 64-bit leg reuses `WortGruppe` unchanged. -/

/-- A bad decode length admits no coherent s32 step. -/
theorem fpCtrlS32_laenge_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : S32Decodiert)
    (hok : laengeOk d.laenge = false)
    (h : FpCtrlSchritt m m' (.s32reg c d)) : False := by
  cases h with
  | s32reg c d t' hstep hmem =>
    rw [s32Schritt_laenge_verweigert _ _ hok] at hstep
    cases hstep

/-- A refused profile admits no coherent f64 step. -/
theorem fpCtrlF64_profil_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : FpDecodiert)
    (hfp : fpEintritt (projFp m c).fp = false)
    (h : FpCtrlSchritt m m' (.f64reg c d)) : False := by
  cases h with
  | f64reg c d t' hstep hmem =>
    have hok := (fpSchritt_zugelassen_heisst d (projFp m c) t' hstep).1
    rw [fpSchritt_profil_verweigert _ _ hok hfp] at hstep
    cases hstep

/-- A LOCK-prefixed MXCSR form faults with `#UD` in the family, so
    it never yields `.weiter` and admits no coherent load step. -/
theorem fpCtrlMxcsrLock_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : MxcsrDec)
    (hok : laengeOk d.laenge = true)
    (hlock : d.gesperrt = true)
    (h : FpCtrlSchritt m m' (.mxcsrLd c d)) : False := by
  cases h with
  | mxcsrLd c d t' hstep hmem =>
    rw [mxcsrSchritt_gesperrt_ud _ _ _ _ hok hlock] at hstep
    cases hstep

/-- An unreadable byte admits no coherent observation. -/
theorem fpCtrlLaden_ohne_lesbar_kein_schritt (m m' : HwMaschine)
    (c : Nat) (a : Adresse) (v : Byte)
    (hperm : (tsoAnsicht m).mem.lesbar a = false)
    (h : FpCtrlSchritt m m' (.leseBeob c a v)) : False := by
  cases h with
  | lade c a v hload =>
    rw [load_verweigert _ _ _ hperm] at hload
    cases hload

/-- An unwritable byte admits no coherent store issue. -/
theorem fpCtrlAusgabe_ohne_schreibbar_kein_schritt (m m' : HwMaschine)
    (c : Nat) (a : Adresse) (v : Byte)
    (hperm : (tsoAnsicht m).mem.schreibbar a = false)
    (h : FpCtrlSchritt m m' (.schreibAusgabe c a v)) : False := by
  cases h with
  | gibAus c a v s' hissue =>
    rw [issue_verweigert _ _ _ _ hperm] at hissue
    cases hissue

/-- The four footprint addresses of a 32-bit access. -/
def fpFuss32 (a : Adresse) : List Adresse :=
  (List.range 4).map (addrOff a)

/-- Foreign-footprint freedom over the four bytes: no other core
    holds a pending entry inside `fpFuss32 a`. -/
def FpFremdFrei32 (s : TSOZustand) (c : Nat) (a : Adresse) : Prop :=
  ∀ d : Nat, d ≠ c → ∀ e : TSOEintrag,
    e ∈ s.puffer d → e.addr ∉ fpFuss32 a

/-- The 32-bit group: the acting core carries exactly the four
    canonical entries and no foreign entry touches the footprint. -/
def FpGruppe32 (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Wort) : Prop :=
  s.puffer c = fpEintraege32 a v ∧ FpFremdFrei32 s c a

/-- A partial 32-bit buffer is no group: tearing refused. -/
theorem fpGruppe32_teilwort (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Wort)
    (hne : s.puffer c ≠ fpEintraege32 a v) :
    ¬ FpGruppe32 s c a v := by
  intro hgrp
  exact hne hgrp.1

/-- A foreign footprint entry breaks the 32-bit group. -/
theorem fpGruppe32_fremd (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Wort) (d : Nat) (hne : d ≠ c)
    (e : TSOEintrag) (hmem : e ∈ s.puffer d)
    (hfuss : e.addr ∈ fpFuss32 a) :
    ¬ FpGruppe32 s c a v := by
  intro hgrp
  exact (hgrp.2 d hne e hmem) hfuss

/-- A successful 32-bit FP store from an empty foreign-free buffer
    establishes the group. -/
theorem fpCtrlAusgabe32_gruppe (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hempty : m.puffer c = [])
    (hfrei : FpFremdFrei32 (tsoAnsicht m) c a)
    (h : fpCtrlAusgabe32 m c a v = some m') :
    FpGruppe32 (tsoAnsicht m') c a v := by
  have hbuf := fpCtrlAusgabe32_puffer m c a v m' h
  unfold fpCtrlAusgabe32 at h
  cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    constructor
    · show s'.puffer c = fpEintraege32 a v
      have hb := issueListe_haengt_an (tsoAnsicht m) s' c _ h1
      show s'.puffer c = fpEintraege32 a v
      rw [hb]
      show m.puffer c ++ fpEintraege32 a v = fpEintraege32 a v
      rw [hempty]
      rfl
    · intro d hne e hmem
      have hfr := issueListe_anderer_kern (tsoAnsicht m) s' c _ d hne h1
      change e ∈ s'.puffer d at hmem
      rw [hfr] at hmem
      exact hfrei d hne e hmem

/-! ## 8. Joint witness: two cores, fetched REX divide, s32 add,
   buffered FP store, forward-only-to-owner, drain, MXCSR reset.

  Core 0 fetches a REX `DIVSD xmm0, xmm1` (`1.0 / +0.0 = +inf`)
  from actual executable bytes, runs a register `ADDSS` (`1.0f32 +
  2.0f32 = 3.0f32`, upper 96 bits preserved), issues the 32-bit
  result as four buffered TSO bytes (owner forwards, foreign core
  still reads zero), drains them into shared memory (both cores
  observe the word), and loads the reset MXCSR word (admission
  established). Core 1 idles on non-executable memory and refuses.
  Every observation below is a closed decidable evaluation. -/

/-- Witness image: REX `DIVSD xmm0, xmm1` (5 bytes). -/
def fpCtrlWitBild : List Byte := fpHwEncodeArithRR .div .xmm0 .xmm1

/-- Witness bytes: the image at 4096, the reset word `0x1F80`
    little-endian at 8196, zeroes elsewhere. -/
def fpCtrlWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match fpCtrlWitBild[a.toNat - 4096]? with
    | some b => b
    | none =>
      if a.toNat = 8196 then BitVec.ofNat 8 0x80
      else if a.toNat = 8197 then BitVec.ofNat 8 0x1F
      else if a.toNat = 8198 then BitVec.ofNat 8 0
      else if a.toNat = 8199 then BitVec.ofNat 8 0
      else BitVec.ofNat 8 0

/-- Witness code permission: exactly the 5 image bytes. -/
def fpCtrlWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 5)

/-- Witness data permission: eight bytes at 8192. -/
def fpCtrlWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 8)

/-- Witness shared memory: code execute-only, data read/write. -/
def fpCtrlWitMem : Speicher :=
  { bytes := fpCtrlWitBytes, lesbar := fpCtrlWitDaten,
    schreibbar := fpCtrlWitDaten, ausfuehrbar := fpCtrlWitCode }

/-- Witness XMM: `xmm0 = 1.0f64`, `xmm1 = +0.0`, `xmm2/xmm3` carry
    `1.0f32`/`2.0f32` in the low single with nonzero upper bits. -/
def fpCtrlWitXmm : XmmDatei := fun q =>
  if q = .xmm0 then vecJoin 0x3FF0000000000000 0
  else if q = .xmm1 then vecJoin 0 0
  else if q = .xmm2 then 0x0000000000000000000000013F800000
  else if q = .xmm3 then 0x00000000000000000000000240000000
  else vecJoin 0 0

/-- Witness core-0 registers: `rax` points at the data cell. -/
def fpCtrlWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def fpCtrlWitKern : Nat → HwKern
  | 0 => ⟨fpCtrlWitReg0, zeugeFlags, BitVec.ofNat 64 4096, fpCtrlWitXmm,
      kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def fpCtrlWitM0 : HwMaschine :=
  ⟨fpCtrlWitMem, fpCtrlWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness data address. -/
def fpCtrlWitAdr : Adresse := BitVec.ofNat 64 8192

/-- The witness machine is well-formed: full silicon admits all. -/
theorem fpCtrlWitM0_wf : HwWf fpCtrlWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The image is five bytes long. -/
theorem fpCtrlWitBild_len : fpCtrlWitBild.length = 5 :=
  fpHwLen_rr .div .xmm0 .xmm1

/-- The fetch window holds exactly the image. -/
theorem fpCtrlWit_geholt :
    fpHwGeholt (projFp fpCtrlWitM0 0) = fpCtrlWitBild := by
  decide

/-- The five image bytes carry execute permission. -/
theorem fpCtrlWit_perm5 :
    ausfuehrbarN (projFp fpCtrlWitM0 0).kern.speicher
      (projFp fpCtrlWitM0 0).kern.rip 5 = true := by
  decide

/-- Five-byte decode lengths are checked data. -/
theorem fpCtrlWit_laenge5 : laengeOk 5 = true := by
  decide

/-- Seven-byte decode lengths are checked data. -/
theorem fpCtrlWit_laenge7 : laengeOk 7 = true := by
  decide

/-- The witness `xmm0` holds `1.0f64`. -/
theorem fpCtrlWit_tief0 :
    xmmTief fpCtrlWitXmm XmmReg.xmm0 = 0x3FF0000000000000 := by
  decide

/-- The witness `xmm1` holds `+0.0`. -/
theorem fpCtrlWit_tief1 : xmmTief fpCtrlWitXmm XmmReg.xmm1 = 0 := by
  decide

/-- The witness `xmm2` low single holds `1.0f32`. -/
theorem fpCtrlWit_tief32_2 :
    xmmTief32 fpCtrlWitXmm XmmReg.xmm2 = 0x3F800000 := by
  decide

/-- The witness `xmm3` low single holds `2.0f32`. -/
theorem fpCtrlWit_tief32_3 :
    xmmTief32 fpCtrlWitXmm XmmReg.xmm3 = 0x40000000 := by
  decide

/-- The witness `xmm2` upper 96 bits are nonzero (value 1). -/
theorem fpCtrlWit_hoch96_2 :
    (fpCtrlWitXmm XmmReg.xmm2).toNat / 2 ^ 32 = 1 := by
  decide

/-- The data cell starts zeroed. -/
theorem fpCtrlWit_anfang_null :
    fpCtrlWitMem.bytes fpCtrlWitAdr = BitVec.ofNat 8 0 := by
  decide

/-- The reset word reads back through the real four-byte load. -/
theorem fpCtrlWit_liest_reset :
    read32 fpCtrlWitMem (BitVec.ofNat 64 8196) =
      some (BitVec.ofNat 64 0x1F80) := by
  decide

/-- The MXCSR witness address: `rax + 4` is `8196`. -/
theorem fpCtrlWit_effAddr4 :
    effAddr (projFp fpCtrlWitM0 0).kern Register.rax 4 =
      BitVec.ofNat 64 8196 := by
  decide

/-- The store witness address: `rax + 0` is `8192`. -/
theorem fpCtrlWit_effAddr0 :
    effAddr (projFp fpCtrlWitM0 0).kern Register.rax 0 =
      fpCtrlWitAdr := by
  decide

/-- Fetch from the actual image yields the REX DIVSD form. -/
theorem fpCtrlWit_fetch1 :
    fpHwFetchDekodiert (projFp fpCtrlWitM0 0) =
      some (⟨.divsdRR .xmm0 .xmm1, 5⟩, []) := by
  have hbytes : fpHwGeholt (projFp fpCtrlWitM0 0) =
      fpHwEncodeArithRR .div .xmm0 .xmm1 := by
    rw [fpCtrlWit_geholt, fpCtrlWitBild]
  have hrt := fpHwRoundtrip_arithRR .div .xmm0 .xmm1 []
  have hred : fpHwArithRR .div .xmm0 .xmm1 = .divsdRR .xmm0 .xmm1 := rfl
  have hlen : (fpHwEncodeArithRR .div .xmm0 .xmm1).length = 5 :=
    fpHwLen_rr .div .xmm0 .xmm1
  rw [hlen, hred] at hrt
  have hdec : fpHwDecode (fpHwGeholt (projFp fpCtrlWitM0 0)) =
      some (⟨.divsdRR .xmm0 .xmm1, 5⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt (projFp fpCtrlWitM0 0)).length = 5 := by
    rw [fpCtrlWit_geholt, fpCtrlWitBild_len]
  have hnil : (([] : List Byte).length : Nat) = 0 := rfl
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, hnil, fpCtrlWit_laenge5, fpCtrlWit_perm5]
  decide

/-- The conversion gate is open on the DIVSD form. -/
theorem fpCtrlWit_gate1 :
    fpHwCvttZugelassen (.divsdRR .xmm0 .xmm1)
      (projFp fpCtrlWitM0 0) = true := rfl

/-! ## 9. Reached steps I: fetched divide and scalar add.

  The fetched REX `DIVSD` runs the accepted divide special case
  (`1.0 / +0.0 = +inf`); the register `ADDSS` runs the accepted
  binary32 sum (`1.0f32 + 2.0f32 = 3.0f32`) with the upper 96 bits
  preserved. Both ride `FpCtrlSchritt` with the memory-unchanged
  gate discharged by the accepted frame lemmas. -/

/-- State after the fetched divide: `xmm0` holds `+∞`. -/
def fpCtrlWitT1 : FpZustand :=
  { projFp fpCtrlWitM0 0 with
    kern := { (projFp fpCtrlWitM0 0).kern with
      rip := ripNach (projFp fpCtrlWitM0 0).kern.rip 5 },
    xmm := xmmSchreibeTief (projFp fpCtrlWitM0 0).xmm .xmm0
      0x7FF0000000000000 }

/-- Machine after the divide. -/
def fpCtrlWitM1 : HwMaschine := setKernVonFp fpCtrlWitM0 0 fpCtrlWitT1

/-- The witness runs under the admitted profile. -/
theorem fpCtrlWit_fp0 : fpEintritt (projFp fpCtrlWitM0 0).fp = true :=
  fpEintritt_reset

/-- Reached divide step on the coherent machine. -/
theorem fpCtrlWit_schritt1 :
    FpCtrlSchritt fpCtrlWitM0 fpCtrlWitM1
      (.f64reg 0 ⟨.divsdRR .xmm0 .xmm1, 5⟩) := by
  have ht0 : xmmTief (projFp fpCtrlWitM0 0).xmm .xmm0 =
      0x3FF0000000000000 := fpCtrlWit_tief0
  have ht1 : xmmTief (projFp fpCtrlWitM0 0).xmm .xmm1 = 0 :=
    fpCtrlWit_tief1
  have hs := fpSchritt_divsdRR ⟨.divsdRR .xmm0 .xmm1, 5⟩
    (projFp fpCtrlWitM0 0) .xmm0 .xmm1 fpCtrlWit_laenge5 fpCtrlWit_fp0
    rfl
  rw [ht0, ht1, div_eins_durch_null] at hs
  exact FpCtrlSchritt.f64reg 0 _ fpCtrlWitT1 hs rfl

/-- After the divide, `xmm0` holds `+∞` on the machine. -/
theorem fpCtrlWit_m1_inf :
    xmmTief (fpCtrlWitM1.kerne 0).xmm .xmm0 = 0x7FF0000000000000 := by
  simp only [fpCtrlWitM1, setKernVonFp_xmm, fpCtrlWitT1]
  exact xmmSchreibeTief_tief _ _ _

/-- After the divide, RIP stands past the 5-byte form. -/
theorem fpCtrlWit_m1_rip :
    (fpCtrlWitM1.kerne 0).rip = BitVec.ofNat 64 4101 := by
  simp only [fpCtrlWitM1, setKernVonFp_rip, fpCtrlWitT1]
  decide

/-- The divide keeps the rounding mode on the machine. -/
theorem fpCtrlWit_m1_rne :
    mxcsrRundungRNE ((fpCtrlWitM1.kerne 0).fp).mxcsr =
      mxcsrRundungRNE ((fpCtrlWitM0.kerne 0).fp).mxcsr :=
  fpCtrlF64_erhaelt_rneMaschine _ _ _ _ fpCtrlWit_schritt1

/-- State after the scalar add: low single `3.0f32`. -/
def fpCtrlWitT2 : FpZustand :=
  { projFp fpCtrlWitM1 0 with
    kern := { (projFp fpCtrlWitM1 0).kern with
      rip := ripNach (projFp fpCtrlWitM1 0).kern.rip 4 },
    xmm := xmmSchreibeTief32 (projFp fpCtrlWitM1 0).xmm .xmm2
      0x40400000 }

/-- Machine after the scalar add. -/
def fpCtrlWitM2 : HwMaschine := setKernVonFp fpCtrlWitM1 0 fpCtrlWitT2

/-- The divide preserves the s32 operand singles. -/
theorem fpCtrlWit_m1_tief32_2 :
    xmmTief32 (projFp fpCtrlWitM1 0).xmm .xmm2 = 0x3F800000 := rfl

/-- The divide preserves the s32 operand singles. -/
theorem fpCtrlWit_m1_tief32_3 :
    xmmTief32 (projFp fpCtrlWitM1 0).xmm .xmm3 = 0x40000000 := rfl

/-- Reached scalar-add step on the coherent machine. -/
theorem fpCtrlWit_schritt2 :
    FpCtrlSchritt fpCtrlWitM1 fpCtrlWitM2
      (.s32reg 0 ⟨.addssRR .xmm2 .xmm3, 4⟩) := by
  have hfp : s32Eintritt (projFp fpCtrlWitM1 0).fp = true := by
    have h1 : (projFp fpCtrlWitM1 0).fp = kontextReset := rfl
    rw [h1]
    exact s32Eintritt_reset
  have h4 : laengeOk 4 = true := by decide
  have hs := s32Schritt_addssRR ⟨.addssRR .xmm2 .xmm3, 4⟩
    (projFp fpCtrlWitM1 0) .xmm2 .xmm3 h4 hfp rfl
  rw [fpCtrlWit_m1_tief32_2, fpCtrlWit_m1_tief32_3,
    s32_eins_plus_zwei] at hs
  exact FpCtrlSchritt.s32reg 0 _ fpCtrlWitT2 hs rfl

/-- After the add, the low single holds `3.0f32` on the machine. -/
theorem fpCtrlWit_m2_tief32 :
    xmmTief32 (fpCtrlWitM2.kerne 0).xmm .xmm2 = 0x40400000 := by
  simp only [fpCtrlWitM2, setKernVonFp_xmm, fpCtrlWitT2]
  exact xmmSchreibeTief32_tief _ _ _

/-- After the add, the upper 96 bits survive on the machine. -/
theorem fpCtrlWit_m2_hoch96 :
    ((fpCtrlWitM2.kerne 0).xmm .xmm2).toNat / 2 ^ 32 = 1 := by
  have hset : (fpCtrlWitM2.kerne 0).xmm =
      xmmSchreibeTief32 (projFp fpCtrlWitM1 0).xmm .xmm2 0x40400000 := by
    simp only [fpCtrlWitM2, setKernVonFp_xmm, fpCtrlWitT2]
  rw [hset, xmmSchreibeTief32_hoch96]
  have hb : ((projFp fpCtrlWitM1 0).xmm .xmm2).toNat / 2 ^ 32 = 1 := rfl
  exact hb

/-- The add keeps the rounding mode on the machine. -/
theorem fpCtrlWit_m2_rne :
    mxcsrRundungRNE ((fpCtrlWitM2.kerne 0).fp).mxcsr =
      mxcsrRundungRNE ((fpCtrlWitM1.kerne 0).fp).mxcsr :=
  fpCtrlS32_erhaelt_rneMaschine _ _ _ _ fpCtrlWit_schritt2

/-! ## 10. Reached steps II: buffered store, drain, MXCSR load.

  Core 0 issues the 32-bit result as four buffered TSO bytes
  (forwarded to the owner only), drains them into shared memory
  (the word reads back on both cores: `0` becomes `0x40400000`),
  and installs the reset MXCSR word (admission established).
  Core 1 refuses the fetch throughout. -/

/-- The stored 32-bit word: `3.0f32` as a target word. -/
def fpCtrlWitWert : Wort := BitVec.ofNat 64 0x40400000

/-- Core 0 issues the result word at the data cell. -/
def fpCtrlWitM3 : Option HwMaschine :=
  fpCtrlAusgabe32 fpCtrlWitM2 0 fpCtrlWitAdr fpCtrlWitWert

/-- Core 0 observes its own third footprint byte (forwarding). -/
def fpCtrlWitLoadEigen : Option (Option Byte) :=
  match fpCtrlWitM3 with
  | some m => some (loadByte (tsoAnsicht m) 0 (addrOff fpCtrlWitAdr 2))
  | none => none

/-- Core 1 observes the old third footprint byte (no forwarding). -/
def fpCtrlWitLoadFremd : Option (Option Byte) :=
  match fpCtrlWitM3 with
  | some m => some (loadByte (tsoAnsicht m) 1 (addrOff fpCtrlWitAdr 2))
  | none => none

/-- Forwarding: core 0 reads its own unflushed `0x40`. -/
theorem fpCtrlWit_weiterleitung :
    fpCtrlWitLoadEigen = some (some (BitVec.ofNat 8 0x40)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem fpCtrlWit_fremd_alt :
    fpCtrlWitLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Core 0 drains its oldest entry. -/
def fpCtrlWitF1 : Option HwMaschine :=
  match fpCtrlWitM3 with
  | some m =>
    match flushKern (tsoAnsicht m) 0 with
    | some s => some (setTso m s)
    | none => none
  | none => none

/-- Second drain. -/
def fpCtrlWitF2 : Option HwMaschine :=
  match fpCtrlWitF1 with
  | some m =>
    match flushKern (tsoAnsicht m) 0 with
    | some s => some (setTso m s)
    | none => none
  | none => none

/-- Third drain. -/
def fpCtrlWitF3 : Option HwMaschine :=
  match fpCtrlWitF2 with
  | some m =>
    match flushKern (tsoAnsicht m) 0 with
    | some s => some (setTso m s)
    | none => none
  | none => none

/-- Fourth drain: the footprint is fully installed. -/
def fpCtrlWitF4 : Option HwMaschine :=
  match fpCtrlWitF3 with
  | some m =>
    match flushKern (tsoAnsicht m) 0 with
    | some s => some (setTso m s)
    | none => none
  | none => none

/-- The shared word after the drain. -/
def fpCtrlWitNachFlush : Option (Option Wort) :=
  match fpCtrlWitF4 with
  | some m => some (read32 m.mem fpCtrlWitAdr)
  | none => none

/-- The drain changes shared memory: the cell reads `3.0f32`. -/
theorem fpCtrlWit_spuelung_aendert :
    fpCtrlWitNachFlush = some (some fpCtrlWitWert) := by
  decide

/-- Core 1 reads the drained byte from shared memory. -/
def fpCtrlWitFremdNach : Option (Option Byte) :=
  match fpCtrlWitF4 with
  | some m => some (loadByte (tsoAnsicht m) 1 (addrOff fpCtrlWitAdr 2))
  | none => none

/-- After the drain core 1 observes the new byte. -/
theorem fpCtrlWit_fremd_neu :
    fpCtrlWitFremdNach = some (some (BitVec.ofNat 8 0x40)) := by
  decide

/-- State after the MXCSR reset-word load. -/
def fpCtrlWitMxcsrT : FpZustand :=
  { projFp fpCtrlWitM0 0 with
    kern := { (projFp fpCtrlWitM0 0).kern with
      rip := ripNach (projFp fpCtrlWitM0 0).kern.rip 7 },
    fp := ⟨0x1F80⟩ }

/-- Machine after the MXCSR reset-word load. -/
def fpCtrlWitMxcsrM : HwMaschine :=
  setKernVonFp fpCtrlWitM0 0 fpCtrlWitMxcsrT

/-- Reached MXCSR reset-word load on the coherent machine. -/
theorem fpCtrlWit_mxcsr_schritt :
    FpCtrlSchritt fpCtrlWitM0 fpCtrlWitMxcsrM
      (.mxcsrLd 0 ⟨.ldmxcsr .rax 4, 7, false⟩) := by
  have hrd : read32 (projFp fpCtrlWitM0 0).kern.speicher
      (effAddr (projFp fpCtrlWitM0 0).kern Register.rax 4) =
      some (BitVec.ofNat 64 0x1F80) := by
    show read32 fpCtrlWitMem _ = _
    rw [fpCtrlWit_effAddr4]
    exact fpCtrlWit_liest_reset
  have hs := mxcsrSchritt_ld_erfolg ⟨.ldmxcsr .rax 4, 7, false⟩
    (projFp fpCtrlWitM0 0) mxcsrProfilModern mxcsrSteuerungOffen
    .rax 4 (BitVec.ofNat 64 0x1F80) 0x1F80
    fpCtrlWit_laenge7 rfl mxcsrSteuerungOffen_ok rfl hrd rfl
    ldmxcsrArchOk_reset_modern
  exact FpCtrlSchritt.mxcsrLd 0 _ fpCtrlWitMxcsrT hs rfl

/-- The reset-word load establishes admission on the core. -/
theorem fpCtrlWit_mxcsr_einlass :
    fpEintritt (fpCtrlWitMxcsrM.kerne 0).fp = true :=
  fpCtrlReset_einlass

/-- Core 1 refuses: its RIP points at non-executable memory. -/
theorem fpCtrlWit_kern1_verweigert :
    hwByteschrittReg fpCtrlWitM0 1 = .verweigert := by
  rfl

/-! ## 11. Joint witness: a reached non-degenerate two-core run.

  Fetched REX divide (`+inf`), register s32 add (`3.0f32`, upper
  preserved), RNE preserved across both, buffered 32-bit store
  forwarded to the owner only, four-drain install (`0` becomes
  `0x40400000`, observed from both cores), MXCSR reset install
  (admission), core-1 refusal, NaN classification and the
  no-contraction split beside it. Non-degenerate: the drain
  changes actual shared memory while both cores participate. -/

/-- JOINT WITNESS (fetched FP run on the coherent machine). -/
theorem fpCtrl_zeuge :
    FpCtrlSchritt fpCtrlWitM0 fpCtrlWitM1
        (.f64reg 0 ⟨.divsdRR .xmm0 .xmm1, 5⟩) ∧
      xmmTief (fpCtrlWitM1.kerne 0).xmm .xmm0 = 0x7FF0000000000000 ∧
      FpCtrlSchritt fpCtrlWitM1 fpCtrlWitM2
        (.s32reg 0 ⟨.addssRR .xmm2 .xmm3, 4⟩) ∧
      xmmTief32 (fpCtrlWitM2.kerne 0).xmm .xmm2 = 0x40400000 ∧
      ((fpCtrlWitM2.kerne 0).xmm .xmm2).toNat / 2 ^ 32 = 1 ∧
      mxcsrRundungRNE ((fpCtrlWitM1.kerne 0).fp).mxcsr =
        mxcsrRundungRNE ((fpCtrlWitM0.kerne 0).fp).mxcsr ∧
      mxcsrRundungRNE ((fpCtrlWitM2.kerne 0).fp).mxcsr =
        mxcsrRundungRNE ((fpCtrlWitM1.kerne 0).fp).mxcsr ∧
      fpCtrlWitLoadEigen = some (some (BitVec.ofNat 8 0x40)) ∧
      fpCtrlWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      fpCtrlWitNachFlush = some (some fpCtrlWitWert) ∧
      fpCtrlWitFremdNach = some (some (BitVec.ofNat 8 0x40)) ∧
      FpCtrlSchritt fpCtrlWitM0 fpCtrlWitMxcsrM
        (.mxcsrLd 0 ⟨.ldmxcsr .rax 4, 7, false⟩) ∧
      fpEintritt (fpCtrlWitMxcsrM.kerne 0).fp = true ∧
      hwByteschrittReg fpCtrlWitM0 1 = .verweigert ∧
      Gleitkomma.klasse Gleitkomma.f32
        (bites32 (s32Rechne .div 0 0)) = .nan ∧
      HwWf fpCtrlWitM0 := by
  refine ⟨fpCtrlWit_schritt1, fpCtrlWit_m1_inf, fpCtrlWit_schritt2,
    fpCtrlWit_m2_tief32, fpCtrlWit_m2_hoch96, fpCtrlWit_m1_rne,
    fpCtrlWit_m2_rne, fpCtrlWit_weiterleitung, fpCtrlWit_fremd_alt,
    fpCtrlWit_spuelung_aendert, fpCtrlWit_fremd_neu,
    fpCtrlWit_mxcsr_schritt, fpCtrlWit_mxcsr_einlass,
    fpCtrlWit_kern1_verweigert, fpCtrlS32_nan, fpCtrlWitM0_wf⟩

/- CUTS: what is not proved here.

   Proved here, over the reused accepted vocabulary (`HardwareExecution`:
   `HwMaschine`/`HwSchritt`/`issueListe`/`setKernVonFp`/`setTso`;
   `ScalarFloat32HardwareForms`: `s32Schritt`; `ScalarFloatHardwareForms`:
   `fpSchritt` via `fpHwDecode`; `FpControlHardwareForms`:
   `mxcsrSchritt`; `TSO`: `issueByte`/`loadByte`/`flushKern`):
   - the family event type and step relation with the `HwSchritt.reg`
     memory-unchanged gate on every register leg; wf preservation;
     exact agreement (the f64 leg IS `HwSchritt.reg` through
     `stepExt_fp`; s32/MXCSR legs run the accepted evaluators, which
     are lifted, never redefined);
   - 32-bit FP stores as four byte issues (buffer, memory, permission
     frames, wf), per-byte owner forwarding, entry-free observation,
     and the 32-bit group with tearing/overlap refusals and
     establishment (64-bit stores reuse `hwWortAusgabe`/`WortGruppe`);
   - control state: s32/f64 steps keep the word (hence RNE) on states
     and on the machine; the reset word establishes RNE/admission
     through the coherent MXCSR load; the FTZ arch-vs-source split;
   - NaN (both widths), signed zero (both widths) and the
     no-contraction split, cited from the accepted kernel;
   - length/profile/LOCK/permission refusals, including the
     LOCK-prefixed MXCSR `#UD` (hence no machine step);
   - the reached two-core joint witness `fpCtrl_zeuge`: fetched REX
     divide, register s32 add with upper preservation, RNE on both
     legs, owner-only forwarding, four-drain install changing actual
     shared memory observed from both cores, MXCSR reset install,
     core-1 refusal, NaN classification.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted canonical
     subsets with self-consistency only. The Intel SDM edition 093
     extracts in `.tmp/HARDWARE-REFERENCES/` (prefix-before-REX
     order, MOVSS load-zeroes-upper, arithmetic-preserves-upper,
     UCOMISS flag rows, CVT semantics, MXCSR layout/reset `1F80H`,
     LDMXCSR/STMXCSR `NP 0F AE /2`/`/3`) are provenance, not proofs.
   - `decodeExt`/`fetchExt` carry no s32/MXCSR rows: those legs plug
     in through `FpCtrlSchritt`, not through the unified dispatcher;
     the REX leg reaches bytes only through the family fetchers
     (`fpHwFetchDekodiert`), and conversion-domain gating
     (`fpHwCvttZugelassen`) is cited, not re-proved, at the machine.
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the byte-drain groups; timing, power,
     interrupts and faults beyond the carried divide halt are
     absent; sticky-flag accumulation, SNaN/DAZ/FTZ execution and
     NaN payloads stay at the inherited family cuts.
-/

#print axioms fpCtrlSchritt_wf
#print axioms fpCtrlF64_reg_ist_hwReg
#print axioms fpCtrlS32_addssRR_rechnet
#print axioms fpCtrlMxcsrLd_installiert
#print axioms fpCtrlAusgabe32_wf
#print axioms fpCtrlWeiterleitung32
#print axioms fpCtrlLade_beobachtet
#print axioms s32Schritt_erhaelt_fp
#print axioms fpCtrlS32_erhaelt_rneMaschine
#print axioms fpCtrlMxcsrReset_stellt_her
#print axioms fpCtrlKeineKontraktion
#print axioms fpCtrlF64_profil_kein_schritt
#print axioms fpCtrlMxcsrLock_kein_schritt
#print axioms fpCtrlAusgabe32_gruppe
#print axioms fpCtrlWit_schritt1
#print axioms fpCtrlWit_schritt2
#print axioms fpCtrlWit_mxcsr_schritt
#print axioms fpCtrl_zeuge

end Gabbro.Grammatik.X86
