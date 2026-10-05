/-
  File:      Grammatik/X86/Avx2State.lean
  Subject:   AVX2 YMM upper-half state, XCR0 gating and zeroing rules.

  Lane 1241 (hardware completion): the YMM register file as upper
  128-bit halves keyed by the shared low-half names (YMMn low 128 =
  XMMn, reuse of `XmmReg`/`XmmDatei`), the AVX2 enabled-state gate
  (CPUID AVX presence, CR4.OSXSAVE, XCR0 bits 1 and 2 via the reused
  `xcr0AvxBereit`, control freedom via the reused `kontrollSseFrei`;
  closed gate = #UD outcome in the accepted `ArchFehler` vocabulary,
  never executed), the VEX 128-bit zeroing rule, the legacy-SSE
  preservation rule, VZEROUPPER/VZEROALL effects, and an extended
  step relation embedding `HwSchritt` exactly on its hardware leg.

  Manual provenance: Intel SDM Vol. 2A Table 2-21 / Vol. 2B VEX
  prefix description (gating shape) and the VZEROUPPER/VZEROALL
  entries (zeroing shape), as extracted in the earlier
  MUSE-REPORT-660 hardware references. Silicon correspondence of
  each bit position stays OPEN and is claimed nowhere. SSE/AVX
  transition-penalty timing is NOT modelled (timing out of scope).
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.HardwareFaults
import Grammatik.X86.HardwareExecution
import Grammatik.X86.TSO
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- YMM upper-half file: bits 255:128 of each YMM register, keyed by
    the shared low-half name. The low 128 bits live in `XmmDatei`. -/
abbrev YmmDatei := XmmReg → Vektor

/-- The clean upper file: no AVX stain on any register. -/
def ymmNull : YmmDatei := fun _ => 0

/-! ## 2. AVX2 enabled-state gate.

  The checked conjunction for the optional 256-bit tier: silicon
  AVX presence (CPUID), XCR0 AVX readiness (bits 2:1 via the reused
  `xcr0AvxBereit`: x87 AND SSE AND AVX), control freedom (the reused
  `kontrollSseFrei`: no emulation, no task switch, OS FXSR) plus
  CR4.OSXSAVE, and the OS vector-state bit. Either side alone
  admits nothing. -/

/-- Control freedom for AVX: the accepted SSE freedom plus OSXSAVE. -/
def avx2KontrollFrei (k : KontrollBild) : Bool :=
  kontrollSseFrei k && k.cr4Osxsave

/-- Checked AVX2 readiness: silicon AVX, XCR0 AVX state, control
    freedom with OSXSAVE, OS vector-state bit. -/
def avx2ZustandBereit (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (b : BereitProfil) : Bool :=
  cpu.hatAvx && xcr0AvxBereit x && avx2KontrollFrei k && b.osXmm

/-- Admission needs silicon AVX. -/
theorem avx2_braucht_cpu (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = true) :
    cpu.hatAvx = true := by
  simp only [avx2ZustandBereit, Bool.and_eq_true] at h
  exact h.1.1.1

/-- Admission needs XCR0 AVX readiness (bits 2:1). -/
theorem avx2_braucht_xcr0 (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = true) :
    xcr0AvxBereit x = true := by
  simp only [avx2ZustandBereit, Bool.and_eq_true] at h
  exact h.1.1.2

/-- Admission needs control freedom with OSXSAVE. -/
theorem avx2_braucht_kontrolle (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = true) :
    avx2KontrollFrei k = true := by
  simp only [avx2ZustandBereit, Bool.and_eq_true] at h
  exact h.1.2

/-- Admission needs the OS vector-state bit. -/
theorem avx2_braucht_osxmm (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = true) :
    b.osXmm = true := by
  simp only [avx2ZustandBereit, Bool.and_eq_true] at h
  exact h.2

/-- Missing silicon AVX refuses, whatever the rest claims. -/
theorem avx2_ohne_cpu (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (hcpu : cpu.hatAvx = false) :
    avx2ZustandBereit cpu x k b = false := by
  unfold avx2ZustandBereit
  rw [hcpu]
  simp

/-- Missing XCR0 AVX readiness refuses. -/
theorem avx2_ohne_xcr0 (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (hx : xcr0AvxBereit x = false) :
    avx2ZustandBereit cpu x k b = false := by
  unfold avx2ZustandBereit
  cases hcpu : cpu.hatAvx <;> simp_all

/-- Missing OSXSAVE refuses. -/
theorem avx2_ohne_osxsave (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (hk : k.cr4Osxsave = false) :
    avx2ZustandBereit cpu x k b = false := by
  unfold avx2ZustandBereit avx2KontrollFrei
  simp_all

/-- A cleared OS vector-state bit refuses. -/
theorem avx2_ohne_osxmm (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (hos : b.osXmm = false) :
    avx2ZustandBereit cpu x k b = false := by
  unfold avx2ZustandBereit
  rw [hos]
  simp

/-- Witness silicon: AVX present (SSE2 alongside, AVX2 row only). -/
def avxZeugeCpu : CpuMerkmal := ⟨true, true⟩

/-- Witness XCR0: x87, SSE and AVX state set. -/
def avxZeugeXcr0 : Xcr0Bild := ⟨true, true, true⟩

/-- Witness readiness holds: the AVX2 gate admits. -/
theorem avx2_zeuge_bereit :
    avx2ZustandBereit avxZeugeCpu avxZeugeXcr0 basisKontrolle
      basisBereit = true := by
  decide

/-- Baseline refusal: the SSE baseline CPU has no AVX bit. -/
theorem avx2_basis_verweigert :
    avx2ZustandBereit basisCpu basisXcr0 basisKontrolle
      basisBereit = false := by
  decide

/-! ## 3. Closed gate = #UD outcome.

  A VEX-encoded form with a closed gate faults as #UD (accepted
  `ArchFehler` vocabulary, invalid-opcode class): the outcome is a
  hardware fault, never execution and never a silent substitution.
  An open gate carries no fault. -/

/-- Gate outcome: closed admits nothing and faults #UD, open runs. -/
def avx2Fehler (zugelassen : Bool) : Option ArchFehler :=
  match zugelassen with
  | true => none
  | false => some .ud

/-- A closed gate faults as #UD. -/
theorem avx2Fehler_ud (zugelassen : Bool)
    (h : zugelassen = false) :
    avx2Fehler zugelassen = some .ud := by
  simp [avx2Fehler, h]

/-- An open gate carries no fault. -/
theorem avx2Fehler_kein (zugelassen : Bool)
    (h : zugelassen = true) :
    avx2Fehler zugelassen = none := by
  simp [avx2Fehler, h]

/-- Gate-level outcome: the AVX2 readiness decides fault or silence. -/
def avx2TorFehler (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil) : Option ArchFehler :=
  avx2Fehler (avx2ZustandBereit cpu x k b)

/-- A refused gate IS the #UD outcome. -/
theorem avx2TorFehler_ud (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = false) :
    avx2TorFehler cpu x k b = some .ud := by
  unfold avx2TorFehler
  exact avx2Fehler_ud _ h

/-- An admitted gate carries no fault. -/
theorem avx2TorFehler_kein (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (b : BereitProfil)
    (h : avx2ZustandBereit cpu x k b = true) :
    avx2TorFehler cpu x k b = none := by
  unfold avx2TorFehler
  exact avx2Fehler_kein _ h

/-- Witness: the admitted gate carries no fault. -/
theorem avx2_zeuge_kein_fehler :
    avx2TorFehler avxZeugeCpu avxZeugeXcr0 basisKontrolle
      basisBereit = none :=
  avx2TorFehler_kein _ _ _ _ avx2_zeuge_bereit

/-- Witness: the baseline gate faults as #UD. -/
theorem avx2_basis_ud :
    avx2TorFehler basisCpu basisXcr0 basisKontrolle
      basisBereit = some .ud :=
  avx2TorFehler_ud _ _ _ _ avx2_basis_verweigert

/-! ## 4. Upper-half rules.

  One VEX-encoded 128-bit operation writes its 128-bit result into
  the destination low half and ZEROES bits 255:128 of the same
  register; every other upper half is kept. One legacy-SSE operation
  writes the low half and leaves ALL upper halves unchanged.
  VZEROUPPER zeroes every upper half and keeps every low half;
  VZEROALL zeroes both files. The low-half writes reuse the
  accepted `xmmSet` vocabulary; the upper file is the same function
  type, so its updates reuse the accepted `xmmSet` lemmas as well. -/

/-- VEX 128-bit upper effect: bits 255:128 of `dst` become zero. -/
def vexNulltOberhalb (y : YmmDatei) (dst : XmmReg) : YmmDatei :=
  xmmSet y dst 0

/-- The zeroed upper half reads back zero. -/
theorem vexNullt_liest_null (y : YmmDatei) (dst : XmmReg) :
    vexNulltOberhalb y dst dst = 0 := by
  unfold vexNulltOberhalb
  exact xmmSet_gleich _ _ _

/-- Every other upper half is kept. -/
theorem vexNullt_fremd (y : YmmDatei) (dst q : XmmReg)
    (h : q ≠ dst) :
    vexNulltOberhalb y dst q = y q := by
  unfold vexNulltOberhalb
  exact xmmSet_fremd _ _ _ _ h

/-- The full 256-bit register pair: low file and upper file. -/
abbrev YmmVoll := XmmDatei × YmmDatei

/-- VEX-encoded 128-bit step on the full pair: low half takes the
    result, the destination upper half is zeroed. -/
def vex128Voll (s : YmmVoll) (dst : XmmReg) (v : Vektor) : YmmVoll :=
  (xmmSet s.1 dst v, xmmSet s.2 dst 0)

/-- The VEX low half carries the result. -/
theorem vex128Voll_tief (s : YmmVoll) (dst : XmmReg) (v : Vektor) :
    (vex128Voll s dst v).1 dst = v := by
  unfold vex128Voll
  simp
  exact xmmSet_gleich _ _ _

/-- The VEX destination upper half is zeroed. -/
theorem vex128Voll_hoch_null (s : YmmVoll) (dst : XmmReg)
    (v : Vektor) :
    (vex128Voll s dst v).2 dst = 0 := by
  unfold vex128Voll
  simp
  exact xmmSet_gleich _ _ _

/-- Every other VEX upper half is kept. -/
theorem vex128Voll_hoch_fremd (s : YmmVoll) (dst q : XmmReg)
    (v : Vektor) (h : q ≠ dst) :
    (vex128Voll s dst v).2 q = s.2 q := by
  unfold vex128Voll
  simp
  exact xmmSet_fremd _ _ _ _ h

/-- Legacy-SSE 128-bit step on the full pair: low half takes the
    result, the upper file is untouched. -/
def legacy128Voll (s : YmmVoll) (dst : XmmReg)
    (v : Vektor) : YmmVoll :=
  (xmmSet s.1 dst v, s.2)

/-- The legacy low half carries the result. -/
theorem legacy128Voll_tief (s : YmmVoll) (dst : XmmReg)
    (v : Vektor) :
    (legacy128Voll s dst v).1 dst = v := by
  unfold legacy128Voll
  simp
  exact xmmSet_gleich _ _ _

/-- Legacy leaves the whole upper file unchanged. -/
theorem legacy128Voll_obere_bleibt (s : YmmVoll) (dst : XmmReg)
    (v : Vektor) :
    (legacy128Voll s dst v).2 = s.2 := by
  simp [legacy128Voll]

/-- VZEROUPPER on the full pair: every upper half zeroed, every low
    half kept. -/
def vzeroOberhalb (s : YmmVoll) : YmmVoll :=
  (s.1, fun _ => 0)

/-- After VZEROUPPER every upper half reads zero. -/
theorem vzeroOberhalb_null (s : YmmVoll) (q : XmmReg) :
    (vzeroOberhalb s).2 q = 0 := rfl

/-- VZEROUPPER keeps the whole low file. -/
theorem vzeroOberhalb_tief_bleibt (s : YmmVoll) :
    (vzeroOberhalb s).1 = s.1 := rfl

/-- VZEROALL result: both files zeroed (no input state kept). -/
def vzeroAlle : YmmVoll :=
  ((fun _ => 0), (fun _ => 0))

/-- After VZEROALL every low half reads zero. -/
theorem vzeroAlle_tief_null (q : XmmReg) :
    (vzeroAlle).1 q = 0 := rfl

/-- After VZEROALL every upper half reads zero. -/
theorem vzeroAlle_hoch_null (q : XmmReg) :
    (vzeroAlle).2 q = 0 := rfl

/-- The clean upper file reads zero everywhere. -/
theorem ymmNull_spur (q : XmmReg) : ymmNull q = 0 := rfl

/-! ## 5. Extended machine and gate-checked adapter.

  `YmmMaschine` pairs the coherent machine with one upper-half file
  per core. The hardware leg embeds `HwSchritt` exactly (same event,
  same successor, upper files untouched). The AVX legs run only
  behind the open gate and keep canonical memory, buffers and
  profiles; the refused AVX leg is the #UD outcome of §3, never a
  state. The `HwAdapter` plug below is the gate-checked register
  path over the accepted `adapterInteger666` vocabulary. -/

/-- Per-core low-half write on the coherent machine. -/
def setXmm (m : HwMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) : HwMaschine :=
  let k := m.kerne c
  setKernDaten m c ⟨k.register, k.flags, k.rip, xmmSet k.xmm dst v, k.fp⟩

/-- A low-half write keeps canonical memory. -/
theorem setXmm_speicher (m : HwMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) :
    (setXmm m c dst v).mem = m.mem := rfl

/-- A low-half write keeps every TSO buffer. -/
theorem setXmm_puffer (m : HwMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (d : Nat) :
    (setXmm m c dst v).puffer d = m.puffer d := rfl

/-- A low-half write preserves well-formedness (profiles untouched). -/
theorem setXmm_wf (m : HwMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (hwf : HwWf m) :
    HwWf (setXmm m c dst v) :=
  setKernDaten_wf _ _ _ hwf

/-- AVX2 state machine: coherent machine plus per-core upper files. -/
structure YmmMaschine where
  hw : HwMaschine
  ober : Nat → YmmDatei

/-- Well-formedness is the coherent well-formedness. -/
def YmmWf (s : YmmMaschine) : Prop := HwWf s.hw

/-- AVX2 state events. -/
inductive AvxZustandEreignis where
  | hwWeiter : HwEreignis → AvxZustandEreignis
  | vex128 : XmmReg → Vektor → AvxZustandEreignis
  | legacy128 : XmmReg → Vektor → AvxZustandEreignis
  | nullOben : AvxZustandEreignis
  | nullAlle : AvxZustandEreignis
  deriving DecidableEq, Repr

/-- VEX 128-bit state step behind the AVX2 gate: low half takes the
    result, the destination upper half is zeroed, refused (with the
    §3 #UD outcome beside it) when the gate is closed. -/
def ymmStepVex (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) : Option YmmMaschine :=
  if avx2ZustandBereit cpu x k (s.hw.bereit c) then
    some ⟨setXmm s.hw c dst v,
      fun d => if d = c then xmmSet (s.ober c) dst 0 else s.ober d⟩
  else none

/-- Admitted VEX step IS the stated successor. -/
theorem ymmStepVex_gleich (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = true) :
    ymmStepVex s c dst v cpu x k =
      some ⟨setXmm s.hw c dst v,
        fun d => if d = c then xmmSet (s.ober c) dst 0 else s.ober d⟩ := by
  unfold ymmStepVex
  rw [if_pos hg]

/-- Refused VEX step is no state. -/
theorem ymmStepVex_verweigert (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = false) :
    ymmStepVex s c dst v cpu x k = none := by
  unfold ymmStepVex
  rw [if_neg (by simp [hg])]

/-- The refused VEX step IS the #UD outcome: gate, fault and refusal
    agree on the same closed gate. -/
theorem ymmStepVex_ud (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = false) :
    ymmStepVex s c dst v cpu x k = none ∧
      avx2TorFehler cpu x k (s.hw.bereit c) = some .ud :=
  ⟨ymmStepVex_verweigert s c dst v cpu x k hg,
    avx2TorFehler_ud cpu x k (s.hw.bereit c) hg⟩

/-- After the admitted VEX step the destination upper half is zero. -/
theorem ymmStepVex_ober_null (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (s' : YmmMaschine)
    (hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = true)
    (hstep : ymmStepVex s c dst v cpu x k = some s') :
    (s'.ober c) dst = 0 := by
  have e := ymmStepVex_gleich s c dst v cpu x k hg
  rw [e] at hstep
  cases hstep
  simp
  exact xmmSet_gleich _ _ _

/-- The admitted VEX step preserves well-formedness. -/
theorem ymmStepVex_wf (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (s' : YmmMaschine)
    (hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = true)
    (hstep : ymmStepVex s c dst v cpu x k = some s')
    (hwf : YmmWf s) :
    YmmWf s' := by
  have e := ymmStepVex_gleich s c dst v cpu x k hg
  rw [e] at hstep
  cases hstep
  exact setXmm_wf _ _ _ _ hwf

/-- Legacy-SSE state step behind the accepted legacy gate: low half
    takes the result, the upper file is untouched. -/
def ymmStepLegacy (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal)
    (k : KontrollBild) : Option YmmMaschine :=
  if vektorLegacyZugelassen s.hw.hw (s.hw.bereit c) cpu k then
    some ⟨setXmm s.hw c dst v, s.ober⟩
  else none

/-- Admitted legacy step IS the stated successor. -/
theorem ymmStepLegacy_gleich (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal)
    (k : KontrollBild)
    (hg : vektorLegacyZugelassen s.hw.hw (s.hw.bereit c) cpu k
      = true) :
    ymmStepLegacy s c dst v cpu k =
      some ⟨setXmm s.hw c dst v, s.ober⟩ := by
  unfold ymmStepLegacy
  rw [if_pos hg]

/-- Refused legacy step is no state. -/
theorem ymmStepLegacy_verweigert (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal)
    (k : KontrollBild)
    (hg : vektorLegacyZugelassen s.hw.hw (s.hw.bereit c) cpu k
      = false) :
    ymmStepLegacy s c dst v cpu k = none := by
  unfold ymmStepLegacy
  rw [if_neg (by simp [hg])]

/-- The legacy step leaves the whole upper file unchanged. -/
theorem ymmStepLegacy_obere_bleibt (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal)
    (k : KontrollBild) (s' : YmmMaschine)
    (hg : vektorLegacyZugelassen s.hw.hw (s.hw.bereit c) cpu k
      = true)
    (hstep : ymmStepLegacy s c dst v cpu k = some s') :
    s'.ober = s.ober := by
  have e := ymmStepLegacy_gleich s c dst v cpu k hg
  rw [e] at hstep
  cases hstep
  rfl

/-- The legacy step preserves well-formedness. -/
theorem ymmStepLegacy_wf (s : YmmMaschine) (c : Nat) (dst : XmmReg)
    (v : Vektor) (cpu : CpuMerkmal)
    (k : KontrollBild) (s' : YmmMaschine)
    (hg : vektorLegacyZugelassen s.hw.hw (s.hw.bereit c) cpu k
      = true)
    (hstep : ymmStepLegacy s c dst v cpu k = some s')
    (hwf : YmmWf s) :
    YmmWf s' := by
  have e := ymmStepLegacy_gleich s c dst v cpu k hg
  rw [e] at hstep
  cases hstep
  exact setXmm_wf _ _ _ _ hwf

/-- VZEROUPPER state step on core `c`: every upper half of that core
    zeroed, low halves and every other core kept. Needs no gate: it
    only clears state. -/
def ymmStepVzeroUpper (s : YmmMaschine) (c : Nat) : YmmMaschine :=
  ⟨s.hw, fun d => if d = c then (fun _ => 0) else s.ober d⟩

/-- After VZEROUPPER every upper half of the core reads zero. -/
theorem ymmStepVzeroUpper_null (s : YmmMaschine) (c : Nat)
    (q : XmmReg) :
    ((ymmStepVzeroUpper s c).ober c) q = 0 := by
  unfold ymmStepVzeroUpper
  simp

/-- VZEROUPPER keeps every other core's upper file. -/
theorem ymmStepVzeroUpper_fremd (s : YmmMaschine) (c d : Nat)
    (h : d ≠ c) :
    (ymmStepVzeroUpper s c).ober d = s.ober d := by
  unfold ymmStepVzeroUpper
  simp [h]

/-- VZEROUPPER preserves well-formedness (hardware leg untouched). -/
theorem ymmStepVzeroUpper_wf (s : YmmMaschine) (c : Nat)
    (hwf : YmmWf s) :
    YmmWf (ymmStepVzeroUpper s c) :=
  hwf

/-- Per-core full clear of the low file (VZEROALL low half). -/
def setXmmAlle (m : HwMaschine) (c : Nat) : HwMaschine :=
  let k := m.kerne c
  setKernDaten m c ⟨k.register, k.flags, k.rip, fun _ => 0, k.fp⟩

/-- VZEROALL state step on core `c`: low and upper halves of that
    core zeroed. Needs no gate: it only clears state. -/
def ymmStepVzeroAll (s : YmmMaschine) (c : Nat) : YmmMaschine :=
  ⟨setXmmAlle s.hw c, fun d => if d = c then (fun _ => 0) else s.ober d⟩

/-- After VZEROALL every low half of the core reads zero. -/
theorem ymmStepVzeroAll_tief_null (s : YmmMaschine) (c : Nat)
    (q : XmmReg) :
    ((ymmStepVzeroAll s c).hw.kerne c).xmm q = 0 := by
  unfold ymmStepVzeroAll setXmmAlle setKernDaten
  simp

/-- After VZEROALL every upper half of the core reads zero. -/
theorem ymmStepVzeroAll_hoch_null (s : YmmMaschine) (c : Nat)
    (q : XmmReg) :
    ((ymmStepVzeroAll s c).ober c) q = 0 := by
  unfold ymmStepVzeroAll
  simp

/-- VZEROALL preserves well-formedness (profiles untouched). -/
theorem ymmStepVzeroAll_wf (s : YmmMaschine) (c : Nat)
    (hwf : YmmWf s) :
    YmmWf (ymmStepVzeroAll s c) :=
  setKernDaten_wf _ _ _ hwf

/-! ## 6. Hardware-leg embedding and gate-checked adapter.

  The hardware leg embeds `HwSchritt` exactly: same event, same
  successor machine, upper files untouched. The AVX legs touch no
  canonical memory, no buffer and no profile. The adapter plug is
  the gate-checked register path over the accepted
  `adapterInteger666` vocabulary: admitted behind the open gate,
  refused with the §3 #UD outcome beside it when closed. -/

/-- EXACT EMBEDDING: every coherent step lifts to the extended
    machine with upper files untouched, and stays a coherent step. -/
theorem ymmEinbettung (s : YmmMaschine) (m' : HwMaschine)
    (e : HwEreignis) (h : HwSchritt s.hw m' e) :
    ∃ s' : YmmMaschine,
      s'.hw = m' ∧ s'.ober = s.ober ∧ HwSchritt s.hw s'.hw e :=
  ⟨⟨m', s.ober⟩, rfl, rfl, h⟩

/-- The hardware-leg witness step used below: lifting preserves
    well-formedness exactly as the coherent step does. -/
theorem ymmEinbettung_wf (s : YmmMaschine) (m' : HwMaschine)
    (e : HwEreignis) (h : HwSchritt s.hw m' e)
    (hwf : YmmWf s) :
    YmmWf ⟨m', s.ober⟩ :=
  hwSchritt_wf s.hw m' e h hwf

/-- The AVX legs touch no canonical memory. -/
theorem ymmAvx_kein_speicher (s : YmmMaschine) (c : Nat)
    (dst : XmmReg) (v : Vektor) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (s' : YmmMaschine)
    (hv : ymmStepVex s c dst v cpu x k = some s') :
    s'.hw.mem = s.hw.mem := by
  have hg : avx2ZustandBereit cpu x k (s.hw.bereit c) = true := by
    cases hg' : avx2ZustandBereit cpu x k (s.hw.bereit c) with
    | true => rfl
    | false =>
      have hnone := ymmStepVex_verweigert s c dst v cpu x k hg'
      rw [hnone] at hv
      cases hv
  have e := ymmStepVex_gleich s c dst v cpu x k hg
  rw [e] at hv
  cases hv
  rfl

/-- Gate-checked register-path plug over the accepted integer
    vocabulary, indexed by the observed control state the coherent
    machine does not carry. -/
def adapterAvx2Tor (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) : HwAdapter ExtInstr :=
  ⟨fun m c i =>
    if avx2ZustandBereit cpu x k (m.bereit c) then
      adapterInteger666.schritt m c i
    else none⟩

/-- Admitted adapter step IS the accepted register path. -/
theorem adapterAvx2Tor_gleich (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (hg : avx2ZustandBereit cpu x k (m.bereit c) = true) :
    (adapterAvx2Tor cpu x k).schritt m c i =
      adapterInteger666.schritt m c i := by
  unfold adapterAvx2Tor
  simp only [hg, if_true]

/-- Refused adapter step is no state, with the #UD outcome beside it. -/
theorem adapterAvx2Tor_verweigert (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (hg : avx2ZustandBereit cpu x k (m.bereit c) = false) :
    (adapterAvx2Tor cpu x k).schritt m c i = none ∧
      avx2TorFehler cpu x k (m.bereit c) = some .ud := by
  refine ⟨?_, avx2TorFehler_ud cpu x k (m.bereit c) hg⟩
  show (if avx2ZustandBereit cpu x k (m.bereit c) = true then
    adapterInteger666.schritt m c i else none) = none
  rw [if_neg (by simp [hg])]

/-- Every adapter step preserves well-formedness: admitted steps are
    the accepted register path, refused steps are no state. -/
theorem adapterAvx2Tor_wf (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (m' : HwMaschine)
    (hg : avx2ZustandBereit cpu x k (m.bereit c) = true)
    (h : (adapterAvx2Tor cpu x k).schritt m c i = some m')
    (hwf : HwWf m) :
    HwWf m' := by
  have e := adapterAvx2Tor_gleich cpu x k m c i hg
  rw [e] at h
  have h2 : (match stepExt i (projFp m c) (m.bereit c) with
    | .weiter t' => some (setKernVonFp m c t')
    | _ => none) = some m' := h
  cases hstep : stepExt i (projFp m c) (m.bereit c) with
  | weiter t' =>
    rw [hstep] at h2
    simp at h2
    cases h2
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | halt =>
    rw [hstep] at h2
    simp at h2
  | verweigert =>
    rw [hstep] at h2
    simp at h2

/-! ## 7. Joint witness: two cores, YMM transitions, buffered store.

  Reached and non-degenerate: core 0 runs an admitted VEX 128-bit
  transition (upper zeroed), core 1 runs an admitted legacy
  transition (uppers kept), core 0 issues a buffered store byte that
  its own later load forwards while core 1 still observes canonical
  memory, and the drain observably changes canonical memory. The
  baseline gate stays refused with the #UD outcome beside the run. -/

/-- Witness core data: zeroed registers, cleared flags, zeroed XMM. -/
def avxWitKern : HwKern :=
  ⟨fun _ => 0, ⟨false, false, none, false, false, false⟩, 0,
    fun _ => 0, kontextReset⟩

/-- Witness coherent machine: permissive memory, two idle cores,
    full silicon, baseline readiness everywhere. -/
def avxWitHw : HwMaschine :=
  ⟨zeugenSpeicher, fun _ => avxWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem avxWitHw_wf : HwWf avxWitHw := by
  intro c f _
  cases f <;> rfl

/-- Witness extended state: clean upper files on every core. -/
def avxWitS0 : YmmMaschine := ⟨avxWitHw, fun _ => ymmNull⟩

/-- The witness extended state is well-formed. -/
theorem avxWitS0_wf : YmmWf avxWitS0 := avxWitHw_wf

/-- Core 0 gate: the AVX2 gate admits at baseline readiness. -/
theorem avxWitS0_tor0 :
    avx2ZustandBereit avxZeugeCpu avxZeugeXcr0 basisKontrolle
      (avxWitS0.hw.bereit 0) = true :=
  avx2_zeuge_bereit

/-- Core 1 legacy gate: the accepted legacy gate admits. -/
theorem avxWitS0_legacy1 :
    vektorLegacyZugelassen avxWitS0.hw.hw (avxWitS0.hw.bereit 1)
      avxZeugeCpu basisKontrolle = true := by
  decide

/-- Core 0 VEX successor: low half takes the result word. -/
def avxWitV : Vektor := BitVec.ofNat 128 1

/-- Core 0 runs the admitted VEX transition. -/
theorem avxWitS0_vex :
    ∃ s1 : YmmMaschine,
      ymmStepVex avxWitS0 0 .xmm0 avxWitV avxZeugeCpu avxZeugeXcr0
        basisKontrolle = some s1 ∧
      (s1.ober 0) .xmm0 = 0 ∧ YmmWf s1 := by
  have hg := avxWitS0_tor0
  have e := ymmStepVex_gleich avxWitS0 0 .xmm0 avxWitV avxZeugeCpu
    avxZeugeXcr0 basisKontrolle hg
  refine ⟨_, e, ?_, ?_⟩
  · have hnull := ymmStepVex_ober_null avxWitS0 0 .xmm0 avxWitV
      avxZeugeCpu avxZeugeXcr0 basisKontrolle _ hg e
    exact hnull
  · exact ymmStepVex_wf avxWitS0 0 .xmm0 avxWitV avxZeugeCpu
      avxZeugeXcr0 basisKontrolle _ hg e avxWitS0_wf

/-- Core 1 runs the admitted legacy transition with uppers kept. -/
theorem avxWitS0_legacy :
    ∃ s1 : YmmMaschine,
      ymmStepLegacy avxWitS0 1 .xmm2 avxWitV avxZeugeCpu
        basisKontrolle = some s1 ∧
      s1.ober = avxWitS0.ober ∧ YmmWf s1 := by
  have hg := avxWitS0_legacy1
  have e := ymmStepLegacy_gleich avxWitS0 1 .xmm2 avxWitV avxZeugeCpu
    basisKontrolle hg
  exact ⟨_, e, ymmStepLegacy_obere_bleibt avxWitS0 1 .xmm2 avxWitV
    avxZeugeCpu basisKontrolle _ hg e,
    ymmStepLegacy_wf avxWitS0 1 .xmm2 avxWitV avxZeugeCpu
      basisKontrolle _ hg e avxWitS0_wf⟩

/-! ## 8. Memory traffic: buffered store, owner-only forwarding,
  foreign canonical read, memory-changing drain.

  The TSO states below are the shared view both cores observe
  (`tsoAnsicht` of the witness machine). Core 0 issues one store
  byte: canonical memory unchanged, only its buffer grows. -/

/-- Witness TSO start: permissive memory, empty buffers. -/
def avxWitTso0 : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- Witness TSO after core 0 issues byte 1 at address zero. -/
def avxWitTso1 : TSOZustand :=
  ⟨zeugenSpeicher,
    pufferSetze avxWitTso0.puffer 0 ([] ++ [⟨0, 1⟩])⟩

/-- The issue goes through. -/
theorem avxWitTso_issue :
    issueByte avxWitTso0 0 (0 : Adresse) (1 : Byte) = some avxWitTso1 := by
  have hc : avxWitTso0.mem.schreibbar (0 : Adresse) = true := rfl
  unfold issueByte
  rw [if_pos hc]
  rfl

/-- The issue changes no canonical byte. -/
theorem avxWitTso_issue_kein_speicher (x : Adresse) :
    avxWitTso1.mem.bytes x = avxWitTso0.mem.bytes x := by
  have h := issue_kein_speicher avxWitTso0 avxWitTso1 0 (0 : Adresse)
    (1 : Byte) avxWitTso_issue x
  exact h

/-- Owner-only forwarding: core 0 loads its own issued byte. -/
theorem avxWitTso_fwd_eigen :
    loadByte avxWitTso1 0 (0 : Adresse) = some (1 : Byte) :=
  load_nach_issue avxWitTso0 avxWitTso1 0 (0 : Adresse) (1 : Byte)
    avxWitTso_issue (by rfl)

/-- Core 1 buffer is untouched by core 0 issue. -/
theorem avxWitTso_puffer1_leer :
    avxWitTso1.puffer 1 = [] := by
  have h := issue_anderer_kern avxWitTso0 avxWitTso1 0 (0 : Adresse)
    (1 : Byte) avxWitTso_issue (show (1 : Nat) ≠ 0 by decide)
  rw [h]
  rfl

/-- Foreign observation: core 1 still reads canonical memory. -/
theorem avxWitTso_fremd_kanonisch :
    loadByte avxWitTso1 1 (0 : Adresse) =
      some (avxWitTso1.mem.bytes (0 : Adresse)) := by
  apply load_ohne_eintrag
  · unfold neuestens
    rw [avxWitTso_puffer1_leer]
  · rfl

/-- Canonical memory still holds zero before the drain. -/
theorem avxWitTso_vor_nach :
    avxWitTso1.mem.bytes (0 : Adresse) = (0 : Byte) := rfl

/-- Witness TSO after core 0 drains: the byte lands in memory. -/
def avxWitTso2 : TSOZustand :=
  ⟨{ zeugenSpeicher with bytes :=
      fun x => if x = (0 : Adresse) then (1 : Byte)
        else zeugenSpeicher.bytes x },
    pufferSetze avxWitTso1.puffer 0 []⟩

/-- The drain goes through. -/
theorem avxWitTso_flush :
    flushKern avxWitTso1 0 = some avxWitTso2 := by
  unfold flushKern avxWitTso1 avxWitTso0
  simp only [pufferSetze_gleich, List.nil_append]
  rfl

/-- The drain observably changes canonical memory: zero becomes one. -/
theorem avxWitTso_speicher_aendert :
    avxWitTso2.mem.bytes (0 : Adresse) = (1 : Byte) ∧
      avxWitTso1.mem.bytes (0 : Adresse) = (0 : Byte) := by
  refine ⟨?_, avxWitTso_vor_nach⟩
  unfold avxWitTso2
  simp

/-- The coherent store-issue step on the witness machine: the same
    buffered byte as a `HwSchritt` event on core 0. -/
theorem avxWitHw_gibAus :
    HwSchritt avxWitHw (setTso avxWitHw avxWitTso1)
      (.schreibAusgabe 0 (0 : Adresse) (1 : Byte)) := by
  apply HwSchritt.gibAus
  exact avxWitTso_issue

/-! ## 9. Joint witness.

  Every premise joined on reached states: the admitted gate with no
  fault, the core-0 VEX transition with its zeroed upper, the core-1
  legacy transition with kept uppers, the refused baseline gate with
  its #UD outcome, the buffered issue with owner-only forwarding and
  the memory-changing drain, and the coherent issue step with
  preserved well-formedness. Non-degenerate: two cores transition,
  a store byte is issued, forwarded to its owner only, and drained
  into canonical memory. -/

/-- JOINT WITNESS: gate, both core transitions, refusal with #UD,
    buffered store with owner-only forwarding, memory-changing
    drain, and the coherent issue step. -/
theorem avx2Zustand_zeuge :
    ∃ (sVex sLeg : YmmMaschine),
      avx2ZustandBereit avxZeugeCpu avxZeugeXcr0 basisKontrolle
          basisBereit = true ∧
      avx2TorFehler avxZeugeCpu avxZeugeXcr0 basisKontrolle
          basisBereit = none ∧
      ymmStepVex avxWitS0 0 .xmm0 avxWitV avxZeugeCpu avxZeugeXcr0
          basisKontrolle = some sVex ∧
      (sVex.ober 0) .xmm0 = 0 ∧
      YmmWf sVex ∧
      ymmStepLegacy avxWitS0 1 .xmm2 avxWitV avxZeugeCpu
          basisKontrolle = some sLeg ∧
      sLeg.ober = avxWitS0.ober ∧
      YmmWf sLeg ∧
      avx2ZustandBereit basisCpu basisXcr0 basisKontrolle
          basisBereit = false ∧
      avx2TorFehler basisCpu basisXcr0 basisKontrolle
          basisBereit = some .ud ∧
      issueByte avxWitTso0 0 (0 : Adresse) (1 : Byte) = some avxWitTso1 ∧
      loadByte avxWitTso1 0 (0 : Adresse) = some (1 : Byte) ∧
      loadByte avxWitTso1 1 (0 : Adresse) =
        some (avxWitTso1.mem.bytes (0 : Adresse)) ∧
      avxWitTso2.mem.bytes (0 : Adresse) = (1 : Byte) ∧
      avxWitTso1.mem.bytes (0 : Adresse) = (0 : Byte) ∧
      HwSchritt avxWitHw (setTso avxWitHw avxWitTso1)
        (.schreibAusgabe 0 (0 : Adresse) (1 : Byte)) ∧
      HwWf (setTso avxWitHw avxWitTso1) := by
  obtain ⟨sV, hsV, hzV, hwV⟩ := avxWitS0_vex
  obtain ⟨sL, hsL, hkL, hwL⟩ := avxWitS0_legacy
  exact ⟨sV, sL, avx2_zeuge_bereit, avx2_zeuge_kein_fehler,
    hsV, hzV, hwV, hsL, hkL, hwL, avx2_basis_verweigert,
    avx2_basis_ud, avxWitTso_issue, avxWitTso_fwd_eigen,
    avxWitTso_fremd_kanonisch, avxWitTso_speicher_aendert.1,
    avxWitTso_speicher_aendert.2, avxWitHw_gibAus,
    setTso_wf _ _ avxWitHw_wf⟩

/- CUTS: what is not proved here.

   - No VEX decoder and no byte encoding: this file models YMM
     upper-half STATE and its transition rules, never instruction
     bytes. Canonical VEX prefix parsing, opcode maps and
     ModRM/SIB/displacement decoding stay with the VEX/Ops/Mem
     sibling lanes; nothing here claims a byte string executes.
   - No silicon correspondence: the gate bit positions (CPUID AVX
     presence, CR4.OSXSAVE, XCR0 bits 2:1), the #UD class for a
     closed gate, the VEX-128 zeroing shape and the
     VZEROUPPER/VZEROALL shapes are stated from the Intel SDM
     extracts named in the header toward MUSE-REPORT-660; each
     position stays OPEN and hardware truth is claimed nowhere.
   - The adapter (`adapterAvx2Tor`) is indexed by observed control
     state because the coherent `HwMaschine` carries no
     CPUID/XCR0/control registers: the observation-to-gate link
     (CPUID/XGETBV chain) stays with the feature-gate consumer
     (`ComposeFeatureGate`), reused by name and never re-proved.
   - Per-access TSO granularity of 256-bit memory traffic, GX
     refinement, source correspondence, budget transfer, progress,
     call-log effects and the SSE/AVX transition-penalty timing
     (stated as NOT modelled) stay open. No new `PerfMerkmal`
     is introduced: AVX2 remains an explicitly optional tier
     outside the finite admitted profile.
   - Execute permission of a concrete loaded image is not
     constructed here: the witness runs on reached states, not on
     fetched bytes.
-/

#print axioms avx2KontrollFrei
#print axioms avx2ZustandBereit
#print axioms avx2_zeuge_bereit
#print axioms avx2_basis_verweigert
#print axioms avx2Fehler
#print axioms avx2TorFehler
#print axioms avx2TorFehler_ud
#print axioms avx2_basis_ud
#print axioms vex128Voll
#print axioms vex128Voll_hoch_null
#print axioms legacy128Voll_obere_bleibt
#print axioms vzeroOberhalb_null
#print axioms vzeroAlle_hoch_null
#print axioms ymmStepVex_gleich
#print axioms ymmStepVex_verweigert
#print axioms ymmStepVex_ud
#print axioms ymmStepVex_ober_null
#print axioms ymmStepVex_wf
#print axioms ymmStepLegacy_obere_bleibt
#print axioms ymmStepLegacy_wf
#print axioms ymmStepVzeroUpper_null
#print axioms ymmStepVzeroAll_hoch_null
#print axioms ymmEinbettung
#print axioms ymmAvx_kein_speicher
#print axioms adapterAvx2Tor_gleich
#print axioms adapterAvx2Tor_verweigert
#print axioms adapterAvx2Tor_wf
#print axioms avx2Zustand_zeuge

end Gabbro.Grammatik.X86
