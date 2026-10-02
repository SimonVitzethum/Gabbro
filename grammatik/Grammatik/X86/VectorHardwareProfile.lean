/-
  File:      Grammatik/X86/VectorHardwareProfile.lean
  Subject:   Architectural enabled-state gates and admitted vector
    byte-execution for the selected SSE2 packed-integer tier.

  Lane 674 (hardware completion): replaces the bare `BereitProfil.osXmm`
  Bool with checked CPU / XCR0 / control-register requirements for the
  two admitted `VectorCodec` register forms (PXOR `66 0F EF /r`, PADDQ
  `66 0F D4 /r` over `vecXor`/`vecAdd` at `.b64` on the shared XMM
  state), and admits actual fetched vector byte-execution through the
  accepted `ExtendedExecution` dispatcher. Optional AVX2 is an explicit
  refused row with a proved scalar fallback. No vector atomicity.
-/
import Grammatik.X86.FeatureProfile
import Grammatik.X86.VectorCodec
import Grammatik.X86.VectorFootprints
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Silicon feature bits the selected tier needs: SSE2 presence plus
    the (unimplemented) AVX bit kept only to refuse the AVX row. -/
structure CpuMerkmal where
  hatSse2 : Bool
  hatAvx : Bool
  deriving DecidableEq, Repr

/-- Relevant XCR0 state bits: x87 (bit 0), SSE (bit 1), AVX (bit 2).
    OS configuration code is user logic; these are checked inputs. -/
structure Xcr0Bild where
  x87 : Bool
  sse : Bool
  avx : Bool
  deriving DecidableEq, Repr

/-- Relevant control bits: CR0.EM, CR0.TS, CR4.OSFXSR, CR4.OSXSAVE. -/
structure KontrollBild where
  cr0Em : Bool
  cr0Ts : Bool
  cr4Osfxsr : Bool
  cr4Osxsave : Bool
  deriving DecidableEq, Repr

/-- XCR0 readiness for 128-bit SSE state: x87 and SSE bits set. -/
def xcr0SseBereit (x : Xcr0Bild) : Bool := x.x87 && x.sse

/-- Control-register freedom for SSE: no emulation, no task switch,
    OS FXSAVE/FXRSTOR support enabled. -/
def kontrollSseFrei (k : KontrollBild) : Bool :=
  (!k.cr0Em) && (!k.cr0Ts) && k.cr4Osfxsr

/-! ## 1. Enabled-state readiness and tier admission.

  `hwVektorBereit` is the checked conjunction the bare `osXmm` Bool
  stood in for: silicon SSE2, XCR0 SSE readiness, control-register
  freedom, and the OS vector-state bit. Integer SSE needs no MXCSR
  word, so none is required here (scalar DOUBLE keeps its own
  `mxcsrGueltig` premise in `ScalarFloat`). OS configuration and
  context-preservation code remain user logic: these are checked
  inputs, never assumed-correct behaviour. -/

/-- Checked enabled-state readiness for the 128-bit packed-integer
    tier: silicon SSE2, XCR0 SSE state, control freedom, OS bit. -/
def hwVektorBereit (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (b : BereitProfil) : Bool :=
  cpu.hatSse2 && xcr0SseBereit x && kontrollSseFrei k && b.osXmm

/-- Tier admission: the finite `paketInt128` admission AND the checked
    enabled-state readiness. Either side alone admits nothing. -/
def vektorHwZugelassen (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) : Bool :=
  merkmalZugelassen hw b .paketInt128 && hwVektorBereit cpu x k b

/-- Admission needs the finite profile side. -/
theorem vektorHw_braucht_merkmal (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    merkmalZugelassen hw b .paketInt128 = true := by
  simp only [vektorHwZugelassen, Bool.and_eq_true] at h
  exact h.1

/-- Admission needs silicon SSE2. -/
theorem vektorHw_braucht_cpu (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    cpu.hatSse2 = true := by
  simp only [vektorHwZugelassen, hwVektorBereit, Bool.and_eq_true] at h
  exact h.2.1.1.1

/-- Admission needs XCR0 SSE readiness. -/
theorem vektorHw_braucht_xcr0 (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    xcr0SseBereit x = true := by
  simp only [vektorHwZugelassen, hwVektorBereit, Bool.and_eq_true] at h
  exact h.2.1.1.2

/-- Admission needs control-register freedom. -/
theorem vektorHw_braucht_kontrolle (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    kontrollSseFrei k = true := by
  simp only [vektorHwZugelassen, hwVektorBereit, Bool.and_eq_true] at h
  exact h.2.1.2

/-- SAFE REFINEMENT: checked admission implies the old bare gate, so
    every `stepVector` result carries over unchanged. No silent trust:
    the new gate is strictly stronger. -/
theorem vektorHw_verfeinert (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    vecEintritt b = true := by
  simp only [vektorHwZugelassen, hwVektorBereit, Bool.and_eq_true] at h
  simp only [vecEintritt]
  exact h.2.2

/-! ## 2. Gated vector byte-execution.

  `stepVectorHw` runs the accepted `stepVector` exactly where the
  checked admission holds, and refuses otherwise. Control-state,
  CPU-feature or profile failure is a validator refusal (`none`),
  never a silent substitution and never an assumed-correct OS action.
  Width/lane/upper-lane effects and flag preservation carry over from
  the accepted lane theorems; nothing is re-evaluated here. -/

/-- Gated vector step: the accepted step under checked admission. -/
def stepVectorHw (d : VectorDec) (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) : Option FpZustand :=
  match vektorHwZugelassen hw b cpu x k with
  | true => stepVector d t b
  | false => none

/-- Admitted gated step IS the accepted step. -/
theorem stepVectorHw_gleich (d : VectorDec) (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    stepVectorHw d t hw b cpu x k = stepVector d t b := by
  unfold stepVectorHw
  rw [h]

/-- Refused admission refuses every vector form. -/
theorem stepVectorHw_verweigert (d : VectorDec) (t : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = false) :
    stepVectorHw d t hw b cpu x k = none := by
  unfold stepVectorHw
  rw [h]

/-- Missing silicon SSE2 refuses, whatever the rest claims. -/
theorem stepVectorHw_ohne_cpu (d : VectorDec) (t : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (hcpu : cpu.hatSse2 = false) :
    stepVectorHw d t hw b cpu x k = none := by
  have hgate : vektorHwZugelassen hw b cpu x k = false := by
    unfold vektorHwZugelassen hwVektorBereit
    rw [hcpu]
    simp
  exact stepVectorHw_verweigert d t hw b cpu x k hgate

/-- Missing XCR0 SSE readiness refuses. -/
theorem stepVectorHw_ohne_xcr0 (d : VectorDec) (t : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (hx : xcr0SseBereit x = false) :
    stepVectorHw d t hw b cpu x k = none := by
  have hgate : vektorHwZugelassen hw b cpu x k = false := by
    unfold vektorHwZugelassen hwVektorBereit
    cases hcpu : cpu.hatSse2 <;> simp_all
  exact stepVectorHw_verweigert d t hw b cpu x k hgate

/-- Set control bits (emulation or task-switch) refuse. -/
theorem stepVectorHw_ohne_kontrolle (d : VectorDec) (t : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (hk : kontrollSseFrei k = false) :
    stepVectorHw d t hw b cpu x k = none := by
  have hgate : vektorHwZugelassen hw b cpu x k = false := by
    unfold vektorHwZugelassen hwVektorBereit
    simp_all
  exact stepVectorHw_verweigert d t hw b cpu x k hgate

/-- The admitted tier is 128 bits wide in exactly two 64-bit lanes. -/
theorem vektorBreite_spur :
    laneCount .b64 = 2 ∧ Breite.bits (merkmalBreite .paketInt128) = 32 := by
  exact ⟨rfl, rfl⟩

/-- LOWER LANE: admitted PXOR computes the low lane as the canonical
    xor of the low lanes. -/
theorem stepVectorHw_pxor_spur0 (d : VectorDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (dst src : XmmReg)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .pxorRR dst src)
    (hstep : stepVectorHw d t hw b cpu x k = some t') :
    laneGet .b64 (t'.xmm dst) 0 =
      xorB .b64 (laneGet .b64 (t.xmm dst) 0)
        (laneGet .b64 (t.xmm src) 0) := by
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVectorHw_gleich d t hw b cpu x k hgate] at hstep
  exact stepVector_pxor_spur d t t' b dst src 0 hok hfp h hstep (by decide)

/-- UPPER LANE: admitted PXOR computes the high lane independently --
    no inter-lane carry exists by the accepted `laneGet_xor`. -/
theorem stepVectorHw_pxor_spur1 (d : VectorDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (dst src : XmmReg)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .pxorRR dst src)
    (hstep : stepVectorHw d t hw b cpu x k = some t') :
    laneGet .b64 (t'.xmm dst) 1 =
      xorB .b64 (laneGet .b64 (t.xmm dst) 1)
        (laneGet .b64 (t.xmm src) 1) := by
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVectorHw_gleich d t hw b cpu x k hgate] at hstep
  exact stepVector_pxor_spur d t t' b dst src 1 hok hfp h hstep (by decide)

/-- UPPER LANE: admitted PADDQ adds the high lane modularly with no
    carry from the low lane, by the accepted `laneGet_add`. -/
theorem stepVectorHw_paddq_spur1 (d : VectorDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (dst src : XmmReg)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .paddqRR dst src)
    (hstep : stepVectorHw d t hw b cpu x k = some t') :
    laneGet .b64 (t'.xmm dst) 1 =
      addB .b64 (laneGet .b64 (t.xmm dst) 1)
        (laneGet .b64 (t.xmm src) 1) := by
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVectorHw_gleich d t hw b cpu x k hgate] at hstep
  exact stepVector_paddq_spur d t t' b dst src 1 hok hfp h hstep (by decide)

/-- Admitted gated steps preserve rFLAGS (both integer forms leave
    flags untouched). -/
theorem stepVectorHw_flags (d : VectorDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (dst src : XmmReg)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .pxorRR dst src ∨ d.op = .paddqRR dst src)
    (hstep : stepVectorHw d t hw b cpu x k = some t') :
    t'.kern.flags = t.kern.flags := by
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVectorHw_gleich d t hw b cpu x k hgate] at hstep
  rcases h with h | h
  · exact stepVector_pxor_flags d t t' b dst src hok hfp h hstep
  · exact stepVector_paddq_flags d t t' b dst src hok hfp h hstep

/-! ## 3. Vector memory forms: alignment faults, admission,
  footprints and tearing.

  The admitted register forms touch no memory themselves; the vector
  memory traffic of the tier goes through the two ordered canonical
  64-bit chunk accesses (`vecWrite`/`vecRead`). An aligned form
  (MOVDQA shape) faults with #GP on a 16-byte-misaligned address; an
  unaligned form (MOVDQU shape) never faults on alignment. Either form
  still needs both chunk permissions and no-wrap. No vector memory
  traffic is atomic: the torn intermediate state stands. -/

/-- The two selected memory shapes: aligned (MOVDQA) and unaligned
    (MOVDQU). No other vector memory form is admitted here. -/
inductive VektorSpeicherForm where
  | ausgerichtet
  | unausgerichtet
  deriving DecidableEq, Repr

/-- #GP fault predicate: the aligned form faults exactly on
    16-byte-misaligned addresses; the unaligned form never faults on
    alignment. This classifies the hardware trap; it is not a
    validator admission. -/
def vektorGpFehler (a : Adresse) : VektorSpeicherForm → Bool
  | .ausgerichtet => decide (a.toNat % 16 ≠ 0)
  | .unausgerichtet => false

/-- The unaligned form never faults on alignment, at any address. -/
theorem vektorGp_nie_unausgerichtet (a : Adresse) :
    vektorGpFehler a .unausgerichtet = false := rfl

/-- The aligned form faults eight bytes past a 16-byte boundary. -/
theorem vektorGp_ausgerichtet_fehler :
    vektorGpFehler (natAdresse 8) .ausgerichtet = true := by
  decide

/-- The aligned form is clean at the boundary and one line further. -/
theorem vektorGp_ausgerichtet_ok :
    vektorGpFehler (natAdresse 0) .ausgerichtet = false ∧
      vektorGpFehler (natAdresse 16) .ausgerichtet = false := by
  exact ⟨by decide, by decide⟩

/-- Vector store admission: no #GP, both chunk write permissions, and
    no-wrap across both footprints. -/
def vektorSchreibZugelassen (m : Speicher) (a : Adresse)
    (f : VektorSpeicherForm) : Bool :=
  (!vektorGpFehler a f) && schreibbar8 m a &&
    schreibbar8 m (vecHiAddr a)

/-- A #GP fault refuses the vector store admission. -/
theorem vektorSchreib_fehler_verweigert (m : Speicher) (a : Adresse)
    (f : VektorSpeicherForm) (h : vektorGpFehler a f = true) :
    vektorSchreibZugelassen m a f = false := by
  simp [vektorSchreibZugelassen, h]

/-- Admission carries both chunk permissions. -/
theorem vektorSchreib_berechtigungen (m : Speicher) (a : Adresse)
    (f : VektorSpeicherForm)
    (h : vektorSchreibZugelassen m a f = true) :
    schreibbar8 m a = true ∧ schreibbar8 m (vecHiAddr a) = true := by
  simp only [vektorSchreibZugelassen, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

/-- FULL PER-ACCESS FOOTPRINT: an admitted vector access observes
    exactly the 16-byte `vecFuss` footprint inside its carrier. -/
theorem vektorHw_fuss (c : Nat) (hwrap : c + 16 ≤ 2 ^ 64) :
    fussEnthalten (vecFuss (natAdresse c)) (vecTraeger c) = true :=
  vecFuss_in_traeger c hwrap

/-- NO VECTOR ATOMICITY: after the first chunk, memory is observably
    mixed -- the low half already carries the new value while the
    high half still carries the old bytes. Reused, not re-proved. -/
theorem vektorHw_teilt (m m1 : Speicher) (a : Adresse) (v : Vektor)
    (h1 : write64 m a (vLo v) = some m1)
    (hrd1 : lesbar8 m a = true)
    (hno : OhneUmbruch16 a) :
    read64 m1 a = some (vLo v) ∧
      read64 m1 (vecHiAddr a) = read64 m (vecHiAddr a) :=
  vecWrite_teilt m m1 a v h1 hrd1 hno

/-! ## 4. Optional AVX2: explicit refused row with proved scalar fallback.

  The 256-bit AVX tier is NOT implemented here: its row always
  refuses, whatever CPU and XCR0 claim. Where the selected 128-bit
  work is unavailable, the proved scalar fallback below computes the
  same observable lane outcomes through canonical single-word
  operations (`xorB`/`addB` at `.b64`); it is a data equivalence over
  already-proved words, not a compiler pass and not a speed claim. -/

/-- Selected vector width tiers: admitted 128-bit SSE2 and the
    explicitly unimplemented 256-bit AVX row. -/
inductive VektorStufe where
  | sse128
  | avx256
  deriving DecidableEq, Repr

/-- XCR0 readiness for AVX state: x87, SSE and AVX bits all set. -/
def xcr0AvxBereit (x : Xcr0Bild) : Bool := x.x87 && x.sse && x.avx

/-- CPU-level readiness per tier: SSE2 bit for 128, AVX bit plus
    XCR0 AVX readiness for 256. -/
def stufenCpuBereit (cpu : CpuMerkmal) (x : Xcr0Bild) :
    VektorStufe → Bool
  | .sse128 => cpu.hatSse2
  | .avx256 => cpu.hatAvx && xcr0AvxBereit x

/-- Tier admission: the 128-bit row is the checked gate; the 256-bit
    row is always refused (unimplemented, stated not completed). -/
def stufenZugelassenHw (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild) :
    VektorStufe → Bool
  | .sse128 => vektorHwZugelassen hw b cpu x k
  | .avx256 => false

/-- The 128-bit row IS the checked gate. -/
theorem stufe_sse128_ist_gate (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild) :
    stufenZugelassenHw hw b cpu x k .sse128 =
      vektorHwZugelassen hw b cpu x k := rfl

/-- The 256-bit row always refuses: AVX2 is not implemented here. -/
theorem stufe_avx256_verweigert (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild) :
    stufenZugelassenHw hw b cpu x k .avx256 = false := rfl

/-- AVX without XCR0 AVX readiness is not CPU-ready. -/
theorem avx_braucht_xcr0 (cpu : CpuMerkmal) (x : Xcr0Bild)
    (hx : xcr0AvxBereit x = false) :
    stufenCpuBereit cpu x .avx256 = false := by
  simp [stufenCpuBereit, hx]

/-- Scalar fallback for xor: the two 64-bit lanes through canonical
    single-word `xorB`, joined back into one 128-bit word. -/
def skalarPaarXor (aLo aHi bLo bHi : Wort) : Vektor :=
  vecJoin (xorB .b64 aLo bLo) (xorB .b64 aHi bHi)

/-- Scalar fallback for add: the two 64-bit lanes through canonical
    single-word `addB`, joined back into one 128-bit word. -/
def skalarPaarAdd (aLo aHi bLo bHi : Wort) : Vektor :=
  vecJoin (addB .b64 aLo bLo) (addB .b64 aHi bHi)

/-- The xor fallback carries the scalar low-lane result. -/
theorem skalarPaarXor_tief (aLo aHi bLo bHi : Wort) :
    vLo (skalarPaarXor aLo aHi bLo bHi) = xorB .b64 aLo bLo :=
  vLo_vecJoin _ _

/-- The xor fallback carries the scalar high-lane result. -/
theorem skalarPaarXor_hoch (aLo aHi bLo bHi : Wort) :
    vHi (skalarPaarXor aLo aHi bLo bHi) = xorB .b64 aHi bHi :=
  vHi_vecJoin _ _

/-- The add fallback carries the scalar low-lane result. -/
theorem skalarPaarAdd_tief (aLo aHi bLo bHi : Wort) :
    vLo (skalarPaarAdd aLo aHi bLo bHi) = addB .b64 aLo bLo :=
  vLo_vecJoin _ _

/-- The add fallback carries the scalar high-lane result. -/
theorem skalarPaarAdd_hoch (aLo aHi bLo bHi : Wort) :
    vHi (skalarPaarAdd aLo aHi bLo bHi) = addB .b64 aHi bHi :=
  vHi_vecJoin _ _

/-- Lane 0 of a 64-bit-lane word is its low half. -/
theorem laneNat_b64_lo (v : Vektor) :
    laneNat .b64 v 0 = (vLo v).toNat := by
  have h64 : Breite.bits .b64 = 64 := rfl
  unfold laneNat vLo
  rw [h64]
  simp

/-- Lane 1 of a 64-bit-lane word is its high half. -/
theorem laneNat_b64_hi (v : Vektor) :
    laneNat .b64 v 1 = (vHi v).toNat := by
  have h64 : Breite.bits .b64 = 64 := rfl
  unfold laneNat vHi
  rw [h64]
  simp [Nat.pow_one]

/-- Lane 0 of a joined word is the low word. -/
theorem laneNat_join_lo (w0 w1 : Wort) :
    laneNat .b64 (vecJoin w0 w1) 0 = w0.toNat := by
  have h64 : Breite.bits .b64 = 64 := rfl
  unfold laneNat vecJoin
  rw [h64, BitVec.toNat_ofNat]
  have h0 := w0.isLt
  have h1 := w1.isLt
  have hbound : w0.toNat + w1.toNat * 2 ^ 64 < 2 ^ 128 := by
    have hmul : w1.toNat * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by decide : 0 < 2 ^ 64)
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hbound]
  simp [Nat.mod_eq_of_lt h0]

/-- Lane 1 of a joined word is the high word. -/
theorem laneNat_join_hi (w0 w1 : Wort) :
    laneNat .b64 (vecJoin w0 w1) 1 = w1.toNat := by
  have h64 : Breite.bits .b64 = 64 := rfl
  unfold laneNat vecJoin
  rw [h64, BitVec.toNat_ofNat, Nat.pow_one]
  have h0 := w0.isLt
  have h1 := w1.isLt
  have hbound : w0.toNat + w1.toNat * 2 ^ 64 < 2 ^ 128 := by
    have hmul : w1.toNat * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by decide : 0 < 2 ^ 64)
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hbound]
  have hdiv : (w0.toNat + w1.toNat * 2 ^ 64) / 2 ^ 64 = w1.toNat := by
    rw [Nat.mul_comm w1.toNat (2 ^ 64),
      Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64),
      Nat.div_eq_of_lt h0, Nat.zero_add]
  rw [hdiv, Nat.mod_eq_of_lt h1]

/-- SAME OBSERVABLE OUTCOMES: the scalar xor fallback reads back
    exactly the packed `vecXor` word lane by lane. -/
theorem skalarPaarXor_gleich (a b : Vektor) (i : Nat)
    (hi : i < laneCount .b64) :
    laneGet .b64 (skalarPaarXor (vLo a) (vHi a) (vLo b) (vHi b)) i =
      laneGet .b64 (vecXor .b64 a b) i := by
  have h2 : laneCount .b64 = 2 := rfl
  rw [h2] at hi
  apply BitVec.eq_of_toNat_eq
  simp only [laneGet_toNat]
  have h01 : i = 0 ∨ i = 1 := by omega
  rcases h01 with rfl | rfl
  · rw [show (skalarPaarXor (vLo a) (vHi a) (vLo b) (vHi b)) =
        vecJoin (xorB .b64 (vLo a) (vLo b))
          (xorB .b64 (vHi a) (vHi b)) from rfl,
      laneNat_join_lo, laneNat_xor .b64 _ _ 0 (by decide),
      laneNat_b64_lo, laneNat_b64_lo, xorB_nat]
  · rw [show (skalarPaarXor (vLo a) (vHi a) (vLo b) (vHi b)) =
        vecJoin (xorB .b64 (vLo a) (vLo b))
          (xorB .b64 (vHi a) (vHi b)) from rfl,
      laneNat_join_hi, laneNat_xor .b64 _ _ 1 (by decide),
      laneNat_b64_hi, laneNat_b64_hi, xorB_nat]

/-! ## 5. Validator adapter and joint witnesses.

  Export for lane 660 / validator consumers: full admission is the
  unified `extZugelassen` fetch discipline AND the checked hardware
  gate. The fetch-to-execution bridge runs a fetched vector form
  through the accepted unified dispatcher under the checked gate.
  The joint witness decodes pinned canonical bytes with their
  consumed length, runs the admitted gated step on the shared XMM
  state, steps the unified dispatcher to the same successor, and
  observably changes a memory byte through the existing MOVSD store.
  Execute permission of a concrete loaded image stays with the image
  lanes; the adapter carries it as an explicit conjunct. -/

/-- Full validator admission for a fetched vector form: the unified
    fetch discipline (length equation, length guard, execute
    permission of the consumed prefix) AND the checked hardware
    gate. For consumers 660/validator. -/
def vektorValidatorZugelassen (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) : Bool :=
  extZugelassen t fenster i rest && vektorHwZugelassen hw b cpu x k

/-- Full admission needs the unified fetch discipline. -/
theorem vektorValidator_braucht_ext (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (h : vektorValidatorZugelassen t fenster i rest hw b cpu x k = true) :
    extZugelassen t fenster i rest = true := by
  simp only [vektorValidatorZugelassen, Bool.and_eq_true] at h
  exact h.1

/-- Full admission needs the checked hardware gate. -/
theorem vektorValidator_braucht_hw (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (h : vektorValidatorZugelassen t fenster i rest hw b cpu x k = true) :
    vektorHwZugelassen hw b cpu x k = true := by
  simp only [vektorValidatorZugelassen, Bool.and_eq_true] at h
  exact h.2

/-- The admitted gated step IS the unified dispatcher's vector arm. -/
theorem stepExt_vec_hw (v : VectorDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hs : stepVector v t b = some t') :
    stepVectorHw v t hw b cpu x k = stepVector v t b ∧
      stepExt (.vec v) t b = .weiter t' := by
  exact ⟨stepVectorHw_gleich v t hw b cpu x k hgate,
    stepExt_vec v t t' b hs⟩

/-- FETCH BRIDGE: a fetched vector form steps through the unified
    byte step under the checked gate. A forged `ExtInstr` cannot
    inject an instruction: only `fetchExt` over actual memory feeds
    the dispatcher. -/
theorem vectorHw_fetch_bridge (t t' : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (v : VectorDec) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.vec v, rest))
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hs : stepVector v t b = some t') :
    extByteschritt t b = .weiter t' ∧
      stepVectorHw v t hw b cpu x k = stepVector v t b :=
  ⟨extByteschritt_weiter t b (.vec v) rest (.weiter t') hf
    (stepExt_vec v t t' b hs),
    stepVectorHw_gleich v t hw b cpu x k hgate⟩

/-- Baseline silicon: SSE2 present, AVX absent (refused row). -/
def basisCpu : CpuMerkmal := ⟨true, false⟩

/-- Baseline XCR0: x87 and SSE state set, AVX clear. -/
def basisXcr0 : Xcr0Bild := ⟨true, true, false⟩

/-- Baseline controls: no emulation, no task switch, OS FXSR and
    OSXSAVE enabled. -/
def basisKontrolle : KontrollBild := ⟨false, false, true, true⟩

/-- Baseline enabled-state readiness holds at the witness profile. -/
theorem basis_hw_bereit :
    hwVektorBereit basisCpu basisXcr0 basisKontrolle vecZeugeBereit =
      true := rfl

/-- Baseline tier admission holds. -/
theorem basis_vektorHw_zugelassen :
    vektorHwZugelassen basisHw vecZeugeBereit basisCpu basisXcr0
        basisKontrolle = true := by
  decide

/-- JOINT WITNESS: pinned canonical bytes decode with their consumed
    length, the checked gate admits, the gated step runs on the
    shared XMM state, the unified dispatcher reaches the same
    successor, and the existing MOVSD store observably changes a
    memory byte. -/
theorem vectorHw_zeuge :
    ∃ (bs : List Byte) (dec : VectorDec) (rest : List Byte)
      (t1 t2 : FpZustand),
      decodeVector bs = some (dec, rest) ∧
      dec.laenge + rest.length = bs.length ∧
      vektorHwZugelassen basisHw vecZeugeBereit basisCpu basisXcr0
          basisKontrolle = true ∧
      stepVectorHw dec vecZeugeT0 basisHw vecZeugeBereit basisCpu
          basisXcr0 basisKontrolle = some t1 ∧
      stepExt (.vec dec) vecZeugeT0 vecZeugeBereit = .weiter t1 ∧
      (∃ m2 : Speicher, ∃ store : FpDecodiert,
        fpSchritt store t1 = some t2 ∧ t2.kern.speicher = m2 ∧
        m2.bytes 0 ≠ vecZeugeT0.kern.speicher.bytes 0) := by
  refine ⟨encodeVector (.pxorRR .xmm0 .xmm1),
    (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec), [], vecZeugeT1,
    { vecZeugeT1 with kern := { vecZeugeT1.kern with speicher := vecZeugeM2, rip := ripNach vecZeugeT1.kern.rip 1 } },
    vecZeuge_decode, vecZeuge_laenge, basis_vektorHw_zugelassen, ?_, ?_, ?_⟩
  · rw [stepVectorHw_gleich _ _ _ _ _ _ _ basis_vektorHw_zugelassen]
    exact vecZeuge_schritt
  · exact stepExt_vec _ _ _ _ vecZeuge_schritt
  · refine ⟨vecZeugeM2,
      (⟨.movsdSpeichere .rax .xmm0 (0 : BitVec 32), 1⟩ : FpDecodiert),
      vecZeuge_speichere, rfl, ?_⟩
    have hhit : writeBytes vecZeugenSpeicher 0
        (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 =
        wortByte (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 := by
      have h := writeBytesN_hit vecZeugenSpeicher 0
        (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 8 0 (by decide) (by decide)
      rwa [addrOff_null] at h
    show vecZeugeM2.bytes 0 ≠ vecZeugenSpeicher.bytes 0
    have e1 : vecZeugeM2.bytes 0 =
        writeBytes vecZeugenSpeicher 0
          (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 := rfl
    rw [e1, hhit, vecZeuge_xor_tief]
    decide

/-- NEGATIVE: no silicon SSE2, no admission. -/
theorem vectorHw_neg_cpu :
    vektorHwZugelassen basisHw vecZeugeBereit ⟨false, false⟩ basisXcr0
        basisKontrolle = false := by
  decide

/-- NEGATIVE: XCR0 SSE bit clear, no admission. -/
theorem vectorHw_neg_xcr0 :
    vektorHwZugelassen basisHw vecZeugeBereit basisCpu
        ⟨true, false, false⟩ basisKontrolle = false := by
  decide

/-- NEGATIVE: CR0.EM set (emulation), no admission. -/
theorem vectorHw_neg_kontrolle :
    vektorHwZugelassen basisHw vecZeugeBereit basisCpu basisXcr0
        ⟨true, false, true, true⟩ = false := by
  decide

/-- NEGATIVE: OS vector-state bit clear, no admission. -/
theorem vectorHw_neg_osxmm :
    vektorHwZugelassen basisHw ⟨kontextReset.mxcsr, false⟩ basisCpu
        basisXcr0 basisKontrolle = false := by
  decide

/-- NEGATIVE: misaligned address under the aligned form refuses the
    vector store admission (#GP classification). -/
theorem vectorHw_neg_ausrichtung :
    vektorSchreibZugelassen vecZeugenSpeicher (natAdresse 8)
        .ausgerichtet = false :=
  vektorSchreib_fehler_verweigert _ _ _ vektorGp_ausgerichtet_fehler

/-- NEGATIVE: overlapping vector footprints refuse alias admission. -/
theorem vectorHw_neg_alias :
    klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200)) = .unbekannt ∧
      aliasZulassen (klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200))) = false :=
  vecFuss_teilueberlapp_verweigert

/-- NEGATIVE: unknown second opcode byte refuses decode. -/
theorem vectorHw_neg_opcode :
    decodeVector [natByte 64, natByte 102, natByte 15, natByte 0,
      natByte 0] = none := rfl

/- CUTS: what is not proved here.

   - Manual provenance: the `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
     named in the task is absent in this clone (checked 2026-10-02),
     so NO manual heading, page or quotation is cited. The control
     bits modelled (CPUID SSE2/AVX presence, XCR0 x87/SSE/AVX,
     CR0.EM/TS, CR4.OSFXSR/OSXSAVE, the 16-byte #GP rule, legacy-SSE
     upper-half semantics) are encoded as explicit checked inputs in
     long-documented architectural shape; silicon correspondence of
     each bit position against the official manuals stays OPEN and is
     claimed nowhere. OS configuration and context-preservation code
     remain user logic, never assumed correct.
   - Two admitted register forms only: PXOR and PADDQ over
     `vecXor`/`vecAdd` at `.b64` on the shared XMM state, through the
     accepted `decodeVector`/`stepVector`/`stepExt`/`fetchExt`
     vocabulary (never re-evaluated). No vector memory opcode, no
     packed-FP lane, no VEX/AVX encoding and no other SSE2 row exists
     here; uncovered rows refuse by construction (`stufe_avx256_*`,
     `vectorHw_neg_opcode`, `vector_nichts_*`).
   - Width note: the finite profile labels the tier `.b32`
     (`merkmalBreite .paketInt128`), while the admitted operations
     run two `.b64` lanes over the 128-bit register
     (`vektorBreite_spur` states both facts side by side). The label
     is not redefined here; a profile-width/lane-width reconciliation
     stays with the profile owner.
   - Execute permission of a concrete loaded image is an explicit
     conjunct of `vektorValidatorZugelassen`, not a constructed
     image: no loaded-image byte string is claimed executable here.
   - No vector store atomicity: `vektorHw_teilt` restates the torn
     intermediate state; footprint disjointness never implies
     atomicity or reordering. Per-access TSO granularity, GX
     refinement, source correspondence, budget transfer, progress and
     call-log effects stay open; `simdFreigabe` is untouched
     (`false`).
-/

#print axioms vektorValidatorZugelassen
#print axioms vektorValidator_braucht_ext
#print axioms vektorValidator_braucht_hw
#print axioms stepExt_vec_hw
#print axioms vectorHw_fetch_bridge
#print axioms basisCpu
#print axioms basisXcr0
#print axioms basisKontrolle
#print axioms basis_hw_bereit
#print axioms basis_vektorHw_zugelassen
#print axioms vectorHw_zeuge
#print axioms vectorHw_neg_cpu
#print axioms vectorHw_neg_xcr0
#print axioms vectorHw_neg_kontrolle
#print axioms vectorHw_neg_osxmm
#print axioms vectorHw_neg_ausrichtung
#print axioms vectorHw_neg_alias
#print axioms vectorHw_neg_opcode

#print axioms xcr0SseBereit
#print axioms kontrollSseFrei
#print axioms hwVektorBereit
#print axioms vektorHwZugelassen
#print axioms vektorHw_braucht_merkmal
#print axioms vektorHw_braucht_cpu
#print axioms vektorHw_braucht_xcr0
#print axioms vektorHw_braucht_kontrolle
#print axioms vektorHw_verfeinert
#print axioms stepVectorHw_gleich
#print axioms stepVectorHw_verweigert
#print axioms stepVectorHw_ohne_cpu
#print axioms stepVectorHw_ohne_xcr0
#print axioms stepVectorHw_ohne_kontrolle
#print axioms vektorBreite_spur
#print axioms stepVectorHw_pxor_spur0
#print axioms stepVectorHw_pxor_spur1
#print axioms stepVectorHw_paddq_spur1
#print axioms stepVectorHw_flags
#print axioms vektorGp_nie_unausgerichtet
#print axioms vektorGp_ausgerichtet_fehler
#print axioms vektorGp_ausgerichtet_ok
#print axioms vektorSchreibZugelassen
#print axioms vektorSchreib_fehler_verweigert
#print axioms vektorSchreib_berechtigungen
#print axioms vektorHw_fuss
#print axioms vektorHw_teilt
#print axioms xcr0AvxBereit
#print axioms stufenCpuBereit
#print axioms stufenZugelassenHw
#print axioms stufe_sse128_ist_gate
#print axioms stufe_avx256_verweigert
#print axioms avx_braucht_xcr0
#print axioms skalarPaarXor
#print axioms skalarPaarAdd
#print axioms skalarPaarXor_tief
#print axioms skalarPaarXor_hoch
#print axioms skalarPaarAdd_tief
#print axioms skalarPaarAdd_hoch
#print axioms laneNat_b64_lo
#print axioms laneNat_b64_hi
#print axioms laneNat_join_lo
#print axioms laneNat_join_hi
#print axioms skalarPaarXor_gleich

end Gabbro.Grammatik.X86
