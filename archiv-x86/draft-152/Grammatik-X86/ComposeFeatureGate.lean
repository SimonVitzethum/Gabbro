/-
  File:      Grammatik/X86/ComposeFeatureGate.lean
  Subject:   Composition closing: every feature-gated form to its
    CPUID/XCR0/enabled-state gate, re-checked per image.

  Lane 843: composes already-accepted modules only; nothing here is
  re-proved and no interpreter or executor is duplicated.

  Producer/consumer interface closed: the observed CPUID/XCR0 answers
  of a reached fetched CPUID-then-XGETBV chain
  (`CpuFeatureHardwareForms.cpu_kette_speichert_gatter`, reused) plus
  the finite profile admission (`FeatureProfile.merkmalZugelassen`,
  reused) plus the checked enabled-state readiness
  (`VectorHardwareProfile.vektorHwZugelassen`, reused) jointly admit
  one checked closing step per feature and image. An absent observed
  bit refuses the encoding. The unimplemented 256-bit AVX row always
  refuses (`stufenZugelassenHw ... .avx256`, reused).
-/
import Grammatik.X86.FeatureProfile
import Grammatik.X86.CpuFeatureHardwareForms
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorCodec
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.Codec
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Observed-bit gate per finite feature, reusing the accepted
    CPUID/XCR0 bit tests: scalar-double and the packed-integer tier
    both need observed silicon SSE2 (`edxSSE2`) and observed XCR0 XMM
    state (`xcrXMM`); the scalar integer rows need no feature bit.
    Enabled-state (MXCSR, OS state, controls) stays with the profile
    and the checked `vektorHwZugelassen` conjunct, never here. -/
def beobachtungsTor (leaf1 : CpuOut) (xcrLo : BitVec 32) :
    PerfMerkmal → Bool
  | .skalar64 => true
  | .skalar32 => true
  | .sseDoppel => edxSSE2 leaf1 && xcrXMM xcrLo
  | .paketInt128 => edxSSE2 leaf1 && xcrXMM xcrLo

/-- Per-feature closing: the finite profile admission AND the
    observed-bit gate (AND, for the packed tier, the checked
    enabled-state readiness). Either side alone admits nothing. -/
def featureGateGeschlossen (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) : PerfMerkmal → Bool
  | .skalar64 => merkmalZugelassen hw b .skalar64
  | .skalar32 => merkmalZugelassen hw b .skalar32
  | .sseDoppel =>
      merkmalZugelassen hw b .sseDoppel
        && beobachtungsTor leaf1 xcrLo .sseDoppel
  | .paketInt128 =>
      vektorHwZugelassen hw b cpu x k
        && beobachtungsTor leaf1 xcrLo .paketInt128

/-- The unimplemented 256-bit AVX row closes to a permanent refusal:
    the accepted tier admission (always false for `.avx256`) AND the
    observed-bit gate. Whatever silicon and control state claim, this
    row admits nothing here. -/
def avx2ReiheGeschlossen (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (leaf1 leaf7 : CpuOut) (xcrLo : BitVec 32) : Bool :=
  stufenZugelassenHw hw b cpu x k .avx256
    && avx2Bereit leaf1 leaf7 xcrLo

/-- The 256-bit row always refuses, whatever the observed answers. -/
theorem avx2_reihe_verweigert_immer (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (leaf1 leaf7 : CpuOut) (xcrLo : BitVec 32) :
    avx2ReiheGeschlossen hw b cpu x k leaf1 leaf7 xcrLo = false := by
  simp [avx2ReiheGeschlossen, stufe_avx256_verweigert]

/-- Absent silicon SSE2 refuses the scalar-double gate. -/
theorem tor_sse_verweigert_ohne_bit (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : edxSSE2 leaf1 = false) :
    beobachtungsTor leaf1 xcrLo .sseDoppel = false := by
  simp [beobachtungsTor, h]

/-- Absent silicon SSE2 refuses the packed-tier gate. -/
theorem tor_paket_verweigert_ohne_bit (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : edxSSE2 leaf1 = false) :
    beobachtungsTor leaf1 xcrLo .paketInt128 = false := by
  simp [beobachtungsTor, h]

/-- Absent XCR0 XMM state refuses the packed-tier gate. -/
theorem tor_paket_verweigert_ohne_xmm (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : xcrXMM xcrLo = false) :
    beobachtungsTor leaf1 xcrLo .paketInt128 = false := by
  simp [beobachtungsTor, h]

/-- Absent silicon bit refuses the scalar-double closing. -/
theorem geschlossen_sse_verweigert_ohne_bit (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : edxSSE2 leaf1 = false) :
    featureGateGeschlossen hw b cpu x k leaf1 xcrLo .sseDoppel
      = false := by
  simp [featureGateGeschlossen, beobachtungsTor, h]

/-- Absent silicon bit refuses the packed-tier closing. -/
theorem geschlossen_paket_verweigert_ohne_bit (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : edxSSE2 leaf1 = false) :
    featureGateGeschlossen hw b cpu x k leaf1 xcrLo .paketInt128
      = false := by
  simp [featureGateGeschlossen, beobachtungsTor, h]

/-- Refused finite profile refuses the packed-tier closing, whatever
    the observed bits. -/
theorem geschlossen_paket_verweigert_ohne_merkmal (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : vektorHwZugelassen hw b cpu x k = false) :
    featureGateGeschlossen hw b cpu x k leaf1 xcrLo .paketInt128
      = false := by
  simp [featureGateGeschlossen, h]

/-- Refused finite profile refuses the scalar-double closing,
    whatever the observed bits. -/
theorem geschlossen_sse_verweigert_ohne_merkmal (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : merkmalZugelassen hw b .sseDoppel = false) :
    featureGateGeschlossen hw b cpu x k leaf1 xcrLo .sseDoppel
      = false := by
  simp [featureGateGeschlossen, h]

/-! ## 2. Encoding-level closing: absent bit refuses the encoding.

  Each tier's canonical byte decoder reuses the accepted decoder by
  name (pilot `decode` for scalar integer, `fpDecode` for
  scalar-double, `decodeVector` for the packed tier). The composed
  encoding admission is the feature closing AND successful decode:
  an absent gate bit refuses every encoding of that tier, and
  undecodable bytes refuse whatever the gate claims. -/

/-- Per-tier encoding check over the accepted canonical decoders. -/
def merkmalKodierungOk : PerfMerkmal → List Byte → Bool
  | .skalar64, bs => (decode bs).isSome
  | .skalar32, bs => (decode bs).isSome
  | .sseDoppel, bs => (fpDecode bs).isSome
  | .paketInt128, bs => (decodeVector bs).isSome

/-- Encoding admission: the feature closing AND a decodable encoding.
    Neither side alone admits an encoding. -/
def kodierungTor (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (m : PerfMerkmal)
    (bs : List Byte) : Bool :=
  featureGateGeschlossen hw b cpu x k leaf1 xcrLo m
    && merkmalKodierungOk m bs

/-- Absent silicon bit refuses every packed-tier encoding. -/
theorem kodierung_paket_verweigert_ohne_bit (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (bs : List Byte) (h : edxSSE2 leaf1 = false) :
    kodierungTor hw b cpu x k leaf1 xcrLo .paketInt128 bs
      = false := by
  unfold kodierungTor
  rw [geschlossen_paket_verweigert_ohne_bit hw b cpu x k leaf1 xcrLo h]
  simp

/-- Undecodable bytes refuse whatever the packed-tier gate claims. -/
theorem kodierung_paket_verweigert_ohne_bytes (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (bs : List Byte) (h : decodeVector bs = none) :
    kodierungTor hw b cpu x k leaf1 xcrLo .paketInt128 bs
      = false := by
  simp [kodierungTor, merkmalKodierungOk, h]

/-- Absent silicon bit refuses every scalar-double encoding. -/
theorem kodierung_sse_verweigert_ohne_bit (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (bs : List Byte) (h : edxSSE2 leaf1 = false) :
    kodierungTor hw b cpu x k leaf1 xcrLo .sseDoppel bs
      = false := by
  unfold kodierungTor
  rw [geschlossen_sse_verweigert_ohne_bit hw b cpu x k leaf1 xcrLo h]
  simp

/-- Undecodable bytes refuse whatever the scalar-double gate claims. -/
theorem kodierung_sse_verweigert_ohne_bytes (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (bs : List Byte) (h : fpDecode bs = none) :
    kodierungTor hw b cpu x k leaf1 xcrLo .sseDoppel bs
      = false := by
  simp [kodierungTor, merkmalKodierungOk, h]

/-- PLANTED ACCEPT: the canonical PXOR encoding is admitted under the
    full baseline gates with observed SSE2 and XCR0 XMM state. -/
theorem kodierung_paket_akzeptiert :
    kodierungTor basisHw vecZeugeBereit basisCpu basisXcr0
        basisKontrolle zeugeOut1 (BitVec.ofNat 32 0x6) .paketInt128
        (encodeVector (.pxorRR .xmm0 .xmm1)) = true := by
  decide

/-- PLANTED ACCEPT: the canonical ADDSD encoding is admitted under the
    full baseline gates with observed SSE2 and XCR0 XMM state. -/
theorem kodierung_sse_akzeptiert :
    kodierungTor basisHw basisBereit basisCpu basisXcr0
        basisKontrolle zeugeOut1 (BitVec.ofNat 32 0x6) .sseDoppel
        (fpEncodeAddsdRR .xmm0 .xmm1) = true := by
  decide

/-! ## 3. Per-image closing: the gate is re-checked per image.

  `bildFeatureTor` conjoins the validator skeleton admission
  (`valX86`, re-decided from the image's own bytes) with the feature
  closing. Validating an image re-decides the gate; no stale
  annotation is trusted. -/

/-- Per-image closing: checked image mapping and decode coverage AND
    the feature gate, re-decided for this image. -/
def bildFeatureTor (p : Profil) (bild : Bild) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild)
    (k : KontrollBild) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m : PerfMerkmal) : Bool :=
  valX86 p bild && featureGateGeschlossen hw b cpu x k leaf1 xcrLo m

/-- The per-image closing implies the checked image admission. -/
theorem bildFeatureTor_braucht_bild (p : Profil) (bild : Bild)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (m : PerfMerkmal)
    (h : bildFeatureTor p bild hw b cpu x k leaf1 xcrLo m = true) :
    valX86 p bild = true := by
  simp [bildFeatureTor] at h
  exact h.1

/-- The per-image closing implies the feature gate. -/
theorem bildFeatureTor_braucht_gate (p : Profil) (bild : Bild)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (m : PerfMerkmal)
    (h : bildFeatureTor p bild hw b cpu x k leaf1 xcrLo m = true) :
    featureGateGeschlossen hw b cpu x k leaf1 xcrLo m = true := by
  simp [bildFeatureTor] at h
  exact h.2

/-- PLANTED REFUSAL: the one-byte-mutated image refuses under full
    gates -- the refusal comes from the image side, never the gate. -/
theorem bild_tor_verweigert_ohne_bild :
    bildFeatureTor .p48 { valZeuge with datei := [natByte 0] }
        basisHw vecZeugeBereit basisCpu basisXcr0 basisKontrolle
        zeugeOut1 (BitVec.ofNat 32 0x6) .paketInt128 = false := by
  decide

/-- PLANTED REFUSAL: the accepted image refuses when the observed
    silicon bit is absent -- the refusal comes from the gate side. -/
theorem bild_tor_verweigert_ohne_bit :
    bildFeatureTor .p48 valZeuge basisHw vecZeugeBereit basisCpu
        basisXcr0 basisKontrolle ⟨0, 0, 0, 0⟩
        (BitVec.ofNat 32 0) .paketInt128 = false := by
  decide

/-! ## 4. The closing connection.

  One reached fetched CPUID-then-XGETBV chain (every premise reused
  from the accepted `cpu_kette_speichert_gatter`, never re-proved)
  observes the answers the per-image gate is re-checked against: the
  derived stored value reads back, RIP chains through both forms, the
  observed ECX is faithful, the packed-tier closing admits under the
  checked enabled-state admission, the per-image closing admits under
  the validated image, and the same observed answers still refuse the
  unimplemented 256-bit row. Every premise is used by the proof. -/

/-- COMPOSITION CLOSING: a reached observation chain closes the
    per-image feature gate and still refuses the unimplemented row. -/
theorem ComposeFeatureGate_verbindung
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild)
    (chw : CpuHw) (scope : CpuScope) (ctrl : CtrlState)
    (p : Profil) (bild : Bild)
    (s s1 s1p s2 : Zustand) (o1 : CpuOut)
    (hi lo : BitVec 32) (m' : Speicher) (daten : Adresse)
    (v w : Wort) (r1 r2 : List Byte) (leaf7 : CpuOut)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (hl1 : leseLock (geholt s) = false)
    (hf1 : fetchCpu s = some (.cpuid, r1))
    (hx1 : ausfuehrbarN s.speicher s.rip 2 = true)
    (ho : o1 = chw.cpuidAns (low32 (s.register .rax))
      (low32 (s.register .rcx)))
    (hs1 : cpuByteschritt chw scope ctrl false s = .ok s1)
    (hsel : low32 (s1p.register .rcx) = 0)
    (hw0 : chw.xcrAns 0 = some (hi, lo))
    (hl2 : leseLock (geholt s1p) = false)
    (hf2 : fetchCpu s1p = some (.xgetbv, r2))
    (hx2 : ausfuehrbarN s1p.speicher s1p.rip 3 = true)
    (hb : ecxXSAVE o1 = true)
    (hc : ctrl.cr4Osxsave = true)
    (hs2 : cpuByteschritt chw scope ctrl (ecxXSAVE o1) s1p = .ok s2)
    (hv : v = if avxBereit o1 lo then BitVec.ofNat 64 1
      else BitVec.ofNat 64 0)
    (hles : lesbar8 s2.speicher daten = true)
    (hmem : write64 s2.speicher daten v = some m')
    (hrd : read64 m' daten = some w)
    (hsse : edxSSE2 o1 = true)
    (hxmm : xcrXMM lo = true)
    (hgate : vektorHwZugelassen hw b cpu x k = true)
    (hval : valX86 p bild = true) :
    w = v ∧ v = (if avxBereit o1 lo then BitVec.ofNat 64 1
      else BitVec.ofNat 64 0)
      ∧ s1.rip = ripNach s.rip 2 ∧ s2.rip = ripNach s1p.rip 3
      ∧ (beobachteCpu s1).ecx.toNat = o1.ecx.toNat
      ∧ merkmalZugelassen hw b .paketInt128 = true
      ∧ featureGateGeschlossen hw b cpu x k o1 lo .paketInt128
        = true
      ∧ bildFeatureTor p bild hw b cpu x k o1 lo .paketInt128
        = true
      ∧ avx2ReiheGeschlossen hw b cpu x k o1 leaf7 lo = false := by
  have hkette := cpu_kette_speichert_gatter chw scope ctrl s s1 s1p
    s2 o1 hi lo m' daten v w r1 r2 hflt hvm hl1 hf1 hx1 ho hs1
    hsel hw0 hl2 hf2 hx2 hb hc hs2 hv hles hmem hrd
  obtain ⟨hw_eq, hv_eq, hrip1, hrip2, htreu⟩ := hkette
  refine ⟨hw_eq, hv_eq, hrip1, hrip2, htreu,
    vektorHw_braucht_merkmal hw b cpu x k hgate, ?_, ?_, ?_⟩
  · simp [featureGateGeschlossen, beobachtungsTor, hsse, hxmm,
      hgate]
  · simp [bildFeatureTor, featureGateGeschlossen, beobachtungsTor,
      hsse, hxmm, hgate, hval]
  · simp [avx2ReiheGeschlossen, stufe_avx256_verweigert]

/-! ## 5. Joint witness: reached observation, gate admission,
  memory-changing runs on both sides.

  The CPUID-then-XGETBV chain runs on actual fetched bytes, the
  observed answers admit the packed-tier closing and the per-image
  closing, the derived store observably changes memory, and the
  admitted gated vector step plus its MOVSD store (reused from the
  accepted `vectorHw_zeuge`, never re-proved) changes a second
  memory byte. Non-degenerate: two fetched steps run and two stores
  change memory. -/

/-- Second observed leaf for the AVX2 row: zero (Reserved). -/
def zeugeBlatt7 : CpuOut := ⟨0, 0, 0, 0⟩

/-- The derived chain store observably changes memory: the data cell
    holds zero before and the derived one-word afterwards. -/
theorem compose_kette_speicher_aendert :
    zeugeM.bytes zeugenDatenCpu
      ≠ zeugeS2.speicher.bytes zeugenDatenCpu := by
  have hspeicher : zeugeS2.speicher = zeugeStart0.speicher := rfl
  have hhit := writeBytesN_hit zeugeS2.speicher zeugenDatenCpu
    (BitVec.ofNat 64 1) 8 0 (by decide) (by decide)
  rw [addrOff_null zeugenDatenCpu] at hhit
  have halt : zeugeS2.speicher.bytes zeugenDatenCpu
      = BitVec.ofNat 8 0 := by
    rw [hspeicher]
    exact zeuge_daten_null
  show writeBytes zeugeS2.speicher zeugenDatenCpu
    (BitVec.ofNat 64 1) zeugenDatenCpu ≠ _
  unfold writeBytes
  rw [hhit, halt]
  decide

/-- JOINT COMPANION WITNESS: every premise of
    `ComposeFeatureGate_verbindung` instantiated jointly on the
    concrete reached chain, plus the memory-change evidence on both
    sides (chain store and admitted gated vector step with MOVSD
    store). -/
theorem ComposeFeatureGate_verbindung_zeuge :
    ((1 : Wort) = BitVec.ofNat 64 1)
      ∧ (1 : Wort) = (if avxBereit zeugeOut1 (BitVec.ofNat 32 0x6)
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)
      ∧ zeugeS1.rip = ripNach zeugeStart0.rip 2
      ∧ zeugeS2.rip = ripNach zeugeS1p.rip 3
      ∧ (beobachteCpu zeugeS1).ecx.toNat = zeugeOut1.ecx.toNat
      ∧ merkmalZugelassen basisHw vecZeugeBereit .paketInt128 = true
      ∧ featureGateGeschlossen basisHw vecZeugeBereit basisCpu
          basisXcr0 basisKontrolle zeugeOut1 (BitVec.ofNat 32 0x6)
          .paketInt128 = true
      ∧ bildFeatureTor .p48 valZeuge basisHw vecZeugeBereit basisCpu
          basisXcr0 basisKontrolle zeugeOut1 (BitVec.ofNat 32 0x6)
          .paketInt128 = true
      ∧ avx2ReiheGeschlossen basisHw vecZeugeBereit basisCpu
          basisXcr0 basisKontrolle zeugeOut1 zeugeBlatt7
          (BitVec.ofNat 32 0x6) = false
      ∧ zeugeM.bytes zeugenDatenCpu
        ≠ zeugeS2.speicher.bytes zeugenDatenCpu
      ∧ read64 zeugeM zeugenDatenCpu = some (BitVec.ofNat 64 1)
      ∧ (∃ (bs : List Byte) (dec : VectorDec) (rest : List Byte)
          (t1 t2 : FpZustand),
          decodeVector bs = some (dec, rest) ∧
          dec.laenge + rest.length = bs.length ∧
          vektorHwZugelassen basisHw vecZeugeBereit basisCpu
              basisXcr0 basisKontrolle = true ∧
          stepVectorHw dec vecZeugeT0 basisHw vecZeugeBereit
              basisCpu basisXcr0 basisKontrolle = some t1 ∧
          stepExt (.vec dec) vecZeugeT0 vecZeugeBereit
            = .weiter t1 ∧
          (∃ m2 : Speicher, ∃ store : FpDecodiert,
            fpSchritt store t1 = some t2 ∧ t2.kern.speicher = m2 ∧
            m2.bytes 0 ≠ vecZeugeT0.kern.speicher.bytes 0)) := by
  obtain ⟨r1, hf1⟩ := zeuge_fetch0
  obtain ⟨r2, hf2⟩ := zeuge_fetch1p
  have hflt : (zeugeScope.faultEnabled && decide (0 < zeugeScope.cpl))
      = false := by
    decide
  have hvm : zeugeScope.vmNonRoot = false := by
    decide
  have ho : zeugeOut1 = zeugeHw.cpuidAns
      (low32 (zeugeStart0.register .rax))
      (low32 (zeugeStart0.register .rcx)) := by
    have e1 : zeugeStart0.register .rax = (zeugenRegCpu 1 0) .rax :=
      rfl
    have e2 : zeugeStart0.register .rcx = (zeugenRegCpu 1 0) .rcx :=
      rfl
    rw [e1, e2, zeuge_low32_rax, zeuge_low32_rcx]
    exact zeugeOut1_ans.symm
  have hsel : low32 (zeugeS1p.register .rcx) = 0 := by
    decide
  have hw0 : zeugeHw.xcrAns 0
      = some (BitVec.ofNat 32 0, BitVec.ofNat 32 0x6) := by
    decide
  have hb : ecxXSAVE zeugeOut1 = true := by
    decide
  have hc : zeugeCtrl.cr4Osxsave = true := by
    decide
  have hv : (1 : Wort) = if avxBereit zeugeOut1 (BitVec.ofNat 32 0x6)
      then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
    decide
  have hsse : edxSSE2 zeugeOut1 = true := by
    decide
  have hxmm : xcrXMM (BitVec.ofNat 32 0x6) = true := by
    decide
  have main := ComposeFeatureGate_verbindung basisHw vecZeugeBereit
    basisCpu basisXcr0 basisKontrolle zeugeHw zeugeScope zeugeCtrl
    .p48 valZeuge zeugeStart0 zeugeS1 zeugeS1p zeugeS2 zeugeOut1
    (BitVec.ofNat 32 0) (BitVec.ofNat 32 0x6) zeugeM zeugenDatenCpu
    1 1 r1 r2 zeugeBlatt7 hflt hvm zeuge_start_ohne_lock hf1
    zeuge_start_exec_cpuid ho zeuge_schritt1 hsel hw0
    zeuge_s1p_ohne_lock hf2 zeuge_s1p_exec_xgetbv hb hc
    zeuge_schritt2 hv zeuge_lesbar zeuge_mem_schritt
    zeuge_mem_liest hsse hxmm basis_vektorHw_zugelassen
    valZeuge_akzeptiert
  obtain ⟨hw1, hv1, hrip1, hrip2, htreu, hprof, hgateclos, hbild,
    havx2⟩ := main
  exact ⟨hw1, hv1, hrip1, hrip2, htreu, hprof, hgateclos, hbild,
    havx2, compose_kette_speicher_aendert, zeuge_mem_liest,
    vectorHw_zeuge⟩

/- CUTS: what is not proved here.

  - Composition only: every execution, decode, gate and witness fact
    is reused from the accepted producer modules by name
    (`cpu_kette_speichert_gatter` and its witness chain,
    `merkmalZugelassen`, `vektorHwZugelassen`,
    `vektorHw_braucht_merkmal`, `stufenZugelassenHw`,
    `stufe_avx256_verweigert`, `avx2Bereit`, `edxSSE2`, `xcrXMM`,
    `decode`/`fpDecode`/`decodeVector` with their round trips,
    `valX86`/`valZeuge`/`valZeuge_akzeptiert`,
    `vectorHw_zeuge`, `writeBytesN_hit`, `read64_nach_write64`).
    Nothing is re-proved and no interpreter or executor is duplicated.
  - The observed answers come from the reached chain's named hardware
    interface (`CpuHw.cpuidAns`/`xcrAns`); silicon correspondence of
    each bit position stays with the producer CUTS, and no new
    hardware claim is made here. The between-fetch selector gap
    (`hsel`/`hw0`) is inherited unchanged from the accepted chain.
  - Scalar integer rows close to the finite profile only: no
    CPUID/XCR0 bit exists for them (their `bereit` is constantly
    true), so there is no absent-bit refusal to close -- stated, not
    proved against silicon.
  - Extended-form decode coverage per image stays open: `valX86`
    covers the pilot forms; vector/scalar bytes validate through the
    fetch-discipline adapters (`vektorValidatorZugelassen`,
    `extZugelassen`) owned by the validator consumers, not through
    section coverage here. A vector-bytes image is not claimed to
    pass `valX86`.
  - Missing producer legs, never assumed: the per-access TSO bridge
    (lane 660 per the `CpuFeatureHardwareForms` CUTS), any
    source/checker/emitter correspondence, budget transfer,
    concurrency beyond the reused sequential round trips, timing
    bounds, and OS configuration (user logic, checked inputs only).
  - The 256-bit AVX row is a permanent refusal here
    (`avx2_reihe_verweigert_immer`); its implementation stays open.
-/

#print axioms avx2_reihe_verweigert_immer
#print axioms tor_sse_verweigert_ohne_bit
#print axioms tor_paket_verweigert_ohne_bit
#print axioms tor_paket_verweigert_ohne_xmm
#print axioms geschlossen_sse_verweigert_ohne_bit
#print axioms geschlossen_paket_verweigert_ohne_bit
#print axioms geschlossen_paket_verweigert_ohne_merkmal
#print axioms geschlossen_sse_verweigert_ohne_merkmal
#print axioms kodierung_paket_verweigert_ohne_bit
#print axioms kodierung_paket_verweigert_ohne_bytes
#print axioms kodierung_sse_verweigert_ohne_bit
#print axioms kodierung_sse_verweigert_ohne_bytes
#print axioms kodierung_paket_akzeptiert
#print axioms kodierung_sse_akzeptiert
#print axioms bildFeatureTor_braucht_bild
#print axioms bildFeatureTor_braucht_gate
#print axioms bild_tor_verweigert_ohne_bild
#print axioms bild_tor_verweigert_ohne_bit
#print axioms ComposeFeatureGate_verbindung
#print axioms ComposeFeatureGate_verbindung_zeuge
#print axioms compose_kette_speicher_aendert

end Gabbro.Grammatik.X86
