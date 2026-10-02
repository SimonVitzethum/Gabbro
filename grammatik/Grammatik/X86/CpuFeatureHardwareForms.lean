/-
  File:      Grammatik/X86/CpuFeatureHardwareForms.lean
  Subject:   CPUID and XGETBV fetched byte execution over canonical state.

  Lane 688: exact fetched byte forms of CPUID (0F A2) and XGETBV
  (NP 0F 01 D0) over canonical `Zustand`/`Speicher`, with one generic
  named hardware CPU-information/XCR0 answer interface. Official
  reference: Intel SDM 325462-093US (Sep 2026), Vol. 2A CPUID entry
  pp. 3-202-3-204 and Vol. 2D XGETBV entry pp. 6-36-6-37, plus Vol. 1
  Chapters 13-14 (XSAVE/XCR0 enumeration, CPUID.01H ECX
  XSAVE[26]/OSXSAVE[27]/AVX[28], EDX SSE2[26], CPUID.07H:00H EBX
  AVX2[5], XCR0 XMM[1]+YMM[2], AVX detection sequence); local snapshot
  `.tmp/HARDWARE-REFERENCES/` (exact record in CUTS). No host probing;
  no AMD snapshot (none available); see CUTS.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- CPUID output: exact 32-bit EAX/EBX/ECX/EDX fields. -/
structure CpuOut where
  eax : BitVec 32
  ebx : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32
  deriving DecidableEq, Repr, Inhabited

/-- Bit test of a 32-bit word. -/
def bit32 (w : BitVec 32) (i : Nat) : Bool :=
  decide ((w.toNat / 2 ^ i) % 2 = 1)

/-- Skeleton witness: bit 26 of 0x04000000 is set. -/
theorem bit32_skelett : bit32 0x04000000 26 = true := by
  decide

/-! ## 1. Generic named hardware interface.

  `CpuHw.cpuidAns` is IMMUTABLE silicon information (leaf/subleaf to
  exact fields); `CpuHw.xcrAns` is SOFTWARE-WRITTEN control state
  (XSETBV-written XCR values, selector to EDX:EAX, `none` = invalid
  selector). `CtrlState` is the CR4.OSXSAVE enable bit. Nothing here
  probes the host; answers come only from the named `hw` parameter.
  Unsupported leaves are whatever `cpuidAns` says (Reserved), never #UD:
  the model invents no universal answers. -/

/-- Generic named hardware CPU-information/XCR0 answer interface. -/
structure CpuHw where
  cpuidAns : BitVec 32 → BitVec 32 → CpuOut
  xcrAns : BitVec 32 → Option (BitVec 32 × BitVec 32)

/-- Selected profile scope: CPUID-faulting enable, caller privilege and
    VMX non-root (VM exit) presence. -/
structure CpuScope where
  faultEnabled : Bool
  cpl : Nat
  vmNonRoot : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Software-written control state relevant here: CR4.OSXSAVE[18]. -/
structure CtrlState where
  cr4Osxsave : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Hardware fault classes: invalid opcode vs general protection. -/
inductive CpuHwFault where
  | ud : CpuHwFault
  | gp : CpuHwFault
  deriving DecidableEq, Repr, Inhabited

/-- Low 32 bits of a 64-bit word (CPUID leaf/subleaf, XGETBV selector). -/
def low32 (w : Wort) : BitVec 32 := BitVec.ofNat 32 (w.toNat % 2 ^ 32)

/-- Zero extension of a 32-bit field: outputs clear the high halves. -/
def zext64 (v : BitVec 32) : Wort := BitVec.ofNat 64 v.toNat

/-- Zero extension keeps the value below 2^32 (high half cleared). -/
theorem zext64_klein (v : BitVec 32) : (zext64 v).toNat = v.toNat := by
  unfold zext64
  rw [BitVec.toNat_ofNat]
  have h64 : v.toNat < 2 ^ 64 := by
    have h := v.isLt
    omega
  exact Nat.mod_eq_of_lt h64

/-- Round trip on the value level: low32 recovers a zero-extended field. -/
theorem low32_zext64_nat (v : BitVec 32) :
    (low32 (zext64 v)).toNat = v.toNat := by
  have h1 : (zext64 v).toNat = v.toNat := zext64_klein v
  unfold low32
  rw [BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt v.isLt,
    Nat.mod_eq_of_lt v.isLt]

/-- Words agreeing on the low 32 bits share their selector/leaf view:
    the high 32 bits of RCX/EAX never steer CPUID/XGETBV. -/
theorem low32_gleich_mod (a b : Wort)
    (h : a.toNat % 2 ^ 32 = b.toNat % 2 ^ 32) :
    low32 a = low32 b := by
  unfold low32
  rw [h]

/-! ## 2. Fetched byte forms.

  CPUID is exactly `0F A2` (Intel SDM Vol. 2A, CPUID pp. 3-202ff);
  XGETBV is exactly `NP 0F 01 D0` (Vol. 2D, XGETBV pp. 6-36f).
  A leading LOCK prefix (F0) is a precise #UD, never silent
  acceptance. Both forms are refused by the canonical pilot decoder,
  so no existing form is shadowed. -/

/-- CPUID/XGETBV instruction form. -/
inductive CpuForm where
  | cpuid : CpuForm
  | xgetbv : CpuForm
  deriving DecidableEq, Repr, Inhabited

/-- Consumed length: 2 for CPUID, 3 for XGETBV. -/
def cpuLen : CpuForm → Nat
  | .cpuid => 2
  | .xgetbv => 3

/-- Canonical bytes. -/
def cpuEncode : CpuForm → List Byte
  | .cpuid => [natByte 15, natByte 162]
  | .xgetbv => [natByte 15, natByte 1, natByte 208]

/-- Decode one CPUID/XGETBV form; truncated or other inputs refuse. -/
def decodeCpuFeature : List Byte → Option (CpuForm × List Byte)
  | b0 :: b1 :: rest =>
    if byteNat b0 == 15 && byteNat b1 == 162 then some (.cpuid, rest)
    else
      match rest with
      | b2 :: rest' =>
        if byteNat b0 == 15 && byteNat b1 == 1 && byteNat b2 == 208 then
          some (.xgetbv, rest')
        else none
      | [] => none
  | _ => none

/-- LOCK prefix byte (F0), read off actual fetched bytes. -/
def lockPrefix : Byte := natByte 240

/-- Prefix observation: the fetched window starts with LOCK. -/
def leseLock : List Byte → Bool
  | b0 :: _ => byteNat b0 == 240
  | [] => false

/-- CPUID bytes decode back to CPUID over any suffix. -/
theorem decodeCpu_cpuid (suffix : List Byte) :
    decodeCpuFeature (cpuEncode .cpuid ++ suffix) = some (.cpuid, suffix) := by
  have h15 : 15 % 256 = 15 := by decide
  have h162 : 162 % 256 = 162 := by decide
  simp only [cpuEncode, List.cons_append, decodeCpuFeature,
    byteNat_natByte_any, h15, h162, beq_self_eq_true, Bool.true_and]
  simp

/-- XGETBV bytes decode back to XGETBV over any suffix. -/
theorem decodeCpu_xgetbv (suffix : List Byte) :
    decodeCpuFeature (cpuEncode .xgetbv ++ suffix)
      = some (.xgetbv, suffix) := by
  have h15 : 15 % 256 = 15 := by decide
  have h1 : 1 % 256 = 1 := by decide
  have h208 : 208 % 256 = 208 := by decide
  simp only [cpuEncode, List.cons_append, decodeCpuFeature,
    byteNat_natByte_any, h15, h1, h208]
  simp

/-- Both lengths are within the 1..15 bound. -/
theorem cpuLen_ok (f : CpuForm) : 1 ≤ cpuLen f ∧ cpuLen f ≤ 15 := by
  cases f <;> decide

/-- The pilot decoder refuses the CPUID bytes: no form is shadowed. -/
theorem pilot_verweigert_cpuid :
    decode [natByte 15, natByte 162] = none := by
  decide

/-- The pilot decoder refuses the XGETBV bytes: no form is shadowed. -/
theorem pilot_verweigert_xgetbv :
    decode [natByte 15, natByte 1, natByte 208] = none := by
  decide

/-- A LOCK prefix before CPUID bytes is no CPUID form. -/
theorem lockPrefix_verweigert_cpuid :
    decodeCpuFeature [lockPrefix, natByte 15, natByte 162] = none := by
  decide

/-- A LOCK prefix before XGETBV bytes is no XGETBV form. -/
theorem lockPrefix_verweigert_xgetbv :
    decodeCpuFeature [lockPrefix, natByte 15, natByte 1, natByte 208]
      = none := by
  decide

/-- A lone 0F prefix is truncated. -/
theorem decodeCpu_nichts_praefix_allein :
    decodeCpuFeature [natByte 15] = none := rfl

/-- Empty input decodes to nothing. -/
theorem decodeCpu_nichts_leer : decodeCpuFeature [] = none := rfl

/-! ## 3. Register steps over canonical state.

  CPUID (Vol. 2A): leaf is low32 RAX, subleaf low32 RCX; the named
  answer is written zero-extended into RAX/RBX/RCX/RDX (high halves
  cleared); RIP advances by 2; flags and memory are untouched.
  XGETBV (Vol. 2D): selector is low32 RCX (high 32 of RCX ignored);
  the named EDX:EAX pair is written zero-extended; RIP advances by 3.
  Fault scope is explicit: LOCK is #UD; faulting-enabled CPL>0 is #GP;
  VMX non-root is a VM exit event; XGETBV needs the OBSERVED XSAVE bit
  plus CR4.OSXSAVE (#UD otherwise) and a valid selector (#GP). -/

/-- Step outcome: success, hardware fault, VM exit event or refusal. -/
inductive CpuErg where
  | ok : Zustand → CpuErg
  | fault : CpuHwFault → CpuErg
  | vmExit : CpuErg
  | refuse : CpuErg

/-- CPUID register step. -/
def cpuSchrittCpuid (hw : CpuHw) (scope : CpuScope) (s : Zustand)
    (lock : Bool) : CpuErg :=
  if lock then .fault .ud
  else if scope.faultEnabled && decide (0 < scope.cpl) then .fault .gp
  else if scope.vmNonRoot then .vmExit
  else
    let out := hw.cpuidAns (low32 (s.register .rax)) (low32 (s.register .rcx))
    let r1 := regSet s.register .rax (zext64 out.eax)
    let r2 := regSet r1 .rbx (zext64 out.ebx)
    let r3 := regSet r2 .rcx (zext64 out.ecx)
    let r4 := regSet r3 .rdx (zext64 out.edx)
    .ok { s with register := r4, rip := ripNach s.rip 2 }

/-- XGETBV register step. `beobXSAVE` is the XSAVE bit OBSERVED in a
    fetched CPUID leaf-1 answer (threaded by the joint sequence §8),
    never a host probe. -/
def cpuSchrittXgetbv (hw : CpuHw) (ctrl : CtrlState) (beobXSAVE : Bool)
    (s : Zustand) (lock : Bool) : CpuErg :=
  if lock then .fault .ud
  else if !beobXSAVE || !ctrl.cr4Osxsave then .fault .ud
  else
    match hw.xcrAns (low32 (s.register .rcx)) with
    | some (hi, lo) =>
      let r1 := regSet s.register .rax (zext64 lo)
      let r2 := regSet r1 .rdx (zext64 hi)
      .ok { s with register := r2, rip := ripNach s.rip 3 }
    | none => .fault .gp

/-- LOCK prefix on CPUID is #UD. -/
theorem cpuid_lock_ud (hw : CpuHw) (scope : CpuScope) (s : Zustand) :
    cpuSchrittCpuid hw scope s true = .fault .ud := by
  unfold cpuSchrittCpuid
  simp

/-- Faulting-enabled CPL>0 on CPUID is #GP (named CPUID-faulting). -/
theorem cpuid_fault_gp (hw : CpuHw) (s : Zustand)
    (scope : CpuScope) (hf : scope.faultEnabled = true)
    (hc : 0 < scope.cpl) :
    cpuSchrittCpuid hw scope s false = .fault .gp := by
  unfold cpuSchrittCpuid
  simp [hf, hc]

/-- VMX non-root CPUID is a VM exit event, not a fault. -/
theorem cpuid_vmExit (hw : CpuHw) (s : Zustand)
    (scope : CpuScope) (hf : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = true) :
    cpuSchrittCpuid hw scope s false = .vmExit := by
  unfold cpuSchrittCpuid
  simp [hf, hvm]

/-- CPUID writes the observed EAX field zero-extended into RAX. -/
theorem cpuid_schreibt_rax (hw : CpuHw) (scope : CpuScope) (s s' : Zustand)
    (lock : Bool) (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (h : cpuSchrittCpuid hw scope s lock = .ok s') :
    s'.register .rax
      = zext64 (hw.cpuidAns (low32 (s.register .rax))
        (low32 (s.register .rcx))).eax := by
  unfold cpuSchrittCpuid at h
  rw [hlock, hflt, hvm] at h
  cases h
  simp only []
  rw [regSet_fremd _ .rdx .rax _ (by decide)]
  rw [regSet_fremd _ .rcx .rax _ (by decide)]
  rw [regSet_fremd _ .rbx .rax _ (by decide)]
  exact regSet_gleich _ _ _

/-- CPUID clears the high half of RAX. -/
theorem cpuid_rax_hoch_null (hw : CpuHw) (scope : CpuScope) (s s' : Zustand)
    (lock : Bool) (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (h : cpuSchrittCpuid hw scope s lock = .ok s') :
    (s'.register .rax).toNat < 2 ^ 32 := by
  have hr := cpuid_schreibt_rax hw scope s s' lock hlock hflt hvm h
  rw [hr, zext64_klein]
  exact (hw.cpuidAns _ _).eax.isLt

/-- CPUID keeps flags and memory; RIP advances by exactly 2. -/
theorem cpuid_rahmen (hw : CpuHw) (scope : CpuScope) (s s' : Zustand)
    (lock : Bool) (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (h : cpuSchrittCpuid hw scope s lock = .ok s') :
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip 2 := by
  unfold cpuSchrittCpuid at h
  rw [hlock, hflt, hvm] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- CPUID never touches the stack pointer. -/
theorem cpuid_rsp_bleibt (hw : CpuHw) (scope : CpuScope) (s s' : Zustand)
    (lock : Bool) (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (h : cpuSchrittCpuid hw scope s lock = .ok s') :
    s'.register .rsp = s.register .rsp := by
  unfold cpuSchrittCpuid at h
  rw [hlock, hflt, hvm] at h
  cases h
  simp only []
  rw [regSet_fremd _ .rdx .rsp _ (by decide)]
  rw [regSet_fremd _ .rcx .rsp _ (by decide)]
  rw [regSet_fremd _ .rbx .rsp _ (by decide)]
  rw [regSet_fremd _ .rax .rsp _ (by decide)]

/-- LOCK prefix on XGETBV is #UD. -/
theorem xgetbv_lock_ud (hw : CpuHw) (ctrl : CtrlState) (beobXSAVE : Bool)
    (s : Zustand) :
    cpuSchrittXgetbv hw ctrl beobXSAVE s true = .fault .ud := by
  unfold cpuSchrittXgetbv
  simp

/-- XGETBV without the observed XSAVE bit is #UD. -/
theorem xgetbv_ohne_beob_ud (hw : CpuHw) (ctrl : CtrlState)
    (s : Zustand) (lock : Bool) :
    cpuSchrittXgetbv hw ctrl false s lock =
      if lock then .fault .ud else .fault .ud := by
  unfold cpuSchrittXgetbv
  cases lock <;> simp

/-- XGETBV without CR4.OSXSAVE is #UD. -/
theorem xgetbv_ohne_os_ud (hw : CpuHw) (beobXSAVE : Bool)
    (s : Zustand) :
    cpuSchrittXgetbv hw ⟨false⟩ beobXSAVE s false = .fault .ud := by
  unfold cpuSchrittXgetbv
  simp

/-- XGETBV with an invalid selector is #GP. -/
theorem xgetbv_ungueltig_gp (hw : CpuHw) (ctrl : CtrlState)
    (beobXSAVE : Bool) (s : Zustand) (lock : Bool)
    (hlock : lock = false) (hb : beobXSAVE = true)
    (hc : ctrl.cr4Osxsave = true)
    (h : hw.xcrAns (low32 (s.register .rcx)) = none) :
    cpuSchrittXgetbv hw ctrl beobXSAVE s lock = .fault .gp := by
  unfold cpuSchrittXgetbv
  rw [hlock, hb, hc] at *
  simp [h]

/-! ## 4. XGETBV success, selector scope and feature gates.

  Bit positions (Intel SDM Vol. 1 Ch. 13-14, Vol. 2A CPUID leaf tables):
  leaf 1 EDX[26] SSE2, ECX[26] XSAVE, ECX[27] OSXSAVE, ECX[28] AVX;
  leaf 7 subleaf 0 EBX[5] AVX2; XCR0 EAX[1] XMM, EAX[2] YMM.
  Immutable silicon bits (observed CPUID answers) stay distinct from
  software-written control state (XCR0 answer, CR4.OSXSAVE). -/

/-- XGETBV writes the named pair zero-extended into RAX/RDX. -/
theorem xgetbv_schreibt (hw : CpuHw) (ctrl : CtrlState) (beobXSAVE : Bool)
    (s s' : Zustand) (lock : Bool) (hi lo : BitVec 32)
    (hlock : lock = false) (hb : beobXSAVE = true)
    (hc : ctrl.cr4Osxsave = true)
    (hans : hw.xcrAns (low32 (s.register .rcx)) = some (hi, lo))
    (h : cpuSchrittXgetbv hw ctrl beobXSAVE s lock = .ok s') :
    s'.register .rax = zext64 lo ∧ s'.register .rdx = zext64 hi := by
  unfold cpuSchrittXgetbv at h
  simp only [hlock, hb, hc, Bool.not_true, Bool.false_or] at h
  rw [hans] at h
  cases h
  constructor
  · simp only []
    rw [regSet_fremd _ .rdx .rax _ (by decide)]
    exact regSet_gleich _ _ _
  · simp only []
    exact regSet_gleich _ _ _

/-- XGETBV keeps RCX/RBX, flags and memory; RIP advances by exactly 3. -/
theorem xgetbv_rahmen (hw : CpuHw) (ctrl : CtrlState) (beobXSAVE : Bool)
    (s s' : Zustand) (lock : Bool) (hi lo : BitVec 32)
    (hlock : lock = false) (hb : beobXSAVE = true)
    (hc : ctrl.cr4Osxsave = true)
    (hans : hw.xcrAns (low32 (s.register .rcx)) = some (hi, lo))
    (h : cpuSchrittXgetbv hw ctrl beobXSAVE s lock = .ok s') :
    s'.register .rcx = s.register .rcx ∧
      s'.register .rbx = s.register .rbx ∧ s'.flags = s.flags ∧
      s'.speicher = s.speicher ∧ s'.rip = ripNach s.rip 3 := by
  unfold cpuSchrittXgetbv at h
  simp only [hlock, hb, hc, Bool.not_true, Bool.false_or] at h
  rw [hans] at h
  cases h
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp only []
    rw [regSet_fremd _ .rdx .rcx _ (by decide)]
    rw [regSet_fremd _ .rax .rcx _ (by decide)]
  · simp only []
    rw [regSet_fremd _ .rdx .rbx _ (by decide)]
    rw [regSet_fremd _ .rax .rbx _ (by decide)]

/-- The selector answer depends only on the low 32 bits of RCX. -/
theorem xgetbv_selektor_nur_tief (hw : CpuHw) (s1 s2 : Zustand)
    (h : low32 (s1.register .rcx) = low32 (s2.register .rcx)) :
    hw.xcrAns (low32 (s1.register .rcx))
      = hw.xcrAns (low32 (s2.register .rcx)) := by
  rw [h]

/-- High-32-bit formulation: words agreeing low give the same answer. -/
theorem xgetbv_rcx_hoch_ignoriert (hw : CpuHw) (s : Zustand) (w : Wort)
    (h : w.toNat % 2 ^ 32 = (s.register .rcx).toNat % 2 ^ 32) :
    hw.xcrAns (low32 w) = hw.xcrAns (low32 (s.register .rcx)) := by
  rw [low32_gleich_mod _ _ h]

/-- Leaf-1 EDX bit 26: silicon SSE2 (observed, immutable). -/
def edxSSE2 (o : CpuOut) : Bool := bit32 o.edx 26

/-- Leaf-1 ECX bit 26: silicon XSAVE (observed, immutable). -/
def ecxXSAVE (o : CpuOut) : Bool := bit32 o.ecx 26

/-- Leaf-1 ECX bit 27: silicon OSXSAVE (observed, immutable). -/
def ecxOSXSAVE (o : CpuOut) : Bool := bit32 o.ecx 27

/-- Leaf-1 ECX bit 28: silicon AVX (observed, immutable). -/
def ecxAVX (o : CpuOut) : Bool := bit32 o.ecx 28

/-- Leaf-7 subleaf-0 EBX bit 5: silicon AVX2 (observed, immutable). -/
def ebxAVX2 (o : CpuOut) : Bool := bit32 o.ebx 5

/-- XCR0 EAX bit 1: control-state XMM enabled (software-written). -/
def xcrXMM (lo : BitVec 32) : Bool := bit32 lo 1

/-- XCR0 EAX bit 2: control-state YMM enabled (software-written). -/
def xcrYMM (lo : BitVec 32) : Bool := bit32 lo 2

/-- AVX usability: silicon AVX AND silicon OSXSAVE AND control-state
    XMM+YMM. The first two premises are leaf-1 observations, the last
    two are XCR0 control state. -/
def avxBereit (leaf1 : CpuOut) (xcrLo : BitVec 32) : Bool :=
  ecxAVX leaf1 && ecxOSXSAVE leaf1 && xcrXMM xcrLo && xcrYMM xcrLo

/-- AVX2 usability adds leaf-7 AVX2 silicon. -/
def avx2Bereit (leaf1 leaf7 : CpuOut) (xcrLo : BitVec 32) : Bool :=
  avxBereit leaf1 xcrLo && ebxAVX2 leaf7

/-- Entry gate for entry validators: the observed triple an image
    entry must establish before AVX forms execute. -/
def eintrittAvxOk (leaf1 : CpuOut) (xcrLo : BitVec 32) : Bool :=
  avxBereit leaf1 xcrLo

/-- The XSAVE bit gating XGETBV is exactly leaf-1 ECX[26]. -/
theorem beobXSAVE_aus_leaf1 (leaf1 : CpuOut) :
    ecxXSAVE leaf1 = bit32 leaf1.ecx 26 := rfl

/-- No silicon AVX means no AVX readiness, whatever the control state. -/
theorem avxBereit_braucht_avx (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : ecxAVX leaf1 = false) : avxBereit leaf1 xcrLo = false := by
  unfold avxBereit
  rw [h]
  simp

/-- No silicon OSXSAVE means no AVX readiness. -/
theorem avxBereit_braucht_osxsave (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : ecxOSXSAVE leaf1 = false) : avxBereit leaf1 xcrLo = false := by
  unfold avxBereit
  rw [h]
  simp

/-- No control-state YMM means no AVX readiness, whatever silicon says. -/
theorem avxBereit_braucht_ymm (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (h : xcrYMM xcrLo = false) : avxBereit leaf1 xcrLo = false := by
  unfold avxBereit
  rw [h]
  simp

/-- Witness: full silicon plus XMM+YMM control state is ready. -/
theorem avxBereit_zeuge : avxBereit ⟨0, 0, 0x18000000, 0⟩ 0x6 = true := by
  decide

/-- Refusal: full silicon without control-state YMM is not ready. -/
theorem avxBereit_verweigert_ohne_ymm :
    avxBereit ⟨0, 0, 0x18000000, 0⟩ 0x2 = false := by
  decide

/-- Refusal: control state without silicon AVX is not ready. -/
theorem avxBereit_verweigert_ohne_silizium :
    avxBereit ⟨0, 0, 0, 0⟩ 0x6 = false := by
  decide

/-! ## 5. Fetched execution from actual executable memory.

  Fetch reuses the canonical window `geholt` (executable prefix only,
  capped at 15); decode runs on ACTUAL bytes, never on a hand-built
  instruction. Execution permission is checked for exactly the consumed
  length; truncation and non-executable RIP refuse. A LOCK prefix read
  off actual bytes turns a decodable form into #UD. -/

/-- Fetch and decode a CPUID/XGETBV form from actual memory. -/
def fetchCpu (s : Zustand) : Option (CpuForm × List Byte) :=
  decodeCpuFeature (geholt s)

/-- Fetched CPUID/XGETBV step from actual memory. -/
def cpuByteschritt (hw : CpuHw) (scope : CpuScope) (ctrl : CtrlState)
    (beobXSAVE : Bool) (s : Zustand) : CpuErg :=
  if leseLock (geholt s) then
    match decodeCpuFeature (geholt s).tail with
    | some _ => .fault .ud
    | none => .refuse
  else
    match fetchCpu s with
    | none => .refuse
    | some (f, _) =>
      if !(ausfuehrbarN s.speicher s.rip (cpuLen f)) then .refuse
      else
        match f with
        | .cpuid => cpuSchrittCpuid hw scope s false
        | .xgetbv => cpuSchrittXgetbv hw ctrl beobXSAVE s false

/-- Fetched CPUID coincides with the register step under fetch,
    permission and prefix premises. -/
theorem cpuByteschritt_wird_cpuid (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (beobXSAVE : Bool) (s : Zustand)
    (rest : List Byte)
    (hl : leseLock (geholt s) = false)
    (hf : fetchCpu s = some (.cpuid, rest))
    (hx : ausfuehrbarN s.speicher s.rip 2 = true) :
    cpuByteschritt hw scope ctrl beobXSAVE s
      = cpuSchrittCpuid hw scope s false := by
  unfold cpuByteschritt
  simp [hl, hf, hx, cpuLen]

/-- Fetched XGETBV coincides with the register step under fetch,
    permission and prefix premises. -/
theorem cpuByteschritt_wird_xgetbv (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (beobXSAVE : Bool) (s : Zustand)
    (rest : List Byte)
    (hl : leseLock (geholt s) = false)
    (hf : fetchCpu s = some (.xgetbv, rest))
    (hx : ausfuehrbarN s.speicher s.rip 3 = true) :
    cpuByteschritt hw scope ctrl beobXSAVE s
      = cpuSchrittXgetbv hw ctrl beobXSAVE s false := by
  unfold cpuByteschritt
  simp [hl, hf, hx, cpuLen]

/-- No fetched form means refusal, never a forged step. -/
theorem cpuByteschritt_verweigert_ohne_fetch (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (beobXSAVE : Bool) (s : Zustand)
    (hl : leseLock (geholt s) = false)
    (hf : fetchCpu s = none) :
    cpuByteschritt hw scope ctrl beobXSAVE s = .refuse := by
  unfold cpuByteschritt
  simp [hl, hf]

/-- A fetched form without execute permission for its bytes refuses. -/
theorem cpuByteschritt_verweigert_ohne_exec (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (beobXSAVE : Bool) (s : Zustand)
    (f : CpuForm) (rest : List Byte)
    (hl : leseLock (geholt s) = false)
    (hf : fetchCpu s = some (f, rest))
    (hx : ausfuehrbarN s.speicher s.rip (cpuLen f) = false) :
    cpuByteschritt hw scope ctrl beobXSAVE s = .refuse := by
  unfold cpuByteschritt
  simp [hl, hf, hx]

/-- A LOCK prefix before a decodable form is #UD at fetch. -/
theorem cpuByteschritt_lock_ud (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (beobXSAVE : Bool) (s : Zustand)
    (f : CpuForm) (rest : List Byte)
    (hl : leseLock (geholt s) = true)
    (hd : decodeCpuFeature (geholt s).tail = some (f, rest)) :
    cpuByteschritt hw scope ctrl beobXSAVE s = .fault .ud := by
  unfold cpuByteschritt
  simp [hl, hd]

/-- Outcome projections for witnesses (concrete data, no function compare). -/
def ergRip : CpuErg → Option Adresse
  | .ok s => some s.rip
  | _ => none

/-- Outcome projections for witnesses (concrete data, no function compare). -/
def ergReg (r : Register) : CpuErg → Option Wort
  | .ok s => some (s.register r)
  | _ => none

/-- Outcome projections for witnesses (concrete data, no function compare). -/
def ergCpuFehler : CpuErg → Option CpuHwFault
  | .fault f => some f
  | _ => none

/-! ## 6. Serialization interface for the TSO bridge (lane 660).

  CPUID is serializing (Vol. 2A): later fetches observe prior stores
  only once the core's own buffer drained. The step itself drains
  NOTHING: the exported precondition is own-buffer emptiness, shared
  with the fence gate (`zaunBereit`), never a foreign drain. -/

/-- CPUID serial precondition on core `c`: the own buffer is empty.
    This IS `zaunBereit`, not a new drain. -/
def cpuidSerialBereit (t : TSOZustand) (c : Nat) : Bool :=
  zaunBereit t c

/-- The serial precondition is the fence gate. -/
theorem cpuidSerialBereit_zaun (t : TSOZustand) (c : Nat) :
    cpuidSerialBereit t c = zaunBereit t c := rfl

/-- A pending own byte blocks the serial precondition. -/
theorem serial_blockiert_bei_eintrag (t t' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte t c a v = some t') :
    cpuidSerialBereit t' c = false := by
  have hbuf := issue_haengt_an t t' c a v h
  unfold cpuidSerialBereit zaunBereit
  rw [hbuf]
  cases t.puffer c <;> simp

/-- Foreign issues never change this core's serial precondition. -/
theorem serial_fremd_issue (t t' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte t c a v = some t')
    (d : Nat) (hd : d ≠ c) :
    cpuidSerialBereit t' d = cpuidSerialBereit t d := by
  unfold cpuidSerialBereit
  exact zaun_fremd_issue t t' c a v h d hd

/-- Foreign flushes never change this core's serial precondition. -/
theorem serial_fremd_flush (t t' : TSOZustand) (c : Nat)
    (h : flushKern t c = some t') (d : Nat) (hd : d ≠ c) :
    cpuidSerialBereit t' d = cpuidSerialBereit t d := by
  unfold cpuidSerialBereit
  exact zaun_fremd_flush t t' c h d hd

/-- Readiness on one core coexists with a pending foreign store: no
    foreign drain is ever claimed. -/
theorem serial_kein_fremd_drain :
    ∃ t : TSOZustand, cpuidSerialBereit t 0 = true ∧ t.puffer 1 ≠ [] := by
  obtain ⟨t, h1, h2⟩ := zaun_kein_fremd_drain
  refine ⟨t, ?_, h2⟩
  unfold cpuidSerialBereit
  exact h1

/-- CPUID writes the observed ECX field zero-extended into RCX. -/
theorem cpuid_schreibt_rcx (hw : CpuHw) (scope : CpuScope) (s s' : Zustand)
    (lock : Bool) (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (h : cpuSchrittCpuid hw scope s lock = .ok s') :
    s'.register .rcx
      = zext64 (hw.cpuidAns (low32 (s.register .rax))
        (low32 (s.register .rcx))).ecx := by
  unfold cpuSchrittCpuid at h
  rw [hlock, hflt, hvm] at h
  cases h
  simp only []
  rw [regSet_fremd _ .rdx .rcx _ (by decide)]
  exact regSet_gleich _ _ _

/-- Observed answer record rebuilt from fetched registers. -/
def beobachteCpu (s1 : Zustand) : CpuOut :=
  ⟨low32 (s1.register .rax), low32 (s1.register .rbx),
   low32 (s1.register .rcx), low32 (s1.register .rdx)⟩

/-- Bit tests depend only on the value. -/
theorem bit32_bei_gleichem_wert (a b : BitVec 32) (i : Nat)
    (h : a.toNat = b.toNat) : bit32 a i = bit32 b i := by
  unfold bit32
  rw [h]

/-- The observed ECX is faithful at the value level. -/
theorem beobachteCpu_ecx_treu (hw : CpuHw) (scope : CpuScope)
    (s s1 : Zustand) (o1 : CpuOut) (lock : Bool)
    (hlock : lock = false)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (ho : o1 = hw.cpuidAns (low32 (s.register .rax))
      (low32 (s.register .rcx)))
    (h : cpuSchrittCpuid hw scope s lock = .ok s1) :
    (beobachteCpu s1).ecx.toNat = o1.ecx.toNat := by
  have hr := cpuid_schreibt_rcx hw scope s s1 lock hlock hflt hvm h
  unfold beobachteCpu
  simp only []
  rw [hr, low32_zext64_nat, ho]

/-! ## 7. Joint fetched sequence with derived memory store.

  A reached fetched CPUID-then-XGETBV sequence records the observed
  answer bits and stores a derived feature value in actual canonical
  memory. The XGETBV gate bit is the OBSERVED leaf-1 XSAVE bit, never
  an assumed host fact. Between the two fetches ordinary straight-line
  code prepares the selector; the theorem takes that gap state with an
  explicit selector premise (`hsel`) and a named selector-0 validity
  premise (`hw0`), so no byte-level gap composition is claimed here. -/

/-- Witness RIP: code at 0x1000. -/
def zeugenRipCpu : Adresse := BitVec.ofNat 64 0x1000

/-- Witness data cell. -/
def zeugenDatenCpu : Adresse := BitVec.ofNat 64 0x2000

/-- Witness program: CPUID then XGETBV. -/
def zeugenProgCpu : List Byte :=
  [natByte 15, natByte 162, natByte 15, natByte 1, natByte 208]

/-- Witness bytes: program at 0x1000, zero elsewhere. -/
def zeugenBytesCpu (prog : List Byte) : Adresse → Byte :=
  fun a =>
    if a.toNat < 0x1000 then BitVec.ofNat 8 0
    else prog.getD (a.toNat - 0x1000) (BitVec.ofNat 8 0)

/-- Witness memory: program executable in its window, data RW at 0x2000. -/
def zeugenSpeicherCpu (prog : List Byte) (execLen : Nat) : Speicher :=
  { bytes := zeugenBytesCpu prog
    lesbar := fun a => decide (0x2000 ≤ a.toNat ∧ a.toNat < 0x2008)
    schreibbar := fun a => decide (0x2000 ≤ a.toNat ∧ a.toNat < 0x2008)
    ausfuehrbar :=
      fun a => decide (0x1000 ≤ a.toNat ∧ a.toNat < 0x1000 + execLen) }

/-- Witness registers over given RAX/RCX words. -/
def zeugenRegCpu (rax rcx : Wort) : Register → Wort := fun q =>
  if q = Register.rax then rax
  else if q = Register.rcx then rcx
  else if q = Register.rsp then BitVec.ofNat 64 0x8000
  else BitVec.ofNat 64 0

/-- Witness start state over program, window and RAX/RCX words. -/
def zeugenStartCpu (prog : List Byte) (execLen : Nat) (rax rcx : Wort) :
    Zustand :=
  { register := zeugenRegCpu rax rcx
    flags :=
      { cf := false, pf := false, af := none, zf := false,
        sf := false, of := false }
    rip := zeugenRipCpu
    speicher := zeugenSpeicherCpu prog execLen }

/-- Witness hardware: leaf 1 carries XSAVE+OSXSAVE+AVX and SSE2;
    every other leaf answers zero (Reserved, never #UD); only
    selector 0 is valid with XMM+YMM control state. -/
def zeugeHw : CpuHw :=
  { cpuidAns := fun leaf sub =>
      if leaf == BitVec.ofNat 32 1 && sub == BitVec.ofNat 32 0 then
        ⟨BitVec.ofNat 32 7, BitVec.ofNat 32 0,
         BitVec.ofNat 32 0x1C000000, BitVec.ofNat 32 0x04000000⟩
      else ⟨0, 0, 0, 0⟩
    xcrAns := fun sel =>
      if sel == BitVec.ofNat 32 0 then
        some (BitVec.ofNat 32 0, BitVec.ofNat 32 0x6)
      else none }

/-- Witness scope: no faulting, CPL 0, no VMX. -/
def zeugeScope : CpuScope := ⟨false, 0, false⟩

/-- Witness control: CR4.OSXSAVE set. -/
def zeugeCtrl : CtrlState := ⟨true⟩

/-- Witness start: CPUID then XGETBV executable, leaf 1 in RAX. -/
def zeugeStart0 : Zustand := zeugenStartCpu zeugenProgCpu 15 1 0

/-- Witness leaf-1 answer record. -/
def zeugeOut1 : CpuOut :=
  ⟨BitVec.ofNat 32 7, BitVec.ofNat 32 0,
   BitVec.ofNat 32 0x1C000000, BitVec.ofNat 32 0x04000000⟩

/-- The witness start fetches without a LOCK prefix. -/
theorem zeuge_start_ohne_lock :
    leseLock (geholt zeugeStart0) = false := by
  decide

/-- The witness start covers the CPUID bytes with execute permission. -/
theorem zeuge_start_exec_cpuid :
    ausfuehrbarN zeugeStart0.speicher zeugeStart0.rip 2 = true := by
  decide

/-- The witness start fetches a CPUID form. -/
theorem zeuge_start_form_cpuid :
    (fetchCpu zeugeStart0).map Prod.fst = some CpuForm.cpuid := by
  decide

/-- The witness start fetches something. -/
theorem zeuge_start_some :
    (fetchCpu zeugeStart0).isSome = true := by
  decide

/-- The witness start fetches CPUID with some rest. -/
theorem zeuge_fetch0 :
    ∃ rest : List Byte, fetchCpu zeugeStart0 = some (.cpuid, rest) := by
  cases h : fetchCpu zeugeStart0 with
  | some pr =>
    obtain ⟨f, restL⟩ := pr
    have h2 := zeuge_start_form_cpuid
    rw [h] at h2
    simp at h2
    rw [h2]
    exact ⟨restL, rfl⟩
  | none =>
    have h2 := zeuge_start_some
    rw [h] at h2
    simp at h2

/-- The witness leaf/subleaf words read back exactly. -/
theorem zeuge_low32_rax : low32 ((zeugenRegCpu 1 0) .rax) = 1 := by
  decide

/-- The witness leaf/subleaf words read back exactly. -/
theorem zeuge_low32_rcx : low32 ((zeugenRegCpu 1 0) .rcx) = 0 := by
  decide

/-- The witness hardware answers leaf 1 with the witness record. -/
theorem zeugeOut1_ans :
    zeugeHw.cpuidAns (BitVec.ofNat 32 1) (BitVec.ofNat 32 0)
      = zeugeOut1 := by
  decide

/-- Witness post-CPUID state: observed answers in place, RIP + 2. -/
def zeugeS1 : Zustand :=
  { register :=
      regSet (regSet (regSet (regSet (zeugenRegCpu 1 0)
        .rax (zext64 zeugeOut1.eax)) .rbx (zext64 zeugeOut1.ebx))
        .rcx (zext64 zeugeOut1.ecx)) .rdx (zext64 zeugeOut1.edx)
    flags := zeugeStart0.flags
    rip := ripNach zeugeStart0.rip 2
    speicher := zeugeStart0.speicher }

/-- The first fetched step reaches the explicit post-CPUID state. -/
theorem zeuge_schritt1 :
    cpuByteschritt zeugeHw zeugeScope zeugeCtrl false zeugeStart0
      = .ok zeugeS1 := by
  obtain ⟨rest, hf⟩ := zeuge_fetch0
  have hflt : (zeugeScope.faultEnabled && decide (0 < zeugeScope.cpl))
      = false := by
    decide
  have hvm : zeugeScope.vmNonRoot = false := by
    decide
  have b := cpuByteschritt_wird_cpuid zeugeHw zeugeScope zeugeCtrl false
    zeugeStart0 rest zeuge_start_ohne_lock hf zeuge_start_exec_cpuid
  rw [b]
  have hans : zeugeHw.cpuidAns (low32 (zeugeStart0.register .rax))
      (low32 (zeugeStart0.register .rcx)) = zeugeOut1 := by
    have e1 : zeugeStart0.register .rax = (zeugenRegCpu 1 0) .rax := rfl
    have e2 : zeugeStart0.register .rcx = (zeugenRegCpu 1 0) .rcx := rfl
    rw [e1, e2, zeuge_low32_rax, zeuge_low32_rcx]
    exact zeugeOut1_ans
  unfold cpuSchrittCpuid
  simp only [hflt, hvm, Bool.false_eq_true, if_false]
  rw [hans]
  rfl

/-- Witness gap state: selector prepared to 0 at the XGETBV bytes.
    Straight-line code between the fetches prepares the selector;
    the byte-level gap composition stays consumer-owned (see §7 head). -/
def zeugeS1p : Zustand :=
  { zeugeS1 with register := regSet zeugeS1.register .rcx (zext64 0) }

/-- The gap state fetches without a LOCK prefix. -/
theorem zeuge_s1p_ohne_lock :
    leseLock (geholt zeugeS1p) = false := by
  decide

/-- The gap state covers the XGETBV bytes with execute permission. -/
theorem zeuge_s1p_exec_xgetbv :
    ausfuehrbarN zeugeS1p.speicher zeugeS1p.rip 3 = true := by
  decide

/-- The gap state fetches an XGETBV form. -/
theorem zeuge_s1p_form_xgetbv :
    (fetchCpu zeugeS1p).map Prod.fst = some CpuForm.xgetbv := by
  decide

/-- The gap state fetches something. -/
theorem zeuge_s1p_some :
    (fetchCpu zeugeS1p).isSome = true := by
  decide

/-- The gap state fetches XGETBV with some rest. -/
theorem zeuge_fetch1p :
    ∃ rest : List Byte, fetchCpu zeugeS1p = some (.xgetbv, rest) := by
  cases h : fetchCpu zeugeS1p with
  | some pr =>
    obtain ⟨f, restL⟩ := pr
    have h2 := zeuge_s1p_form_xgetbv
    rw [h] at h2
    simp at h2
    rw [h2]
    exact ⟨restL, rfl⟩
  | none =>
    have h2 := zeuge_s1p_some
    rw [h] at h2
    simp at h2

/-- The observed XSAVE bit on the witness post-state is set. -/
theorem zeuge_beob_xsvae :
    ecxXSAVE (beobachteCpu zeugeS1) = true := by
  decide

/-- The witness hardware answers selector 0 with XMM+YMM. -/
theorem zeuge_xcr_0 :
    zeugeHw.xcrAns (low32 (zeugeS1p.register .rcx))
      = some (BitVec.ofNat 32 0, BitVec.ofNat 32 0x6) := by
  decide

/-- Witness post-XGETBV state: named pair in place, RIP + 3. -/
def zeugeS2 : Zustand :=
  { register :=
      regSet (regSet zeugeS1p.register .rax
        (zext64 (BitVec.ofNat 32 0x6))) .rdx (zext64 (BitVec.ofNat 32 0))
    flags := zeugeS1p.flags
    rip := ripNach zeugeS1p.rip 3
    speicher := zeugeS1p.speicher }

/-- The second fetched step reaches the explicit post-XGETBV state. -/
theorem zeuge_schritt2 :
    cpuByteschritt zeugeHw zeugeScope zeugeCtrl
      (ecxXSAVE (beobachteCpu zeugeS1)) zeugeS1p = .ok zeugeS2 := by
  obtain ⟨rest, hf⟩ := zeuge_fetch1p
  have b := cpuByteschritt_wird_xgetbv zeugeHw zeugeScope zeugeCtrl
    (ecxXSAVE (beobachteCpu zeugeS1)) zeugeS1p rest
    zeuge_s1p_ohne_lock hf zeuge_s1p_exec_xgetbv
  rw [b]
  have hb : ecxXSAVE (beobachteCpu zeugeS1) = true := zeuge_beob_xsvae
  have hc : zeugeCtrl.cr4Osxsave = true := by
    decide
  unfold cpuSchrittXgetbv
  simp only [hb, hc, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    if_false]
  rw [zeuge_xcr_0]
  rfl

/-- Witness post-store memory: derived value 1 at the data cell. -/
def zeugeM : Speicher :=
  { zeugeS2.speicher with
    bytes :=
      writeBytes zeugeS2.speicher zeugenDatenCpu (BitVec.ofNat 64 1) }

/-- The data cell is writable on the witness post-state. -/
theorem zeuge_schreibbar :
    schreibbar8 zeugeS2.speicher zeugenDatenCpu = true := by
  decide

/-- The derived value stores into the explicit post-store memory. -/
theorem zeuge_mem_schritt :
    write64 zeugeS2.speicher zeugenDatenCpu (BitVec.ofNat 64 1)
      = some zeugeM := by
  unfold write64
  rw [if_pos zeuge_schreibbar]
  rfl

/-- The data cell is readable on the witness post-state. -/
theorem zeuge_lesbar :
    lesbar8 zeugeS2.speicher zeugenDatenCpu = true := by
  decide

/-- The derived value reads back from the post-store memory. -/
theorem zeuge_mem_liest :
    read64 zeugeM zeugenDatenCpu = some (BitVec.ofNat 64 1) := by
  exact read64_nach_write64 _ _ _ _ zeuge_mem_schritt zeuge_lesbar

/-- The data cell starts as zero: the store observably changes memory. -/
theorem zeuge_daten_null :
    zeugeStart0.speicher.bytes zeugenDatenCpu = BitVec.ofNat 8 0 := by
  decide

/-- Joint fetched CPUID/XGETBV sequence with derived memory store.
    Both fetched steps succeed, the observed XSAVE bit gates XGETBV,
    the derived AVX-ready value stores and reads back, RIP chains
    through both forms, and the observed ECX is faithful. Every
    premise is used by the proof. -/
theorem cpu_kette_speichert_gatter (hw : CpuHw) (scope : CpuScope)
    (ctrl : CtrlState) (s s1 s1p s2 : Zustand) (o1 : CpuOut)
    (hi lo : BitVec 32) (m' : Speicher) (daten : Adresse) (v w : Wort)
    (r1 r2 : List Byte)
    (hflt : (scope.faultEnabled && decide (0 < scope.cpl)) = false)
    (hvm : scope.vmNonRoot = false)
    (hl1 : leseLock (geholt s) = false)
    (hf1 : fetchCpu s = some (.cpuid, r1))
    (hx1 : ausfuehrbarN s.speicher s.rip 2 = true)
    (ho : o1 = hw.cpuidAns (low32 (s.register .rax))
      (low32 (s.register .rcx)))
    (hs1 : cpuByteschritt hw scope ctrl false s = .ok s1)
    (hsel : low32 (s1p.register .rcx) = 0)
    (hw0 : hw.xcrAns 0 = some (hi, lo))
    (hl2 : leseLock (geholt s1p) = false)
    (hf2 : fetchCpu s1p = some (.xgetbv, r2))
    (hx2 : ausfuehrbarN s1p.speicher s1p.rip 3 = true)
    (hb : ecxXSAVE o1 = true)
    (hc : ctrl.cr4Osxsave = true)
    (hs2 : cpuByteschritt hw scope ctrl (ecxXSAVE o1) s1p = .ok s2)
    (hv : v = if avxBereit o1 lo then BitVec.ofNat 64 1
      else BitVec.ofNat 64 0)
    (hles : lesbar8 s2.speicher daten = true)
    (hmem : write64 s2.speicher daten v = some m')
    (hrd : read64 m' daten = some w) :
    w = v ∧ v = (if avxBereit o1 lo then BitVec.ofNat 64 1
      else BitVec.ofNat 64 0)
      ∧ s1.rip = ripNach s.rip 2 ∧ s2.rip = ripNach s1p.rip 3
      ∧ (beobachteCpu s1).ecx.toNat = o1.ecx.toNat := by
  have b1 := cpuByteschritt_wird_cpuid hw scope ctrl false s r1
    hl1 hf1 hx1
  rw [b1] at hs1
  have hrahmen1 := cpuid_rahmen hw scope s s1 false rfl hflt hvm hs1
  have b2 := cpuByteschritt_wird_xgetbv hw scope ctrl (ecxXSAVE o1) s1p
    r2 hl2 hf2 hx2
  rw [b2] at hs2
  have hans : hw.xcrAns (low32 (s1p.register .rcx)) = some (hi, lo) := by
    rw [hsel, hw0]
  have hrahmen2 := xgetbv_rahmen hw ctrl (ecxXSAVE o1) s1p s2 false hi lo
    rfl hb hc hans hs2
  have hrd2 : read64 m' daten = some v :=
    read64_nach_write64 _ _ _ _ hmem hles
  rw [hrd] at hrd2
  cases hrd2
  refine ⟨rfl, hv, ?_, ?_, ?_⟩
  · obtain ⟨_, _, hrip1⟩ := hrahmen1
    exact hrip1
  · obtain ⟨_, _, _, _, hrip2⟩ := hrahmen2
    exact hrip2
  · exact beobachteCpu_ecx_treu hw scope s s1 o1 false rfl hflt hvm ho hs1

/-- Joint companion witness: the generic chain instantiated with
    all premises jointly on the concrete reached sequence, plus the
    memory-change evidence (data cell zero before, derived one after).
    Non-degenerate: two fetched steps run and the store changes memory. -/
theorem cpu_kette_speichert_gatter_zeuge :
    ((1 : Wort) = BitVec.ofNat 64 1)
      ∧ zeugeS1.rip = ripNach zeugeStart0.rip 2
      ∧ zeugeS2.rip = ripNach zeugeS1p.rip 3
      ∧ (beobachteCpu zeugeS1).ecx.toNat = zeugeOut1.ecx.toNat
      ∧ read64 zeugeM zeugenDatenCpu = some (BitVec.ofNat 64 1)
      ∧ zeugeStart0.speicher.bytes zeugenDatenCpu = BitVec.ofNat 8 0 := by
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
    have e1 : zeugeStart0.register .rax = (zeugenRegCpu 1 0) .rax := rfl
    have e2 : zeugeStart0.register .rcx = (zeugenRegCpu 1 0) .rcx := rfl
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
  have main := cpu_kette_speichert_gatter zeugeHw zeugeScope zeugeCtrl
    zeugeStart0 zeugeS1 zeugeS1p zeugeS2 zeugeOut1
    (BitVec.ofNat 32 0) (BitVec.ofNat 32 0x6) zeugeM
    zeugenDatenCpu 1 1 r1 r2 hflt hvm
    zeuge_start_ohne_lock hf1 zeuge_start_exec_cpuid ho
    zeuge_schritt1 hsel hw0
    zeuge_s1p_ohne_lock hf2 zeuge_s1p_exec_xgetbv hb hc
    zeuge_schritt2 hv zeuge_lesbar zeuge_mem_schritt zeuge_mem_liest
  obtain ⟨hw1, _, hrip1, hrip2, htreu⟩ := main
  exact ⟨hw1, hrip1, hrip2, htreu, zeuge_mem_liest, zeuge_daten_null⟩

/-- The first fetched step lands at 0x1002. -/
theorem zeuge_rip1_wert :
    zeugeS1.rip = BitVec.ofNat 64 0x1002 := by
  decide

/-- The second fetched step lands at 0x1005. -/
theorem zeuge_rip2_wert :
    zeugeS2.rip = BitVec.ofNat 64 0x1005 := by
  decide

/-- VM exit projection (no state compare needed). -/
def ergVm : CpuErg → Bool
  | .vmExit => true
  | _ => false

/-! ## 8. Planted refusals: selector, control, prefix, boundary, forgery.

  Wrong selector/feature/control/prefix/nonexec/forged-bit mutations
  show precise refusals or differing outcomes on actual fetched bytes. -/

/-- Witness XGETBV-only program. -/
def zeugenProgXgetbv : List Byte := [natByte 15, natByte 1, natByte 208]

/-- Witness XGETBV start over a given RCX word. -/
def zeugeStartSel (rcx : Wort) : Zustand :=
  zeugenStartCpu zeugenProgXgetbv 15 1 rcx

/-- Selector 2 on actual fetched bytes is #GP. -/
theorem zeuge_selektor_gp :
    ergCpuFehler (cpuByteschritt zeugeHw zeugeScope zeugeCtrl true
      (zeugeStartSel 2)) = some .gp := by
  decide

/-- XGETBV without CR4.OSXSAVE is #UD on actual fetched bytes. -/
theorem zeuge_ohne_os_ud :
    ergCpuFehler (cpuByteschritt zeugeHw zeugeScope ⟨false⟩ true
      (zeugeStartSel 0)) = some .ud := by
  decide

/-- Witness program: LOCK + CPUID. -/
def zeugenProgLock : List Byte := [natByte 240, natByte 15, natByte 162]

/-- LOCK before CPUID bytes faults #UD at fetch. -/
theorem zeuge_lock_ud :
    ergCpuFehler (cpuByteschritt zeugeHw zeugeScope zeugeCtrl false
      (zeugenStartCpu zeugenProgLock 15 1 0)) = some .ud := by
  decide

/-- Witness program: truncated XGETBV (third byte cut off). -/
def zeugenProgStumpf : List Byte := [natByte 15, natByte 1]

/-- A cut-off XGETBV has no transition. -/
theorem zeuge_stumpf_verweigert :
    ergRip (cpuByteschritt zeugeHw zeugeScope zeugeCtrl true
      (zeugenStartCpu zeugenProgStumpf 2 1 0)) = none := by
  decide

/-- Execute-denied XGETBV bytes admit no fetch. -/
theorem zeuge_ohne_exec_verweigert :
    ergRip (cpuByteschritt zeugeHw zeugeScope zeugeCtrl true
      (zeugenStartCpu zeugenProgXgetbv 0 1 0)) = none := by
  decide

/-- CPUID-faulting at CPL 3 is #GP on actual fetched bytes. -/
theorem zeuge_fault_gp :
    ergCpuFehler (cpuByteschritt zeugeHw ⟨true, 3, false⟩ zeugeCtrl false
      zeugeStart0) = some .gp := by
  decide

/-- VMX non-root CPUID is a VM exit on actual fetched bytes. -/
theorem zeuge_vmExit :
    ergVm (cpuByteschritt zeugeHw ⟨false, 0, true⟩ zeugeCtrl false
      zeugeStart0) = true := by
  decide

/-- Hardware without the XSAVE observation: leaf answers carry no bit. -/
def zeugeHwOhneXSAVE : CpuHw :=
  { cpuidAns := fun _ _ => ⟨0, 0, 0, 0⟩
    xcrAns := zeugeHw.xcrAns }

/-- The zero leaf genuinely clears the observed XSAVE bit. -/
theorem zeuge_xsvae_bit_klar :
    ecxXSAVE (zeugeHwOhneXSAVE.cpuidAns 1 0) = false := by
  decide

/-- With the observed bit clear, XGETBV faults #UD for every state. -/
theorem zeuge_ohne_beob_ud (s : Zustand) (lock : Bool) :
    cpuSchrittXgetbv zeugeHwOhneXSAVE zeugeCtrl
      (ecxXSAVE (zeugeHwOhneXSAVE.cpuidAns 1 0)) s lock
      = .fault .ud := by
  unfold cpuSchrittXgetbv
  rw [zeuge_xsvae_bit_klar]
  cases lock <;> simp

/-- Hardware with forged EBX bits. -/
def zeugeHwFalsch : CpuHw :=
  { cpuidAns := fun _ _ =>
      ⟨BitVec.ofNat 32 7, BitVec.ofNat 32 0xFFFFFFFF,
       BitVec.ofNat 32 0x1C000000, BitVec.ofNat 32 0x04000000⟩
    xcrAns := zeugeHw.xcrAns }

/-- Forged EBX bits change the observed outcome: no silent equality. -/
theorem zeuge_ausgang_unterscheidet :
    ergReg .rbx (cpuByteschritt zeugeHw zeugeScope zeugeCtrl false
      zeugeStart0)
      ≠ ergReg .rbx (cpuByteschritt zeugeHwFalsch zeugeScope zeugeCtrl
        false zeugeStart0) := by
  decide
/- CUTS: what is not proved here.

  Provenance (checked 2026-10-02 against the local snapshot
  `.tmp/HARDWARE-REFERENCES/`, REFERENCES.json sha256
  `a4a62e6a7ba11a76c7753a195b825087306812aac39b930973f9168ee599f321`,
  Intel SDM 325462-093US September 2026): the CPUID instruction entry
  (Vol. 2A pp. 3-202-3-204: opcode 0F A2, implicit EAX/ECX inputs,
  EAX/EBX/ECX/EDX outputs, high halves cleared on Intel 64,
  serializing, #UD iff LOCK, invalid leaves Reserved, VM exit under
  VMX non-root); the XGETBV instruction entry (Vol. 2D pp. 6-36-6-37:
  NP 0F 01 D0, ECX selector with high 32 of RCX ignored, EDX:EAX
  answer, #GP on any other selector, #UD on XSAVE=0, CR4.OSXSAVE=0
  or LOCK); Vol. 1 Chapters 13-14 (CPUID.01H ECX XSAVE[26],
  OSXSAVE[27], AVX[28]; EDX SSE2[26]; CPUID.07H:00H EBX AVX2[5];
  XCR0 XMM[1] and YMM[2]; the Example 14-1 AVX detection sequence).
  No AMD reference snapshot was available; no vendor-difference,
  silicon-timing or physical-hardware claim is made anywhere here.

  - Unsupported CPUID leaves answer Reserved from `hw`, never #UD;
    the selected fault/virtualization scope is explicit and narrow.
  - The between-fetch selector preparation is an explicit gap state
    (`hsel`/`hw0`); byte-level composition with a MOV lowering stays
    with the consumer lanes, as does fuller dispatcher integration
    (pilot disjointness is proved here; decodeExt composition is open).
  - CPUID serialization is a precondition interface
    (`cpuidSerialBereit` = `zaunBereit`); no drain, no timing bound,
    no cross-core effect and no bounded-hardware-timing claim.
  - No source/checker/emitter correspondence, no TSO-to-W/GX bridge
    (only the precondition interface for lane 660), no 674/670 or
    entry-validator integration (only the exported gate boundary:
    `CpuHw`, `CpuScope`, `CtrlState`, `avxBereit`, `eintrittAvxOk`,
    `cpuidSerialBereit`, `beobachteCpu`, `fetchCpu`, `cpuByteschritt`).
  - Only the selected leaves (1, 7/0), selector 0/1-scope validity
    and the SSE2/AVX/AVX2/OSXSAVE/XMM+YMM gates are modelled; all
    other leaves, selectors, features and control state stay open.
-/

#print axioms zext64_klein
#print axioms low32_zext64_nat
#print axioms decodeCpu_cpuid
#print axioms decodeCpu_xgetbv
#print axioms cpuid_schreibt_rax
#print axioms cpuid_rax_hoch_null
#print axioms xgetbv_schreibt
#print axioms avxBereit_zeuge
#print axioms cpuByteschritt_wird_cpuid
#print axioms cpuByteschritt_wird_xgetbv
#print axioms serial_kein_fremd_drain
#print axioms beobachteCpu_ecx_treu
#print axioms cpu_kette_speichert_gatter
#print axioms cpu_kette_speichert_gatter_zeuge
#print axioms zeuge_selektor_gp
#print axioms zeuge_ausgang_unterscheidet

end Gabbro.Grammatik.X86
