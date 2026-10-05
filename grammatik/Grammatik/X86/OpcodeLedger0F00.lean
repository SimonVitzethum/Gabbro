/-
  File:      Grammatik/X86/OpcodeLedger0F00.lean
  Subject:   Opcode ledger: two-byte opcodes 0F 00-0F 3F.

  Lane 1341: every opcode byte (and legal prefix/ModRM.reg extension)
  in the region, from SDM Vol 2 Table A-3 (snapshot in
  `.tmp/HARDWARE-REFERENCES/`, Intel 325462-093US Sep 2026),
  classified against the capstone chain `kapDecode`
  (`HwKapsteinDecoder.lean`). Self-contained schema.
-/
import Grammatik.X86.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86.OpcodeLedger0F00

/-- Ledger status of one opcode (prefix/extension) row. -/
inductive LStatus | modelliert | zurueckgestellt | verweigert | ungueltig64 | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: opcode byte, extension, mnemonic, status, family, reason. -/
structure LEintrag where
  op : Nat
  ext : String
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
deriving DecidableEq, Repr

open Gabbro.Grammatik.X86

/-! ## 1. Modelled rows: the chain takes these five witnesses.

  Found by probing `kapDecode` on every defined cell of rows
  0F 10-0F 2F (four probe rounds, see MUSE-REPORT-1341.md):
  only the scalar MOVSD/MOVSS loads, CVTSI2SS, CVTTSS2SI and
  UCOMISS decode. Every statement below is `decide`d. -/

/-- MOVSD load (F2 0F 10 /r): unified chain, FP arm. -/
theorem takes_movsd :
    kapDecode [natByte 242, natByte 15, natByte 16, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.fp
          { befehl := FpBefehl.movsdRR XmmReg.xmm0 XmmReg.xmm0,
            laenge := 4 })), []) := by
  decide

/-- MOVSS load (F3 0F 10 /r): s32 arm. -/
theorem takes_movss :
    kapDecode [natByte 243, natByte 15, natByte 16, natByte 192] =
      some (KapDekodiert.s32
        { befehl := S32Befehl.movssRR XmmReg.xmm0 XmmReg.xmm0,
          laenge := 4 }, []) := by
  decide

/-- CVTSI2SS (F3 0F 2A /r): s32 arm. -/
theorem takes_cvtsi2ss :
    kapDecode [natByte 243, natByte 15, natByte 42, natByte 192] =
      some (KapDekodiert.s32
        { befehl := S32Befehl.cvtsi2ss XmmReg.xmm0 Register.rax false,
          laenge := 4 }, []) := by
  decide

/-- CVTTSS2SI (F3 0F 2C /r): s32 arm. -/
theorem takes_cvttss2si :
    kapDecode [natByte 243, natByte 15, natByte 44, natByte 192] =
      some (KapDekodiert.s32
        { befehl := S32Befehl.cvttss2si Register.rax XmmReg.xmm0 false,
          laenge := 4 }, []) := by
  decide

/-- UCOMISS (0F 2E /r): s32 arm. -/
theorem takes_ucomiss :
    kapDecode [natByte 15, natByte 46, natByte 192] =
      some (KapDekodiert.s32
        { befehl := S32Befehl.ucomissRR XmmReg.xmm0 XmmReg.xmm0,
          laenge := 3 }, []) := by
  decide

/-! ## 2. Group 6 (0F 00): segment/protection forms, all refused. -/

theorem refuses_sldt : kapDecode [natByte 15, natByte 0, natByte 192] = none := by decide
theorem refuses_str : kapDecode [natByte 15, natByte 0, natByte 200] = none := by decide
theorem refuses_lldt : kapDecode [natByte 15, natByte 0, natByte 208] = none := by decide
theorem refuses_ltr : kapDecode [natByte 15, natByte 0, natByte 216] = none := by decide
theorem refuses_verr : kapDecode [natByte 15, natByte 0, natByte 224] = none := by decide
theorem refuses_verw : kapDecode [natByte 15, natByte 0, natByte 232] = none := by decide
theorem refuses_grp6res : kapDecode [natByte 15, natByte 0, natByte 240] = none := by decide
theorem refuses_lkgs : kapDecode [natByte 242, natByte 15, natByte 0, natByte 240] = none := by decide

/-! ## 3. Group 7 (0F 01): system-table and special forms, all refused. -/

theorem refuses_sgdt : kapDecode [natByte 15, natByte 1, natByte 0] = none := by decide
theorem refuses_sidt : kapDecode [natByte 15, natByte 1, natByte 8] = none := by decide
theorem refuses_lgdt : kapDecode [natByte 15, natByte 1, natByte 16] = none := by decide
theorem refuses_lidt : kapDecode [natByte 15, natByte 1, natByte 24] = none := by decide
theorem refuses_smsw_mem : kapDecode [natByte 15, natByte 1, natByte 32] = none := by decide
theorem refuses_smsw_reg : kapDecode [natByte 15, natByte 1, natByte 224] = none := by decide
theorem refuses_lmsw : kapDecode [natByte 15, natByte 1, natByte 40] = none := by decide
theorem refuses_rdpkru : kapDecode [natByte 15, natByte 1, natByte 238] = none := by decide
theorem refuses_grp7r5res : kapDecode [natByte 15, natByte 1, natByte 233] = none := by decide
theorem refuses_vmcall : kapDecode [natByte 15, natByte 1, natByte 193] = none := by decide
theorem refuses_monitor : kapDecode [natByte 15, natByte 1, natByte 200] = none := by decide
theorem refuses_clac : kapDecode [natByte 15, natByte 1, natByte 202] = none := by decide
theorem refuses_xgetbv : kapDecode [natByte 15, natByte 1, natByte 208] = none := by decide
theorem refuses_xsetbv : kapDecode [natByte 15, natByte 1, natByte 209] = none := by decide
theorem refuses_encls : kapDecode [natByte 15, natByte 1, natByte 207] = none := by decide
theorem refuses_vmxoff : kapDecode [natByte 15, natByte 1, natByte 196] = none := by decide
theorem refuses_invlpg : kapDecode [natByte 15, natByte 1, natByte 56] = none := by decide
theorem refuses_swapgs : kapDecode [natByte 15, natByte 1, natByte 248] = none := by decide
theorem refuses_rdtscp : kapDecode [natByte 15, natByte 1, natByte 249] = none := by decide
theorem refuses_grp7r7res : kapDecode [natByte 15, natByte 1, natByte 250] = none := by decide
theorem refuses_rstorssp : kapDecode [natByte 243, natByte 15, natByte 1, natByte 62] = none := by decide

/-! ## 4. Rows 0F 02-0F 0F: protection, system and reserved rows. -/

theorem refuses_lar : kapDecode [natByte 15, natByte 2, natByte 192] = none := by decide
theorem refuses_lsl : kapDecode [natByte 15, natByte 3, natByte 192] = none := by decide
theorem refuses_res04 : kapDecode [natByte 15, natByte 4] = none := by decide
theorem refuses_syscall : kapDecode [natByte 15, natByte 5] = none := by decide
theorem refuses_clts : kapDecode [natByte 15, natByte 6] = none := by decide
theorem refuses_sysret : kapDecode [natByte 15, natByte 7] = none := by decide
theorem refuses_invd : kapDecode [natByte 15, natByte 8] = none := by decide
theorem refuses_wbinvd : kapDecode [natByte 15, natByte 9] = none := by decide
theorem refuses_wbnoinvd : kapDecode [natByte 243, natByte 15, natByte 9] = none := by decide
theorem refuses_res0A : kapDecode [natByte 15, natByte 10] = none := by decide
theorem refuses_ud2 : kapDecode [natByte 15, natByte 11] = none := by decide
theorem refuses_res0C : kapDecode [natByte 15, natByte 12] = none := by decide
theorem refuses_prefetchw : kapDecode [natByte 15, natByte 13, natByte 5, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem refuses_res0D : kapDecode [natByte 15, natByte 13, natByte 192] = none := by decide
theorem refuses_res0E : kapDecode [natByte 15, natByte 14] = none := by decide
theorem refuses_res0F : kapDecode [natByte 15, natByte 15, natByte 192, natByte 0] = none := by decide

/-! ## 5. Rows 0F 10-0F 17: SSE/AVX move rows. -/

theorem refuses_movups : kapDecode [natByte 15, natByte 16, natByte 192] = none := by decide
theorem refuses_movupd : kapDecode [natByte 102, natByte 15, natByte 16, natByte 192] = none := by decide
theorem refuses_movups_st : kapDecode [natByte 15, natByte 17, natByte 192] = none := by decide
theorem refuses_movupd_st : kapDecode [natByte 102, natByte 15, natByte 17, natByte 192] = none := by decide
theorem refuses_movss_st : kapDecode [natByte 243, natByte 15, natByte 17, natByte 192] = none := by decide
theorem refuses_movsd_st : kapDecode [natByte 242, natByte 15, natByte 17, natByte 192] = none := by decide
theorem refuses_movlps : kapDecode [natByte 15, natByte 18, natByte 192] = none := by decide
theorem refuses_movlpd : kapDecode [natByte 102, natByte 15, natByte 18, natByte 192] = none := by decide
theorem refuses_movsldup : kapDecode [natByte 243, natByte 15, natByte 18, natByte 192] = none := by decide
theorem refuses_movddup : kapDecode [natByte 242, natByte 15, natByte 18, natByte 192] = none := by decide
theorem refuses_movlps_st : kapDecode [natByte 15, natByte 19, natByte 192] = none := by decide
theorem refuses_movlpd_st : kapDecode [natByte 102, natByte 15, natByte 19, natByte 192] = none := by decide
theorem refuses_res13pre : kapDecode [natByte 243, natByte 15, natByte 19, natByte 192] = none := by decide
theorem refuses_unpcklps : kapDecode [natByte 15, natByte 20, natByte 192] = none := by decide
theorem refuses_unpcklpd : kapDecode [natByte 102, natByte 15, natByte 20, natByte 192] = none := by decide
theorem refuses_res14pre : kapDecode [natByte 243, natByte 15, natByte 20, natByte 192] = none := by decide
theorem refuses_unpckhps : kapDecode [natByte 15, natByte 21, natByte 192] = none := by decide
theorem refuses_unpckhpd : kapDecode [natByte 102, natByte 15, natByte 21, natByte 192] = none := by decide
theorem refuses_res15pre : kapDecode [natByte 243, natByte 15, natByte 21, natByte 192] = none := by decide
theorem refuses_movhps : kapDecode [natByte 15, natByte 22, natByte 192] = none := by decide
theorem refuses_movhpd : kapDecode [natByte 102, natByte 15, natByte 22, natByte 192] = none := by decide
theorem refuses_movshdup : kapDecode [natByte 243, natByte 15, natByte 22, natByte 192] = none := by decide
theorem refuses_res16f2 : kapDecode [natByte 242, natByte 15, natByte 22, natByte 192] = none := by decide
theorem refuses_movhps_st : kapDecode [natByte 15, natByte 23, natByte 192] = none := by decide
theorem refuses_movhpd_st : kapDecode [natByte 102, natByte 15, natByte 23, natByte 192] = none := by decide
theorem refuses_res17pre : kapDecode [natByte 243, natByte 15, natByte 23, natByte 192] = none := by decide

/-! ## 6. Rows 0F 18-0F 1F: hints, reserved NOPs and MPX rows. -/

theorem refuses_prefetch : kapDecode [natByte 15, natByte 24, natByte 5, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem refuses_res18 : kapDecode [natByte 15, natByte 24, natByte 228] = none := by decide
theorem refuses_prefetch66 : kapDecode [natByte 102, natByte 15, natByte 24, natByte 5, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem refuses_hint19 : kapDecode [natByte 15, natByte 25, natByte 192] = none := by decide
theorem refuses_bndldx : kapDecode [natByte 15, natByte 26, natByte 192] = none := by decide
theorem refuses_bndmov_ld : kapDecode [natByte 102, natByte 15, natByte 26, natByte 192] = none := by decide
theorem refuses_bndcl : kapDecode [natByte 243, natByte 15, natByte 26, natByte 192] = none := by decide
theorem refuses_bndcu : kapDecode [natByte 242, natByte 15, natByte 26, natByte 192] = none := by decide
theorem refuses_bndstx : kapDecode [natByte 15, natByte 27, natByte 192] = none := by decide
theorem refuses_bndmov_st : kapDecode [natByte 102, natByte 15, natByte 27, natByte 192] = none := by decide
theorem refuses_bndmk : kapDecode [natByte 243, natByte 15, natByte 27, natByte 192] = none := by decide
theorem refuses_bndcn : kapDecode [natByte 242, natByte 15, natByte 27, natByte 192] = none := by decide
theorem refuses_cldemote : kapDecode [natByte 15, natByte 28, natByte 5, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem refuses_res1C : kapDecode [natByte 15, natByte 28, natByte 200] = none := by decide
theorem refuses_hint1D : kapDecode [natByte 15, natByte 29, natByte 192] = none := by decide
theorem refuses_hint1E : kapDecode [natByte 15, natByte 30, natByte 192] = none := by decide
theorem refuses_endbr64 : kapDecode [natByte 243, natByte 15, natByte 30, natByte 250] = none := by decide
theorem refuses_nop : kapDecode [natByte 15, natByte 31, natByte 0] = none := by decide

/-! ## 7. Rows 0F 20-0F 27: control/debug registers and reserved rows. -/

theorem refuses_mov_cr : kapDecode [natByte 15, natByte 32, natByte 192] = none := by decide
theorem refuses_mov_dr : kapDecode [natByte 15, natByte 33, natByte 192] = none := by decide
theorem refuses_mov_to_cr : kapDecode [natByte 15, natByte 34, natByte 192] = none := by decide
theorem refuses_mov_to_dr : kapDecode [natByte 15, natByte 35, natByte 192] = none := by decide
theorem refuses_res24 : kapDecode [natByte 15, natByte 36] = none := by decide
theorem refuses_res25 : kapDecode [natByte 15, natByte 37] = none := by decide
theorem refuses_res26 : kapDecode [natByte 15, natByte 38] = none := by decide
theorem refuses_res27 : kapDecode [natByte 15, natByte 39] = none := by decide

/-! ## 8. Rows 0F 28-0F 2F: aligned moves, streaming stores, converts. -/

theorem refuses_movaps : kapDecode [natByte 15, natByte 40, natByte 192] = none := by decide
theorem refuses_movapd : kapDecode [natByte 102, natByte 15, natByte 40, natByte 192] = none := by decide
theorem refuses_res28pre : kapDecode [natByte 243, natByte 15, natByte 40, natByte 192] = none := by decide
theorem refuses_movaps_st : kapDecode [natByte 15, natByte 41, natByte 192] = none := by decide
theorem refuses_movapd_st : kapDecode [natByte 102, natByte 15, natByte 41, natByte 192] = none := by decide
theorem refuses_res29pre : kapDecode [natByte 243, natByte 15, natByte 41, natByte 192] = none := by decide
theorem refuses_cvtsi2sd : kapDecode [natByte 242, natByte 15, natByte 42, natByte 192] = none := by decide
theorem refuses_res2A : kapDecode [natByte 15, natByte 42, natByte 192] = none := by decide
theorem refuses_movntps : kapDecode [natByte 15, natByte 43, natByte 192] = none := by decide
theorem refuses_movntpd : kapDecode [natByte 102, natByte 15, natByte 43, natByte 192] = none := by decide
theorem refuses_res2Bpre : kapDecode [natByte 243, natByte 15, natByte 43, natByte 192] = none := by decide
theorem refuses_cvttsd2si : kapDecode [natByte 242, natByte 15, natByte 44, natByte 192] = none := by decide
theorem refuses_res2C : kapDecode [natByte 15, natByte 44, natByte 192] = none := by decide
theorem refuses_cvtss2si : kapDecode [natByte 243, natByte 15, natByte 45, natByte 192] = none := by decide
theorem refuses_cvtsd2si : kapDecode [natByte 242, natByte 15, natByte 45, natByte 192] = none := by decide
theorem refuses_res2D : kapDecode [natByte 15, natByte 45, natByte 192] = none := by decide
theorem refuses_ucomisd : kapDecode [natByte 102, natByte 15, natByte 46, natByte 192] = none := by decide
theorem refuses_res2Epre : kapDecode [natByte 243, natByte 15, natByte 46, natByte 192] = none := by decide
theorem refuses_comiss : kapDecode [natByte 15, natByte 47, natByte 192] = none := by decide
theorem refuses_comisd : kapDecode [natByte 102, natByte 15, natByte 47, natByte 192] = none := by decide
theorem refuses_res2Fpre : kapDecode [natByte 243, natByte 15, natByte 47, natByte 192] = none := by decide

/-! ## 9. Rows 0F 30-0F 3F: system counters, entry and escapes. -/

theorem refuses_wrmsr : kapDecode [natByte 15, natByte 48] = none := by decide
theorem refuses_rdtsc : kapDecode [natByte 15, natByte 49] = none := by decide
theorem refuses_rdmsr : kapDecode [natByte 15, natByte 50] = none := by decide
theorem refuses_rdpmc : kapDecode [natByte 15, natByte 51] = none := by decide
theorem refuses_sysenter : kapDecode [natByte 15, natByte 52] = none := by decide
theorem refuses_sysexit : kapDecode [natByte 15, natByte 53] = none := by decide
theorem refuses_res36 : kapDecode [natByte 15, natByte 54] = none := by decide
theorem refuses_getsec : kapDecode [natByte 15, natByte 55] = none := by decide
theorem refuses_esc38 : kapDecode [natByte 15, natByte 56] = none := by decide
theorem refuses_res39 : kapDecode [natByte 15, natByte 57] = none := by decide
theorem refuses_esc3A : kapDecode [natByte 15, natByte 58] = none := by decide
theorem refuses_res3B : kapDecode [natByte 15, natByte 59] = none := by decide
theorem refuses_res3C : kapDecode [natByte 15, natByte 60] = none := by decide
theorem refuses_res3D : kapDecode [natByte 15, natByte 61] = none := by decide
theorem refuses_res3E : kapDecode [natByte 15, natByte 62] = none := by decide
theorem refuses_res3F : kapDecode [natByte 15, natByte 63] = none := by decide

/-! ## 10. The ledger: one row per opcode (prefix/extension) cell.

  `op` is the second opcode byte (0-63 for 0F 00-0F 3F), `ext` the
  prefix or ModRM.reg extension, `familie` names the Lean module
  that models the row (empty when none does). Every `modelliert`
  row is backed by a `takes_*` theorem above, every other row by
  its `refuses_*` theorem. -/

def ledger0F00 : List LEintrag :=
  [ { op := 0, ext := "/0", mnemonik := "SLDT", status := .verweigert,
      familie := "", grund := "no segment-descriptor model; refusal checked" },
    { op := 0, ext := "/1", mnemonik := "STR", status := .verweigert,
      familie := "", grund := "no task-register model; refusal checked" },
    { op := 0, ext := "/2", mnemonik := "LLDT", status := .verweigert,
      familie := "", grund := "privileged descriptor load; refusal checked" },
    { op := 0, ext := "/3", mnemonik := "LTR", status := .verweigert,
      familie := "", grund := "privileged task-register load; refusal checked" },
    { op := 0, ext := "/4", mnemonik := "VERR", status := .verweigert,
      familie := "", grund := "segment verify needs a segment model; refusal checked" },
    { op := 0, ext := "/5", mnemonik := "VERW", status := .verweigert,
      familie := "", grund := "segment verify needs a segment model; refusal checked" },
    { op := 0, ext := "/6-/7", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "Group 6 reg /6 /7 are blank in Table A-6; nothing pinned" },
    { op := 0, ext := "F2 /6", mnemonik := "LKGS", status := .verweigert,
      familie := "", grund := "privileged kernel GS load; refusal checked" },
    { op := 1, ext := "/0", mnemonik := "SGDT", status := .verweigert,
      familie := "", grund := "privileged table store; refusal checked" },
    { op := 1, ext := "/1", mnemonik := "SIDT", status := .verweigert,
      familie := "", grund := "privileged table store; refusal checked" },
    { op := 1, ext := "/2", mnemonik := "LGDT", status := .verweigert,
      familie := "", grund := "privileged table load; refusal checked" },
    { op := 1, ext := "/3", mnemonik := "LIDT", status := .verweigert,
      familie := "", grund := "privileged table load; refusal checked" },
    { op := 1, ext := "/4 mem", mnemonik := "SMSW", status := .verweigert,
      familie := "", grund := "machine-word store without a CR0 model; refusal checked" },
    { op := 1, ext := "/4 reg", mnemonik := "SMSW", status := .verweigert,
      familie := "", grund := "register form reads CR0; no CR0 model; refusal checked" },
    { op := 1, ext := "/5 mem", mnemonik := "LMSW", status := .verweigert,
      familie := "", grund := "privileged machine-word load; refusal checked" },
    { op := 1, ext := "/5 EE-EF", mnemonik := "RDPKRU/WRPKRU",
      status := .zurueckgestellt, familie := "",
      grund := "protection keys have no model; deferred" },
    { op := 1, ext := "/5 other", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "Group 7 reg /5 outside EE/EF is blank; nothing pinned" },
    { op := 1, ext := "/6 C1", mnemonik := "VMCALL", status := .verweigert,
      familie := "", grund := "VMX has no model; refusal checked" },
    { op := 1, ext := "/6 C8-C9", mnemonik := "MONITOR/MWAIT",
      status := .zurueckgestellt, familie := "",
      grund := "sleep states have no power model; rare in output" },
    { op := 1, ext := "/6 CA-CB", mnemonik := "CLAC/STAC", status := .verweigert,
      familie := "", grund := "supervisor flag access outside the user model; refusal checked" },
    { op := 1, ext := "/6 D0", mnemonik := "XGETBV", status := .fehlt,
      familie := "", grund := "CPUID/XCR0 dispatch in every AVX runtime; very common" },
    { op := 1, ext := "/6 D1", mnemonik := "XSETBV", status := .verweigert,
      familie := "", grund := "privileged control-register write; refusal checked" },
    { op := 1, ext := "/6 CF-D7", mnemonik := "ENCLS/ENCLU",
      status := .zurueckgestellt, familie := "",
      grund := "SGX enclaves have no model; deferred" },
    { op := 1, ext := "/6 other", mnemonik := "VMX/TDX/rest",
      status := .zurueckgestellt, familie := "",
      grund := "VMLAUNCH VMRESUME VMXOFF PCONFIG WRMSRNS VMFUNC XEND XTEST deferred as one group" },
    { op := 1, ext := "/7 mem", mnemonik := "INVLPG", status := .verweigert,
      familie := "", grund := "privileged TLB invalidate; refusal checked" },
    { op := 1, ext := "/7 F8", mnemonik := "SWAPGS", status := .verweigert,
      familie := "", grund := "privileged GS swap; refusal checked" },
    { op := 1, ext := "/7 F9", mnemonik := "RDTSCP", status := .fehlt,
      familie := "", grund := "benchmark and vDSO timing; very common" },
    { op := 1, ext := "/7 other", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "Group 7 reg /7 mod=11 outside F8/F9 is blank; nothing pinned" },
    { op := 1, ext := "F3 CET-SS", mnemonik := "RSTORSSP/UIRET/CLUI/STUI",
      status := .zurueckgestellt, familie := "",
      grund := "CET shadow-stack supervisor forms; deferred" },
    { op := 2, ext := "", mnemonik := "LAR", status := .verweigert,
      familie := "", grund := "segment rights need a segment model; refusal checked" },
    { op := 3, ext := "", mnemonik := "LSL", status := .verweigert,
      familie := "", grund := "segment limits need a segment model; refusal checked" },
    { op := 4, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 5, ext := "", mnemonik := "SYSCALL", status := .verweigert,
      familie := "", grund := "kernel entry without an OS model; refusal checked" },
    { op := 6, ext := "", mnemonik := "CLTS", status := .verweigert,
      familie := "", grund := "privileged task-switched clear; refusal checked" },
    { op := 7, ext := "", mnemonik := "SYSRET", status := .verweigert,
      familie := "", grund := "privileged return; refusal checked" },
    { op := 8, ext := "", mnemonik := "INVD", status := .verweigert,
      familie := "", grund := "privileged cache invalidate; refusal checked" },
    { op := 9, ext := "", mnemonik := "WBINVD", status := .verweigert,
      familie := "", grund := "privileged writeback invalidate; refusal checked" },
    { op := 9, ext := "F3", mnemonik := "WBNOINVD", status := .verweigert,
      familie := "", grund := "privileged writeback no-invalidate; refusal checked" },
    { op := 10, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 11, ext := "", mnemonik := "UD2", status := .fehlt,
      familie := "", grund := "compiler trap in Rust panics and kernel BUG; very common" },
    { op := 12, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 13, ext := "/1", mnemonik := "PREFETCHW", status := .fehlt,
      familie := "", grund := "write-prefetch in memcpy loops; common" },
    { op := 13, ext := "other", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "0F 0D outside /1 is blank; nothing pinned" },
    { op := 14, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "3DNow FEMMS has no 64-bit form; blank cell; nothing pinned" },
    { op := 15, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "3DNow has no 64-bit form; blank cell; nothing pinned" },
    { op := 16, ext := "", mnemonik := "MOVUPS", status := .fehlt,
      familie := "", grund := "unaligned vector spills everywhere; very common" },
    { op := 16, ext := "66", mnemonik := "MOVUPD", status := .fehlt,
      familie := "", grund := "unaligned double spills; very common" },
    { op := 16, ext := "F3", mnemonik := "MOVSS", status := .modelliert,
      familie := "ScalarFloat32HardwareForms (s32Decode)", grund := "" },
    { op := 16, ext := "F2", mnemonik := "MOVSD", status := .modelliert,
      familie := "ExtendedExecution (decodeExt FP arm)", grund := "" },
    { op := 17, ext := "", mnemonik := "MOVUPS", status := .fehlt,
      familie := "", grund := "unaligned vector store; very common" },
    { op := 17, ext := "66", mnemonik := "MOVUPD", status := .fehlt,
      familie := "", grund := "unaligned double store; very common" },
    { op := 17, ext := "F3", mnemonik := "MOVSS", status := .fehlt,
      familie := "", grund := "store refused while the load decodes; asymmetric gap" },
    { op := 17, ext := "F2", mnemonik := "MOVSD", status := .fehlt,
      familie := "", grund := "store refused while the load decodes; asymmetric gap" },
    { op := 18, ext := "", mnemonik := "MOVLPS", status := .fehlt,
      familie := "", grund := "low quad move; common in shuffles" },
    { op := 18, ext := "66", mnemonik := "MOVLPD", status := .fehlt,
      familie := "", grund := "low double move; common" },
    { op := 18, ext := "F3", mnemonik := "MOVSLDUP", status := .fehlt,
      familie := "", grund := "duplicate-single; used in numeric code" },
    { op := 18, ext := "F2", mnemonik := "MOVDDUP", status := .fehlt,
      familie := "", grund := "duplicate-double; used in numeric code" },
    { op := 19, ext := "", mnemonik := "MOVLPS", status := .fehlt,
      familie := "", grund := "low quad store; common" },
    { op := 19, ext := "66", mnemonik := "MOVLPD", status := .fehlt,
      familie := "", grund := "low double store; common" },
    { op := 19, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 13; nothing pinned" },
    { op := 20, ext := "", mnemonik := "UNPCKLPS", status := .fehlt,
      familie := "", grund := "interleave loads; very common in vector code" },
    { op := 20, ext := "66", mnemonik := "UNPCKLPD", status := .fehlt,
      familie := "", grund := "interleave doubles; very common" },
    { op := 20, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 14; nothing pinned" },
    { op := 21, ext := "", mnemonik := "UNPCKHPS", status := .fehlt,
      familie := "", grund := "interleave highs; very common" },
    { op := 21, ext := "66", mnemonik := "UNPCKHPD", status := .fehlt,
      familie := "", grund := "interleave double highs; very common" },
    { op := 21, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 15; nothing pinned" },
    { op := 22, ext := "", mnemonik := "MOVHPS", status := .fehlt,
      familie := "", grund := "high quad move; common" },
    { op := 22, ext := "66", mnemonik := "MOVHPD", status := .fehlt,
      familie := "", grund := "high double move; common" },
    { op := 22, ext := "F3", mnemonik := "MOVSHDUP", status := .fehlt,
      familie := "", grund := "duplicate-high; used in numeric code" },
    { op := 22, ext := "F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F2 row for 0F 16; nothing pinned" },
    { op := 23, ext := "", mnemonik := "MOVHPS", status := .fehlt,
      familie := "", grund := "high quad store; common" },
    { op := 23, ext := "66", mnemonik := "MOVHPD", status := .fehlt,
      familie := "", grund := "high double store; common" },
    { op := 23, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 17; nothing pinned" },
    { op := 24, ext := "/0-/3,/6,/7", mnemonik := "PREFETCHh", status := .fehlt,
      familie := "", grund := "compiler builtin prefetch; very common" },
    { op := 24, ext := "/4-/5", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "0F 18 reg /4 /5 are blank; nothing pinned" },
    { op := 24, ext := "66", mnemonik := "PREFETCHh", status := .fehlt,
      familie := "", grund := "prefixed hint row of Table A-3; common" },
    { op := 25, ext := "", mnemonik := "HINT-NOP", status := .fehlt,
      familie := "", grund := "documented reserved NOP; rare, compilers prefer 0F 1F" },
    { op := 26, ext := "", mnemonik := "BNDLDX", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 26, ext := "66", mnemonik := "BNDMOV", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 26, ext := "F3", mnemonik := "BNDCL", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 26, ext := "F2", mnemonik := "BNDCU", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 27, ext := "", mnemonik := "BNDSTX", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 27, ext := "66", mnemonik := "BNDMOV", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 27, ext := "F3", mnemonik := "BNDMK", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 27, ext := "F2", mnemonik := "BNDCN", status := .zurueckgestellt,
      familie := "", grund := "Intel MPX removed from silicon; no new software" },
    { op := 28, ext := "/0", mnemonik := "CLDEMOTE", status := .fehlt,
      familie := "", grund := "cache-line demote in queue runtimes; uncommon but real" },
    { op := 28, ext := "other", mnemonik := "reserved NOP", status := .fehlt,
      familie := "", grund := "documented NOP without byte effect; refused by the chain" },
    { op := 29, ext := "", mnemonik := "reserved NOP", status := .fehlt,
      familie := "", grund := "documented reserved NOP; refused by the chain" },
    { op := 30, ext := "", mnemonik := "reserved NOP", status := .fehlt,
      familie := "", grund := "documented reserved NOP; refused by the chain" },
    { op := 30, ext := "F3", mnemonik := "ENDBR64", status := .fehlt,
      familie := "", grund := "every CET indirect-branch target; very common" },
    { op := 31, ext := "/0", mnemonik := "NOP", status := .fehlt,
      familie := "", grund := "alignment padding in every binary; the most common gap" },
    { op := 32, ext := "", mnemonik := "MOV from CR", status := .verweigert,
      familie := "", grund := "privileged control-register file; refusal checked" },
    { op := 33, ext := "", mnemonik := "MOV from DR", status := .verweigert,
      familie := "", grund := "privileged debug-register file; refusal checked" },
    { op := 34, ext := "", mnemonik := "MOV to CR", status := .verweigert,
      familie := "", grund := "privileged control-register file; refusal checked" },
    { op := 35, ext := "", mnemonik := "MOV to DR", status := .verweigert,
      familie := "", grund := "privileged debug-register file; refusal checked" },
    { op := 36, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 37, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 38, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 39, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 40, ext := "", mnemonik := "MOVAPS", status := .fehlt,
      familie := "", grund := "aligned vector spill; very common" },
    { op := 40, ext := "66", mnemonik := "MOVAPD", status := .fehlt,
      familie := "", grund := "aligned double spill; very common" },
    { op := 40, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 28; nothing pinned" },
    { op := 41, ext := "", mnemonik := "MOVAPS", status := .fehlt,
      familie := "", grund := "aligned vector store; very common" },
    { op := 41, ext := "66", mnemonik := "MOVAPD", status := .fehlt,
      familie := "", grund := "aligned double store; very common" },
    { op := 41, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 29; nothing pinned" },
    { op := 42, ext := "F3", mnemonik := "CVTSI2SS", status := .modelliert,
      familie := "ScalarFloat32HardwareForms (s32Decode)", grund := "" },
    { op := 42, ext := "F2", mnemonik := "CVTSI2SD", status := .fehlt,
      familie := "", grund := "int-to-double convert refused while single decodes; asymmetric gap" },
    { op := 42, ext := "none/66", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no none/66 row for 0F 2A; nothing pinned" },
    { op := 43, ext := "", mnemonik := "MOVNTPS", status := .fehlt,
      familie := "", grund := "streaming store; common in memset and memcpy" },
    { op := 43, ext := "66", mnemonik := "MOVNTPD", status := .fehlt,
      familie := "", grund := "streaming double store; common" },
    { op := 43, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 2B; nothing pinned" },
    { op := 44, ext := "F3", mnemonik := "CVTTSS2SI", status := .modelliert,
      familie := "ScalarFloat32HardwareForms (s32Decode)", grund := "" },
    { op := 44, ext := "F2", mnemonik := "CVTTSD2SI", status := .fehlt,
      familie := "", grund := "truncate-double refused while single decodes; asymmetric gap" },
    { op := 44, ext := "none/66", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no none/66 row for 0F 2C; nothing pinned" },
    { op := 45, ext := "F3", mnemonik := "CVTSS2SI", status := .fehlt,
      familie := "", grund := "rounded convert; common in float-int code" },
    { op := 45, ext := "F2", mnemonik := "CVTSD2SI", status := .fehlt,
      familie := "", grund := "rounded double convert; common" },
    { op := 45, ext := "none/66", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no none/66 row for 0F 2D; nothing pinned" },
    { op := 46, ext := "", mnemonik := "UCOMISS", status := .modelliert,
      familie := "ScalarFloat32HardwareForms (s32Decode)", grund := "" },
    { op := 46, ext := "66", mnemonik := "UCOMISD", status := .fehlt,
      familie := "", grund := "unordered double compare; very common" },
    { op := 46, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 2E; nothing pinned" },
    { op := 47, ext := "", mnemonik := "COMISS", status := .fehlt,
      familie := "", grund := "ordered single compare; very common" },
    { op := 47, ext := "66", mnemonik := "COMISD", status := .fehlt,
      familie := "", grund := "ordered double compare; very common" },
    { op := 47, ext := "F3/F2", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "no F3/F2 row for 0F 2F; nothing pinned" },
    { op := 48, ext := "", mnemonik := "WRMSR", status := .verweigert,
      familie := "", grund := "privileged model-register write; refusal checked" },
    { op := 49, ext := "", mnemonik := "RDTSC", status := .fehlt,
      familie := "", grund := "cycle timing in benchmarks; very common" },
    { op := 50, ext := "", mnemonik := "RDMSR", status := .verweigert,
      familie := "", grund := "privileged model-register read; refusal checked" },
    { op := 51, ext := "", mnemonik := "RDPMC", status := .fehlt,
      familie := "", grund := "profiler counters; moderately common" },
    { op := 52, ext := "", mnemonik := "SYSENTER", status := .verweigert,
      familie := "", grund := "privileged entry, valid in 64-bit per SDM; refusal checked" },
    { op := 53, ext := "", mnemonik := "SYSEXIT", status := .verweigert,
      familie := "", grund := "privileged return; refusal checked" },
    { op := 54, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 55, ext := "", mnemonik := "GETSEC", status := .verweigert,
      familie := "", grund := "SMX privileged launch; refusal checked" },
    { op := 56, ext := "", mnemonik := "escape", status := .zurueckgestellt,
      familie := "", grund := "three-byte escape of Table A-4 (SSSE3 SSE4 AES); separate region" },
    { op := 57, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 58, ext := "", mnemonik := "escape", status := .zurueckgestellt,
      familie := "", grund := "three-byte escape of Table A-5; separate region" },
    { op := 59, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 60, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 61, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 62, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" },
    { op := 63, ext := "", mnemonik := "reserved", status := .ungueltig64,
      familie := "", grund := "blank cell in Table A-3; nothing pinned" } ]

/-! ## 11. Summary: counts per status, exact coverage of the region. -/

/-- Status counts: 5 modelled, 36 refused by scope, 34 invalid, 49 missing, 15 deferred. -/
theorem ledger_anzahl_modelliert :
    (ledger0F00.filter fun e => decide (e.status = .modelliert)).length = 5 := by
  decide

theorem ledger_anzahl_verweigert :
    (ledger0F00.filter fun e => decide (e.status = .verweigert)).length = 36 := by
  decide

theorem ledger_anzahl_ungueltig :
    (ledger0F00.filter fun e => decide (e.status = .ungueltig64)).length = 34 := by
  decide

theorem ledger_anzahl_fehlt :
    (ledger0F00.filter fun e => decide (e.status = .fehlt)).length = 49 := by
  decide

theorem ledger_anzahl_zurueck :
    (ledger0F00.filter fun e => decide (e.status = .zurueckgestellt)).length = 15 := by
  decide

set_option maxRecDepth 10000 in
theorem ledger_anzahl_gesamt : ledger0F00.length = 139 := by decide

set_option maxRecDepth 10000 in
/-- No (opcode, extension) key is listed twice. -/
theorem ledger_schluessel_eindeutig :
    (ledger0F00.map fun e => (e.op, e.ext)).Nodup := by
  decide

set_option maxRecDepth 10000 in
/-- Every opcode byte 0F 00-0F 3F occurs at least once: nothing skipped. -/
theorem ledger_deckt_ab : ∀ b < 64, ∃ e ∈ ledger0F00, e.op = b := by
  decide

/- CUTS:
  Proven here, over the reused accepted chain only (`kapDecode` lifted,
  never redefined):
  - schema `LStatus` / `LEintrag`, self-contained (no other ledger lane);
  - 5 `takes_*` acceptances, each `decide`d against `kapDecode`;
  - 134 `refuses_*` refusals, each `decide`d against `kapDecode`;
  - `ledger0F00`: 139 rows (5 modelliert, 36 verweigert, 34 ungueltig64,
    49 fehlt, 15 zurueckgestellt), key-nodup and full 0F 00-0F 3F coverage.
  NOT proven here, and not claimed:
  - silicon correspondence beyond the cited map: the Table A-3/A-6 cell
    transcription is taken from the clone-local Intel snapshot
    (325462-093US, `.tmp/HARDWARE-REFERENCES/`, sha in REFERENCES.json);
    the checked facts are the `kapDecode` evaluations, not the silicon;
  - only the listed canonical byte strings are decided; redundant-prefix
    combinations (e.g. 66 0F 1F) and other ModRM/SIB/displacement shapes
    of the same cell are not pinned;
  - folded group rows (Group 7 mod=11 exotics, 0F 38/0F 3A escapes) carry
    one witness each; the fold is documented in the row reason;
  - no execution, fault, ordering or W/GX claim: this file classifies
    decoding only; PREFETCHW hint semantics and removed MPX silicon stay
    FREE (refused, nothing pinned); no AMD provenance is claimed.
-/

#print axioms takes_movsd
#print axioms takes_movss
#print axioms takes_cvtsi2ss
#print axioms takes_cvttss2si
#print axioms takes_ucomiss
#print axioms refuses_sldt
#print axioms refuses_str
#print axioms refuses_lldt
#print axioms refuses_ltr
#print axioms refuses_verr
#print axioms refuses_verw
#print axioms refuses_grp6res
#print axioms refuses_lkgs
#print axioms refuses_sgdt
#print axioms refuses_sidt
#print axioms refuses_lgdt
#print axioms refuses_lidt
#print axioms refuses_smsw_mem
#print axioms refuses_smsw_reg
#print axioms refuses_lmsw
#print axioms refuses_rdpkru
#print axioms refuses_grp7r5res
#print axioms refuses_vmcall
#print axioms refuses_monitor
#print axioms refuses_clac
#print axioms refuses_xgetbv
#print axioms refuses_xsetbv
#print axioms refuses_encls
#print axioms refuses_vmxoff
#print axioms refuses_invlpg
#print axioms refuses_swapgs
#print axioms refuses_rdtscp
#print axioms refuses_grp7r7res
#print axioms refuses_rstorssp
#print axioms refuses_lar
#print axioms refuses_lsl
#print axioms refuses_res04
#print axioms refuses_syscall
#print axioms refuses_clts
#print axioms refuses_sysret
#print axioms refuses_invd
#print axioms refuses_wbinvd
#print axioms refuses_wbnoinvd
#print axioms refuses_res0A
#print axioms refuses_ud2
#print axioms refuses_res0C
#print axioms refuses_prefetchw
#print axioms refuses_res0D
#print axioms refuses_res0E
#print axioms refuses_res0F
#print axioms refuses_movups
#print axioms refuses_movupd
#print axioms refuses_movups_st
#print axioms refuses_movupd_st
#print axioms refuses_movss_st
#print axioms refuses_movsd_st
#print axioms refuses_movlps
#print axioms refuses_movlpd
#print axioms refuses_movsldup
#print axioms refuses_movddup
#print axioms refuses_movlps_st
#print axioms refuses_movlpd_st
#print axioms refuses_res13pre
#print axioms refuses_unpcklps
#print axioms refuses_unpcklpd
#print axioms refuses_res14pre
#print axioms refuses_unpckhps
#print axioms refuses_unpckhpd
#print axioms refuses_res15pre
#print axioms refuses_movhps
#print axioms refuses_movhpd
#print axioms refuses_movshdup
#print axioms refuses_res16f2
#print axioms refuses_movhps_st
#print axioms refuses_movhpd_st
#print axioms refuses_res17pre
#print axioms refuses_prefetch
#print axioms refuses_res18
#print axioms refuses_prefetch66
#print axioms refuses_hint19
#print axioms refuses_bndldx
#print axioms refuses_bndmov_ld
#print axioms refuses_bndcl
#print axioms refuses_bndcu
#print axioms refuses_bndstx
#print axioms refuses_bndmov_st
#print axioms refuses_bndmk
#print axioms refuses_bndcn
#print axioms refuses_cldemote
#print axioms refuses_res1C
#print axioms refuses_hint1D
#print axioms refuses_hint1E
#print axioms refuses_endbr64
#print axioms refuses_nop
#print axioms refuses_mov_cr
#print axioms refuses_mov_dr
#print axioms refuses_mov_to_cr
#print axioms refuses_mov_to_dr
#print axioms refuses_res24
#print axioms refuses_res25
#print axioms refuses_res26
#print axioms refuses_res27
#print axioms refuses_movaps
#print axioms refuses_movapd
#print axioms refuses_res28pre
#print axioms refuses_movaps_st
#print axioms refuses_movapd_st
#print axioms refuses_res29pre
#print axioms refuses_cvtsi2sd
#print axioms refuses_res2A
#print axioms refuses_movntps
#print axioms refuses_movntpd
#print axioms refuses_res2Bpre
#print axioms refuses_cvttsd2si
#print axioms refuses_res2C
#print axioms refuses_cvtss2si
#print axioms refuses_cvtsd2si
#print axioms refuses_res2D
#print axioms refuses_ucomisd
#print axioms refuses_res2Epre
#print axioms refuses_comiss
#print axioms refuses_comisd
#print axioms refuses_res2Fpre
#print axioms refuses_wrmsr
#print axioms refuses_rdtsc
#print axioms refuses_rdmsr
#print axioms refuses_rdpmc
#print axioms refuses_sysenter
#print axioms refuses_sysexit
#print axioms refuses_res36
#print axioms refuses_getsec
#print axioms refuses_esc38
#print axioms refuses_res39
#print axioms refuses_esc3A
#print axioms refuses_res3B
#print axioms refuses_res3C
#print axioms refuses_res3D
#print axioms refuses_res3E
#print axioms refuses_res3F
#print axioms ledger_anzahl_modelliert
#print axioms ledger_anzahl_verweigert
#print axioms ledger_anzahl_ungueltig
#print axioms ledger_anzahl_fehlt
#print axioms ledger_anzahl_zurueck
#print axioms ledger_anzahl_gesamt
#print axioms ledger_schluessel_eindeutig
#print axioms ledger_deckt_ab

end Gabbro.Grammatik.X86.OpcodeLedger0F00
