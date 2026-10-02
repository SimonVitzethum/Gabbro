# MUSE-REPORT-688: Hardware completion — CPUID and XGETBV byte execution

Lane 688, clone `/home/simon/Dokumente/gabbro-muse/a688`, branch `muse/688`.
Owned files only: `grammatik/Grammatik/X86/CpuFeatureHardwareForms.lean`,
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was done

New module `Grammatik/X86/CpuFeatureHardwareForms.lean` (~1230 lines):
exact fetched byte forms of CPUID (`0F A2`, length 2) and XGETBV
(`NP 0F 01 D0`, length 3) executed over canonical `Zustand`/`Speicher`,
with one explicit generic named hardware CPU-information/XCR0 answer
interface (`CpuHw`: immutable `cpuidAns` leaf/subleaf -> exact 32-bit
fields, plus software-written `xcrAns` selector -> EDX:EAX option).

- §1 Interface: `CpuHw`, `CpuScope` (faulting/CPL/VMX), `CtrlState`
  (CR4.OSXSAVE), `CpuFault` (#UD/#GP), `low32`/`zext64` with value
  lemmas (high halves cleared, high 32 of RCX/EAX ignored).
- §2 Byte forms: `CpuForm`, `cpuEncode`/`decodeCpuFeature` with round
  trips over any suffix, pilot-decoder disjointness (`decode` refuses
  both forms), LOCK-prefix and truncation refusals.
- §3 Register steps: `cpuSchrittCpuid` (leaf=low32 RAX, subleaf=low32
  RCX, zero-extended writes, RIP+2, flags/memory kept) and
  `cpuSchrittXgetbv` (selector=low32 RCX, RIP+3) with explicit fault
  scope: LOCK->#UD, faulting CPL>0->#GP, VMX non-root->VM exit event,
  missing observed-XSAVE or OSXSAVE->#UD, invalid selector->#GP.
- §4 Gates from observed bits: leaf-1 EDX[26] SSE2, ECX[26] XSAVE,
  ECX[27] OSXSAVE, ECX[28] AVX; leaf-7 EBX[5] AVX2; XCR0 EAX[1] XMM,
  EAX[2] YMM; combined `avxBereit`/`avx2Bereit`/`eintrittAvxOk` with
  need-each-side refusal lemmas and true/false witnesses.
- §5 Fetched layer reusing canonical `geholt`/`ausfuehrbarN`:
  `fetchCpu`/`cpuByteschritt` with bridge lemmas to the register steps
  and fetch/permission/prefix refusals. Outcome projections
  (`ergRip`/`ergReg`/`ergFehler`/`ergVm`) carry concrete data.
- §6 TSO serialization interface for lane 660: `cpuidSerialBereit`
  IS `zaunBereit` (own-buffer empty); pending own byte blocks it;
  foreign issue/flush never changes it; readiness coexists with a
  pending foreign store (no foreign drain, no timing claim).
- §7 Joint sequence `cpu_kette_speichert_gatter`: fetched CPUID then
  fetched XGETBV (gap selector state via explicit `hsel`/`hw0`
  premises), observed XSAVE bit gates XGETBV, derived AVX-ready value
  stores via `write64` and reads back, RIP chains 2 then 3, observed
  ECX faithful. Every premise is used. Companion
  `cpu_kette_speichert_gatter_zeuge` instantiates all premises jointly
  on explicit reached states (CPUID+XGETBV at 0x1000/0x1002, leaf 1,
  selector 0, XMM+YMM) with memory change (data cell 0 -> 1).
- §8 Planted refusals on actual fetched bytes: selector 2 -> #GP,
  OSXSAVE off -> #UD, LOCK+CPUID -> #UD, truncated XGETBV -> refuse,
  exec-denied -> refuse, faulting CPL3 -> #GP, VMX -> VM exit,
  cleared XSAVE observation -> #UD for every state, forged EBX bits ->
  differing outcome.

## Checks

- `./lean-probe grammatik/Grammatik/X86/CpuFeatureHardwareForms.lean`:
  `== 0 error(s)`, exit 0. All `#print axioms` are subsets of
  `[propext, Classical.choice, Quot.sound]`.
- `./lean-bau`: `== exit 0; 0 error line(s)`, 464 jobs, build success.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no host probing;
  no changes outside the three owned files.

## Provenance checked

Local `.tmp/HARDWARE-REFERENCES/` (Intel SDM 325462-093US Sep 2026,
sha256 a4a62e6a…): CPUID entry Vol. 2A pp. 3-202-3-204; XGETBV entry
Vol. 2D pp. 6-36-6-37; Vol. 1 Ch. 13-14 incl. Example 14-1 AVX
detection. No AMD snapshot available; no vendor/silicon claim.

## Open / not claimed

Per CUTS: other leaves/selectors/features; byte-level MOV-gap
composition and decodeExt integration (consumer lanes); no
TSO-to-W/GX bridge (precondition interface only); no source/checker/
emitter correspondence; no timing bounds. No full hardware-model
closure is claimed from this subset.
