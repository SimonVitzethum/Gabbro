# MUSE-REPORT-689: Review of author 688 (CPUID and XGETBV byte execution)

Lane 689, clone `/home/simon/Dokumente/gabbro-muse/a689`, branch `muse/689`.
Review-only lane. No source file was modified; this report is the only owned file.

## CANDIDATE

CANDIDATE: 688 2c15674ab5d4d1af93a0a9c135c4cd97deeb28d1

Files (from `.tmp/review/SNAPSHOT.json`): `MUSE-REPORT-688.md`,
`grammatik/Grammatik.lean` (one additive import line),
`grammatik/Grammatik/X86/CpuFeatureHardwareForms.lean` (1234 lines, new module).

## VERDICT

VERDICT: ACCEPT (bounded; three minor safe-direction observations below, none a repair).

## What was checked

1. **Exact snapshot inspected.** Read the full 1234-line candidate file in
   `.tmp/review/author-688/` (§§1-8 plus CUTS), the owner task, the author
   report, `BUILD-EVIDENCE.json`, and `PATCH.diff`. The `Grammatik.lean`
   change is one additive import line; nothing else in the tree is touched.
2. **Lean reproduced in this clone.** Copied the exact snapshot file into
   `grammatik/Grammatik/X86/` temporarily, ran `./lean-probe` (then removed
   the copy; working tree is clean apart from this report):
   `== 0 error(s) in the COMPLETE output; exit 0`. All `#print axioms`
   outputs are subsets of `[propext, Classical.choice, Quot.sound]`
   (standard `gabbro_ziel` axioms). No `sorry`/`admit`/`axiom`/
   `native_decide`/`unsafe` (one comment contains the English word "admit";
   no tactic use). No `Prop`-typed premise; no `intro _` / `have _ :=`.
   Author's `./lean-bau` evidence (464 jobs, exit 0) is consistent.
3. **Producer symbols are real.** Every reused identifier (`geholt`,
   `ausfuehrbarN`, `zaunBereit`, `issueByte`, `flushKern`,
   `issue_haengt_an`, `zaun_fremd_issue/flush/kein_fremd_drain`, `regSet`
   family, `ripNach`, `write64`, `read64_nach_write64`, `decode`,
   `natByte`/`byteNat`, `lesbar8`/`schreibbar8`) resolves to the canonical
   `Codec`/`Ausfuehrung`/`Byteschritt`/`Speicher`/`TSO` modules present in
   this clone. No guessed symbols from unaccepted producers.
4. **Manual provenance verified locally.** Against
   `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
   (Intel SDM 325462-093US, sha256 `a4a62e6a...`):
   - CPUID entry: opcode `0F A2`, ZO, EAX/ECX inputs, EAX/EBX/ECX/EDX
     outputs, high 32 of RAX/RBX/RCX/RDX cleared on Intel 64, serializing,
     invalid leaves Reserved, VM exit in non-root, `#UD iff LOCK`, flags
     None. Model matches on every point.
   - XGETBV entry (Vol. 2D 6-36): `NP 0F 01 D0`, ECX selector with high 32
     of RCX ignored, EDX:EAX answer with high halves of RAX/RDX cleared,
     `#GP` on any other selector value, `#UD` on XSAVE=0 / CR4.OSXSAVE=0 /
     LOCK, flags None. Model matches on every point.
   - AVX detection flow (Vol. 1 §14, Fig. 14-2): OSXSAVE[27], then
     XCR0[2:1]=11b, plus AVX[28]. `avxBereit` is exactly this conjunction;
     silicon bits stay distinct from XCR0 control state.
   - No XGETBV VM-exit control exists in the snapshot (only XSAVES/XRSTORS
     have one), so the model's lack of a VMX gate on XGETBV is consistent
     with the reference, not an omission.
5. **Architecture review.**
   - Byte forms exact (`cpuEncode`, lengths 2/3); round trips over any
     suffix; pilot `decode` provably refuses both forms (`decide`), so no
     shadowing; LOCK-prefix and truncation refusals proved.
   - Implicit operands right: leaf=low32 RAX, subleaf=low32 RCX;
     selector=low32 RCX (high halves ignored, with lemmas); outputs
     zero-extended (`zext64` + `zext64_klein`, high-half-cleared lemmas).
     Flags/memory preserved, RIP+2/+3, RSP untouched, RCX/RBX preserved
     on XGETBV. No memory operands exist, so no access-order claim is
     needed or made. Fault paths change no state.
   - Feature/control gates: XGETBV needs the *observed* leaf-1 XSAVE bit
     (threaded through the joint sequence, never a host probe) AND
     CR4.OSXSAVE; invalid selector is `#GP`. Undefined XCR bits pass
     through the named `hw` answer instead of being fixed — sound
     abstraction, no invented determinism.
   - TSO: `cpuidSerialBereit` IS `zaunBereit` (own buffer empty); pending
     own byte blocks it; foreign issue/flush provably never change it; a
     ready core coexists with a pending foreign store. No drain and no
     timing bound is claimed — exactly what the task demanded.
   - No desired-correctness premise: `CpuHw`/`CpuScope`/`CtrlState` are
     explicit generic parameters; unsupported leaves answer Reserved via
     `hw`, never `#UD`. Every premise of `cpu_kette_speichert_gatter` is
     used by its proof (checked by reading the proof term usage).
6. **Witnesses and refusals are real and non-degenerate.** The joint
   `_zeuge` instantiates all premises jointly on reached fetched states
   (CPUID+XGETBV at 0x1000/0x1002, leaf 1, selector 0, XMM+YMM) with an
   observable memory change (data cell zero before, derived 1 after,
   read back). The between-fetch selector preparation is an explicit gap
   state (`hsel`/`hw0`), disclosed in the section head and CUTS, matching
   the owner task's allowance — no byte-level gap composition is claimed.
   Planted mutations on actual fetched bytes: selector 2 `#GP`, OSXSAVE
   off `#UD`, cleared XSAVE observation `#UD` for every state, LOCK+CPUID
   `#UD`, truncated XGETBV and exec-denied refusals, faulting CPL3 `#GP`,
   VMX VM-exit, forged EBX bits differing outcome. Witness RIPs decide to
   0x1002/0x1005.
7. **CUTS/claim boundary is precise.** Provenance with page numbers, open
   leaves/selectors/features, consumer-owned MOV-gap and decodeExt work,
   precondition-only serialization, no source/checker/emitter or bridge
   claims, no timing bounds, no vendor/silicon claims. Nothing reviewed
   exceeds what is proved.

## Bounded observations (accepted as-is, not repairs)

1. Non-LOCK prefixes (66/F2/F3/REX) before either form refuse instead of
   the hardware-precise ignore-or-`#UD`. Safe direction (refusal claims
   no execution); completeness only.
2. If CPUID-faulting (CPL>0) and VMX non-root coincide, the model reports
   `#GP` (fault checked first). Both block success and the success path
   needs both false, so no success-path effect; priority corner only.
3. The serial precondition is exported for lane 660 but not wired into
   `cpuByteschritt` — disclosed as interface-only in CUTS.

## Last check results

- `./lean-probe` on the exact candidate file in this clone:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `git status`: clean except this report. No network, no push, no other
  clones touched.
