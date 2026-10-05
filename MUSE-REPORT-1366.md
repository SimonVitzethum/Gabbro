# MUSE-REPORT-1366: Exact review of lane 1365 (system/privileged decoder rows)

CANDIDATE: 1365 6a67cc7ff3f608f00abed250c4261ff40012aa1d

VERDICT: ACCEPT

## What was done

Independent exact review of the candidate delivered as files under
`.tmp/review/author-1365/` (SNAPSHOT.json, PATCH.diff, copied tree,
OWNER-TASK.md, BUILD-EVIDENCE.json). The author clone and pinned hash
were never touched: no `git show/log/diff` on the pinned hash, per the
lane task. All findings below come from the delivered files, from this
clone's accepted tree, and from executed wrapper runs.

Checks performed:

1. **Forbidden tactics/axioms.** Searched the candidate
   `SystemDecode.lean` (707 lines, read in full): no `sorry`, no
   standalone `admit` tactic, no `axiom` declaration, no
   `native_decide`, no `sorryAx`, no `unsafe`. The only matches for
   `admit` are the English words "admitted"/"admits" in prose comments.
   No `intro _` / `have _ :=` discards. No premise typed as `Prop`
   itself.
2. **Probe of the candidate file.** Ran
   `./lean-probe .tmp/review/author-1365/grammatik/Grammatik/X86/SystemDecode.lean`
   (the wrapper accepts any path; imports resolve through the package
   `.lake`, so no copy into the tree was needed and the tree stayed
   clean). Result:
   `== 0 error(s) in the COMPLETE output; exit 0`, with `#print axioms`
   for all 9 main theorems: `sysRoundTrip` and `sysEreignis_extra` on
   `[propext]`; `kapDecodeSys_alt`, `kapDecodeSys_nichts`,
   `adapterSysDecode_ok`, `adapterSysDecode_extra`, `adapterSystem_wf`,
   `adapterSysDecode_wf`, `sysDecode_zeuge` on `[propext, Quot.sound]`.
   All are subsets of the standard trio. Matches BUILD-EVIDENCE.json.
3. **Existing files untouched except one import line.** SNAPSHOT.json
   lists exactly 3 files; PATCH.diff confirms: new
   `grammatik/Grammatik/X86/SystemDecode.lean`, new
   `MUSE-REPORT-1365.md`, and exactly one appended line
   `import Grammatik.X86.SystemDecode` in `grammatik/Grammatik.lean`.
4. **Every premise used.** `kapDecodeSys_alt` rewrites with `h`;
   `kapDecodeSys_nichts` rewrites with `h1, h2`;
   `adapterSysDecode_ok` rewrites with `h`;
   `adapterSysDecode_extra` uses `x, ev` via `sysEreignis_extra`;
   `adapterSystem_wf` destructures `h` and returns `hwf` (the `exact
   hwf` closes only because the ok-successor keeps the `HwWf`-relevant
   fields `hw`/`bereit` definitionally — mechanical, not hand-waving);
   `adapterSysDecode_wf` delegates to `adapterSystem_wf`;
   `sysEreignis_extra` case-splits `x` with `ev` in the goal;
   `sysDecode_zeuge` and all row pins are closed equations;
   `sysDecode_intN` is schematic over every `n` by `rfl`, not one
   literal.
5. **Accepted evaluator lifted, not copied.** The file defines only
   `SysExtra`, `SysDecodiert`, `sysFormOfRow`, `sysDecode`,
   `sysEncode`, `sysNorm`, `SysKette`, `kapDecodeSys`,
   `sysEreignisOfRow`, `adapterSysDecode`. No redefinition of
   `SysFormArt`, `SysEreignis`, `sysSnapSchritt`, or `adapterSystem`.
   Lowering builds the accepted `SysEreignis`; the plug delegates to
   `adapterSystem.schritt`; execution reuses `sysAusfuehren` and the
   accepted `sysWit*` theorems. All reused names
   (`sysWitEingaben`, `sysWitO_int`, `sysWitO_int1`, `sysWitHochM`,
   `sysWit_int_rip`, `sysWit_int_frame_rip`, `sysWit_int1_rip`,
   `sysWit_ud_frei`, `sysWit_gp_hlt`,
   `sysWit_spuelung_aendert_speicher`, `sysWitNachFlush`,
   `sysRipOut/sysHaltedOut/sysKlasseOut/sysMemOut`, `HwWf`,
   `HwAdapter`, `kapDecode`) were confirmed present in this clone's
   accepted tree.
6. **Planted refusals really refuse (machine-checked).**
   `sysDecode_leer/int_abgeschnitten/esc_abgeschnitten/rex_abgeschnitten`,
   23 `kapDecode_nimmt_*_nicht` decides (zero old-chain overlap on any
   new row), `kapSys_leer`, `kapDecodeSys_nichts`,
   `sysEreignis_extra` (all 9 deferred rows lower to `none`),
   `adapterSysDecode_extra` (no plug step for deferred rows).
7. **Witness is non-degenerate.** `sysDecode_zeuge` joins all 21 chain
   pins with: HLT halts core 0, INT 2 lowers with its vector byte and
   reaches the handler on core 0 (`sysWit_int_rip`) and core 1
   (`sysWit_int1_rip`), the INT frame byte lands in real memory
   (`sysMemOut ... = some 0x02`), the TSO drain moves 0 to 42
   (`sysWitNachFlush`, `sysWit_spuelung_aendert_speicher` — a
   memory-changing step), plus freestanding SYSCALL `#UD`
   (`sysWit_ud_frei`) and CPL-3 HLT `#GP` (`sysWit_gp_hlt`) refusals.
   Two cores where the family touches memory: yes.
8. **Silicon facts against the Intel extract**
   (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`): HLT
   F4, CLI FA, STI FB, INT3 CC, INT1 F1, CLD FC, STD FD, IRET CF,
   IRETQ REX.W+CF, INT CD ib, PAUSE F3 90, CPUID 0F A2, RDTSC 0F 31,
   RDTSCP 0F 01 F9, XGETBV 0F 01 D0, RDMSR 0F 32 (opcode table
   `0000 1111 : 0011 0010`), WRMSR 0F 30, RDPMC 0F 33, SYSCALL 0F 05,
   SYSRET 0F 07 and REX.W+0F 07 — all confirmed verbatim. No
   silicon claim beyond these transcriptions; fault/privilege
   behaviour is inherited from the accepted `HwSystemForms` legs.
9. **CUTS honest, no oversized claim.** The CUTS block disclaims
   hardware correspondence beyond self-consistency, names Intel-only
   provenance with no AMD fact claimed, lists the 9 deferred rows as
   decode-but-refuse, leaves PREFETCHh/W, SYSENTER/SYSEXIT, CLTS,
   INVD/WBINVD, SMSW/LMSW and CR/DR moves uncovered, error-code
   frames OPEN, undefined flags FREE, timing/serialisation as the
   named assumptions of `HwSystemForms`, and the W/GX bridge OPEN.
   The maintainer wiring note (`sys` arm last in `kapDecode`) and the
   merge-gate layout move (`Befehle/System/`) are disclosed, not
   hidden.

Last `./lean-bau` result line (this clone, clean tree without the
candidate, since this lane owns report only):
`== exit 0; 0 error line(s) in the COMPLETE output` /
`Build completed successfully (708 jobs).`
(708 vs the author's 709 is exactly the absent new module.)

## What remains open

- Nothing in this review: the candidate is accepted as-is. Integration
  order for the maintainer: add the `sys` arm for `sysDecode` in last
  position of `kapDecode` (`HwKapsteinDecoder.lean`, after the `avx2`
  arm) per the `kapDecodeSys_*` theorems; the merge gate moves the
  module to `Befehle/System/` per rule `^System\w+$`.
- Family residue stays with follow-up lanes, as the candidate's CUTS
  states: accepted evaluators for the 9 deferred rows, PREFETCHh/W
  (needs `AddressEncoding` tails plus hint semantics),
  SYSENTER/SYSEXIT (vendor-dependent in 64-bit, correctly left
  refused/uncovered), CLTS, INVD/WBINVD, SMSW/LMSW, CR/DR moves,
  Group 6/7 ModRM splits, error-code IRET frames, and any W/GX bridge.

## What I believe is wrong in the task

- Nothing blocking. Two author judgments I expressly endorse against
  the owner task text: (a) WRMSR/RDMSR decode as deferred refusals
  because `HwSystemForms` models only 10 forms — inventing MSR
  semantics to "cover" them would violate rule 16; (b) rule 13's
  `_zeuge` companion requirement does not trigger — no theorem
  quantifies over program syntax and the owner task names no `ZEUGE:`
  target; the joint closed witness `sysDecode_zeuge` (21 pins plus a
  reached two-core memory-changing run) is the right shape here.
- Partial family coverage (PREFETCH/SYSENTER/CLTS/INVD/CR-DR absent)
  is correctly handled as disclosed CUTS, not silent scope loss, and
  is not a REPAIR reason: covering those rows now would require either
  invented semantics (rule 16 violation) or lowering without an
  evaluator.
