# MUSE-REPORT-1351: MOV, TEST, LEA, PUSH/POP, NOP and the frame instructions

## What was done

NEW FILE `grammatik/Grammatik/X86/IntMovTest.lean` (~1993 lines) plus one
`import Grammatik.X86.IntMovTest` line appended to `grammatik/Grammatik.lean`.
Own namespace `Gabbro.Grammatik.X86`, reusing accepted definitions unchanged
(`NarrowOps.mergeRegNarrow`, `ShiftLogic.andW`/`logikFlags`, `AddressEncoding`
`parseAdrTail`/`adrEff`/`encodeAdr`, `HwAddressed.hwAddrStore`/`hwAddrLoad`,
`HwStackCalls` TSO helpers, `Ausfuehrung` `schrittRegister`/`ripNach`/
`laengeOk`/`regSet`, `Hudson` machine `HwMaschine`/`HwWf`/`HwAdapter`).

Sections: §1 family decoder `decodeMovTest`; §2 decode pins; §3 chain
verdicts against `kapDecode`; §4 boundary ownership probes; §5 canonical
encoder `encodeMt`; §6 round trips; §7 register semantics `mtSchritt`;
§8 extended chain `kapDecodeMitMt`; §9 adapter `adapterMt` over
`MtEreignis`; §10 reached two-core witness with joint `mt_zeuge`;
CUTS block and `#print axioms` per main theorem (all standard:
`[propext]` or `[propext, Quot.sound]`, no `sorryAx`).

## Definitions (exact names)

`MtForm` (24 constructors: `movRR/RM/MR`, `movRI8`, `movRIB16`,
`movRImm8/16/32`, `movMImm8/16/32/64`, `testRR/RM`,
`testAI8/16/32/64`, `testRImm8/16/32/64`, `testMImm8/16/32/64`,
`leaBare`, `nopMem/nopReg`, `endbr64`, `pushR/M`, `popR/M`, `leave`,
`retImm`, `int3`, `ud2`), `MtDecodiert`, `mtPraefix`, `mtWeiteMov`,
`mtByteRegOk`, `mtSplitModrm`, `mtParseLe16`, `mtLeBytes16`,
`mtDecodeMovRM`, `mtDecodeTestRM`, `mtDecodeImmReg`, `mtDecodeImmMem`,
`mtDecodeImm`, `mtDigit`, `mtDecodeMisc`, `mtDecodeOpcode`,
`decodeMovTest`, `mtRexFuer`, `mtRexReg`, `mtPre16`, `mtNarrowLoch`,
`encodeMtMem`, `encodeMt`, `MtKap`, `kapDecodeMitMt`, `mtSchritt`,
`fMT`, `fMTSib`, `MtEreignis`, `setKernVonZustandMt`, `mtAdapterReg`,
`adapterMt`, `mtPushKern`, `mtPushOben`, `mtPushW`, `mtPopKern`,
`mtPopW`, `mtLeaveKern`, `mtLeaveW`, `mtRetKern`, `mtRetW`, `mtWitV`,
`mtWitTop`, `mtWitSlot`, `mtWitReg0`, `mtWitKern`, `mtWitM0`,
`mtWitM1`, `mtWitM2`, `mtWitT1`, `mtWitF1` .. `mtWitF8`.

## Theorems (exact names)

Decode pins `pin_mt_*`: `movRR32/88/8B/8A/66`, `movRRw64_refuses`,
`movRRw64_8b`, `movRI8`, `movRIB16_r8`, `movRIB16`, `movRImm32`,
`testRImm32`, `89_nw_mem_mod1`, `c7_w64_mem`, `testAI8/32/64`,
`movRImm8`, `testRImm8`, `testRR84/85/85_16`, `popR`, `pushR`,
`pushRrsi`, `leave`, `retImm`, `int3`, `nopReg`, `nopReg66`, `ud2`,
`endbr64`, `mem_ok`, `fremd_verweigert`.
Removed during scope correction (rows owned elsewhere, never
redefined): `movRIB32`, `movRImm64` (+ their pins).
Chain verdicts `pin_kap_*`: refusal pins `89/8b/88/8a/89_66/b0/
b8_66/89_mem/a8/a9/a9_w64/c6/f6/84/85/85_66/misc_verweigert/
8b_mem/8d/c7_mem/f7_mem/nop_mem`; acceptance (`isSome`) pins
`89_w64` (pilot movReg64), `b8` (decodeC mov32imm), `c7_w64`
(decodeC), `89_w64_mem`, `8b_w64_mem`, `89_nw`, `89_nw_mem`
(decodeNarrow), `fremd_nimmt` (REX.W 85 via decodeCore, REX.W
B8-imm64 via pilot).
Boundary probes `probe_kap_*` (all refused, rows kept):
`8b_w64`, `88_w64`, `8a_w64`, `c7_reg`, `c7_reg_66`,
`c7_reg_rex`, `f7_reg`, `f7_reg_rex`, `b8_66_rex`, `c6_rex`,
`c7_mem_66`, `c7_w64_mem`, `c7_66_rex`, `c7_nw_mem`,
`f7_w64_mem`, `c6_w64_mem`, `f6_w64_mem`, `8f_w64`, `ff_w64`.
Round trips `roundtrip_mt_*`: `movRR`, `testRR`, `nopReg`,
`pushR`, `popR`, `endbr64`, `leave`, `int3`, `ud2` (general,
suffix-threaded, befehl-projected) and closed `movRM_mem`,
`movMR_mem`, `leaBare_mem`.
Step agreement: `mtSchritt_movRR_ist_moveNarrow`,
`mtSchritt_testRR_flags`, `mtSchritt_movRR_rahmen`.
Chain agreement: `kapDecodeMitMt_kap`, `kapDecodeMitMt_mt`,
`kapDecodeMitMt_nichts`.
Adapter: `adapterMt_store`, `adapterMt_load`,
`adapterMt_verweigert`, `adapterMt_reg/pushW/popW/leaveW/retW`,
`adapterMt_wf`, `mtAdapterReg_wf`, `mtPushW_wf`, `mtPopW_wf`,
`mtLeaveW_wf`, `mtRetW_wf`, `mtPushW_laenge_verweigert`,
`mtPopW_laenge_verweigert`, `mtLeaveW_laenge_verweigert`,
`mtAdapterReg_laenge_verweigert` (accepted `hwAddrStore_wf` /
`hwAddrLoad_wf` reused, never redefined).
Witness: `mtWitM0_wf`, `mtWit_puffer8`, `mtWit_rsp_slot`,
`mtWit_rip_weitet`, `mtWit_mem_still`, `mtWit_pop_wert`,
`mtWit_pop_rsp`, `mtWit_weiterleitung`, `mtWit_fremd_alt`,
`mtWit_spuelung`, `mtWit_fremd_neu`, `mtWit_mov_wert`,
`mtWit_test_zf`, `mtWit_adapter_reg`, joint `mt_zeuge`
(push then pop through the adapter, eight-flush drain changing
memory 0 to `0x08`, owner-only forwarding, MOV value, TEST zero
flag, planted refusal; non-degenerate two-core run).

## Verification

Last `./lean-bau` result line:
`Build completed successfully (709 jobs).`
(`== exit 0; 0 error line(s) in the COMPLETE output`.)
`./lean-probe grammatik/Grammatik/X86/IntMovTest.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new
file; `#print axioms` is `[propext]` or `[propext, Quot.sound]`
for every main theorem (full list in the file tail).
`python3 instrumente/lean-layout.py --check`: NOT PLACED for the
new file (conflict documented below); everything else placed.

## Findings (product)

Ownership verdicts measured by `decide` against `kapDecode`:
the old chain already takes REX.W 89-reg (pilot `movReg64`),
REX.W 89/8B memory, bare/REX B8-imm32 and REX.W C7-reg
(decodeC), REX 89 mod 2/3 (decodeNarrow), REX.W 85-reg
(decodeCore) and REX.W B8-imm64 (pilot) — all refused here,
never redefined. Kept rows (chain refuses): bare/66/REX MOV
88/8A/8B and 89 except the narrowed rows, B0-B7, 66-B8, A8/A9
incl. REX.W A9, C6/C7 digit 0 except REX.W C7-reg, F6/F7
digits 0/1, 84/bare-85/66-85, bare 8D, 0F 1F NOP bare/66,
ENDBR64, 8F digit 0, FF digit 6, LEAVE, RET imm16, INT3, UD2.
Forced-REX finding: byte codes 4-7 name high bytes without
REX, so the encoder emits a bare 0x40 REX there (decoder
accepts); without it the round trip genuinely fails.
`-/` finding: the two-letter sequence `-` + `/` closes a Lean
block comment. It appeared once in my CUTS text (`/0-/1`),
broke parsing of everything after it, and made the next build
report `sorryAx` on `mt_zeuge` (error recovery fills failed
proofs with sorry) — fixed by rewording, final axioms clean.
This also explains the earlier confusing build state.

## What remains open (see CUTS)

No silicon correspondence (canonical subsets, self-consistency
only); no general memory round trip (needs a
parseAdrTail∘encodeAdr inversion lemma); no per-access
target-to-W/GX simulation; no LOCK/RMW path; no interrupts; no
source/ABI/loader/entry/budget claim. Maintainer wiring: add
the family rows behind the last (`avx2`) arm of `kapDecode` in
`grammatik/Grammatik/X86/Hw/Kapstein/HwKapsteinDecoder.lean`;
the `kapDecodeMitMt_*` theorems state the contract (old chain
first, exact agreement).

## Task issues believed wrong

1. Layout conflict: lane task mandates NEW FILE
`grammatik/Grammatik/X86/IntMovTest.lean` (and OWN ONLY that
path), but `lean-layout-rules.py` rule 36 assigns
`Int[A-Z]\w*` to `Befehle/Ganzzahl`. Running `--apply` would
move the file outside the owned set and rename the module,
breaking the task-required import line. Kept the task path;
the merge gate runs `--apply` at merge.
2. XCHG 90+r/86/87 and REX.W LEA are listed as family rows but
are owned by accepted decoders (`decodeSx`, `decodeCore`/
`decodeLea`) — correctly excluded here, never duplicated.
3. CONTEXT/MECHANISM describe two lane kinds (ledger pins vs
HwAdapter connection); this lane delivers both (decode pins
plus adapter with witness).
4. Rule 13 inhabitation does not trigger mechanically (no
premise quantifies over program syntax, no ZEUGE target), but
MECHANISM (4) is delivered as the joint `mt_zeuge` witness.

## Integration repair analysis (gate FAILED, nothing merged)

Gate evidence (verbatim): `RuntimeError: goal axiom check
failed`; integration lean output `== exit 0; 0 error line(s)`,
`Build completed successfully (718 jobs)`, all lane axioms
standard; integration axioms output `== 1 error(s)`: file
`merge-1351-axioms.lean:1:0: error: import
Grammatik.Bausteine.Gleitkomma.Gleitkomma failed, environment
already contains 'Gabbro.Grammatik.Gleitkomma.instReprGBits'
from Grammatik.Gleitkomma`.

Diagnosis (all evidence gathered read-only inside this clone):
the merged Lean code is green — the gate's own lean output
proves it (exit 0, 718 jobs, every lane axiom standard). Only
the gate's auxiliary axioms-check file fails, at import time,
on a duplicate declaration whose home module is
`Grammatik.Gleitkomma`. That module has NO source file anywhere
in this clone's tracked tree (`git ls-files
grammatik/Grammatik/Gleitkomma.lean` is empty; glob finds only
`Bausteine/Gleitkomma/Gleitkomma.lean` and `GleitkommaBits.lean`).
No file in this clone imports the stale module name. My file
declares a single `namespace Gabbro.Grammatik.X86`, defines
nothing named `GBits`/`instReprGBits`, and imports only sixteen
`Grammatik.X86.*` modules — all long-accepted and already in
the root closure. All four lane commits touch only the three
owned files, so the branch cannot create, delete, or resurrect
any `Gleitkomma.lean` path. The sole in-clone definer of
`Gabbro.Grammatik.Gleitkomma.instReprGBits` is the Bausteine
file itself (`structure GBits ... deriving Repr` under
`namespace Gabbro.Grammatik.Gleitkomma`), which the root
`Grammatik.lean` already imports at line 224 alongside my
module at line 712 — a combination proven green twice
(exit 0, 709 jobs here; exit 0, 718 jobs in the gate's own
lean output).

Conclusion: no repair within the owned files addresses this.
Removing my import line would not dissolve a duplicate whose
both sides live outside my files, and would break the
task-mandated wiring. The defect lives in the coordinator
workspace state, not the candidate: a stale
`grammatik/Grammatik/Gleitkomma.lean` source file there, or —
more likely given the documented poisoned-cache class
(AGENTS.md section 9) — a stale `.lake` olean for the
pre-layout module being loaded into the check environment.

Concrete blocker for the coordinator (outside my directory,
not touchable from this lane): in the merge workspace,
confirm with `git status`/`git ls-files` whether a stale
`grammatik/Grammatik/Gleitkomma.lean` exists and delete it if
untracked; otherwise drop the poisoned `.lake` caches per the
documented procedure (replace with the warm master cache,
never resume them) and re-run the gate. Fresh independent
review of the changed commit is still required.

No acceptance of the full source/binary chain is claimed
here; the candidate stands exactly as reviewed: green build,
standard axioms, open items per CUTS above.
