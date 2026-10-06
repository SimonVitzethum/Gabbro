# MUSE-REPORT-1375: Evaluators for system rows that `SystemDecode` could only refuse

## What was done

New file `grammatik/Grammatik/X86/SystemEvaluators.lean` (namespace
`Gabbro.Grammatik.X86`, ~920 lines), plus one import line appended to
`grammatik/Grammatik.lean`. Nine evaluated system rows: five admitted
hint/cache NOPs and four decoded-but-refused MSR/CR0 rows.

Content:
- `SysEvalArt` (9 rows: `prefetchW`, `prefetchWT1`, `clts`, `invd`,
  `wbinvd`, `wbnoinvd`, `sysenter`, `sysexit`, `msw`) with
  `sysEvalLaenge` and `sysEvalLaenge_pins`.
- `sysEvalDecode`: exact-length shapes only (CLTS 0F 06, INVD 0F 08,
  WBINVD 0F 09, SYSENTER 0F 34, SYSEXIT 0F 35, PREFETCHW 0F 0D /1 and
  PREFETCHWT1 0F 0D /2 with MEMORY ModRM, LMSW/SMSW 0F 01 /6//4 with
  MEMORY ModRM, WBNOINVD F3 0F 09). Register forms, wrong reg fields,
  neighbour RDTSCP/XGETBV/CLFLUSH rows and truncated inputs refuse;
  per-row pins (`sysEvalDecode_*`, all `decide`).
- `sysEvalEncode` with `sysEvalRoundTrip` (decoding inverts encoding
  on every row) and `sysEvalEncode_laengen`.
- `kapDecodeSysEval` over `kapDecode` (`SysEvalKette.alt`/`eval`):
  exact agreement on every byte string the old chain decodes
  (`kapDecodeSysEval_alt`, schematic), refusal where both refuse
  (`kapDecodeSysEval_nichts`), old-chain refusal pinned per row
  (`kapDecode_nimmt_*_nicht`, 10 `decide`s — zero overlaps found),
  and one-taking of every new row (`kapSysEval_*`).
- Evaluator legs `sysEvalSnapSchritt` on the accepted outcome
  vocabulary (`SysSnapAusgang`, `kernMitRegRip`, `ArchFehler`,
  reused unchanged, never redefined), driven by `SysEvalEreignis`
  (row plus two explicit CPUID feature-bit inputs, environment
  answers): admitted legs advance RIP only (no fault, no memory or
  buffer effect); absent prefetch features are #UD
  (`sysEval_prefetchW_ud`, `sysEval_prefetchWT1_ud`); CPL/vm
  violations are #GP (`sysEval_*_gp`, `sysEval_*_gp_vm` for
  clts/invd/wbinvd/wbnoinvd); the MSR/CR0 rows refuse
  (`sysEval_sysenter/sysexit/msw_verweigert`).
- `HwAdapter` plug `adapterSysEval` in the style of `adapterSystem`:
  exact snap agreement (`adapterSysEval_ok`), fault/refusal
  admission of nothing (`adapterSysEval_fehler/verweigert`),
  well-formedness preservation (`adapterSysEval_wf`), buffer
  preservation (`adapterSysEval_puffer`), and plug-level refusal of
  the MSR/CR0 rows (`adapterSysEval_sysenter/sysexit/msw`).
- Execution: PREFETCHW advances core-0 RIP 0x1000→0x1003 with memory
  provably unchanged, WBINVD advances core-1 RIP 0x1000→0x1002,
  CPL-3 CLTS is #GP, bit-less PREFETCHW is #UD, SYSENTER is refused
  at both levels, and the joint `sysEval_zeuge` (9 chain pins + 5
  run pins + 2 refusal pins + plug refusal + 3 TSO pins + `SysWf`)
  closes with a TSO issue/forward/drain that changes ACTUAL shared
  memory 0-to-42 with owner-only forwarding. Reuses the accepted
  `sysWitStart`/`sysWitSteuer`/`sysWitHochM` witnesses (never
  redefined).
- CUTS block and `#print axioms` for the 11 main theorems: all
  depend only on `[propext]`, `[propext, Quot.sound]`, or nothing
  (subset of the standard trio). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`.

Last `./lean-bau` result line:
`== exit 0; 0 error line(s) in the COMPLETE output` /
`Build completed successfully (712 jobs).`
`./lean-probe` on the file: `== 0 error(s) ...; exit 0`.
`python3 instrumente/lean-layout.py --check`: every folder at most
20 entries; all 855 Lean files placed.

## Names of new definitions/theorems

`SysEvalArt`, `sysEvalLaenge`, `sysEvalLaenge_pins`,
`sysEvalDecode`, `sysEvalDecode_clts/invd/wbinvd/wbnoinvd/
sysenter/sysexit/prefetchW/prefetchWT1/msw`,
`sysEvalDecode_prefetch/msw_register_verweigert`,
`sysEvalDecode_rdtscp/falsches_reg_verweigert`,
`sysEvalDecode_leer/esc/prefetch/wbnoinvd_abgeschnitten`,
`sysEvalEncode`, `sysEvalRoundTrip`, `sysEvalEncode_laengen`,
`SysEvalKette`, `kapDecodeSysEval`, `kapDecodeSysEval_alt/nichts`,
`kapDecode_nimmt_*_nicht` (10), `kapSysEval_*` (10 incl.
`kapSysEval_leer`), `SysEvalEingaben`, `SysEvalEreignis`,
`sysEvalSnapSchritt`, `sysEval_prefetchW_ok/ud`,
`sysEval_prefetchWT1_ok/ud`, `sysEval_clts/invd/wbinvd/wbnoinvd_
ok/gp/gp_vm` (12), `sysEval_sysenter/sysexit/msw_verweigert`,
`adapterSysEval`, `adapterSysEval_ok/fehler/verweigert/wf/puffer`,
`adapterSysEval_sysenter/sysexit/msw`, `sysEvalWitEingaben`,
`evalRipOut/KlasseOut/MemOut`, `sysEvalWitO_prefetchW/wbinvd/
cltsHoch/prefetchWohne/sysenter`, `sysEvalWit_prefetchW_rip/
wbinvd_rip/prefetchW_mem/clts_gp/prefetchW_ud/sysenter`,
`sysEvalWitAdr/Tso0/Tso1/Eigen/Fremd/Tso2/NachFlush`,
`sysEvalWit_weiterleitung/fremd_alt/spuelung_aendert_speicher`,
`sysEval_zeuge`.

## What remains open

- Wiring into the built chain: add a `syseval` arm for
  `sysEvalDecode` in last position of `kapDecode`
  (`HwKapsteinDecoder.lean`, after the `avx2` arm). Deliberately NOT
  done here (existing files may not be edited by this lane); the
  `kapSysEval_*` theorems state the exact required behaviour for the
  maintainer.
- SIB/displacement address tails refuse (exact-length shapes only,
  the accepted prefetch precedent); the formed effective address is
  not computed. The `SysExtra` nine of `SystemDecode` (INT3/INT1
  debug delivery, CLD/STD over the unmodelled DF bit, RDMSR/WRMSR/
  RDPMC/RDTSCP/XGETBV over unmodelled MSR/counter/XCR0 state) stay
  with their own lanes. SMSW register forms (mod=3) are not decoded.
- CLTS clears no tracked bit (no CR0 in the model); INVD/WBINVD/
  WBNOINVD retire with no modelled cache effect; timing,
  serialisation, the INVD post-BIOS platform refusal and WBNOINVD
  enumeration stay named assumptions (CUTS).
- No W/GX bridge, no width-merge obligations (no register or memory
  writes exist in this family; that is stated, not dodged — every
  admitted leg carries `m.mem` and unchanged control syntactically).
- `lean-layout --apply` (merge gate) moves this module to
  `Befehle/System/` per rule `^System\w+$` and rewrites the import.
- Rule 13 (`_zeuge` for ∀-over-syntax premises) does not trigger:
  all theorems are closed byte/step equations plus one joint closed
  witness (`sysEval_zeuge` joins all rows with the reached run); no
  theorem quantifies over program syntax and the task names no
  `ZEUGE:` target.

## What I believe is wrong in the task

- The FAMILY paragraph is truncated in my copy (`.tmp/LANE.md` line
  26 ends mid-sentence at "no-visible-effect-on-the-memory-mode..."),
  so the exact intended nine rows are unrecoverable from the task
  text. I reconstructed them from report 1365's OPEN list and the
  ledger: PREFETCHW is `fehlt` ("common"), CLTS/INVD/WBINVD/
  SYSENTER are `verweigert`-without-evaluator, PREFETCHWT1/WBNOINVD/
  LMSW/SMSW likewise uncovered. If the intended nine differ, the
  module is structured so a follow-up can swap rows without touching
  the chain/adapter/witness pattern.
- PREFETCHh is named in the visible fragment but already has an
  accepted evaluator (`HwMemTypesWC` decode + NOP + adapter); I reuse
  that fact and do not duplicate it (rule 16). The task's "nine
  rows" cannot include PREFETCHh without double-modelling.
- CONTEXT para 28 describes the generic adapter-lane mechanism with
  `HwSchritt`-embedding and two-core forwarding witnesses; the
  ledger-style obligations of para 26 (round trip, extended chain,
  agreement, refusals, memory-changing witness) are what I
  implemented. The width-merge sentence of para 26 does not apply to
  a writeless NOP family; the report states this plainly instead of
  manufacturing width theorems.
- One `./lean-probe` attempt timed out at 600s (cold manifest build
  in this clone); the retry with a longer budget passed. No slot
  contention was created (no raw `lake`, no duplicate builds).
