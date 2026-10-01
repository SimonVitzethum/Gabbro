# MUSE-REPORT-473: Independent exact-candidate review of 425

Lane 473, clone `/home/simon/Dokumente/gabbro-muse/a473`, branch `muse/473` (verified).
Candidate: author lane 425, snapshot `.tmp/review/SNAPSHOT.json`.

## Scope inspected

- `.tmp/review/SNAPSHOT.json`: author 425, head `022cdf295921c3694780d4b4c8ef671b8c5d4dbd`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-425.md`, `grammatik/Grammatik.lean` (one additive import), `grammatik/Grammatik/X86/FloatExceptions.lean` (new, 213 lines), `clean: true`.
- `.tmp/review/author-425/OWNER-TASK.md` (lane 425 task), `MUSE-REPORT-425.md`, `BUILD-EVIDENCE.json` (19 queued commands), `PATCH.diff` (325 lines), supplied `grammatik/Grammatik/X86/FloatExceptions.lean`.
- Dependency ground truth in this clone: `grammatik/Grammatik/X86/Gleitprofil.lean` (`mxcsrGueltig`, `mxcsr_ftz_verweigert`, `kontextReset`, `kontextReset_gueltig`, `mxcsr_sticky_egal_gueltig`, `fdiv64`, `muster64`), `grammatik/Grammatik/Gleitkomma.lean` (`zeuge_einsDurchNull`, `zeuge_nullDurchNull`, `zeuge_divDrittel`), `grammatik/Grammatik/X86/Speicher.lean` (`write64`, `read64`, `read64_nach_write64`, `writeBytesN_hit`, `zeugenSpeicher`).

## Independent reproduction

- Staged the supplied `FloatExceptions.lean` verbatim into this clone (umbrella untouched; file imports only `Grammatik.X86.Gleitprofil`), ran `./lean-probe grammatik/Grammatik/X86/FloatExceptions.lean`, then deleted the staged file. Tree is clean again (`git status` empty before report).
- Result: `rc=0`, `== 0 error(s) in the COMPLETE output; exit 0`, all 13 `#print axioms` lines print: 12x `[propext]`, 1x `[propext, Quot.sound]` (`guardedDiv_speicher`). No `sorryAx`. This matches the author's claimed probe evidence exactly (BUILD-EVIDENCE entry with the same 13 lines).
- Grep over the candidate file: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `intro _` / `have _ :=`. 13 `#print axioms` present. English only. Trailing `CUTS:` block present and honest (fault-vs-refusal, sticky accumulation/clearing, NaN payloads, f32/FMA/other ops and exception classes, SSE/div-byte correspondence, decoder/cost/TSO/final-image, hardware bit positions).
- Full `./lean-bau` (umbrella) and the `gabbro_ziel` axiom re-check were NOT re-run here: author's BUILD-EVIDENCE documents the umbrella `Grammatik` target crashing with `failed to create thread / exit 134` both WITH the module and WITHOUT it (control entry `bau425c`: import line removed, same crash; swap exhaustion visible in `free` outputs). That control is the correct experiment and its outputs are internally consistent, so the red umbrella is accepted as a pre-existing environmental failure, not candidate-caused. The bounded claim needs only the module probe plus the additive import, both verified.

## Semantic checks

- Correctness: `floatGuard k = mxcsrGueltig k.mxcsr` reuses the accepted profile (RNE, FTZ/DAZ off, all masks set; sticky bits unchecked). `guardedDiv64` returns `some (fdiv64 a b)` under a valid context and `none` otherwise — a lowering refusal, never a modelled trap. Both directions are proved by `simp [h]`, so the guard premise is genuinely used. `guard_standard`, `guard_ftz_verweigert`, `guard_sticky_offen` reuse the accepted `decide` witnesses (`kontextReset_gueltig`, `mxcsr_ftz_verweigert`, `mxcsr_sticky_egal_gueltig`). `divEinsNull_modell` / `divNullNull_modell` reuse `zeuge_einsDurchNull` / `zeuge_nullDurchNull` through the `fdiv64 = Gleitkomma.div` wrapper — valid since `fdiv64` is definitionally the accepted divide. `divDrittel_muster` rewrites with `zeuge_divDrittel` after unfolding `muster64`/`fdiv64` — valid. `guardedDiv_speicher` threads a real `write64`/`read64` round-trip at address 0 with pattern `0x3FD5555555555555` over `zeugenSpeicher` (all-zero bytes, fully permissive), closing memory change via `writeBytesN_hit` + `addrOff_null` + `decide` (low byte `0x55` vs `0x00`). No invented machine, no second IR/executor, no hardware/trap/decoder/cost/TSO/final-byte claim.
- No vacuity: both guard outcomes are inhabited (`kontextReset` valid, `0x9F80` refused) and jointly witnessed on complementary sides (`guardedDiv_gueltig_zeuge` over reset + `1/3` with pattern `≠ 0`; `guardedDiv_verweigert_zeuge` over `0x9F80` + `1/0` classified `.unendlich`). Every theorem premise is used; no conclusion restates a premise; no contract quantified away; nothing is called a semantics without memory change (the only memory claim goes through real `Speicher` ops with an inequality).
- Trust boundaries preserved: source checker, Spec, goal, Rust, emitter, Typen/execution/codec untouched (PATCH confirms: one import line + new file + report). Friend files untouched. Masked exceptions delivered as values, faults distinguished from refusals in both code and CUTS, per-context (not global) validity kept, no fastmath/FMA/NaN-payload/f32 invention.
- Bounded claim only: guarded binary64-divide slot + refusal discipline + one observed memory write. Report does not claim closed lowering, hardware verification, emitted ISA, final-byte validation, or speed. ACCEPT applies to exactly this bounded claim, never full compiler closure.

## Defects

None blocking. One advisory (not a repair trigger): the valid-side joint witness covers guard + value + pattern-nonzero but not the memory round-trip itself; the memory change lives in the separate `guardedDiv_speicher` theorem. Joint coverage is still adequate and the report describes it accurately, so no repair is demanded.

## Files changed by this review

- `MUSE-REPORT-473.md` only (this file). Candidate files were staged temporarily for the probe and fully removed before writing this report.

CANDIDATE: 425 022cdf295921c3694780d4b4c8ef671b8c5d4dbd
VERDICT: ACCEPT
