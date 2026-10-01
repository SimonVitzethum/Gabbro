# MUSE-REPORT-473: Independent exact-candidate review of 425 (re-review of second repaired head)

Lane 473, clone `/home/simon/Dokumente/gabbro-muse/a473`, branch `muse/473` (verified).
Candidate: author lane 425, snapshot `.tmp/review/SNAPSHOT.json` (NEW pinned head; this report supersedes the stale verdicts on `022cdf29` and `64d29a78`).

## Scope inspected (new snapshot)

- `.tmp/review/SNAPSHOT.json`: author 425, head `506f5fb1086a1a7ffd0f79664a0635a101881403`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-425.md`, `grammatik/Grammatik.lean` (one additive import), `grammatik/Grammatik/X86/FloatExceptions.lean` (new, 213 lines), `clean: true`.
- `.tmp/review/author-425/OWNER-TASK.md`, `MUSE-REPORT-425.md` (now with `Second integration gate failure` + `Olean-weight analysis` sections on top of the previous gate-failure/repair sections), `BUILD-EVIDENCE.json` (28 queued commands incl. olean sizes, re-verify probe `probe425c`, report-only commit `506f5fb1`), `PATCH.diff` (Lean hunks identical: `Grammatik.lean` +1 import line, new `FloatExceptions.lean` blob `096de3b2`, 213 lines), supplied `grammatik/Grammatik/X86/FloatExceptions.lean` (md5 `52dea56356f10d5d42aff450f21af56f`, identical to both prior rounds).
- Dependency ground truth in this clone unchanged: `Gleitprofil.lean` (`mxcsrGueltig`, `mxcsr_ftz_verweigert`, `kontextReset`, `kontextReset_gueltig`, `mxcsr_sticky_egal_gueltig`, `fdiv64`, `muster64`), `Gleitkomma.lean` (`zeuge_einsDurchNull`, `zeuge_nullDurchNull`, `zeuge_divDrittel`), `X86/Speicher.lean` (`write64`, `read64`, `read64_nach_write64`, `writeBytesN_hit`, `zeugenSpeicher`).

## Delta vs previous reviews (old heads `022cdf29`, `64d29a78`)

- Author's repair statement verified again: NO Lean content change. Commit `506f5fb1` sits on `64d29a78` (BUILD-EVIDENCE `git log` shows the chain) and the supplied Lean file is byte-identical (same md5, same blob `096de3b2`, same 213 lines). New report sections are evidence/argument only: second gate failure with byte-identical log modulo step time, and olean weights (`FloatExceptions` 76,848 vs `Gleitprofil` 503,728 vs `Speicher` 1,735,696). No new theorems, no changed proofs, no new premises — all previous findings carry over and were re-checked, not assumed.
- The olean-weight argument is correctly framed as supporting evidence alongside the no-import control (umbrella crashes with zero bytes of candidate work in the closure), not as a standalone proof; the `exact`-reuse-cost remark is accurate (use sites reference checked proofs, no re-evaluation). No overclaim.
- Minor staleness (non-blocking, report text only): the `Repair outcome (unchanged)` section still says "tree still at `022cdf29`"; the chain is now `022cdf29` -> `64d29a78` -> `506f5fb1`, all with empty `git diff HEAD -- grammatik`. Substantive claim (no Lean change) verified true via identical blob hash.
- Previous advisory carries over (still not blocking): the valid-side joint witness covers guard + value + pattern-nonzero while the memory round-trip lives in the separate `guardedDiv_speicher` theorem. Described accurately by the author; no repair demanded.

## Independent reproduction (fresh, against NEW pinned content)

- Staged the NEW supplied `FloatExceptions.lean` verbatim into this clone (umbrella untouched; file imports only `Grammatik.X86.Gleitprofil`), ran `./lean-probe grammatik/Grammatik/X86/FloatExceptions.lean`, then deleted the staged file. Tree clean again before writing this report.
- Result: `rc=0`, `== 0 error(s) in the COMPLETE output; exit 0`, all 13 `#print axioms` lines print: 12x `[propext]`, 1x `[propext, Quot.sound]` (`guardedDiv_speicher`). No `sorryAx`. Matches the author's claimed probe evidence (`probe425c` entry: rc=0, 0 errors, 0 `sorryAx`) exactly.
- Grep over the NEW candidate file: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `intro _` / `have _ :=`. 13 `#print axioms` present. English only. Trailing `CUTS:` block present and honest (fault-vs-refusal, sticky accumulation/clearing, NaN payloads, f32/FMA/other ops and exception classes, SSE/div-byte correspondence, decoder/cost/TSO/final-image, hardware bit positions).
- Full `./lean-bau` (umbrella) and the `gabbro_ziel` axiom re-check were NOT re-run here: author's extended BUILD-EVIDENCE documents the umbrella `Grammatik` target crashing with `failed to create thread / exit 134` both WITH the module and WITHOUT it (no-import control `bau425c`, failing at `AccessList` axioms print, i.e. before any candidate code) and identically in the main checkout. The control is the correct experiment and its outputs remain internally consistent, so the red umbrella is still accepted as a pre-existing environmental failure, not candidate-caused. The bounded claim needs only the module probe plus the additive import, both verified.

## Semantic checks (re-verified on new head)

- Correctness: `floatGuard k = mxcsrGueltig k.mxcsr` reuses the accepted profile; `guardedDiv64` returns `some (fdiv64 a b)` under a valid context and `none` otherwise — a lowering refusal, never a modelled trap. Both directions proved by `simp [h]` (guard premise genuinely used). `guard_standard` / `guard_ftz_verweigert` / `guard_sticky_offen` reuse the accepted `decide` witnesses. `divEinsNull_modell` / `divNullNull_modell` reuse `zeuge_einsDurchNull` / `zeuge_nullDurchNull` through the definitional `fdiv64` wrapper. `divDrittel_muster` rewrites with `zeuge_divDrittel` after unfolding `muster64`/`fdiv64`. `guardedDiv_speicher` threads a real `write64`/`read64` round-trip at address 0 with pattern `0x3FD5555555555555` over `zeugenSpeicher`, closing memory change via `writeBytesN_hit` + `addrOff_null` + `decide`. No invented machine, no second IR/executor, no hardware/trap/decoder/cost/TSO/final-byte claim.
- No vacuity: both guard outcomes inhabited (`kontextReset` valid, `0x9F80` refused) and jointly witnessed on complementary sides. Every theorem premise used; no conclusion restates a premise; no contract quantified away; the only memory claim goes through real `Speicher` ops with an inequality.
- Trust boundaries preserved: source checker, Spec, goal, Rust, emitter, Typen/execution/codec untouched (PATCH confirms: one import line + new file + report). Friend files untouched. Masked exceptions as values, faults distinguished from refusals in code and CUTS, per-context validity kept, no fastmath/FMA/NaN-payload/f32 invention.
- Bounded claim only: guarded binary64-divide slot + refusal discipline + one observed memory write. ACCEPT applies to exactly this bounded claim, never full compiler closure.

## Defects

None blocking.

## Files changed by this review

- `MUSE-REPORT-473.md` only (this file). Candidate files were staged temporarily for the probe and fully removed before writing this report.

CANDIDATE: 425 506f5fb1086a1a7ffd0f79664a0635a101881403
VERDICT: ACCEPT
