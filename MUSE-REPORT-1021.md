# MUSE-REPORT-1021: Exact review of author 871 (strength reduction rule)

## CANDIDATE

CANDIDATE: 871 ca858ebe6b3bf24b83994cf10307a22614f8eabf

## VERDICT

VERDICT: ACCEPT (bounded: source-level `eval`/`execEnd`/word connection only; no machine-byte, TSO/GX, ABI/loader, or machine-work claim — exactly the boundary stated in the candidate's CUTS, which I endorse as the acceptance scope).

## What was reviewed

- Pinned snapshot files: `.tmp/review/author-871/grammatik/Grammatik/X86/OptStrengthRed.lean` (378 lines), the one-line `Grammatik.lean` import append, `MUSE-REPORT-871.md`, `OWNER-TASK.md`, `PATCH.diff`, `BUILD-EVIDENCE.json` (`SNAPSHOT.json`: base `b040b155`, == this clone's base; files list clean, no other paths).
- Official local reference: `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt` (Intel SDM 325462-093US, verified 2026-10-02) — IMUL flag lines (~58250) and SHL flag lines (~93490).
- Base-tree vocabulary the candidate reuses (all present at the snapshot base, unchanged by the candidate): `mul_pow2_shl` + `sdiv_kein_shift` (`X86/StaerkeReduktion.lean`), `mulFlagsS` (`X86/MulDiv.lean`), `shlTrag`/`shlUeberlauf` (`X86/ShiftLogic.lean`), `schiebeZaehler`/`mulTragS` (`X86/Ganzzahl.lean`), `refD`/`refEin`/`refEin_schreibt`/`refO`/`refB_erreicht`/`refB_schreibt`/`keinRuf`/`vertragVon` (`ReferenzB.lean`/`Maschine.lean`/`Syntax.lean`, including the established two-argument `vertragVon refD refEin` idiom).
- DESIGN scope: `DIRECT-COMPILER-DESIGN.md` section 7 row ("Strength reduction | per-width flag/fault identity lemma (CF vs OF distinct) | A register rule | `imul r,8 -> shl r,3` with live CF; signed-divide rounding via shift; `a*2.0 -> a+a` (rounding/NaN) | L / O(window)") — the candidate covers all three failure cases with named refusals.

## Findings (all checked, none blocking)

1. **Flag/fault identity is architecturally correct.** Intel: IMUL sets-and-clears CF and OF together on signed overflow (CF = OF always) — matches `imul_cf_gleicht_of` (`rfl` over `mulFlagsS`, consistent with `MulGueltigS`). Intel SHL: CF = last bit shifted out, OF defined only for 1-bit shifts — matches `shl_drei_trag` (OF `none` at masked count 3, CF = bit 61 = `64 - 3`). The CE-6 distinguisher (`2^62 * 8` vs `2^62 << 3`: both value 0, IMUL CF `true` vs SHL CF `false`) is arithmetically sound and kernel-checked by `decide`. No invented determinism: OF-undefined is modelled as `none`, not zeroed.
2. **No banned constructs.** No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file (the only "admit" substrings are the English word "admitted"). No `intro _` / `have _ :=` discards; no premise typed as `Prop` itself. Every premise of `OptStrengthRed_verbindung` is used (`hz` via `hAdm`, `hW` via `staerkeWort_acht`, widths/evidence in the expression constructors, `O`/`passes`/`R`/`rest`/`σ`/`ρ` in `hOut`).
3. **Refusals are real, not warnings.** Four general refusal theorems (`staerkeVerweigert_cf/breite/float/sdiv`) plus positive and negative `decide` probes (`ok`, live-CF, float). The float `a*2.0 -> a+a` and `sdiv`-via-shift shapes have no rewrite arm at all; the report honestly states the float refusal rests on missing identity evidence (NaN payload, invalid/inexact flags differ on silicon), not on a model counterexample. No `ensures` derived; a refused optional optimisation falls back to another certified translation.
4. **Connection theorem is exactly as strong as stated, no stronger.** Four formal conjuncts (bound-value equality, `execEnd` outcome equality via `hort : orte` by `rfl` + `hEq` + `simp only [execEnd, ...]`, word readback, admission implies `cfTot`/`breiteOk`) — all machine-checked. IEEE/contracts/call-logs/concurrency/budget appear only as documented consequences of the `execEnd` + `orte` equalities with no `Block.gleit` rewritten and one shared block shape, not as separate formal conjuncts; that matches what the formulae prove and does not over-claim. No desired-simulation premise is assumed.
5. **Witness is joint and non-degenerate.** `OptStrengthRed_verbindung_zeuge` instantiates every premise together (`5 * 8` to `5 << 3` under `bind`/`leave` on `refD`) beside the reached memory-changing run (`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`). The `_hz`/`_hW` underscore binders are supplied by `by decide` in the existential package, not discarded.
6. **Scope hygiene.** One new file + one import line; no friend-reserved optimiser file, no source/checker/Spec/goal/emitter edit, no diagnostic/gift/example/CLI numbers, no MARKE changes. CUTS block and `#print axioms` for every main theorem are present.
7. **Build evidence.** `BUILD-EVIDENCE.json` records the honest iterative path (intermediate `lean-probe` failures, each repaired) to a final `0 error(s)` probe and full `./lean-bau` green (`Build completed successfully (511 jobs)`), with every axiom set a subset of `{propext, Classical.choice, Quot.sound}`. `gabbro_ziel` untouched (additive-only change), so its axiom set is unaffected.

## Observations (not defects, recorded for the record)

- Conjunct (4) of the connection (admission implies `cfTot`/`breiteOk`) restates part of `hz`; as one guardrail conjunct inside a four-conjunct preservation theorem this is defence-in-depth, not a rule-4(a) restatement — accepted as is.
- The flag identity is established at `.b64` (the rule's operating width, CE-6 witness included) with width-exactness enforced by the `breiteOk` refusal; no per-width (b8/b16/b32) flag lemma is claimed or needed at this source-level scope. Any future machine-byte transfer must re-establish the width it fires at — already excluded by CUTS.
- Negative probes exist for live-CF and float; `sdiv` and `breite` have general refusal theorems but no `decide` probe each. Adequate for a Bool-level admission gate; a future edit may add the two one-line probes without changing any claim.

## What remains open (agreed, per candidate CUTS)

No machine-byte correspondence (encoding/decoding/RIP stepping/loading stay with the validation lanes); no `sdiv`/float rewrite arms; no new `Befehl` forms (wiring stays with the Typen owner); no per-access TSO/GX bridge, ABI/loader, contract inference, or machine-work inequality.

## Build/wrapper status in this clone

No source owned or touched by this lane (report-only review), so no `./lean-bau`/`./lean-probe` run was started in `a1021`: re-running the 511-job build over unchanged inputs would measure nothing. Verification rests on the pinned `BUILD-EVIDENCE.json` (final green) plus the independent file/manual inspection above. I did not copy candidate sources into this tree (would violate single-file ownership) and `git branch`/`git log --all` invocations were permission-blocked in this session, so the pinned HEAD is taken from `.tmp/review/SNAPSHOT.json`, not re-resolved locally.
