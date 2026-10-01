# MUSE-REPORT-401.md

Lane 401: Continuous workforce organisation and next dependency-aware proof queue.

## Clone/branch check

- Clone: `/home/simon/Dokumente/gabbro-muse/a401`, branch `muse/401`. Match confirmed before any edit.
- Owned files only: `dokumente/x86/NEXT-PROOF-WAVE.md` (new), `MUSE-REPORT-401.md` (this file). No other tree path touched; `git status` shows only these two files.

## What was done

- Read DIRECT-COMPILER.md (ledger: 27 merged x86 modules, 287 IR working, 340 working, 335/344-348 candidates pending, 349 WAITING), WORK-ALLOCATION.md (dependency graph, 16-row wave, 40/20 slot arithmetic now superseded), WELLE-A.md (history), the provisional tasks 402/404-435 and the actual `grammatik/Grammatik/X86/` tree (27 modules, 14 `Befehl` constructors, no `sorry`/`admit` tactic or new `axiom` in merged modules; the `admit` grep hits are review prose).
- Wrote the owned plan `dokumente/x86/NEXT-PROOF-WAVE.md`: 15-process permanent cap; triage of 416-435 (13 KEEP with 428 combined into 427, 1 RESCOPE, 5 DELAY); audit-routing rule for 404-415; 22 nonoverlapping next deliverables N1-N20 + R1-R2 each with owned path, existing definitions/consumer, dependency, target obligation, positive/negative JOINT witness, CUTS and paired review (proposed lanes 496-539, registry to confirm); deterministic tier/backfill scheduling; honest PID accounting (model loops only, wrappers excluded); stop conditions for count drops.

## Judgements the plan makes (for root review)

- DELAY 418/419/420 (BitScan/BitCount/ByteSwap): no native form in the 14-constructor pilot and no consumer; standalone arithmetic is exactly what the task says to deprefer. They return as ONE combined module if native forms are ever admitted.
- COMBINE 428 into 427 (one allocation-correctness module); DELAY 430/431 until consumers C5-349/C3-347 land (430 additionally high-risk: reuse certificates must never trust Rust-supplied conclusions); RESCOPE 424 to the admission predicate to avoid overlap with C3-347 and 434.
- New rows prefer closers (tearing, per-access simulation legs, CAS bounds, image coverage, jump-table certs, trap/handoff, payload residue, publication, f32 refusal, time transfer) over more arithmetic.
- Steady state under paired review is ~13 of 15; the plan forbids filling the remainder with sleeping agents or duplicates.

## Checks

- No Lean file added or modified, so no `./lean-bau` regression surface exists; umbrella `Grammatik.lean` untouched; friend files untouched. (Docs-only commit; full Lean gate applies at integration of proof lanes, not here.)
- English only. No network, no push, no credentials, no other clones touched.

## Open / possibly wrong

- Proposed lane numbers 496-539 need coordinator-registry confirmation (AGENTS.md §7: 496 next free; 464-495 already reserved for 404-435 pairs).
- If 287/340/344-348 land or fail before seeding, §4 tier 1 of the plan re-seeds first; the triage table may need a refresh.
- N8 vs C4-348 boundary (predicates vs transfer proofs) and 424 vs C3/434 boundary need reviewer care at seed time to prevent overlap drift.
- This is a plan; no jobs started, no guarantees proved, full source-to-final-byte validation remains OPEN.
