# MUSE-REPORT-1000: Exact review of author 850 (handler-table closing)

## Candidate and verdict

CANDIDATE: 850 43392858a3fc395dfc76942bacbe650a4313fe39
VERDICT: ACCEPT

Pinned base b040b155159f47629542b0083e2f0a8a607f2b4c; files MUSE-REPORT-850.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/ComposeHandlerTable.lean. The acceptance above is bounded as stated under Bounded acceptance.

Clone/branch verified: /home/simon/Dokumente/gabbro-muse/a1000 on refs/heads/muse/1000; base matches the candidate base. Owns only this report; no source or live controls touched.

## What was reviewed

Full PATCH.diff (476 lines, new file ComposeHandlerTable.lean + one import line), OWNER-TASK.md, MUSE-REPORT-850.md, BUILD-EVIDENCE.json, and the accepted producer grammatik/Grammatik/X86/InterruptDescriptorHardware.lean (lane 728) in this clone at the candidate base. Reference scope: local Intel SDM edition 093 record (.tmp/HARDWARE-REFERENCES/REFERENCES.json); no AMD provenance claimed or needed.

## Architecture findings

1. Byte forms: the composition decodes nothing itself; gate bytes come from actual canonical IDT memory via accepted liesTorBytes at torAdresse, parsed by accepted pruefeTor. No duplicate decoder.
2. Binding: handlerEintritt checks the declared table first (undeclared vectors refuse before any byte is read), then reads gate bytes, runs the accepted gate check, checks g.offset == declared RIP, and delivers through accepted liefere called with { q with tor := t } — the same bytes that were checked, so no check/delivery TOCTOU.
3. Flag semantics: IF propagation (if unterbrechung then false else s.ifBit) is taken verbatim from the accepted liefere_zugestellt legs, not reinvented; the witness interrupt gate clears IF, matching SDM Vol.3 interrupt-gate behavior.
4. Memory order/effects: delivery memory comes from the accepted liefere equation; the composition adds no memory model. Failure legs produce no memory (refusal only).
5. Producer-name reuse verified by grep in this clone: torAdresse, liesTorBytes, pruefeTor, waehleStapel, liefere, torFehlerCode, witMem, witMemDunkel, idtWitSteuer, witAnfrage, loWit, wit_rahmen_ss, wit_rahmen_rip, wit_rahmen_aendert, ergebnisSpeicher, liefere_zugestellt_wechsel/behalten all exist with matching signatures. rahmenWorte ignores q.tor (line 653), so rahmenWorte_mit_tor by rfl is legitimate. witGate literal matches the producer wit_bereit gate exactly; witness addresses check out (IST1 0x4000 = 16384; five-word frame 16376..16344; SS=16, RIP=4660).
6. Premise use: every hypothesis of every theorem is used in its proof (checked by reading each proof). No conclusion restates a premise; no contract quantification; no discarded premises; no Prop-sorted premises.
7. Witness: ComposeHandlerTable_verbindung_zeuge instantiates all success premises jointly by decide on the byte-populated IDT/TSS images, with a reached memory-changing run (two frame cells read back, two bytes-inequalities) plus three planted refusals (undeclared, renamed handler, dark stack). Non-degenerate. Rule-13 syntax clause does not trigger (quantification is over X86 machine values only), consistent with the ComposeImageFetch precedent.
8. Forbidden tokens: none in the patch (no sorry/admit/axiom/native_decide/unsafe) — verified by reading the complete file text.
9. Scope hygiene: no diagnostic/gift/example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files. CUTS block is precise (codeOk as explicit input, no async completion, no handler fetch past delivery, no 256-vector table, no source lowering, no silicon claims; unreadable-half conflation into unlesbar documented against the producer's vocabulary).

## Build evidence

BUILD-EVIDENCE.json records the full trajectory: two intermediate failures (an unsolved-goal simp normal-form issue and a rewrite-pattern mismatch, both repaired honestly in-file) and final `./lean-probe == 0 error(s)` plus `./lean-bau Build completed successfully (511 jobs)` with `#print axioms` standard ([propext, Classical.choice, Quot.sound] for the main theorems, inherited). No rebuild was run in this review clone: the candidate file is not present here, this lane owns no source, and nothing found above warranted reproduction; the decide-checked facts were additionally verified by reading the producer definitions they compute against.

## Bounded acceptance

Acceptance covers: faithful thin composition over the accepted producer, generic switched-stack and kept-stack success closings with producer agreement, four refusal directions, and the joint non-degenerate witness. Explicitly NOT covered (per the file CUTS, accepted as open, not as proved): kept-stack witness instance, planted unlesbar instance, GDT/code-row ownership, async/nested/#DF/TSO behavior, fetch past delivery, full table, source lowering, hardware claims.

## Remaining open / believed-wrong

Nothing believed wrong in the owner task or the candidate. Open work is the CUTS list above, owned by the named lanes (672/708, concurrency lanes, IR lane 287).

## Lean build result

No new Lean work in this lane (report-only review); `./lean-bau` last result: not run here — see build-evidence paragraph. New definitions/theorems added by this lane: none.
