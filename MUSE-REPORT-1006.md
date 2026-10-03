CANDIDATE: 856 9908c9ede78b644894f7311cad3133cb69a63948
VERDICT: ACCEPT

Bounded acceptance: the verdict covers the VA-closing composition as stated; all wider claims stay open per its CUTS.

## Scope verified

- Clone `/home/simon/Dokumente/gabbro-muse/a1006`, branch `muse/1006`, HEAD `b040b155` equals the snapshot base. The pinned candidate head differs from base by exactly three files: `MUSE-REPORT-856.md`, `grammatik/Grammatik.lean` (one added import line, confirmed in PATCH diff), `grammatik/Grammatik/X86/ComposeVaCheck.lean` (463 lines, new file).
- No diagnostic/gift/example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files. Owned file of this lane is only this report; no source or live controls touched.

## Independent checks performed

1. Producer existence against the exact base: `adrPruefe_gleich_fuss`, `adrPruefe_ordnung_kanonisch/umbruch`, `adrPruefe_schreib_frei/verweigert`, `adrLade_basisForm_pilot` (AddressedHardwareExecution), `adrEff_basisForm`, `kanonisch48_8192`, `kanonisch48_loch` (AddressEncoding), `seitenKlasse_nicht_vorhanden/vorhanden` (ExceptionPriorityHardware), `write64_erhaelt_berechtigungen`, `read64_nach_write64`, `writeBytesN_hit`, `addrOff_null` (Speicher), `zeuge_speicher_aendert_sich` (Ausfuehrung), `basisForm`, `effAddr`, `zeugeSpeicher`, `writeBytes` all present with matching roles.
2. Definition agreement: `kanonisch48` and `istKanonisch` are textually the same predicate (`decide (a.toNat < 2^47 ∨ 2^64 - 2^47 ≤ a.toNat)`), so the `rfl` bridge is genuine, not invented.
3. Order and fault classes: `adrPruefe` checks canonical, then wrap, then permission; `vaKlasse` preserves exactly this order. Noncanonical stack references map to #SS, data to #GP, matching the SDM rule; permission failures resolve through caller-stated `seitenKlasse` (present to #GP, absent to #PF). Direction bit is correctly irrelevant to that resolution.
4. Full read of the 463-line candidate: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, no `intro _` / `have _ :=` discards (grep hits are only "admits/admitted" in comments and `#print axioms`). Every premise of every theorem is used; conclusions are derived by applying named producer lemmas, never a renamed premise; quantification is over arbitrary admitted inputs, no desired-simulation assumption.
5. Witnesses: `ComposeVaCheck_verbindung_zeuge` instantiates all four premises jointly (`rsp + 0 = 8192`, store of 42, `witVaNach`), shows the composed `adrSpeichere` execution, an observably changed byte, the no-fault class, and the accepted reached run (`zeuge_speicher_aendert_sich`: rbx 42, byte 42 at 8192, byte was 0). Non-degenerate with a memory-changing reached run. The load companion reads 42 back through the composed checked load. Planted refusals cover the hole (#GP data / #SS stack for every memory/page state), the wrap edge (ordered refusal, no fault), the dark store (`.inr .keinSchreiben`), and the dark page (#PF).
6. Wrap-edge mapping (`umbruch` to `none`) is a validator refusal, never a hardware claim, and CUTS states explicitly that silicon behaviour there is undecided. Mapped status stays caller-stated per the lane-738 interface; no paging-structure truth is inferred from refusal. No invented determinism, no ignored defined effects.
7. CUTS names every missing producer leg with owners (decoder length soundness lane 279; wider execution integer666/locked662/FP668 consumers) and disclaims hardware correspondence, TSO/GX, source/ABI/loader/entry/budget/cost, and full source-to-byte validation. Claim boundary is precise.
8. Build evidence in the snapshot: final `./lean-probe` 0 errors, axioms subset of standard (`[propext]` / `[propext, Quot.sound]`), `./lean-bau` 511 jobs green. Own base check just run: `./lean-bau` on `b040b155` ends `Build completed successfully (510 jobs)` — consistent (candidate adds exactly one file).

## What remains open (not a repair)

Nothing in this candidate needs repair. The open items are the candidate's own stated CUTS (paging-structure truth, wrap-edge silicon class, TSO/GX bridge, source correspondence), which belong to other lanes.

## Notes on the task

- The ZEUGE companion `ComposeVaCheck_verbindung_zeuge` is present under the exact required name; the extra load companion is suffixed `_zeige`, so no gate collision.
- The duplicate `kanonisch48`/`istKanonisch` predicates are a real cleanup opportunity but unifying them is correctly left out of this lane.
