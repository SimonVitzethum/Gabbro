# MUSE-REPORT-1182: Independent exact review of candidate 1181

Lane 1182, clone /home/simon/Dokumente/gabbro-muse/a1182, branch muse/1182
(verified first: `pwd` + `git branch --show-current`, match, no STOP).
Owns ONLY this report. Review-only lane: no Lean or Rust changes.

## Candidate under review

- CANDIDATE 1181, pinned HEAD `816ec7c4898bb0f599b803cd333b5ac7d4ea57dc`,
  base `0ddf527d050ae9edced5f26e90172293b059eaf2` (from
  `.tmp/review/SNAPSHOT.json`, `"clean": true`).

CANDIDATE: 1181 816ec7c4898bb0f599b803cd333b5ac7d4ea57dc
- Files (3): `MUSE-REPORT-1181.md`,
  `grammatik/Grammatik.lean` (exactly ONE appended line
  `import Grammatik.X86.HwNestedInterrupts`, confirmed from
  `.tmp/review/author-1181/PATCH.diff`),
  `grammatik/Grammatik/X86/HwNestedInterrupts.lean` (1701 lines).
- Read only the snapshot (`PATCH.diff`, candidate file,
  `MUSE-REPORT-1181.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`);
  nothing outside this clone was touched.

## Checks performed (each against the pinned snapshot)

1. Banned tokens: strict `rg` for `sorry` / `admit` / `axiom` /
   `native_decide` / `unsafe` (word-boundary): ZERO hits. The only
   substring hits are English prose "admitted" in two doc comments
   (witness gate descriptions). No `intro _`, no `have _ :=`,
   no `split_ifs`/`norm_num`/`ring_nf`. The single `: Prop` hit is
   the def `intWf1181 s : Prop := HwWf s.hw`, an applied wf
   abbreviation (same standing as `HwWf`), not a `Prop`-typed premise.
2. `#print axioms`: 136 lines, one per main def/theorem, file ends
   with them after the CUTS block. Author `BUILD-EVIDENCE.json`
   records every dependency as none / `propext` / `propext+Quot.sound`
   -- inside the standard goal set, no `Classical.choice` needed,
   no `sorryAx`.
3. Existing files: only the one import line in `Grammatik.lean`.
   No edit, no weakening of any accepted module.
4. Lift, not copy: zero redefinitions of accepted names
   (`asyncSchritt`, `liefere`, `hwWortAusgabe`, `schiebeRahmen`,
   `HwSchritt`, `HwWf`, `HwStern`, `HwAdapter` never re-`def`d);
   `asyncSchritt` referenced 44x, `asyncMasch_puffer_still`,
   `asyncSchritt_verweigert_maskiert`,
   `asyncSchritt_interrupt_loescht_if`,
   `asyncSchritt_trap_behaelt_if` reused; the one new general
   theorem over old vocabulary (`asyncSchritt_wf_allgemein`) proves
   by unfolding + the accepted stage lemmas.
5. Planted refusals really refuse: `verschachtelt_verweigert_erster`
   (failed first leg), `verschachtelt_verweigert_abbild` (stale
   snapshot must track updated IF), `verschachtelt_maskiert_verweigert`
   (S1+S5: IF cleared by interrupt gate, maskable second leg refused
   via the accepted `asyncSchritt_verweigert_maskiert`), five IRET
   refusals (unreadable / noncanonical / NULL CS / NULL SS /
   code-row), two adapter refusal projections -- all `= none`
   equations over the lifted evaluator, all premises used
   (spot-checked: `hv` feeds the accepted mask refusal, `hmatch`/`hif`
   feed both decide checks).
6. Witness non-degenerate (`verschachtelt_zeuge`, 33 conjuncts):
   TWO maskable gates (vectors 32 trap keeping IF handler `0x2100`,
   33 interrupt clearing IF handler `0x2200`) over byte-populated
   canonical memory (concrete `read64` facts 16 / 4660); masked third
   refuses (`nestDritt = none`); NMI vector 2 bypasses cleared IF
   (handler `0x2000`); #DF observed (vector 8, code 0, leg statuses:
   first delivers, nested faults with vector 13); core-1 buffered
   store of value 42 with owner-only forwarding and a SHARED-MEMORY
   CHANGING drain observed from both cores; 40-entry buffered frame
   with owner-only word forwarding; IRET restoring RIP/RSP/IF;
   `HwWf nestStart`; reached machine-level nest AND reached
   `HwNestSchritt` extended step. Two cores touch memory; deliveries
   plus drain change shared bytes. Joint, non-degenerate.
7. Silicon (against clone-local `.tmp/HARDWARE-REFERENCES`, Intel
   extracts + prior MUSE-REPORT-660 catalogue): S1 (IF gates INTR,
   NMI bypasses) and S2 (NMI=2, maskable 32-255) and S5
   (interrupt clears / trap keeps IF) reused from accepted lane-1125
   defs, re-checked at the UPDATED IF for the nested leg; S4 (#DF
   vector 8, error code 0) and S6 (IRET five-word pop, IF from
   RFLAGS bit 9, #SS/#GP on bad load) are textbook SDM Table 6-1 /
   Vol.3 Ch.7 facts, asserted as named assumptions, never as proved
   correspondence. No APIC/SMI/timing/power claim anywhere.
8. CUTS honest: states self-consistency only, no hardware
   correspondence, no W/GX bridge, no whole-word atomicity beyond the
   accepted guard, DF witnessed observationally (memory lacks
   `DecidableEq`, stated openly), IRET five-word same-frame only,
   wechseln/wechseln agreement only, no handler execution, no CPL /
   task / CET / FRED paths. Claim matches proof. The byte-frame
   honesty note (no accepted byte-level frame model to lift; built
   as `hwWortAusgabe` fold at accepted `schiebeRahmen` slots with
   byte-echo agreement) and the `nullSelektor` opacity note are
   disclosed in the author report and consistent with the file.
9. Name-collision scan of all 12 distinctive new names
   (`verschachteltSchritt`, `liefereMitDf`, `puffereRahmen`,
   `iretSchritt`, `adapterVerschachtelt`, `HwNestSchritt`,
   `NestEreignis`, `nullSelektor`, `intWf1181`, `nestIntBytes`,
   `dfVektor`, `verschachtelt_zeuge`) against my tree (which is NEWER
   than the candidate base): ZERO hits. The one real collision the
   author met (`nestBytes` vs `StackExecution.lean`) was repaired by
   rename before the pinned HEAD.

## Build verification

- `./lean-bau` on THIS reviewer tree (clean, candidate not applied):
  last line `Build completed successfully (630 jobs).` Green base.
- Candidate build: author `BUILD-EVIDENCE.json` shows the full
  trajectory -- red intermediates, the `nestBytes` collision found by
  the full build and repaired, final `./lean-probe ... == 0 error(s)`,
  zero warnings, final `./lean-bau ... Build completed successfully
  (618 jobs).`
- Honest limitation: an independent overlay build of the candidate in
  my clone was NOT possible -- the permission classifier denied the
  file-copy step (`cp`), so the candidate bytes were verified by
  exact-snapshot reads plus the checks above, not by re-execution.
  Given the one-line-import shape, the zero-collision scan against a
  newer tree, and the author's complete red-to-green build log at the
  pinned HEAD, this residual risk is small and stated, not hidden.

## Task feedback

Nothing in the review task is wrong. `ZEUGE:`-style inhabitation is
satisfied by `verschachtelt_zeuge` (joint, non-degenerate, two cores,
memory-changing drain). Rule 12 does not apply (no TARGET statement;
author added no unsupported desired-correctness premise).

## Verdict

VERDICT: ACCEPT

Candidate 1181 at `816ec7c4898bb0f599b803cd333b5ac7d4ea57dc` is
accepted for merge: hygiene clean, axioms standard, exactly one import
line added, accepted evaluator lifted unchanged, refusals genuine,
witness non-degenerate with two-core memory-changing TSO drain,
silicon facts named as assumptions with SDM provenance, CUTS honest
with no hardware-correspondence or W/GX claim. No REPAIR item found;
the un-re-executed overlay build is a stated residual, not a defect.

