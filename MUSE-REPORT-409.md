# MUSE-REPORT-409: Adversarial implementation audit INVARIANT-LIFETIME

Clone: `/home/simon/Dokumente/gabbro-muse/a409`, branch `muse/409` —
verified (`git rev-parse --show-toplevel`, `git branch --show-current`).
No prior lane work existed (no audit file, no report, empty diff vs
master); the two `.tmp/probe409_*.lean` files were present and were
reused as the reproduced probes below.

## What was done

Read `grammatik/Grammatik/X86/InvariantenOpt.lean` (550 lines) and
`grammatik/Grammatik/X86/AufrufOpt.lean` (288 lines) in full against
the actual goal-leg definitions (`Zielsatz/Spec.lean` 1915-2000,
2157-2230) and the OPTIMIZER.md consumer rows. Ran a no-consumer grep
over `grammatik/` + `bruecke/` (single hit: umbrella imports in
`Grammatik.lean` 383/387 — no in-tree consumer of any helper).
Reproduced two Lean probes, both green:

- `.tmp/probe409_a.lean` — positive: `isWahr wCond = true` by `rfl`;
  ghost-pair length 2 on the value channel. `./lean-probe`: 0 errors.
- `.tmp/probe409_b.lean` — negative: `isWahrAll (.nicht .wahr) =
  false` by `rfl` (negation correctly has no arm); `#check`
  `@slot_read_stabil` / `@exec_pruefung_inv` exhibiting the exact
  assumed premises. `./lean-probe`: 0 errors.

Wrote the owned deliverable
`dokumente/x86/AUDIT-INVARIANT-LIFETIME.md` (Vd/V1-V8 verdicts,
F1-F9 findings, R1-R6 prioritised repairs, claim ledger, CUTS).

## Exact names

New definitions/theorems: none (docs-only audit; no Lean file added
or changed). Audited existing names: `isWahrAll`, `isWahrAll_sound`,
`alsLitOpt_lit`, `eval_alsLit`, `litLeBool_sound`, `litEqBool_sound`,
`foldAddLit`, `eval_foldAddLit`, `eval_weiter_n`,
`exec_pruefung_wahr`, `exec_ite_wahr`, `InvScope`,
`exec_pruefung_inv`, `slot_read_stabil`, `GeistAntwort`, `geistPaar`,
`geistPaar_laenge`, `geistRekon_folge`, `geistRekon_folge_grund`,
`rufSchrittG_logSchritt`, `InlinePflicht`, `rufAt_ok_vorOk`,
`geistRekon_zeuge`, plus witnesses `wit_*` / `*_zeuge`.

## Build result

No `./lean-bau` run: the commit touches only
`dokumente/x86/AUDIT-INVARIANT-LIFETIME.md` and this report, so the
Lean build state is unchanged. `./lean-probe` on both `.tmp` probe
files: `0 error(s)`, exit 0.

## What remains open

The six prioritised consumer-side tasks R1-R6 in the audit (P0:
scope-discharge rule linking `InvScope` tags to the actual goal
legs; P1: carrier-refusal enforcement, invalidation lemmas, inline
return-duty + armed-condition discharge; P2: effect exports, OPEN
markings). No follow-up Lean work belongs to this lane.

## Task feedback

Nothing in the task was found to be wrong. One scoping note: the
task's phrase "source invariant evidence at holder/quiescent/entry/
exit" could be misread as expecting such evidence to exist — the
audit's central result is that neither module contains any invariant
facts (only an assumed truth hypothesis plus a proof-irrelevant
scope tag), with the bridged fragment additionally vacuous
(`S = leer`, cf. REVIEW-QUELLE-INVARIANTEN §5). This is recorded as
a legitimate incompleteness with named bridge tasks, not as a defect
in the proved transfer lemmas.
