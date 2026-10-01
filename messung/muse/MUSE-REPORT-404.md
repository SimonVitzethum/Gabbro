# Muse report 404: adversarial audit ARITHMETIC-FLAGS

## What was done

Wrote the owned audit `dokumente/x86/AUDIT-ARITHMETIC-FLAGS.md` (only owned
file besides this report). Read the accepted modules `Wort`, `Ganzzahl`,
`FlagBeweis`, `StaerkeReduktion` in full, plus wired consumers/extensions
`Ausfuehrung` (`schritt`), `MulDiv`, `ShiftLogic` and the source arithmetic
definitions (`Typen.lean` `Zahl` ops, `Syntax.lean` `Expr`). Checked consumer
wiring with a tree-wide grep and reproduced every probe mechanically.

## Findings (see audit §§2–4 for evidence)

Sound within stated claim: CF/OF independence, OF-iff-range (`add64_of_iff` /
`sub64_of_iff`), unsigned/signed MUL carry split, two-sided division refusal
causes, signed-reduction refusals with `-3` value, all reduction premises used,
undefined-flags-never-false discipline, width-correct `negB` sign.

New actionable findings: **F1** (latent unsoundness) the shift `ohne_eins`
snapshots apply at masked-zero counts although the file claims no snapshot
there — `∃ f, SchiebeGueltig .b64 (shlNachweis .b64 1 64) 64 f ∧ f.cf = false`
while `schiebeZaehler .b64 64 = 0`; **F4** the two shift models diverge —
`shlB .b64 1 64 = 1` vs `shlW 1 64 = 0`. Missing bridges: **F2** no
source-to-target arithmetic lowering (source total, target wraps/traps;
`passtU/S` unconnected; no add/sub lowering; fault introduction and fault
order open), **F3** flag liveness/definedness untracked across MUL/DIV
preservation into `bedingung` reads, **F5** dividend construction unlinked
(`divU/divS` vs `divWeitU/S`), **F6** narrow ADD/SUB flags absent plus a
`LogikGueltig`-is-64-bit-only trap, **F7** a `passtU` name collision. Priority
order P1–P5 in the audit.

## New definitions/theorems

None. Docs-only lane: no Lean, Rust, checker, emitter, goal or ledger file
was created or modified. Experimental probes stayed private in `.tmp/`
(gitignored, not committed): `.tmp/probe404.lean` (pre-existing) and
`.tmp/probe404b.lean` (F1/F4 exhibits, this lane).

## Check results

- `./lean-probe .tmp/probe404.lean`: **0 error(s), exit 0**.
- `./lean-probe .tmp/probe404b.lean`: **0 error(s), exit 0**.
- `./lean-bau` was not re-run: no build input changed (docs-only diff), so
  master build state is unaffected. `gabbro_ziel` axioms untouched.

## Open / not claimed

Everything in audit §§4–5 and §7 (CUTS): the P1–P5 repairs and bridge tasks
belong to the shift/lowering/ControlFlow owners, not to this audit. Silicon
behaviour is audited as stated semantics, not verified against hardware.

## Task remarks

Nothing in the task was wrong. The "do not invent a bug because an explicitly
OPEN bridge is OPEN" instruction was honoured: F2/F3/F5/F6 are recorded as
missing bridges with the exact refusal shapes the discharge must meet, and
only F1 is called an unsoundness (proved snapshot contradicts the file's own
"no snapshot claimed" sentence). The 15-process limit and no-network / no-push
rules were observed; this commit stays on branch `muse/404`.
