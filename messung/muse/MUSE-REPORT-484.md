# Muse report 484: independent exact-candidate review of 404

## What was done

Independently reviewed candidate 404 (pinned HEAD `0fb32748750340603b3e3e0030c7879bc2dfdc96`,
base `0b3132b7`, per `.tmp/review/SNAPSHOT.json`) against the owner task
(adversarial audit ARITHMETIC-FLAGS), the supplied `PATCH.diff`, the supplied
`dokumente/x86/AUDIT-ARITHMETIC-FLAGS.md` + `MUSE-REPORT-404.md`, and the actual
accepted models in this clone (`grammatik/Grammatik/X86/{Wort,Ganzzahl,FlagBeweis,
ShiftLogic,StaerkeReduktion,MulDiv}.lean`, `Wort.lean`, `SperreBeweis.lean`).

Integrity: the PATCH `+` lines split exactly into the two supplied files
(314 lines total; head == report, tail == audit, verified mechanically).
SNAPSHOT lists exactly those two files, `clean: true`. Docs-only: no Lean,
Rust, checker, emitter, goal, ledger, or friend-owned file touched.

Reproduced the load-bearing exhibits with `./lean-probe` on a private
`.tmp` probe (deleted afterwards): `schiebeZaehler .b64 64 = 0`,
`schiebeZaehler .b64 64 ≠ 1`, `shlUeberlauf .b64 1 64 = none`,
`shlB .b64 1 64 = 1`, `shlW 1 64 = 0`, `shlB .b64 1 64 ≠ shlW 1 64` —
**0 error(s), exit 0**.

## Findings

- **F1 is genuine** (doc-vs-code contradiction, correctly called latent, not
  active): `ShiftLogic.lean:84-86` and `:203-204` promise the §2 snapshots are
  the nonzero-count profile with no snapshot at masked-zero counts, but
  `shlNachweis_ohne_eins` / `shrNachweis_ohne_eins` / `sarNachweis_ohne_eins`
  (`:149-153,171-175,193-197`) require only `schiebeZaehler b c ≠ 1`, which a
  masked-zero count (`64 % 64 = 0`, reproduced) satisfies; via
  `schiebe_gueltig_existenz` (`Ganzzahl.lean:395-404`) a `CF = false` snapshot
  is handed out where hardware preserves flags. Repair direction (restrict to
  `≠ 0` or add the promised zero-count preservation shape) is sound and
  correctly assigned to the shift/lowering owner.
- **F4 is genuine**: masked `shlB` vs saturating `shlW` diverge at count 64
  (reproduced). Recorded as a clarify/canonicalize task with an agreement-lemma
  shape, not as a soundness hole — fair.
- **F2/F3/F5/F6/F7 accurately recorded as missing bridges or traps**, with
  correct file anchors spot-verified: MUL/DIV flag preservation as explicit
  modelling choice (`MulDiv.lean:130-141,227-259,539-541`); `LogikGueltig`
  64-bit-only trap real (`sfTest` reads bit 63, `Wort.lean:78`); `passtU` name
  collision real (`SperreBeweis.passtU_leer/append` vs `Ganzzahl.passtU`);
  `divS_verweigerung_ursache`, `divWeitS_verweigert_bei_*`,
  `probe_mul_trag_vorzeichen`, `sdiv_kein_shift`, `bedingung` (`Wort.lean:151-167`)
  all exist as cited. The "no consumer yet" rows are fair (no external
  lowering/ControlFlow consumer; internal lemma-to-lemma use inside
  `FlagBeweis.lean:247-291` proves the transfers, it does not consume them
  downstream — at most a nit, not a defect).
- **No overclaim**: "review evidence, not a proof", full validation stays OPEN,
  CUTS §7 present, line-drift disclaimer present, silicon audited as stated
  semantics. The OPEN-bridge instruction was honoured: only F1 is called an
  unsoundness; the rest are missing-bridge obligations with refusal shapes.
- **No vacuity, forgery, or safety weakening**: no new theorems (no `_zeuge`
  obligation — docs-only), no `sorry`/`axiom`/`native_decide` surface (no code
  at all), no benchmark/axiom evidence claimed, `lean-bau` correctly not
  re-run for a docs-only diff, guarantees untouched.
- English only; owned-file discipline kept (audit + report only).

## New definitions/theorems

None. Review-only lane; no code written or modified.

## Check results

- `./lean-probe .tmp/probe484-check.lean` (private, since deleted): **0 error(s), exit 0**.
- `./lean-bau` not re-run: neither the candidate nor this branch changes any build input.

## Open / not claimed

Merging the audit is a docs merge; the P1–P5 repairs stay with the
shift/lowering/ControlFlow owners. Candidate commit object itself is not
fetchable in this offline clone, but PATCH↔supplied-files equality was verified
byte-for-byte, so the reviewed content is exactly the pinned candidate diff.

## Task remarks

Nothing in the owner task was wrong; the candidate fulfils it precisely.

CANDIDATE: 404 0fb32748750340603b3e3e0030c7879bc2dfdc96
VERDICT: ACCEPT
