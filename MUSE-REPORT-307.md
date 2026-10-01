# MUSE-REPORT-307: Independent review of candidate 291 (X86/Relokation.lean)

Lane 307, independent candidate review. Reviewed ONLY the pinned snapshot
`.tmp/review/author-291/` (SNAPSHOT.json: author 291, HEAD
`9730427b5f0c61187dd60bcda3e11baca8d33aa5`, base
`f49581505cda367b97d4f3d89faa1b2f33413497`, clean true) and its
BUILD-EVIDENCE.json tool log (34 entries, through the repair commit).
No other clone read, no code or central file edited. This report is the
only owned deliverable.

This is a RE-REVIEW: a first verdict (ACCEPT) was given on the previous
snapshot HEAD `4d1e4f6d5f2a42dbcf6da37f181cb704e6177993`. That verdict is
stale. The author repaired an integration-gate failure (name collision,
see below) in commit `9730427b`. Every previous finding was re-inspected
against the NEW snapshot; only §0 changed, all other sections verified
unchanged (identical declaration names, each shifted by exactly -6 lines).

Owner task (OWNER-TASK.md): `grammatik/Grammatik/X86/Relokation.lean` —
canonical address-relative rel32 calculation (target minus actual next-RIP),
signed-32 fit/refusal with generic sign-extension target equation under exact
no-wrap/address premises, abs64 values, finite `List Byte` operand/data-field
patching with range/disjoint checks, exact patched bytes + outside-site
preservation, concrete negative/boundary/out-of-range/overlap refusal
witnesses. Reuse canonical Byte/Wort, wortByte, address arithmetic; no second
model. Code-operand vs data-site admissibility belongs to the checked
image+decoder proof; caller-claimed starts/kinds untrusted. Helper
arithmetic/patching green but complete relocation acceptance explicitly
OPEN/refused. No loader/linker assumption, no final-byte source claim.

## What was checked

- Read the full NEW snapshot file (669 lines, was 675): all definitions,
  theorem statements AND proofs, CUTS block, `#print axioms` lines.
- Read the updated MUSE-REPORT-291.md (114 lines, new § "Repair after
  failed integration gate") and PATCH.diff (same 3 files: report, one
  additive `import Grammatik.X86.Relokation` in `grammatik/Grammatik.lean`,
  the file). No Rust, no diagnostic/gift/example/CLI/MARKE numbers.
- Read BUILD-EVIDENCE.json end to end (34 entries): post-repair
  `./lean-probe` 0 errors, post-repair `./lean-bau` exit 0 / 0 errors,
  then commit `9730427b Lane 291 repair: drop duplicate RelArt, keep OPEN
  marker` — matching the NEW snapshot HEAD. Diff stat of the repair:
  Relokation.lean 30 changed lines, report +28. (The quoted merge-gate
  failure line itself is not in the tool log, so the collision was
  verified independently against source instead — see next point.)
- Collision independently confirmed: this clone's
  `grammatik/Grammatik/X86/Bild.lean` line 49 owns
  `Gabbro.Grammatik.X86.RelArt` with the IDENTICAL constructor names
  `codeOperand`/`datenFeld` the deleted helper inductive had. The gate
  failure was real, and deleting the duplicate is the correct minimal fix.
- Ran `./lean-probe .tmp/review/author-291/grammatik/Grammatik/X86/Relokation.lean`
  independently on the NEW snapshot: first line
  `== 0 error(s) in the COMPLETE output`, axiom lines identical to the
  author's (every theorem: no axioms or subset of `[propext, Quot.sound]`;
  no `Classical.choice`; `relAnnahme_offen` now depends on no axioms).
- Token-precise grep for forbidden tactics
  (`sorry|admit|axiom|native_decide|unsafe`): zero hits — remaining
  substring matches are English prose ("admits a site") and `#print
  axioms` lines. No `Prop`-typed premise, no `intro _` / `have _ :=`,
  no N-codes, MARKE, example or name-specific rules anywhere.
- Name-overlap sweep (discharges the author's stated residual risk for the
  current tree): every introduced name (`relAnnahmeEndgueltig`,
  `relAnnahme_offen`, `tcNat`, all `rel32*`, `abs64*`, `patch*`,
  `disjunktStellen`, all 14 `sonde_*`) grepped as declarations over this
  clone's whole `grammatik/` (which already contains `Bild.lean`) — zero
  collisions. No `inductive` declaration remains in the candidate.
- Verified canonical reuse against this clone's sources: `wortByte`/
  `bytesWort`/`bytesWort_wortByte` are `Speicher.lean` (lines 18/36/309),
  `sext` is `Wort.lean` (line 60). Imports are exactly
  `Typen`/`Speicher`/`Wort` — no new dependency on `Bild.lean`. No second
  image/register/ISA model.

## Claim-by-claim cross-check (all hold on the NEW snapshot)

- Site admissibility (CHANGED by the repair): the local `RelArt`
  inductive is deleted; the OPEN marker is now the Bool flag
  `relAnnahmeEndgueltig : Bool := false` with
  `relAnnahme_offen : relAnnahmeEndgueltig = false := by rfl`. Same
  documented meaning (doc comment + CUTS still name the two classes and
  assign them to the image+decoder proof), no parallel type, no weakened
  guarantee: helper-level acceptance still refuses every site. This is a
  strict improvement — one vocabulary owner (`Bild.lean`) instead of two.
  Not a restated premise (no premises at all).
- rel32: `rel32Passt` exact signed-32 bounds; `rel32_rundgang` generic
  over all in-range `d`, both premises load-bearing in the `omega` closes.
  Unchanged (line shift only).
- Address equations: `rel32_adress_gleichung` needs no wrap premises
  (modular `ofNat` addition is wrap-consistent; author documents this as a
  finding after the linter caught dead premises — credible). Exact no-wrap
  premises live only in `rel32_next_rip`, each used by the rewrite.
  `rel32Fuer` refuses out-of-range with `none` (`rel32Fuer_verweigert`);
  in-range hits decode back (`rel32Fuer_trifft` via the generic round-trip).
- abs64: `abs64Bytes` via `wortByte`, `abs64Wort` via `bytesWort` (wrong
  width `none`), `abs64_rundgang` is exactly `bytesWort_wortByte` — no
  second codec, as claimed.
- Patching: `patchAt` refuses overrun including empty-patch-past-end;
  `patchAt_bereich`/`_laenge`/`_stelle`/`_rahmen` all present and generic.
  `patchZwei` refuses overlap on lengths of the actual patch lists (no
  caller-claimed register), `patchZwei_erhaelt_erste` keeps the first site.
  `patchRel32`/`patchAbs64` corollaries + width facts (4/8) present.
- Probes recomputed by hand: -5 = `FB FF FF FF` LE correct; boundaries
  `2^31-1`/`-2^31` fit with exact bytes, `±2^31` refused; `rel32Fuer 0
  2^31 = none`, `rel32Fuer 10 0 = some (rel32Bytes (-10))` correct;
  `0x1005 -> 0x1000` address equation and next-RIP probe correct;
  abs64 `0x0102030405060708` LE bytes correct; overlap `[1,2)` vs `[2,2)`
  refused, disjoint sites exact, 2-byte patch at offset 2 of 3-byte image
  refused. `sonde_abs64_rund` is an instance of the generic theorem, not
  just `decide` — stronger than required.
- Boundaries: no source/target/cost/TSO/hardware claim is made; CUTS
  lists site admissibility, loader/linker, load bias, entry states,
  per-instruction correspondence, control-target, ABI, concurrency and
  cost as OPEN/separate. Matches the owner task's explicit OPEN/refused
  requirement. No final-byte source claim anywhere.
- Inhabitation: no premise quantifies over program syntax and the task
  names no `ZEUGE:` target, so no `_zeuge` is owed; the §6 probes are real
  operand/byte values over the actual helpers, as the owner task requires
  for target helpers.

## Notes (not defects, no action required)

- `rel32Byte` maps every index >= 3 to the top byte, but it is only ever
  called with 0..3 via `rel32Bytes`. Unreachable through the delivered API.
- Only the first site's survival is stated for double patches; the second
  follows directly from `patchAt_stelle` + the second patch hypothesis.
- `#print axioms` covers the 18 main theorems; the remaining `decide`
  probes print nothing, which is fine.

No counterexample reproduced because no finding was made; every probe value
above was hand-verified correct against two's-complement/little-endian arithmetic.

## Verdict

The bounded delivered claim — checked relocation arithmetic and byte
patching helpers with generic round-trip/range/frame/disjointness theorems,
concrete probes, and complete relocation acceptance explicitly OPEN — is
true on the NEW snapshot. The repair removes the evidenced `RelArt`
duplicate (collision with `Bild.lean` confirmed in source), changes nothing
else (declaration inventory identical minus the inductive, -6 lines), and
re-verifies green (independent `./lean-probe`: 0 errors, standard axioms;
author `./lean-bau`: exit 0). Proof/witness gates hold, no material defect
remains. ACCEPT does not mean whole-compiler or binary validation is
complete; the file itself states that boundary.

CANDIDATE: 291 9730427b5f0c61187dd60bcda3e11baca8d33aa5
VERDICT: ACCEPT
