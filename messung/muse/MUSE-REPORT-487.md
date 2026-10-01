# MUSE-REPORT-487

*Lane 487 — Independent exact-candidate review of 407 (adversarial audit FINAL-IMAGE).*

## What was done

- Verified clone `/home/simon/Dokumente/gabbro-muse/a487`, branch `muse/487`; clean tree, no other files touched. Own only this report.
- Read exact review inputs: `.tmp/review/SNAPSHOT.json` (author 407, head `8df52d64cdb350c481d1929549ee0bc071b0c676`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-407.md` + `dokumente/x86/AUDIT-FINAL-IMAGE.md`, clean true), `.tmp/review/author-407/OWNER-TASK.md`, `MUSE-REPORT-407.md`, `BUILD-EVIDENCE.json`, `PATCH.diff` (exactly 2 new files, no other paths), and the full supplied `dokumente/x86/AUDIT-FINAL-IMAGE.md` (508 lines).
- Independently checked material claims against accepted sources in this clone: `grammatik/Grammatik/X86/Bild.lean` (578 lines), `Relokation.lean` (669), `Byteschritt.lean` (510), `dokumente/x86/IMAGE-ABI.md` (675) — line counts match the audit header exactly. Spot-verified every load-bearing citation: `relokOk` virtual-site bound `siteOff < s.memLen` (Bild.lean 240–251) vs `patchAt` file-list range (`patchAt_bereich` 234–235); `eintragEnthalten`/`zielInCode` containment-only (226–231); `wxOk` W^X-only (222–223); `modusOk` param-alignment-only (255–257); `geladen` pure function (192–196) vs hand-built `ketteSpeicher` (Byteschritt 313–317, never `geladen`); `relAnnahmeEndgueltig = false` + `relAnnahme_offen` (Relokation 28–32); re-decode OPEN on both sides (Bild CUTS 531–537, Relokation CUTS 635–639, `patchAt` doc 222–226); loader contract unwitnessed (Bild CUTS 542–544); decoder length-soundness OPEN (Byteschritt CUTS 477–484); IMAGE-ABI secs. 3/4/5–6/11 demands (re-decode, decoded starts, page granularity/shared page, loader obligations, permission schema) present as cited.
- Confirmed F3's concrete parenthetical by inspection: `zeugenCode` is `[0x1000,0x1004)` with entry `[0x1000]`, so `0x1001` satisfies containment — the gap illustration is true, and correctly framed as validator-completeness gap, not unsound theorem.
- Checked review red flags: no Lean/Rust/checker/emitter/goal/ledger change (PATCH = 2 prose `.md` only, no forbidden `OptimizationRules`/`OptimizationWitnesses` touch); no new IR/executor/semantics; no safety weakening; no closure claim (verdict states couplings do not exist, validation remains OPEN; OPEN bridges recorded as OPEN); no forged evidence — sec. 6 and the 407 report honestly disclose probes were read/verified by eye, not re-executed (execution tool unavailable; only wrapper `cat` in evidence, no fake green claimed); no `sorry`/`axiom`/`native_decide` (no Lean added); scope matches OWNER-TASK owned files.
- BUILD-EVIDENCE supports the pinned commit: final entry shows commit `8df52d64` with message and both files staged/committed, prior entries show only the two untracked `.md` files. The candidate object itself is not resolvable in this isolated clone (expected), but snapshot head, evidence commit hash, file list and PATCH content are mutually consistent.

## Exact names of new definitions/theorems

None. Docs-only audit (candidate) and docs-only review (this lane). No Lean definition, theorem, witness, diagnostic code, gift probe or example added or modified.

## Last `./lean-bau` result line

Not executed, deliberately: neither the candidate (2 prose `.md` files) nor this lane (this report only) changes any `*.lean` or `*.rs` file, so no Lean/Rust regression is possible. Full `./lean-bau` plus `gabbro_ziel` axiom check remain integration-side, consistent with the candidate report's deferral.

## What remains open

- Root integration: merge-side `./lean-bau`, `gabbro_ziel` axiom probe, `./cargo-pruef`, emission check, secret-pattern grep.
- Substance (correctly left open by the audit): bridge tasks P0–P2 (F1 relocation glue, F2/F3 re-decode + decoded-start table, F4 `geladen`-to-`Zustand` bridge, F5 permission schema + section→region wiring, F6 bias pins, F7 page model).

## Anything in the task believed wrong

Nothing material. One note: OWNER-TASK asked for "actual reproduced positive/negative Lean probes where useful"; the audit cites committed `decide` theorems with file/line instead of re-executing them, and discloses this limit explicitly. For a prose audit lane this is acceptable and does not inflate any claim — not a defect.

CANDIDATE: 407 8df52d64cdb350c481d1929549ee0bc071b0c676
VERDICT: ACCEPT
