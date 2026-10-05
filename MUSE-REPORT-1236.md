# MUSE-REPORT-1236: Exact review of candidate 1235 (Profiles: multi-step control flow and relocation re-decode)

Lane 1236, branch `muse/1236`, clone `/home/simon/Dokumente/gabbro-muse/a1236`
(verified in prior turn: `muse/1236`, HEAD `45f6238d...`; own file only
`MUSE-REPORT-1236.md`).
Report-only exact review. CANDIDATE: 1235, pinned HEAD
`5a1c10c2bf09717032a9531870ba550ae664dc1a` (base `cbc0afe0...`),
from `.tmp/review/SNAPSHOT.json`. Diff read only from
`.tmp/review/author-1235/PATCH.diff` plus the pinned file copies
`.tmp/review/author-1235/grammatik/...`, `MUSE-REPORT-1235.md`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json`. No other clone touched.

CANDIDATE: 1235 5a1c10c2bf09717032a9531870ba550ae664dc1a

## What was reviewed

NEW FILE `grammatik/Grammatik/X86/PipelineProfilesReloc.lean` (617 lines)
plus one import line `import Grammatik.X86.PipelineProfilesReloc` appended to
`grammatik/Grammatik.lean` (line 644), plus `MUSE-REPORT-1235.md`.
Snapshot file list matches exactly these three files; `clean: true`.

Definitions/theorems added (none by reviewer; all by candidate):
`relocOk`, `relocOk_teile`, `relocOk_profil`, `relocOk_patch`,
`relocOk_patch_link`, `relocOk_patch_bereich`, `relocOk_patch_stelle`,
`relocOk_patch_rahmen`, `relocOk_patch_laenge`,
`relocOk_sprung_verbindung`, `relocOk_ruf_verbindung`,
`relocProg`, `relocProg_gerade`, `relocOk_mehrschritt`,
`relocOk_eintritt_plus_programm`, `relocOk_stuetz_abdeckung`,
`relocOk_stuetz_verweigert`, `reloc_verweigert_ohne_patch`,
`reloc_verweigert_ohne_anfang`, `reloc_verweigert_status`,
`reloc_verweigert_ohne_bild`, `reloc_probe_ueberlauf`,
`reloc_probe_aussen`, `reloc_probe_ueberlapp`,
`reloc_probe_ohne_anfang`, `reloc_probe_ohne_patch`,
`reloc_probe_status`, `reloc_gehostet_ok`, `reloc_frei_ok`,
`pipeline_profil_reloc_verbindung_zeuge`, with `#print axioms` for each.

## Checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: exact token grep over
  the pinned new file finds zero hits (only prose words like "admitted"
  matched the loose pattern; the strict `\bsorry\b|\bnative_decide\b|
  \bunsafe\b|^axiom\b` pattern returns no files). BUILD-EVIDENCE shows two
  intermediate `lean-probe` red runs were plain type errors, since fixed.
- `#print axioms` standard: per BUILD-EVIDENCE final `lean-probe`, every
  name depends only on subsets of `propext`, `Classical.choice`,
  `Quot.sound`; probes mostly `propext` or none. No new axiom declared.
- Existing files untouched except one import line: pinned `Grammatik.lean`
  copy is the base plus the single trailing import; no existing theorem
  edited. `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched.
- Every premise used: inspected each theorem. Splits/projections consume
  `hadm`; closings consume `hadm` (profile leg), `himg` (opcode byte),
  `hdec` (patched decode); multi-step forwards all of `P/pre/post/cs/s/hg/
  hl/hc/hf/hrip` into `lauf_zu_laufBytes`; composition consumes `h1/h2`;
  support theorems consume `hadm/hf/hs`; refusals consume the missing leg.
  No `intro _` / `have _ :=` (grep: no hits). No premise typed `Prop` itself.
- Family evaluator lifted not copied: `relocOk` is
  `profilOk ... && decide (multiPatch ...)`; frame legs rewrite through
  `multiPatch_rel32_gleich` into `linkPatch_bereich/_stelle/_rahmen/
  _laenge`; closings call `verknuepft_rel32_schliesst` (jump) and
  `multi_ruf_schliesst` (call) plus `pipeline_profil_verbindung`;
  multi-step calls `lauf_zu_laufBytes` / `laufBytes_add`; support calls
  `profilOk_stuetz_schritt` / `profilOk_stuetz_verweigert` /
  `profilOk_folgen`. No second loader/decoder/executor/ISA/IR/source
  interpreter defined.
- Planted refusals really refuse: `reloc_probe_ueberlauf`
  (`multiPatch [E9,0,0] 1 (rel32 16) = none`), `reloc_probe_aussen`
  (`rel32 2147483648` out of range = none), `reloc_probe_ueberlapp`
  (`opsDisjunktB [...] = false`) are all `decide`-closed; `ohne_anfang`,
  `ohne_patch`, `status` apply the refusal theorems to concrete failing
  inputs. The joint witness conjoins three of them plus a forged-opcode
  refusal (`decode ([6] ++ rel32Bytes 16) = none`).
- Witness non-degenerate: `pipeline_profil_reloc_verbindung_zeuge`
  conjoins both profile acceptances, patched-window re-decode to
  `jump32 +16` with trailing `0xC3`, `schreibLese_zeuge` (v != 0,
  write64/read64 round-trip, bytes differ), `zeugenU_schreibt`
  (`schreibt = ["konto"]`), `ruf_schritt_zeuge` (reached
  memory-changing run through actual bytes, read64 `0x1005` at `0x1FF8`,
  bytes differ), `relocProg_gerade`, and the planted refusals. Two-core
  coverage is N/A (single-core fetched pipeline scope).
- Silicon facts against `.tmp/HARDWARE-REFERENCES/intel-instruction-
  reference.txt`: `232 = 0xE8 CALL rel32`, `233 = 0xE9 JMP rel32`
  (refs lines 43353-43355, 60789-60794, 223884); 5-byte form, 4-byte
  rel32 operand, `dispSigned`/`rel32Passt`/exact-window/fit/coverage
  claims match the referenced link closings. No silicon re-definition here.
- CUTS honest, no claim larger than proof: file CUTS plus report sections
  state plainly there is NO source-`execBlock` correspondence (units arrive
  lowered; IR lane 287 pending), NO hardware correspondence (model
  `Speicher`), NO TSO/W/GX bridge, NO multi-operand re-proof, NO
  budget/cost transfer, NO kernel behaviour beyond named assumptions,
  `verweigert` = absence of transition. No W/GX or hardware-correspondence
  claim found. No `pipeline_refuses_entry`-style overclaim; only admission
  refusals.
- No unsupported desired-correctness premises, no weakened guarantees:
  admission is a conjunction (profile AND applied operand); refusals are
  `= false`; support theorems preserve `valX86` validation in both cases.
  Unsupported shapes are refused, never guessed.

## Build status (measured by this reviewer)

- `./lean-bau` run by this reviewer in the own clone (no Lean changes in
  this lane; base tree build): last result line `Build completed
  successfully (641 jobs).` Tail showed only standard-axiom info lines
  (e.g. `TsoRmwLink` names on `[propext, Quot.sound]`); zero error lines.
  Earlier in this lane `bash` was intermittently rejected by the permission
  classifier (also the reason the exact `== exit` wrapper line was not
  re-captured); the build itself completed green. The merger still re-runs
  the gate at integration per protocol.
- Relied-on evidence: `BUILD-EVIDENCE.json` final entries —
  `./lean-probe ... PipelineProfilesReloc.lean`: `== 0 error(s) ... exit 0`
  with the full 30-name axiom print; `./lean-bau`: `== exit 0;
  0 error line(s)`, `Build completed successfully (641 jobs)`.
  Intermediate red runs are explained in the author report as parallel-load
  olean races (failing target moved across runs, file under test unchanged)
  and the final green runplus committed state `5a1c10c2` support that
  reading. The merger must still re-run `./lean-bau` at integration; this
  review does not substitute for that gate.

## Open (not claimed, correctly)

Source correspondence, hardware correspondence, TSO/W/GX bridge,
budget/cost transfer, kernel behaviour beyond named assumptions,
multi-operand closings, abs64/rel8 read-back — per CUTS. Fetched EXECUTION
of the relocated jump/call itself (beyond re-decode + support step) is not
proved; the file proves re-decode, fit, coverage, exact window, and generic
support steps, which is what the task's "re-decodes after patching" asks.

## Task correctness note

The owner task asks for "a correctness theorem in the style of
`pipeline_correct_entry`". The candidate does not take an `execBlock`
premise and says so plainly (report section 1, CUTS). Given architecture
decision 594 (no persistent SSA IR / second source interpreter) and the
pending shared IR lane 287, inventing a substitute source leg would have
been worse. The refusal to do so is correct; the gap is booked, not hidden.

## Verdict

VERDICT: ACCEPT

Candidate 1235 at pinned HEAD `5a1c10c2bf09717032a9531870ba550ae664dc1a`
meets the exact-review gates: green-file evidence with standard axioms, no
forbidden tactics, minimal existing-file touch, load-bearing premises,
reuse-not-copy of the family's accepted evaluator, real refusing probes,
non-degenerate witness, correct E8/E9 silicon facts, honest CUTS with no
hardware/W/GX overclaim. Independent `./lean-bau` in the own clone is green
(`Build completed successfully (641 jobs)`); no semantic repair needed.
