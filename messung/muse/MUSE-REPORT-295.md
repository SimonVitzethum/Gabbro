# MUSE-REPORT-295: Independent candidate review (278, 281)

Lane 295. Model: opencode-go/muse-spark-1.3-contributor. No delegation, no other model processes.
Independent from authors 278, 281. Reviewed ONLY the pinned snapshots in `.tmp/review/`
(`SNAPSHOT.json`: 278 @ `a8f24afd4571cabdabc274fd652ff886f3dcb14f`,
281 @ `992c6264d1fe69c9627e42105a407b6e4cd807fb`) and existing source in this clone.
No other clone read, no code or central file edited. Own file: this report only.

Isolation: `pwd` = `/home/simon/Dokumente/gabbro-muse/a295`, toplevel matches, branch `muse/295`. Pass.

## Candidate 278 — FLOAT-ZEIT.md (docs-only wave-A mapping)

Scope check: `PATCH.diff` touches exactly 2 files (`MUSE-REPORT-278.md`,
`dokumente/x86/FLOAT-ZEIT.md`). No Lean/Rust/central edits, no diagnostic/gift/example
numbers (grepped: zero `N[0-9]{3}` / `MARKE_EMIT` hits), no `Spec.lean`/checker/emitter change.
Matches the owner task's owned set and wave-A "no numbers, no MARKE_EMIT" rule.

Claim verification (spot-checked against this clone's source):
- Pilot `Befehl` has no float constructor: confirmed (`X86/Typen.lean:53-68`, 14 integer/control ctors).
- `ZeitAb` / `FortschrittG` / `KeinWarteZyklus` statements: quoted exactly
  (`Spec.lean:1828-1831, 1840-1842, 1896-1900`).
- `GFloat` = binary64 width cut (`Typen.lean:79-82`), `gleitPasst` (`Semantik.lean:351`),
  NaN-bit propagation arms (`Gleitkomma.lean:228-237`), `Logik.bereich` on range failure
  (`Semantik.lean:862-876`): all confirmed as cited.
- Claim boundaries hold: every hardware/cycle item marked proposal/UNPROVED/OPEN; f32 nodes
  refused pending a proved bridge (no double-rounding paragraph passed off as proof);
  MXCSR as checked establishes/preserves per context, not a bare stability assumption;
  `FortschrittG` preserved as enabledness with no invented fairness/OS premise;
  NaN class relaxation conditional on the named OPEN non-observability lemma plus
  sticky-flag reservation; cost-summary schema repaired to bound `targetWork` over `XCorr`
  instead of re-summed source steps (third commit). No assumed simulation, no per-program
  rule, no inferred ensures, no weakening of any goal conclusion. The `kosten.rs`-vs-`kostenK`
  gleit-arm gap is disclosed as finding 1 / blocker 5, not hidden.
- No build run: permitted (docs-only; wave rules require file/claim checks, not gratuitous
  builds). The report states this honestly; no green claimed. No Lean theorems added, so the
  inhabitation gate is N/A. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (no code at all).

Nits (not material): line numbers are as-read and may drift (disclosed in CUTS);
`kosten.rs` gleit correspondence left unverified (disclosed, booked as blocker).

## Candidate 281 — REVIEW-GRUNDLAGEN.md (docs-only independent review)

Scope check: `PATCH.diff` touches exactly 2 files (`MUSE-REPORT-281.md`,
`dokumente/x86/REVIEW-GRUNDLAGEN.md`). No code modified, no numbers allocated. Matches owner task.

Claim verification (independently recomputed in this clone, plain integer arithmetic):
- Flag/extension boundaries: `0xFF..FF+1` carry-without-overflow, `0x7F..FF+1`
  overflow-without-carry, `1-2` giving `l`+`b`/not `g`/`a`, parity `0/0x03/0x01/0xFF` =
  `true/true/false/true`, `sext` `0xFF->0xFF..FF` / `0x7F->0x7F` / `0x8000->0xFF..8000`,
  LE coefficients `256^0..256^7`: all match the reviewed files.
- Encoding issue bytes: `add r15,r8` = `4D 01 C7`, `load r9,[r12-8]` =
  `4D 8B 8C 24 F8 FF FF FF`, `push r9` = `41 51`, `pop r12` = `41 5C`,
  `jcc l/ge/le/g` = `8C/8D/8E/8F`, `cmp rax,rcx` ModRM `C8`, `Disp32` edges
  (`0x80000000 -> -2147483648`, `0xFFFFFFFF -> -1`): all correct per the x86-64 encoding.
- Source anchors confirmed: `cfAdd`/`ofAdd` structurally distinct (`Wort.lean:101-108`),
  `probe_add_carry_no_overflow` / `probe_add_overflow_no_carry` present, permission
  separation and whole-store refusal as described.
- Claim-strength discipline holds after the second commit: sparse-Rust/total-Lean relation
  stated UNPROVED (the remaining grep hit at line 88 is the sentence "no generic
  safe-direction refinement ... is claimed here" — a refusal of the claim, not an
  overstatement); round-trip-catches-divergence removed; architecture rechecks disclosed
  as trained-knowledge comparison with no manual fetched. The bounded verdict ("no error
  found in the inspected equations/encodings", explicitly not hardware correctness and
  establishing no correspondence) is true at that strength. Stronger claims correctly left open.
- No build run: permitted (docs-only claim checks). Report cites the foundation builds from
  270/271/273 + WELLE-A rather than claiming its own. No code, so no forbidden tactics and
  no witness gate applies.

Nit (not material): section 6 prints replay commands with schematic placeholders
(`<cfAdd/... definitions>`) rather than full verbatim command text, so a third party must
reconstruct the definitions from the named sources; results are verbatim and I reproduced
the load-bearing values independently. Recommend full command text in future reviews.

## Assessment

Both candidates deliver exactly their bounded docs-only claims with honest OPEN labelling,
no out-of-scope edits, no number/counter use, and no assumed or weakened result.
No material defect found in either snapshot. Per-candidate verdicts: 278 ACCEPT, 281 ACCEPT.
No `lean-bau`/`cargo-pruef` run applies to this review (no Lean/Rust files in either
candidate; no gratuitous full builds for prose per task).

CANDIDATE: 278 a8f24afd4571cabdabc274fd652ff886f3dcb14f
CANDIDATE: 281 992c6264d1fe69c9627e42105a407b6e4cd807fb
VERDICT: ACCEPT
