# MUSE-REPORT-384: Independent exact-candidate C2 re-review of 346 GateStub

## Candidate under review (NEW PIN — previous verdict is stale)

- Author lane 346, NEW pinned HEAD `240846a78edde146c992d837ace6ab0aca146b8a`,
  base `f737a6f04c22dfdd9499532e0535ad119cf2e56d` (per `.tmp/review/SNAPSHOT.json`).
- Owned files per snapshot: `MUSE-REPORT-346.md`, `grammatik/Grammatik.lean`
  (one additive import), `grammatik/Grammatik/X86/GateStub.lean` (443 lines).
- Previous round (HEAD `232765e4`) got VERDICT: REPAIR on F1 (C187 pool/
  occupancy mismatch) and F2 (vacuous M140). This round re-reviews the fixed
  candidate only; the old verdict is superseded.
- Review run on branch `muse/384` at `8d0d69ed`. Staged privately in this clone
  (file copy + appended import), probed, then fully restored (`git status`
  clean apart from this report). No other clone read, no network, no push.

## What was checked

1. **Byte identity:** staged `GateStub.lean` diffed against
   `.tmp/review/author-346/grammatik/Grammatik/X86/GateStub.lean` → IDENTICAL.
   Author's BUILD-EVIDENCE (386-job `./lean-bau` green, goal probe unchanged)
   therefore refers to exactly these bytes.
2. **Staged `./lean-probe grammatik/Grammatik/X86/GateStub.lean`: 0 errors.**
   Axioms all standard: admission/refusal/stub/decode theorems depend on
   nothing or `[propext]`; `m140_*` on `[propext, Quot.sound]`;
   `torStub_zeuge` on `[propext, Quot.sound]`.
3. **Forbidden tokens:** `grep -nwE "sorry|admit|axiom|native_decide|unsafe"`
   → single hit is CUTS prose ("never a hardware axiom"), not a command.
   No `intro _` / `have _ :=` discards. No `: Prop` premise anywhere.
   Every theorem is ground (`decide`/`rfl`/`refine` using all components).
4. **F1 re-verification (C187):** `trampolinVorrat = [r12,r13,r14,r15,rbx]`
   and `freieTrampolin` excluding in-registers + answer register + clobbers
   now mirror `emit.rs::syscall_stumpf` (`emit.rs:9941-9954`: `belegt =
   regs_in + regs_out + clobbers + fest_zerstoert`, pool `["r12","r13","r14",
   "r15","rbx"]`) exactly. The fixed-destroyed set (`rcx`,`r11`,memory) never
   meets the pool, so omitting it is faithful, and CUTS states this. The new
   divergence witness `torStapelAntwortBelegt` (`aus = rbx`, `r12`-`r15`
   clobbered → refused) pins the answer-occupancy behavior the old model
   missed; `torStapelZeuge` still clears. **F1 CLOSED.**
5. **F2 re-verification (M140):** `m140VerweigertB` is now site-indexed over
   tagged `StubenWert` (`.zahl` bare word / `.zeiger` base+extent) against a
   pointer-expecting site list, with three pinning theorems
   (`m140_geschmiedet` true, `m140_echt_kein_fund` + `m140_zahl_erlaubt`
   false). This is the offered repair direction "minimal inspected site
   mirror": a refusal-shape mirror over caller-supplied tags, with detection
   (which site expects a pointer) openly assigned to the checker (`m1.rs`) in
   CUTS — not claimed as derived here. **F2 CLOSED as an honest shape mirror.**
6. **Canonical reuse verified against this clone's sources:** `Register`
   (16 GPR, `Typen.lean:13`), `roundtrip_movReg64` (`Codec.lean:468`),
   `write_read_zeuge` (nonzero write, read-back, observable byte change,
   `Speicher.lean:681`) — joint witness is non-degenerate via the canonical
   memory witness, no second memory minted. No second IR, no `exec`/`schritt`
   duplicate, trap checked as literal `0F 05` shape only. CUTS + `#print
   axioms` present. English only.
7. **Source fidelity spot-checked:** N063/N064/N065 in
   `crates/gabbro-check/src/syscall.rs:159-292` (faithful mirrors; N066
   implicit-by-construction is openly stated, not duplicated); C186 in
   `emit.rs:9584`; C187/trampoline/`-4095`-fence decode in sentence
   `syscall.stub` (`saetze.rs:4360`).
8. **Merge mechanics:** snapshot's `Grammatik.lean` predates the SpillPrivate
   merge (appends `GateStub` where this clone has `SpillPrivate` last) —
   trivial import-union conflict, auto-resolvable per the merge script.

## BLOCKER (environmental, proven not candidate-caused)

- Full staged `./lean-bau` and the `gabbro_ziel` axiom probe could NOT be
  re-executed in this clone: Lean dies with `failed to create thread`
  (exit 134) under box-wide memory/thread exhaustion (swap 100% full, ~40
  concurrent lanes). **Baseline control: with the candidate fully removed,
  `./lean-bau` fails on `Grammatik` itself with the identical error.**
  A dead/blocked check is not acceptance: the missing re-execution must be
  covered by the merge-gate rebuild (`muse-merge.sh` builds `grammatik/`
  before committing — that build is the backstop).
- What stands in for it: (a) byte-identical file to the author's
  386-job-green build, (b) my staged `lean-probe` 0 errors on those exact
  bytes, (c) line-level source correspondence verified above.

## Findings

- F1 (previous round): FIXED and verified — no further action.
- F2 (previous round): FIXED as an honest shape mirror with OPEN detection —
  no further action.
- No new material findings. Observations O1–O5 from the previous round
  (Linux-only `linuxClobberB`, N065 positional encoding, N066 implicit,
  `fehlerOkB` edge, `klassifiziere` range provenance OPEN) are unchanged and
  remain non-repair-grade; all are stated in CUTS.

## Last check result lines

- Staged `./lean-probe`: `== 0 error(s) in the COMPLETE output`.
- Staged `./lean-bau`: NOT green — environmental thread exhaustion (see
  BLOCKER); baseline fails identically. Author evidence on identical bytes:
  `Build completed successfully (386 jobs).`
- Tree restored before this commit: `git status` clean except
  `MUSE-REPORT-384.md`.

CANDIDATE: 346 240846a78edde146c992d837ace6ab0aca146b8a
VERDICT: ACCEPT
