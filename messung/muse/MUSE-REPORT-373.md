# MUSE-REPORT-373: Independent exact-candidate A1 review of 335 NarrowOps

Lane 373, reviewer. Clone/toplevel verified `/home/simon/Dokumente/gabbro-muse/a373`,
branch `muse/373`. Reviewed exact author snapshot in `.tmp/review/author-335`
(SNAPSHOT NarrowOps.lean 690 lines, OWNER-TASK.md, PATCH.diff, BUILD-EVIDENCE.json,
MUSE-REPORT-335.md) against the accepted canonical sources in this clone.

## Staging and reproduction (private, restored)

- Staged ONLY the candidate owned module (`grammatik/Grammatik/X86/NarrowOps.lean`)
  plus the one additive import line, ran the queued checks, then restored both:
  `git status` is clean except this report.
- `./lean-probe grammatik/Grammatik/X86/NarrowOps.lean`: 0 errors (first line).
  Every `#print axioms` is a subset of `propext`, `Classical.choice`, `Quot.sound`;
  several probes depend on no axioms at all.
- Full `./lean-bau`: `exit 0`, 0 error lines, `Build completed successfully (387 jobs)`
  (386 base here + the staged module; author evidence says 386 on its older base —
  the delta is the newer base's `SpillPrivate`, not the candidate).
- Word-boundary grep for `sorry|admit|axiom|native_decide|unsafe`: clean.
  No `intro _` / `have _ :=`. No `: Prop` premise. CUTS block and 55 `#print axioms`
  lines present. File is English (remaining substring hits are English words
  such as "decoder"/"wider").

## Task-done check (owner task A1 direction)

All target bullets are delivered, reusing canonical defs resolved against this
clone (`Typen.Breite/bits/bytes`, `Wort.maske/trunc/sext/trunc_b64`,
`Speicher.readBreite/writeBreite/read32/write32/read8/zeugenSpeicher/lesbarN/
schreibbarN/read32_nach_write32/write32_rahmen/lesbarN_update/writeBytesN_hit/
addrOff_null`, `Ausfuehrung.effAddr/regSet` — all exist with the used signatures):
register merge with the architectural upper-bit rule (8/16 preserve, 32 clears
upper32 via `trunc .b32`, 64 identity); explicit `ExtendMode` over canonical
`trunc`/`sext` with generic fit facts via the `narrowMaskMod`/`narrowTruncMod`
bridge; profile admission `narrowAdmitted` (alignment, single-carrier, canonical
permissions) with four generic refusal theorems; state helpers `loadNarrow`/
`storeNarrow`/`moveNarrow`/`loadNarrowExtend` over `readBreite`/`writeBreite`;
64-bit cases definitionally the existing 64-bit ops (`loadNarrow_b64_isRead64`,
`storeNarrow_b64_isWrite64`, `moveNarrow_b64`) — no duplicated evaluator of the
14 pilot forms; MOV flag preservation with no narrow flag snapshot (booked);
pre-state base addressing with `rfl` links; loud `SignKind.unknown` guard;
`extendFormOk` gate with refusal theorem; permission-only scalar fallbacks with
the pinned unaligned-fallback probe (admission refuses at 8193, scalar 32-bit
read still answers); aligned mixed-width spill/fill witness (`0x01020304` at
8192, 32-bit fill, 8-bit `0x04` agreement, proven memory change — non-degenerate:
real store-changing execution on real `zeugenSpeicher`-based memory);
concrete refusal probes for unaligned/carrier/extension-form.

## Rule and honesty checks

- Refusal Bool is validator/profile admission with a certified scalar fallback,
  never an invented hardware fault — matches the task safety correction. No
  DIV/IDIV, FP-width, LOCK-latency, per-byte-TSO-atomicity, indirect-call,
  gate/OS-as-axiom, or cost claim anywhere; all booked OPEN in CUTS. No narrow
  `Befehl`/encoding/decoding claim (pilot codec is 64-bit-only; module imports
  no codec — correct, and the report says so plainly).
- No conclusion restates a premise; no contract is quantified away (no source
  syntax occurs); every named premise is used (`simp` with the named equation).
  The witness theorem is a closed concrete existential, and its substantive
  conjuncts (8-bit readback, memory inequality, 32-bit readback) are derived
  through `spillFillAgree`/`storeNarrow_readback_b32`, not assumed.
- No `ZEUGE:` line in the owner task and no theorem quantifies over source
  syntax, so HARD RULE 13 has no mechanical trigger; the joint memory-changing
  witness is provided anyway.
- Ownership: PATCH touches only `MUSE-REPORT-335.md`, one additive import line
  in `grammatik/Grammatik.lean`, and the new module. No checker/Spec/goal/
  central `Typen`/Rust/emitter/docs/friend-reserved path touched.
- Claim is bounded: report and CUTS describe helpers plus admission, not a
  closed source lowering, emitted ISA, or validator. No forged benchmark.

## Non-blocking notes (no repair required)

- Candidate base predates `SpillPrivate`: its `Grammatik.lean` hunk appends the
  import after `Byteschritt` while current master ends with `SpillPrivate`.
  Clean union at merge; verified the staged module builds on the newer base here.
- Generic 8/16-bit merge upper-preservation is pinned concretely
  (`probe_mergeRegNarrow_8/16`), not proved generically — honestly booked in CUTS.
- The witness's load conjunct is stated through `mergeRegNarrow`; the independent
  content (readback values, memory change) is proved through canonical lemmas.

No material defect found. No repair direction needed.

CANDIDATE: 335 2814da5488c09ce2133e7f2648884b34576fffea
VERDICT: ACCEPT
