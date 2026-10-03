# MUSE-REPORT-751 — Hardware completion: compact AND/OR/XOR with imm8

Lane 751, clone `/home/simon/Dokumente/gabbro-muse/a751`, branch `muse/751`.
Owned files only: `grammatik/Grammatik/X86/CompactImm8Logic.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New file `grammatik/Grammatik/X86/CompactImm8Logic.lean` (~550 lines) is a
CONNECTION module over the accepted `IntegerHardwareForms` vocabulary. It
adds no canonical definition: encoder, decoder, step, fetched fetch and
byte step (`encodeIntHwImm`, `decodeIntHwImm`, `stepIntHwImm`,
`immWort`, `imm8Erweitern`, `immPasst8`, `fetchIntHwImm`,
`intHwImmByteschritt`) are all reused. This is deliberate: the REX.W 83
/1 /4 /6 imm8 rows already have their codec and step in
`IntegerHardwareForms.lean`, and the lane rules forbid overlapping writers
of canonical vocabulary.

Proved:

- §1 per-width logic-flag identity, one lemma per op, generic over the
  carried width: `kompakt_and_flaggen`, `kompakt_or_flaggen`,
  `kompakt_xor_flaggen`. Each step installs CF = OF = false with AF
  undefined, reusing `intHwFlagsLogik` (= `logikFlags`).
- §2 pinned bytes and decodes for all three REX.W rows plus one b32 row:
  `pin_or_kompakt` / `pin_or_kompakt_dekode` (`or rax, 1` =
  REX.W, 83, C8, 01), `pin_and_kompakt` / `pin_and_kompakt_dekode`
  (83, E0, 01), `pin_xor_kompakt` / `pin_xor_kompakt_dekode`
  (`xor rax, -1`, sign-extends through one byte), `pin_and32_kompakt`.
- §3 compact choice and outside-i8 refusal: `kompakt_or_feuert`,
  `kompakt_and_feuert`, `kompakt_xor_feuert` (compact 83 form iff the
  int32 fits in a signed byte, else the wide 81 form),
  `kompakt_ausserhalb_i8` (128/256 refuse, 127/-128 admitted),
  `kompakt_weit_bei_256`, `kompakt_abgeschnitten` (truncated tails refuse).
- §4 successor projections of the witness OR step: `kompakt_s1_rax`
  (rax = 0xF1), `kompakt_s1_rbx`, `kompakt_s1_rip` (4100),
  `kompakt_s1_eff` (store address = data cell), `kompakt_fetch_dekode`
  (fetched window decodes to the stepped row), `kompakt_fetch_zugelassen`,
  `kompakt_or_wert`, `kompakt_start_null`.
- §5 `CompactImm8Logic_verbindung` (11-conjunct joint connection: flag
  identity, value, RIP, fetched decode, admission, byte step through the
  accepted dispatcher, memory read-back 0xF1, start cell 0, wide form at
  256), `kompakt_store_trifft`, and the companion
  `CompactImm8Logic_verbindung_zeuge`, which instantiates both step
  hypotheses jointly on the non-degenerate reached run
  (rax 0xF0 -> 0xF1, data cell 0x00 -> 0xF1 via the pilot store).
- Witness state: `kompaktRax`, `datenZelle`, `kompaktProg`,
  `kompaktBytes`, `kompaktExec`, `kompaktDaten`, `kompaktReg`,
  `kompaktFlags`, `kompaktStart`, `kompaktRest`.
- File ends with a `CUTS:` block and `#print axioms` for every theorem.

Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
Intel SDM 325462-093US (`REFERENCES.json`: `intel-instruction-reference`);
AND row txt line 40726, AND flags txt 40766-40768; OR row txt 71678, OR
flags txt 71721-71722; XOR row txt 138276, XOR flags txt 138319-138321.
All three flag sentences are the same identity the lemmas prove
(OF/CF cleared; SF/ZF/PF from result; AF undefined).

## Verification

- `./lean-probe grammatik/Grammatik/X86/CompactImm8Logic.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (whole `grammatik/`): first line
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  final line `Build completed successfully (483 jobs).`
- Every `#print axioms` reports `[propext, Quot.sound]` or `[propext]`
  only: no `sorry`/`admit`/`axiom`/`native_decide`, a subset of the
  standard `gabbro_ziel` axiom set. `gabbro_ziel` itself is untouched
  (no edits to its dependencies; only an additive import).
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files.

## What remains open (plainly: weaker than the task asks)

The lane task also names TSO bridges, fault delivery, feature/control
gates, asynchronous effects, SIMD/entry/profile forms and the
optimiser chain. None of that is claimed here: this module proves the
83 /1 /4 /6 imm8 rows as byte-connected register logic with manual-grade
flag identity, explicit refusals, and one memory-changing reached run.
Fault classification stays with `DecodeFault`/`HardwareFaults`, the TSO
bridge with the concurrency lanes, wider coverage with the follow-up
hardware lanes. The overlap finding is recorded, not worked around:
`IntegerHardwareForms.lean` already owns these rows' codec and step, so
a second canonical vocabulary would have been the real defect; §5 ties
the reused pieces into the byte-facing dispatcher instead.

## Incidents and lessons for the next lane

- `./lean-bau` failed twice at the root `Grammatik` link step with a
  missing dep olean (first `Grammatik/FortschrittZeuge.olean`, then
  `Grammatik/X86/ScalarFloatHardwareForms.olean`), although all 482
  module jobs succeeded. Both files existed on later inspection and the
  third run completed 483 jobs green. This is build-cache/apparatus
  flakiness in files this lane does not own, not a proof defect.
- Full `simp` normalises BitVec literals (`1` to `1#32`) and breaks
  subsequent `rw` matches; use `simp only` for literal-carrying goals.
  After `rw` with a fetched pair, a projection redex `(row, rest).1`
  blocks further rewriting; a `show` with the iota-reduced form
  restores it. State equalities are fragile to rewrite; projections
  (`Option.map ... = some v` by `decide`, transported along the step
  hypothesis) are robust.
- `Option.isSome_iff_exists` yields the unflipped `∃ m, o = some m`
  (unlike `Option.ne_none_iff_exists`, which is flipped).
- `push_neg` is unavailable (no Mathlib in `grammatik/`); use
  `by_cases` on the `= none` equation directly.
- A direct `git status`/`ls` probe via bash was permission-rejected
  mid-lane; diagnosis used the Read/Glob tools and the queued wrappers
  instead.
