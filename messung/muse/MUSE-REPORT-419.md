# MUSE-REPORT-419: X86 BitCount (fixed-width population count)

## What was done

Created the new reusable module `grammatik/Grammatik/X86/BitCount.lean`
(~470 lines) plus one additive import line (`import Grammatik.X86.BitCount`)
at the end of `grammatik/Grammatik.lean`. No other file was touched;
in particular no `Befehl` constructor, no `schritt` equation, no
`OptimizationRules.lean` / `OptimizationWitnesses.lean`, no source
checker, Spec, goal, Rust or emitter file.

The module provides, over the REAL canonical `Wort` (BitVec 64),
`Breite`, `Register`, `Flags`, `Zustand` from `Grammatik/X86/Typen.lean`
and reusing `trunc`/`bitAt` (Wort.lean), `popCount8` only as a
non-duplicated neighbour, `laengeOk`/`ripNach`/`regSet`/`zeugeFlags`
(Ausfuehrung.lean) and `write64`/`read64`/`writeBytes`/`zeugenSpeicher`
(Speicher.lean):

- `popCountAux` / `popCount`: fixed-width population count (set bits
  among the low `b.bits` bits), with proved bounds
  (`popCountAux_schranke`, `bits_schranke`, `popCount_schranke`,
  `popCount_wort_schranke`) and the exact result-word reading
  (`popWort_wert`, `popWort_null`).
- Defined/undefined flag contract: ZF is DEFINED (`popNull`,
  `popNull_heisst`); CF/OF/SF/PF are UNDEFINED behind the validity
  relation `PopcntGueltig` (destination = count, ZF pinned, AF `none`,
  rest unconstrained); the snapshot `popcntFlags` keeps incoming
  undefined bits as an explicit modelling choice
  (`popcntFlags_gueltig`, `popcnt_gueltig_existenz`,
  `popcnt_unbestimmt_unbeschraenkt`, `unbestimmt_bleibt_unbestimmt`).
- Explicit future feature admission: data-only `PopcntMerkmal`
  (decided validator admission, never a hardware probe),
  `popcntZugelassen`, and the register consumer `popcntSchritt` with
  outcomes `ok` / `verweigert` (refusal, never executed, NOT a
  `hardware` stop) / `misslungen`, plus the equations `bc_ok`,
  `bc_verweigert`, `bc_laenge_misslungen`, guard/step agreement
  (`verweigert_heisst_verweigert`, `zugelassen_verweigert_ohne_merkmal`)
  and the negative case `ohne_merkmal_kein_ok` (no success without the
  feature).
- Witnesses: value probes sparse/dense/narrow/zero (`probe_zaehlung`,
  incl. `popCount .b8 0x1FF = 8` for width truncation), step probes
  (`probe_sparse_schritt`, `probe_dense_schritt`, `probe_null_schritt`
  with ZF set), refusal probes (`probe_merkmal_verweigert`,
  `probe_laenge_verweigert`), and the JOINT non-degenerate witness
  `bitcount_speicher_zeuge` (computed sparse count 1 and dense count 64
  through real permission-checked `write64`/`read64` with observable
  memory change, jointly with their ZF facts, on nonzero words).

## Check results

- `./lean-probe grammatik/Grammatik/X86/BitCount.lean`: **RC=0,
  0 errors** (re-verified at report time). All 25 `#print axioms`
  lines are within `[propext, Quot.sound]` or fewer; **no `sorryAx`
  anywhere** (mechanical grep count 0). No `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`; no `Prop`-typed premise; every premise of
  every theorem is used by its proof (checked by hand).
- `BitCount.olean` builds as a dependency during `./lean-bau`.
- `./lean-bau` (whole project) is **RED for environmental reasons
  only**: after 392/393 targets build, the final `Grammatik` umbrella
  link crashes with `failed to create thread` (Lean exit 134).
  CONTROL: with my umbrella import stashed (tree without my change),
  `./lean-bau` fails identically at `[391/392] Building Grammatik`
  with the same crash. The machine has swap 100% full with ~15
  concurrent lane processes; other lanes hit the same crash on
  unrelated files. ~10 retries over 40 minutes all fail at the same
  umbrella link step. The goal files are untouched, so `gabbro_ziel`
  is unaffected, but the standard axiom re-check could not be run;
  the merge gate must re-run `./lean-bau` when the machine allows.

## What remains open (also in the file's CUTS block)

Arithmetic only (no silicon/latency/speed claim); no codec bytes and
no `Befehl`/`schritt`/decoder/image wiring (Typen owner); no source
correspondence; no cost transfer; no TSO bridge; the ZF/rest contract
is stated executable semantics; no `count = 0 ↔ trunc = 0`
characterisation (would need the mask bound); no new checker rule,
diagnostic, poison-probe, example or CLI numbers taken.

## What I believe is wrong in the task

Nothing material. One note: the task asks for a "standard
`gabbro_ziel` axiom check before committing Lean" — impossible for any
lane while the umbrella link cannot run environmentally; module-level
`#print axioms` (all standard) is the strongest evidence obtainable
right now.

## Addendum 2026-10-01 (evening): integration gate failure assessed

The integration gate failed on the merge of this lane with the exact
evidence quoted in the repair request. Assessment against that evidence:

- The 7 quoted `info:` lines are my module's own `#print axioms`
  outputs, all `[propext, Quot.sound]` — standard, not errors. They
  prove `BitCount.lean` itself elaborated inside the integration build.
- The gate's "2 error lines" are the crash lines (`Lean exited with
  code 134`, `build failed`), not type errors. The failing target is
  the `Grammatik` umbrella link in the main checkout, crashing with
  `failed to create thread` — byte-identical to the environmental
  failure documented above, including my pre-merge control run
  (umbrella fails the same way with my import stashed).
- Fresh local re-checks at addendum time: `./lean-probe
  grammatik/Grammatik/X86/BitCount.lean` gives **RC=0, 0 errors, 0
  `sorryAx`, 0 `error(lean…)`**; local `./lean-bau` again builds
  392/393 (including `BitCount.olean`) and crashes only at the
  umbrella link with the same thread-creation failure.

Repair made: NONE — there is no defect in the owned files for the
evidence to point at, and changing proved-green code to work around a
machine resource failure would be fabrication, not repair. No premise
was weakened, no guarantee touched, no file outside
`grammatik/Grammatik/X86/BitCount.lean`, `grammatik/Grammatik.lean`
(the one import line) and this report was read or modified. The
concrete blocker is unchanged: the machine cannot link the ~398-module
`Grammatik` umbrella under current load (thread creation fails);
integration must be retried when resources allow, and a fresh
independent review of the unchanged commit is required as stated.

## Addendum 2 (same day, later): gate failed again with identical evidence

The integration gate failed a second time with byte-identical evidence
(`[397/398] Building Grammatik`, `failed to create thread`, exit 134;
the 7 `BitCount.lean` axiom lines all standard). Nothing new to assess:
same target, same crash, same conclusion — no defect in the owned
files, no code repair made.

New supporting observation this round: a single-file `./lean-probe`
of the unchanged module crashed once with RC=134 (zero type errors)
and passed on immediate retry with **RC=0, 0 errors, 0 `sorryAx`**;
local `./lean-bau` again builds 392/393 including `BitCount.olean`
and crashes only at the umbrella link. Crash-then-pass within minutes
on identical input confirms load fluctuation, not code. Blocker and
recommendation unchanged: retry integration when the machine allows;
fresh independent review required.
