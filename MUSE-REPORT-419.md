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
