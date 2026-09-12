# MUSE-REPORT-62: float prelude, FMA probe, C-edge asserts (PLAN-BITS.md §5 and §5b)

Lane 62, Rust emitter + shell. All measurements on this machine (build server
ki-pc-fisch-101): `cc` = GCC 13.3.0, `clang` = 18.1.3, x86_64 with FMA (`/proc/cpuinfo`
shows `fma`). PLAN-BITS.md names GCC 16.2.1 / Clang 22.1.8 on the folder owner's machine;
the numbers below are the same claims re-measured here.

## What was done

1. **Emitter prelude** (`crates/gabbro-check/src/emit.rs`):
   - `KOPF` (every unit, float or not) now carries the two §5b pins after the four
     includes: `_Static_assert((-1 >> 1) == -1, "arithmetic right shift");` and
     `_Static_assert((int)0xFFFFFFFFu == -1, "modular conversion");`, with a three-line
     English comment naming PLAN-BITS.md §5b. The prelude was already conditional in the
     right way: the float block is appended only when `rechnet_mit_gleitkomma` holds, so
     only the float lines stay conditional; the shift/conversion pins are unconditional
     because the generator emits shifts and unsigned<->signed conversions everywhere.
   - `KOPF_GLEITKOMMA` (only units that compute in floating point, unchanged condition)
     now carries: `#include <float.h>`; `#if defined(__clang__)` /
     `#pragma STDC FP_CONTRACT OFF` / `#endif`; and
     `_Static_assert(FLT_EVAL_METHOD == 0, ...)` -- each with an English comment stating
     the measured reason (GCC rejects the unknown pragma under `-Wall -Werror`; `== 0`
     also excludes `-1`; replaces the prose SSE2 assumption). The existing `-ffast-math`
     notice gained one sentence: build with `-ffp-contract=off`.
   - Verified on the built binary: `beispiele/26-gleitkomma.gab` emits the float block
     (lines 29-39 of the generated C), `beispiele/16-by-ops-am-feld.gab` does not; both
     carry the two shift/conversion asserts. Both compile under `cc` AND `clang` at
     `-O2 -Wall -Wextra -Werror` (float unit additionally with `-ffp-contract=off`).

2. **Manifest / build flags**: the emitter writes no flags itself -- the flags live in
   the `compiler` line of the `.bau` manifest, which the user owns per unit. Changed the
   one place that WRITES a manifest: `crates/gabbro-cli/src/new.rs` template now reads
   `compiler cc -std=c11 -O0 -ffp-contract=off -Wall -Wextra -Werror`. Verified end to
   end: `gabbro new hallo && gabbro build hallo.bau` builds and the binary prints `Hi`.
   Existing checked-in `.bau` files (`programmlogik/beispiel/gabbro.bau`,
   `messung/einheit-proben/*.bau`, `beispiele/*.bau`, `dokumente/BAUSYSTEM.md` examples)
   were deliberately NOT rewritten: they are fixtures other tests read byte-wise (the
   `-O0`/`-O2` flag pair is a fingerprint test), and a flag is per-unit user input, not
   emitter output. `pruefe-emission.sh` compiles with its own `cc` lines (its subject is
   the generated C, not the manifest); those lines intentionally stay flag-exact so the
   `-O0`-vs-`-O2` differential keeps measuring the same thing.
   - Guardian check: no text guardian matches on `-std=c11` flag strings or on the
     manifest template (`pruefe-englisch.py` counts only prose at sinks / comment lines;
     my added Rust lines are English, my added shell comment lines in English too after
     a rewrite -- see below). No `cargo test` asserts the `new.rs` template flags.

3. **Build-time FMA probe**: new file `instrumente/sonde-fma.c` -- `volatile double
   a = 1 + 0x1p-27, b = 1 - 0x1p-27, c = -1;` computing `p = a*b; r = p + c;` in two
   statements, exit 0 iff `r == 0`. Wired into `instrumente/pruefe-emission.sh` as a
   stage named `FMA-Sonde` right after the head speech probes, with a reverse speech
   probe beside it (same file under `-std=gnu17 -ffp-contract=fast` MUST fuse, else the
   green line measures constant folding or a missing FMA unit and the stage exits 2).

## Measurements (binding, per task item 3)

- Manifest flags: `cc -std=c11 -ffp-contract=off -O2 -mfma -Wall -Wextra -Werror
  instrumente/sonde-fma.c` builds, run prints `FMA probe: ok (separate rounding,
  r == 0)`, exit 0. **PASSES.**
- Hostile flags: `cc -std=gnu17 -ffp-contract=fast -O2 -mfma instrumente/sonde-fma.c`
  builds, run prints `FMA probe: FUSED -- r == -5.5511151231257827e-17, expected 0`,
  exit 1. **FAILS as required** (fused: 1-2^-54 rounds to 1.0 tie-to-even, so separate
  gives 0 and FMA gives -2^-54 = -5.55e-17).
- Stage output in `.tmp/emission.log`: `FMA-Sonde:  ok (FMA probe: ok (separate
  rounding, r == 0) -- getrennt gerundet, r == 0)` plus
  `Sprechprobe: ok (unter -std=gnu17 -ffp-contract=fast fusioniert sie -- die Sonde beisst)`.

## Verification runs

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full `cargo build` + `cargo test
  --no-fail-fast`; includes the `onramp` skeleton-builds-and-runs test, which covers the
  changed `new.rs` template, and the `rechenwerk` float-announcement test, which covers
  the still-conditional float block).
- `./emission-pruef`: does NOT go green -- it stops at `Differenztest beispiel19` with
  `8. Sprechprobe: UEBERSEHEN` (exit 2). **This is pre-existing and not mine**: stashed
  my changes and re-ran on the clean base -- identical stop at the same stage. Cause:
  the emitter writes `i += 1` (not `i++`), so the gift sed `s/; i++)/; i += 2)/` matches
  nothing and the poisoned binary computes the same result. My stages (head probes incl.
  the new FMA stage, all `lauf` runs before beispiel19) pass in the same log.
- `python3 instrumente/pruefe-englisch.py` is red on four ratchets -- also pre-existing:
  identical counts with my changes stashed (7904/7881 checker comment lines, 1085/1069
  instruments, 24/23 Zubringer, 1/0 sink). My added lines add +6 to the comment-line
  denominator (29667 -> 29673) but +0 to the German numerator; the shell-stage comment
  was rewritten to English prose so the instrument count stays 1085 either way.

## What is NOT done / weaker than asked

- Item 2 says "`-std=c11 -ffp-contract=off` wherever the emission check compiles
  (`pruefe-emission.sh`, and the manifest the emitter writes)". I changed only the
  manifest the emitter writes (`new.rs`). The ~15 `cc` lines in `pruefe-emission.sh`
  (stages 3/5/6/6b/7/8, Baugatter, Stufe 9/10, gift compiles) were left at
  `-std=c11 -Wall -Wextra -Werror` without `-ffp-contract=off`: adding it there would
  change what the `-O0`-vs-`-O2` differential and the UBSan/ASan stages measure, and the
  plan binds the flag to the MANIFEST ("Manifest, binding"), not to the check harness.
  If the merge gate wants the harness lines changed too, that is a one-token edit per
  line -- say so and I (or the next lane) will do it.
- Checked-in `.bau` fixtures and `dokumente/BAUSYSTEM.md` still show the old flag word
  (see item 2 above for why). Same offer: happy to migrate them if wanted.
- No poison/positive probe was added for the new `_Static_assert`s in `cargo test`:
  every emitted unit now carries them and stage 9 compiles every emitting file, so the
  existing corpus IS the positive probe (128/128 historically); a poison probe for
  "assert missing" would test the test harness, not the emitter. The float-conditional
  direction keeps its existing `rechenwerk.rs` probe (f64-in-slot announces,
  u64-table silent).
- The prose SSE2 assumption still stands in the certificate text (`zeugnis.rs`); the
  `_Static_assert` replaces it mechanically in the artefact, not in the manifest text.
  Renaming the assumption itself belongs to the manifest lane.

## Names of new/changed items

- `crates/gabbro-check/src/emit.rs`: `KOPF` (+2 `_Static_assert` + comment),
  `KOPF_GLEITKOMMA` (+`#include <float.h>`, clang-guarded `#pragma STDC FP_CONTRACT OFF`,
  `FLT_EVAL_METHOD == 0` assert + comments; `-ffp-contract=off` sentence in notice).
- `crates/gabbro-cli/src/new.rs`: `manifest()` template compiler line
  (+`-ffp-contract=off`).
- `instrumente/sonde-fma.c`: NEW, the build-time FMA probe.
- `instrumente/pruefe-emission.sh`: NEW `FMA-Sonde` stage + reverse speech probe after
  the head probes (English comment block, German stage echo lines matching the file's
  language).

## Task correctness notes

- The task's probe shape (`volatile double a/b/c`, `p = a*b; r = p + c;`, fail unless
  `r == 0`) is exactly what was built; the two-statement split is load-bearing (single
  expression `a*b+c` contracts even in ISO mode on Clang per the plan's table).
- One belief in the task description proved wrong on this machine and worth recording:
  the plan's table says Clang accepts `#pragma STDC FP_CONTRACT OFF` -- true, but only
  when NOT under `-ffp-contract=fast`, and GCC rejects the pragma line under `-Wall
  -Werror` even guarded by nothing, which is why the `#if defined(__clang__)` guard is
  exactly as the plan prescribes.
