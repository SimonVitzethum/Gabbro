# MUSE-REPORT-202 -- The runtime, part 2: starting the threads

Lane 202. Task: close the measured gap of TODO.md section 0 -- the emitted C
of `beispiele/124-two-threads-private.gab` contains `static void hauptA(void)`
and `static void hauptB(void)`, nobody calls them, there is no `main`.
Result: `laufzeit/start.c`, a hosted POSIX runtime driver, plus this report.
No existing file touched; no Lean work (no new definitions or theorems).

## 1. What was delivered

- `laufzeit/start.c` (210 lines, reads in one sitting). For one concurrent
  unit: defines the lock primitives the emitter only declares (`L_nimm` /
  `L_gib` as a `pthread_mutex`), starts exactly the declared roots
  (`hauptA`, `hauptB`) one thread each, joins them, then checks the lock
  invariant and the private slots and exits nonzero on violation. Every
  decision line carries its WHY in the comment above it.
- Nothing else committed. The handwritten comparison program and all build
  artefacts live in `.tmp/` (git-excluded) and are described in section 4.

## 2. The driver (shape)

```
emitted unit (static roots, `void L_nimm(void);` declared)
  #included into start.c            -- static roots are nameable only by inclusion;
                                       a second TU could not call them
lock primitives                     -- runtime objects, defined here (mutex on hosted)
ROOTS section                       -- one pthread_create per declared root, via a
                                       one-line adapter each (signature mismatch
                                       void(*)(void) vs pthread's void*(*)(void*))
ruhe()                              -- the idle root (`none` of E.P.mitRuhe): blocks in
                                       pause() forever, touches no Gabbro carrier;
                                       never spawned on hosted (no spare cores to park)
main                                -- spawn exactly N_WURZELN threads, join all, assert
                                       konto[0]==konto[1], privA==7,7, privB==5
```

Build (from tree root):

```
target/debug/gabbro emit beispiele/124-two-threads-private.gab > .tmp/einheit124.c
cc -std=c11 -O0 -Wall -Wextra -Werror -pthread -I .tmp \
   -DEINHEIT_INCLUDE='"einheit124.c"' -o .tmp/start124 laufzeit/start.c
```

## 3. The run's actual output

Confirmed first that the gap is real: the emitted C (89 lines) defines
`hauptA`/`hauptB` as `static`, declares `L_nimm`/`L_gib` without defining
them, and contains zero occurrences of `main`.

```
$ .tmp/start124; echo "exit: $?"
konto=70 konto=70 privA=7 privA=7 privB=5
exit: 0
```

- 200/200 runs exit 0. Both orders occur (first batch: `konto=30` and
  `konto=70` both seen), the invariant `konto[0]==konto[1]` holds on every
  run, privates are exact on every run.
- `-O2` build: identical behaviour (5/5 runs pass). UBSan build: clean, same
  output. TSan build (`-fsanitize=thread`): 3/3 runs with no race report --
  the expected machine-readable echo of `RennfreiBis` for this unit.
- Strict flags throughout: `-std=c11 -Wall -Wextra -Werror`, the guardian's
  stage-3 bar. (Two `-Werror=return-type` iterations on `ruhe()` are booked
  in the file's own comment: an empty spin loop may be assumed to terminate
  by C11, so the idle root blocks in `pause()` instead.)

## 4. Handwritten comparison (the guardian's shape)

`.tmp/hand124.c` (NOT committed) mirrors `messungen/hand-*.c`: the same
tables, mutex and thread bodies written by hand, same printf line, same
checks. 200-run sorted-unique comparison:

```
emitted+driver:  200x  konto=70 konto=70 privA=7 privA=7 privB=5   (this batch;
                 first batch also showed konto=30 -- scheduling bias toward B-last)
handwritten:       3x  konto=30 konto=30 ... / 197x konto=70 konto=70 ...
```

Same observable set on both sides: invariant always, privates always exact,
final shared value schedule-dependent. The emitted unit and the hand program
behave alike under real concurrency -- not under the sequential composition
the 104 driver uses (which cannot show this at all).

## 5. How "exactly the declared roots" is held (the decisive property)

Not by care: by a mechanical pin between two extracts. The source declares
`concurrent { hauptA, hauptB };` (line 84); the driver spawns at exactly the
`pthread_create(..., faden_<root>, ...)` sites, counted by `N_WURZELN`:

```
src: hauptA hauptB      (from `concurrent { ... }` in the .gab)
drv: hauptA hauptB      (from pthread_create sites in start.c)
N_WURZELN = 2           (sizes the spawn-and-join array)
PIN HOLDS: identical sets
```

Negative control run: renaming one spawn site to a non-declared root makes
the comparison fail (`PIN BROKEN (drift detected, as intended)`). The natural
permanent home is generation-or-pin from `gabbro emit` (which already knows
the declared roots): either emit the ROOTS section, or run this comparison as
a guardian probe per concurrent unit. I built neither -- the emitter and
`pruefe-emission.sh` are out of bounds for this lane -- but the check above
is the exact predicate such a probe would assert, and `N_WURZELN` plus the
one-wrapper-per-root shape exist so the probe has something stable to read.

## 6. Hosted-only vs bare-metal

Hosted-only in `start.c`: `pthread_create`/`pthread_join`/`pthread_mutex`
(thread creation and the lock object), `printf`/`fprintf` (observation),
`abort` (failure), `pause()` (the idle block). Would differ bare-metal: one
thread per core pinned at boot, the lock as the ticket lock of
NICHTINTERFERENZ.md section 10, the idle root as `wfi` (noted at the
`pause()` line), observation via a log device instead of stdout. What does
NOT differ: the split itself -- roots the unit declares run, everything else
parks in a root that touches nothing -- which is assumption (d) `Laufzeit`
verbatim, and the reason the file exists as a `.c` beside the unit rather
than as emitted C inside it.

## 7. Executed-set number for the merger

`instrumente/pruefe-emission.sh` holds 37 `lauf` runs today, all
single-threaded with exact-string comparison. This concurrent run would make
it **38** -- but NOT as a plain 38th `lauf` line: `lauf` compares one exact
expected string, and a concurrent run has no one exact output (konto is 30
or 70 by schedule). Taking it in needs a predicate comparison (invariant +
privates, the shape `main` already returns) beside the string comparison, or
a normalisation step. `MARKE_EMIT*` untouched, as instructed; nothing in
`instrumente/` changed. Merger books it.

## 8. What was NOT measured

- No Lean work: `grammatik/` untouched, checker untouched, `MARKE_EMIT*`
  untouched. `./lean-bau`: exit code 0, 0 error lines, `Build completed
  successfully (263 jobs)`.
- Only `beispiele/124` runs. Other concurrent units (108, 125, ...) were not
  driven; the ROOTS section is per-unit handwork until generation-or-pin
  exists (section 5).
- No starvation/fairness claim: 200 runs show both orders occur, not that any
  order is guaranteed. No weak-memory claim beyond TSan on x86-64.
- The `ruhe()` idle root is present but never executed on hosted -- its
  "touches nothing" is by inspection (it names no carrier), not by a run.
- Poison direction not run for the driver: a wrong expected value (e.g.
  privA==8) was not demonstrated to fail; the exit-1 paths are by inspection.
  Recommended as the first probe if this becomes a guardian stage.

## 9. Where I disagree with the task (one point)

"Compare against a handwritten version, the way the emission guardian already
does for 37 single-threaded units" -- the guardian does NOT do that for its
37 runs: its handwritten comparisons (`messungen/hand-*.c`) are a separate
differential measurement over 2 programs (`MARKE_EMIT_N=2`), while the 37
`lauf` runs compare against hand-written EXPECTED STRINGS, not hand-written
programs. I did the `messungen/`-style program comparison (section 4), which
is the stronger of the two readings and the one that means something under
concurrency; a fixed expected string would have been the wrong artefact here
(section 7).
