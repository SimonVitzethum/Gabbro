# The two-family tool booked `0 Unterschiede` and its zero was TRUE

*Measured 2026-09-02. Machines: this one (gcc 16.2.1, clang 22.1.8, `free -g` 31 total /
16 available, 20 cores) and `ki-pc-fisch-101` (gcc 13.3.0, clang 18.1.3, 110 total /
85 available, 16 cores). Every compiler run below is `LC_ALL=C`.*

---

## 0. The occasion

A generator defect reached the tree at `0e328c7`: an `exchange update` body answering on one
path only handed the compare-exchange a value the emitter never wrote.

```
gabbro pruefe                          0 errors
gabbro emit                            exit 0
cc -std=c11 -Wall -Wextra  -O0/-O1/-O2 silent   <- the WHOLE of what pruefe-emission.sh asked
zaehle-c-formen.py                     blind (the unit compiles)
clang -Wsometimes-uninitialized        NAMES IT
```

`instrumente/pruefe-uebersetzerfamilie.py` runs **both** families over the whole corpus and
books `0 Unterschiede`. It exists for exactly this class. It saw nothing.

**The question of this report is why** — and whether that is a defect in the tool or a
misreading of it.

---

## 1. The answer, in one line

**The tool's flags were never the gap; its POPULATION is, and the population cannot be
fixed, because it is downstream of the very checker whose defect the tool is supposed to
catch.**

Three measured reasons, and the third is the one that settles it.

### 1.1 The flags name the defect verbatim — measured, not read

The tool compiles with `FLAGGEN = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"]`, the
same set stage 9 uses, for **both** families. Two of the four plausible shapes are therefore
refuted by the source alone: it does *not* compile without `-Werror` (so a warning **is** a
rejection), and it does not compare "accept/reject" in the sense of language acceptance — with
`-Werror` its verdict is a diagnostics verdict.

Reconstructed the emitted shape from `0e328c7` into one `.c` file and ran the tool's own flag
set over it:

```
gcc   -std=c11 -Wall -Wextra -Werror     exit 0
clang -std=c11 -Wall -Wextra -Werror     exit 1
  error: variable '_cn1' is used uninitialized whenever 'if' condition is false
         [-Werror,-Wsometimes-uninitialized]
```

`-Wsometimes-uninitialized` sits **inside clang's `-Wall`**. The tool's flag set was already
sufficient. Had the file been in its population, it would have gone red on the first run.

### 1.2 No committed unit ever triggered it

The defect lived in `emit.rs`, not in any `.gab`. Every `update` body in the corpus ends in a
bare `return v;` and none of the six moved when the fix landed (`0e328c7`, verbatim). So the
corpus never held a file whose C carried the shape.

### 1.3 And the corpus never CAN hold it — this is the structural half

`emittiert()` returns `False` when `gabbro emit` refuses, and the loop then `continue`s. The
one file in the tree that carries the shape is
`beispiele/gift/658-an-update-body-that-falls-through.gab`, and it is `-- erwartet: C001`:

```
$ ./target/debug/gabbro emit beispiele/gift/658-an-update-body-that-falls-through.gab
error: [C001] ... no lowering: `update` body that can fall through without a `return` ...
gabbro emit: ... has errors -- no C written
exit=1                       <- so pruefe-uebersetzerfamilie.py SKIPS it
```

And the probe arrived in the **same commit as the fix** — `git log --diff-filter=A` names
`0e328c7` for the probe, and `0e328c7` is the commit that added the `C001` check to
`emit.rs`. There is therefore **no commit in the history** at which a `.gab` in the tree
emitted the defective C.

> **The probe that documents the defect is invisible to the instrument that would have named
> it.** Not by accident: a generator defect, once understood, becomes a `C001` refusal, and a
> refused file leaves the emitting population. The tool's denominator shrinks by exactly the
> class that has just been learned.

---

## 2. What its object actually is, versus what its name and placement imply

| | |
|---|---|
| **What the name implies** | "the emitted C is checked by two compiler families, so a single-family blind spot cannot hide a generator defect" |
| **What it measures** | over the set of `.gab` files that `gabbro emit` accepts **today**, whether gcc and clang return the same verdict under `-std=c11 -Wall -Wextra -Werror` |

The gap is not the flags and not the families. It is the quantifier and the tense:

* **A census, not a gate.** It runs over what is already committed, after the fact. A gate
  runs at the moment a unit arrives. Two questions, and only the first was being asked.
* **A regression detector, not a discovery instrument.** It can only find a generator defect
  that some *committed, clean* file happens to trigger by accident. Nobody writes a clean
  example in order to exhibit a defect nobody knows about yet.
* **Its denominator is chosen by its own subject.** The emitter decides which files enter the
  population, and the emitter is what is being measured. That is the same shape as
  `MARKE_EMIT`'s own warning one level up in `pruefe-emission.sh` — *"ein WAECHTER, dessen
  Nenner das ist, was das Werkzeug selbst liefert, misst seine eigene Reichweite"*.

**So: `D1`'s shape a third time.** The tool is right, its zero is true, and it was misread —
by its own docstring, which promises a *difference between two compiler families* without
saying over which population that difference is quantified. **The finding is the missing
sentence, not a wrong number.** That sentence is added in this lane (§5.3).

---

## 3. The census, with its denominator

`gabbro emit` over every `.gab` in the tree minus `target/.claude/.lake/arbeitsprotokoll` —
the same reach stage 9's `find` uses. Emitted once into a cache, then each switch set run over
the cache. **No `-Werror` anywhere: this counts diagnostics, it does not gate.**

```
612 .gab in the tree
130 emit                    120 the population  ·  10 reverse probes (`-- erwartet: cc`)
```

### 3.1 The named switches — both machines, identical

| switch set | clang 18.1.3 (server) | clang 22.1.8 (local) |
|---|---|---|
| `-Wall -Wextra` (base) | **0** hits / 0 of 120 | **0** / 0 |
| `+ -Wsometimes-uninitialized` | **0** / 0 | **0** / 0 |
| `+ -Wconditional-uninitialized` | **0** / 0 | **0** / 0 |
| `+ -Wshadow` | **0** / 0 | **0** / 0 |
| `+` seven `-Wtautological-*` | **0** / 0 | **0** / 0 |
| `+ -Wcast-align` | 100 / 15 | 100 / 15 |
| `+ -Wunreachable-code-aggressive` | 37 / **10** | 37 / **10** |

*The seven are* `-Wtautological-compare`, `-constant-in-range-compare`, `-type-limit-compare`,
`-unsigned-zero-compare`, `-unsigned-enum-zero-compare`, `-value-range-compare`,
`-overlap-compare`.

### 3.2 The full denominator: `-Weverything` over the same 120

Because "205 warnings and no information" is a mistake this tree has made once, the honest
denominator is the whole arsenal, tallied per tag.

| hits/units 22.1.8 | hits/units 18.1.3 | tag | class |
|---:|---:|---|---|
| 914 / 75 | 920 / 76 | `unsafe-buffer-usage` | style — a C++ hardening warning, no C meaning |
| 122 / 71 | 122 / 71 | `unused-macros` | style — emitted constants a unit does not use |
| 100 / 15 | 100 / 15 | `cast-align` | **booked** — provably aligned since `N047`–`N049` |
| 71 / 51 | 71 / 51 | `padded` | style — struct padding, informational |
| 63 / 30 | — | `pre-c11-compat` | style — the target IS c11 |
| 35 / 14 | 35 / 14 | `used-but-marked-unused` | style — the emitter's OWN `__attribute__((unused))`, the 2026-08-31 repair |
| 31 / 13 | 31 / 13 | `missing-variable-declarations` | style |
| 27 / 18 | 27 / 18 | `declaration-after-statement` | style — a C89 rule |
| 24 / 6 | 24 / 6 | `unreachable-code-break` | style — see §3.3 |
| 13 / 10 | 13 / 10 | `switch-default` | style |
| 7 / 5 | 7 / 5 | `unreachable-code` | style — see §3.3 |
| 5 / 3 | 5 / 3 | `unreachable-code-return` | style — see §3.3 |
| 1 / 1 | 1 / 1 | `unreachable-code-loop-increment` | style — see §3.3 |
| 1 / 1 | — | `jump-misses-init` | style — see §3.5 |
| **1414 / 101** | **1356 / 97** | | |

### 3.3 The three-way split

```
a real defect                 0 of 1414
a known-and-booked class    100 of 1414   `-Wcast-align`, 15 units
pure style                 1314 of 1414
```

**Zero.** Not one diagnostic under the full clang arsenal names a value, a lifetime, a branch
or a conversion that a reader would act on. The emitted C is clean under every analysis clang
can perform on it.

### 3.4 `-Wcast-align` is not a family difference at all

The obvious reading of "100 hits clang finds" is that clang is stricter. Measured, it is not:

```
gcc   -std=c11 -Wall -Wextra -Wcast-align=strict    100 hits over 15 units
clang -std=c11 -Wall -Wextra -Wcast-align           100 hits over 15 units
only gcc: []   only clang: []   same unit, different count: {}
```

**Identical units, identical per-unit counts.** It is a switch difference (gcc needs
`=strict`, clang does not), not a family difference — and the alignment behind all 100 is
proved since `N047`–`N049`. It belongs on neither list.

*Named for the record, since a count without its units is a rumour:* `beispiele/02`, `04`,
`09`, `12`, `20`, `37`, `40`, `41`, `44`, `45`, `messung/fragmente/F02`, `F04`,
`messung/grammatik/geraeteworte`, `raumworte`, `messung/proben/probe-feldzugriffe-frei`.

### 3.5 The two single-hit curiosities, chased and closed

* `jump-misses-init`, 1 hit, `beispiele/39-auftragsdienst.gab`. Reproduced by hand: the text
  is *"jump from this goto statement to its label is incompatible with **C++**"*. The emitted
  language is C11. **Style.**
* The `unreachable-code*` family, 37 hits over 10 units, is the emitter's deliberate
  terminator after a block that already answers — the same shape the `goto` note at
  `MARKE_TABELLE` in `zaehle-c-formen.py` describes. **Style**, and a gate red on 10 of 120
  units on its first day is not a gate.

### 3.6 The gate compiles at `-O0`, and that costs nothing — swept

Stage 9 and this census compile at the default `-O0`. gcc was swept at `-O0`, `-O1` and `-O2`
when the defect was found; clang never was, so the question *"does the gate lose anything by
not optimising?"* stood open. Swept over the same 120-unit cache, both families, four levels,
gate flag set (`-std=c11 -Wall -Wextra`):

```
clang -O0/-O1/-O2/-O3    0 hits over 0 of 120 units
gcc   -O0/-O1/-O2/-O3    0 hits over 0 of 120 units
```

**Bit-identical at every level.** Over the full 130-file cache — the 10 reverse probes
included, whose C is *supposed* to fall — the tally is likewise invariant across all four
levels (clang 9 hits / 6 units, gcc 8 / 7), and every one of those hits belongs to a reverse
probe. *An `-O` level buys this gate nothing, and it is now measured rather than assumed.*
The reason is structural and worth naming: `-Wsometimes-uninitialized` is clang's
**semantic-analysis** warning, computed from the CFG before any optimisation — unlike gcc's
`-Wmaybe-uninitialized`, which needs the optimiser and is why the gcc sweep was necessary in
the first place.

---

## 4. The minimal switch set, and the argument per switch

**The honest answer is that the added switch set is EMPTY, and the added TOOL is one.**

| candidate | verdict | argument |
|---|---|---|
| `-Wsometimes-uninitialized` | **already there** | It is the one switch that caught the real defect — and it rides in on `-Wall`. Naming it explicitly adds a word to a command line and changes no verdict. The thing that was missing was not the switch but the **second compiler**. |
| `-Wconditional-uninitialized` | **no** | 0 of 120. It is `-Wsometimes-uninitialized`'s may-analysis sibling; over emitted C it says nothing the `-Wall` member does not. |
| `-Wshadow` | **no** | 0 of 120. The emitter mangles its own names; shadowing is structurally impossible here. |
| seven `-Wtautological-*` | **no** | 0 of 120. gcc's `-Wtype-limits` (in `-Wextra`) already covers the case this tree actually met — `F06`'s *"comparison is always true due to limited range"*, stage 9, 2026-08-31. |
| `-Wcast-align` | **no** | 100 of 120, and §3.4 shows it is not a family difference and `N047`–`N049` show it is not a defect. Adding it books 15 permanent exemptions to catch nothing. |
| `-Wunreachable-code-aggressive` | **no** | 37 over 10 units on day one, every one deliberate. A gate whose first run needs ten exemptions is a list, and this tree replaced a list with a rule on 2026-08-20 for exactly that reason. |

> **One switch that catches a wrong value entering a compare-exchange is worth more than
> twenty that catch braces** — and here that one switch is not a switch. It is
> `clang` standing beside `cc` with the flag word the gate already spoke.

---

## 5. Where it is wired, and why there

**Stage 9 of `pruefe-emission.sh`, and it was already wired there** — by the lane at
`6214aa2`, merged into `master` at `a2cd217`, hours before this lane started. This report
verifies that wiring rather than duplicating it. What stage 9 now does, per emitting unit that
`cc` accepts:

```sh
clang -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/regel.c"
```

and a missing `clang` colours the stage **red** (W1: an absent tool is not a passed test).

**Why there and not in `pruefe-uebersetzerfamilie.py`:** §2 is the whole argument. The
two-family tool is a census over the committed corpus; stage 9 is the gate a unit passes on
arrival. The defect class in question can never enter the census — §1.3 — so extending the
census would have added a flag to a population that structurally excludes the subject.
*Extending the wrong instrument is how a green run gets built over a blind spot.*

**No third place was added.** The rule *"every file that emits must pass `cc -Werror`"* now
reads *"…must pass `cc -Werror` and `clang -Werror`"*, in the one place that already owned it.

### 5.1 The gate BITES, and that was measured and not assumed

A gate whose new branch cannot fire is a green line, so stage 9 carries a two-sided speech
test (`Sprechprobe 9b`) that compiles the CAS shape itself: half (a) fails the run if `cc`
*catches* it — because then the second family adds nothing and the reason for the extension is
gone; half (b) fails the run if `clang` *lets it through* — because then `n_clang_ok von n_ok`
is a number without a claim. Both halves ran green on `ki-pc-fisch-101` under clang 18.1.3:

```
Sprechprobe 9b: ok (cc nimmt die CAS-Gestalt an, clang lehnt sie ab)
```

*A guardian whose occasion has lapsed is a finding* — that reading is built into the branch,
so the day the emitter or gcc changes, the gate says so instead of going quietly green.

### 5.2 The run, on the machine the tree is measured on

`ki-pc-fisch-101`, `free -g` 110 total / 85 available, 16 cores:

```
./instrumente/pruefe-emission.sh          EXIT=0   EMISSION: ALL PASS
    120 von 120 emittierenden Dateien uebersetzen; 10 umgekehrte Proben -> 130 emittieren
    120 von 120, die cc annimmt, nimmt auch `clang` an   (18.1.3 gegen gcc 13.3.0)
      1 von 10 umgekehrten Proben beissen nur unter `cc`  (Marke 1)
cargo test --offline --no-fail-fast       EXIT=0   399 passed, 0 failed, 31 result lines
```

**The gate's own population and this report's census are the same 120**, arrived at
independently — stage 9 by its `find`, this census by `rglob`. That agreement is the reason
the numbers in §3 can be read as a statement about stage 9's subject and not about a
neighbouring set.

Ratchets after the change: `zaehle-wortschatz.py` **221 / 208 / 333** unmoved,
`pruefe-englisch.py` **7883 / 1069** unmoved (the instrument comment TOTAL rises 5496 → 5542
by the English block added below, and the German count does not move — which is what the
ratchet asks).

**One mark did move, and it was this lane's own file.** `pruefe-zahlen.py` went red with
*"Dateien, die der Widerrufwaechter liest steht als 176, der Lauf sagt 177"*. Cause measured
the way this tree asks: the new report was moved out of the tree, the run went green, the
report was moved back and the run went red again. `TODO.md` carries the number to 177 with
the reason written at it. *A mark that moves for a document its own lane wrote is not a
finding about the tree — but only a measurement can say that, and the measurement is cheap.*

### 5.3 What this lane changed

1. **`instrumente/pruefe-uebersetzerfamilie.py`** — the missing sentence of §2, at the tool's
   own docstring and at `MARKE_FAMILIENUNTERSCHIED`. Its zero is true; a reader had no way to
   know what the zero is quantified over. *A tool that cannot see a class should say which.*
2. **`instrumente/pruefe-emission.sh`** — one measured number in the census block corrected:
   `-Wunreachable-code-aggressive` is **37 hits over 10 units**, not over 8. Both clangs, both
   machines, same 10. The hit count `37` in that block is right and reproduces exactly.

---

## 6. What stays unmeasured

* **A third family.** Everything here is gcc against clang. `tcc`, `icx`, MSVC and the
  Compcert front end are not on either machine and were not asked. The two-family tool's own
  closing sentence already says this and it stays true.
* **The reverse probes under clang.** 10 files carry `-- erwartet: cc`; stage 9 books
  `MARKE_UMG_NUR_CC = 1` — `beispiele/gift/642`, which bites under gcc alone. This lane did
  not re-derive that number; it read it.
* **Whether `-Weverything`'s style tags stay at zero information as the corpus grows.** The
  census is a snapshot over 120 units. `unsafe-buffer-usage` at 914 hits is the tag most
  likely to one day hide something real inside its own volume, and nothing watches it.
* ~~**Optimisation levels under clang.**~~ **Measured and closed** — see §3.6.
* **Every `.gab` that does not emit.** 482 of 612 files never reach a C compiler at all. Their
  refusals are `pruefe-gifttreffer.py`'s object, not this one's.
