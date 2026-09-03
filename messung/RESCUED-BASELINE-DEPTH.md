# A rescued baseline check — the report a dead lane never wrote

**Written 2026-09-03**, closing out branch `worktree-agent-a5322cf249eb7f146`, commit
`a6f24eb` (*"Eine Grundlinie ist nur gut gegen die FRAGE, die ihr gestellt wurde --
GERETTET, Bericht fehlt"*, 2026-09-02 15:41). That lane died at its own account limit
immediately after making the commit — the code was saved, the report it owed was not. This
is that report: what question the change answers, what it could not have seen before, the
before/after totals, and the merge verdict.

## What the change does

Two files, one property.

`instrumente/fuzze-grenzen.py` validates 63 declaration-form baselines through **`gabbro
check` only** — that is its whole job, agreement between two builds of the checker. Until
this change it said nothing about that scope; a reader saw "known-good baseline" and read a
promise about `emit` and `cc` that the file never made.

`instrumente/fuzze-erzeuger.py` reads those same baselines and sweeps each form's value
through `gabbro emit` and `cc` — one stage deeper. Until this change, when a swept case's C
failed to compile, the tool counted it as *one boundary-condition defect the swept value
caused*, full stop. It never asked whether the form's own **baseline** — the value that
never varies, present in every rung of that form's ladder — already failed the same gate.

## The question the old report could not have been asked

A ladder has N rungs. If a form's baseline itself does not compile, **every one of that
form's N cases fails at `cc`**, for a reason that has nothing to do with which rung ran —
the fixture was broken before the sweep touched it. The old report placed all N of those
failures in the same bucket as a case where 1 specific rung tripped a real edge the swept
value reached. A reader counting "boundary defects found" from that bucket was counting a
single broken fixture N times over.

`fuzze-grenzen.py` could not have told you which of its own baselines lower and compile — it
never ran `emit` or `cc` on any of them. `fuzze-erzeuger.py` had the data (it runs `emit` and
`cc` on every case, baseline included) but never asked the question of the baseline
specifically; it asked it of every swept value and let the baseline ride along unmarked
inside the population.

## What the new report can see

`fuzze-grenzen.py` now prints, every run, which stage its baselines were validated to, and —
computed from the ladders, not typed as a literal — how many of its cases sit on a baseline
that is known not to reach `cc`, naming the forms.

`fuzze-erzeuger.py` now runs every accepted baseline through the same `cc` gate the swept
cases face, and reports which baselines fail it (`kaputte_basis`, "FORM-LEVEL defect"). Where
the shape-2 bucket ("THE C DOES NOT COMPILE") is non-empty, it is now split in two: the count
sitting in a form whose baseline already fails (not the swept value's doing) against the
count reached by forms whose baseline is clean (the swept value's own doing — the
interesting half).

## Before / after, measured on `ki-pc-fisch-101`

Both fuzzers were run twice against the **same pair of binaries** (`target/debug/gabbro`,
`target/release/gabbro`, built from this tree) — once with the committed (pre-merge) script
text, once with `a6f24eb`'s changes applied — so only the *reporting* differs, never the
object being reported on.

```
ssh ki-pc-fisch-101 'cd gabbro-karten && export PATH=$HOME/.cargo/bin:$PATH && \
  python3 instrumente/fuzze-grenzen.py --debug target/debug/gabbro --release target/release/gabbro'
ssh ki-pc-fisch-101 'cd gabbro-karten && export PATH=$HOME/.cargo/bin:$PATH && \
  python3 instrumente/fuzze-erzeuger.py --debug target/debug/gabbro --release target/release/gabbro --cc cc'
```

**`fuzze-grenzen.py`** — `diff` of the two runs, in full:

```
0a1,7
> == BASELINES: 63 of 63 accepted at `gabbro pruefe` ==
>    NOT measured: whether a baseline LOWERS (`gabbro emit`), nor whether its C
>    COMPILES (`cc`). This table is read by `fuzze-erzeuger.py`, whose property
>    ends at the compile gate -- that sweep validates these baselines to its own
>    depth and names the ones that fail. *A baseline is only good against the
>    question it was asked.*
```

Both runs otherwise agree byte for byte: **5778 of 5778 cases answer the same in both builds,
without a panic**, before and after.

**`fuzze-erzeuger.py`** — the only substantive line added:

```
before:  66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
after:   66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
         61 of those 61 COMPILE under the gate -- 0 do not, and each one is a FORM-LEVEL defect:
            none. Every lowered baseline compiles, so every shape-2 finding below
            is the swept VALUE's own doing.
```

`-- 2. THE C DOES NOT COMPILE --` reads **0** in both runs, so the `formkrank`/`auf_form`
split this change adds to that section's report never has anything to divide — it is
present, correct, and currently silent for lack of a population. The two remaining diff
lines are noise (`/tmp/tmpXXXXXX` — a fresh temp directory per invocation).

## Why "0" is the right answer here, and not an empty test

The orphan commit's own payload was measured on a **different, unrelated tree**
(descended from `f718ca7`, not from `a053d3a`) where it found **"195 of 273 non-compiling
cases are three broken fixtures, counted 195 times; only 78 trace back to the swept value
itself."** Those three broken fixtures were not this lane's find to close, and this branch
does not attempt to identify them — `f718ca7`'s lineage and `a053d3a`'s lineage are siblings,
not ancestor and descendant (`git merge-base --is-ancestor a053d3a f718ca7` fails both ways).

This tree descends from `a053d3a` by way of `messung/ERZEUGERDEFEKTE.md`: six emitter
defects (`D1`-`D6`) found by an earlier `fuzze-erzeuger.py` sweep were repaired there,
`D1` and its walk-template baselines among them (`beispiele/gift/641` moved from
`-- erwartet: cc` to `-- erwartet: C001` — the descent through a `reserved` field now
refuses by name instead of reaching a compiler that rejects it). **The class of defect this
rescued change exists to catch has already been closed on this tree, by a different lane,
before this report was written.** Running the new diagnostic here and getting "0 broken
baselines" is the mechanism working correctly over a clean population, not the mechanism
finding nothing to say — the distinction the tool itself makes explicit
(`messung/VORRICHTUNGEN.md`:133 already credits this exact repair as done, from a lane six
hours after `a6f24eb` that could see the branch existed but does not touch
`fuzze-grenzen.py`'s source; this merge is what makes that credit true in `master`).

## A neighbouring staleness, named and not fixed here

`fuzze-grenzen.py`'s own "HOW FAR THE BASELINES WERE VALIDATED" block (pre-dating this
change) still reads: *"`walk-knoten`, `walk-levels` (`D1`, gift/641)... are sound for the
agreement property and unsound as example programs."* That was true when written. Since
`D1`'s repair, both baselines now **refuse by name at `emit`** rather than silently reaching
`cc` with bad C — "does not reach `cc`" is still literally correct, but "unsound as example
programs" overstates it: a named `C001` refusal is not the same failure as a silent
miscompile. Left as a finding for whoever next touches that block; fixing the wording is not
this report's claim to make.

## Verdict: HOLDS — merged

The change measures its stated object (whether a baseline clears the same gate its
descendants are held to) and nothing else; it does not change what the sweep measures, only
how honestly it attributes what it already found (`5778 of 5778` and `3443 of 3584` are
unmoved). Merged into this branch via `git cherry-pick -n a6f24ebf7e4abd61ad0ba56c0a603837ba25ae65`,
with one conflict resolved by hand in `fuzze-erzeuger.py` (this branch's `bericht()` had
grown a `halt_n` parameter for "net 8" in the meantime; both parameters now thread through
together).
