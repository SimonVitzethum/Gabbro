# «K3», a SECOND reading -- 2026-09-04, after two repairs the first reading caused

**The first reading is [`K3-BEFUND.md`](K3-BEFUND.md), and it stands. It is 0 of 8, and it
remains the honest one.** That document is frozen the way it was written -- nothing in it or
in [`k3-fragmente/`](k3-fragmente/) moved for this repair, and the two commands it names still
answer the same way:

```bash
git diff --stat 61a1b35 HEAD -- messung/K3-AUSWAHL.md messung/k3-fragmente/   # empty
git diff --stat 61a1b35 HEAD -- crates/                                       # NOT empty, now --
```

The second line is the whole difference between the two readings: the first was taken with
`crates/` untouched; this one is taken after `crates/` moved, on purpose, because of what the
first reading found. **This document exists so that the distance between "0 of 8, measured
before a repair" and "0 of 8, measured after two repairs" is stated rather than left to
whoever next runs the fragments and gets the same number.**

## 0. What changed under `crates/`, in one paragraph

`messung/K3-BEFUND.md` §4 named two defects and left both unrepaired, by the rule of that
lane. Both are fixed here:

1. **§4.1 -- `u64(x)` refused as `P002`.** The grammar already said a call whose path names a
   type IS the conversion (`SYNTAX.md`:588, 656-659); the reader had never been widened to
   reach that rule for a bare `u64(a)` (only `u64::max` parsed). Repaired in `parse.rs`
   (the reader), `m1.rs` (a new typing rule, `umwandlung_ruf`, with two refusals of its own --
   arity and argument type), `aufrufgraph.rs` and `kosten.rs` (so the conversion has a cost and
   an effect, the same way a record constructor does), and `emit.rs` (lowers to an ordinary C
   cast).
2. **§4.2 -- a named address space unequal to itself.** `Raum::Benannt(Ident)` derived
   `PartialEq` over `{ text, span }`, so two DECLARATIONS of the same named space never
   compared equal and the address-space rule in `m3.rs` refused a call passing `user` to
   `user`. Repaired with a three-line manual `PartialEq for Raum` in `ast.rs` that reads a
   named space by its text.

Full detail -- the pre-run against the unchanged checker, the cause verified in the code, what
each repair newly accepts measured over the whole corpus, and the probes and mutations added
-- is in the commit that carries this file, not restated here (W7: one register per fact).

## 1. The primary re-run -- the eight frozen files, byte-identical, against the repaired binary

```bash
for f in messung/k3-fragmente/K0*.gab; do ./target/debug/gabbro pruefe "$f"; done
```

| fragment | first reading (`K3-BEFUND.md`) | second reading (here) | changed? |
|---|---|---|---|
| K01 `allocinfo_start` | 3×`P002`, 4 err, 1 hint | identical | no |
| K02 `pool_pop_batch` | 4×`P002`, 5 err | identical | no |
| K03 `copy_from_user_iter` | 1×`P002`, 1 err | identical | no |
| K04 `lc_del` | clean parse, 1 err (`M137`) | identical | no |
| K05 `percpu_ref_init` | 1×`P002`, 1 err | identical | no |
| K06 `depot_pop_free_pool` | 3×`P002`, 7 err | identical | no |
| K07 `test_firmware_exit` | clean parse, 1 err (`E010`) | identical | no |
| K08 `test_func` | 2×`P002`, 4 err | identical | no |

**`check with 0 errors`: 0 of 8. `lower`: 0 of 8. Unmoved.** A corpus-wide sweep (below) over
all 658 previously-tracked `.gab` files, the eight K3 fragments among them, confirms this by
diff rather than by re-reading eight files by eye: comparing the unchanged checker's verdict
against the repaired one, byte for byte, **zero files changed verdict** -- the K3 fragments
are eight of the zero.

**Why the headline does not move, stated plainly and not left to be inferred:** both repairs
stand *behind* a `P002` in every fragment that could have shown them (K03, K08) -- the SAME
class of defect `K3-BEFUND.md` §3 already named and left alone by its own rule ("nothing under
`crates/` moves" after that measurement): ordinary kernel identifiers (`progress` in K03,
`index` in K08) collide with Gabbro's closed vocabulary and the reader refuses the file before
`M1` or `M3` ever reach the repaired code. **Two defects out of 37 walls, in files gated by a
THIRD, unrepaired defect, should not be expected to move a 0.** This is that expectation,
confirmed rather than assumed.

## 2. What the repairs actually do, measured on the fragments they were written for

The first reading's own §3 already answered the "what is really behind the `P002`" question
for the vocabulary collision, on throwaway renamed copies. This section repeats exactly that
method -- **rename only the one colliding identifier each fragment carries, nothing else, on a
throwaway copy that is not part of the corpus and is not committed** -- so that K03's and K08's
OWN diagnostics, the ones «K3» would have produced with a naming convention that did not
collide, can be read directly against the two repairs.

```bash
python3 - <<'PY'
import re, pathlib
def rename(quelle, wort, ersatz, ausgabe):
    text = pathlib.Path(quelle).read_text()
    pathlib.Path(ausgabe).write_text(re.sub(rf'\b{wort}\b', ersatz, text))
rename("messung/k3-fragmente/K03-copy-from-user-iter.gab", "progress", "fortschritt", "/tmp/K03-renamed.gab")
rename("messung/k3-fragmente/K08-test-func.gab", "index", "feldindex", "/tmp/K08-renamed.gab")
PY
```

*Not a fragment that was `pruefe`-clean and edited to make it look better -- the SAME finding
K3-BEFUND.md §3 reports (K03 "1 error -> 4", K08 "4 errors -> 16" on the unchanged checker),
carried through to the repaired one.*

### K03 `copy_from_user_iter`, renamed copy

| | unchanged checker | repaired checker |
|---|---|---|
| | `error: [E005] iter_from is written but appears in no effect` | *(same)* |
| | `error: [R008] copy_from_user_iter passes iter_from in space user to a parameter of mask_user_address declared user` | **gone** |
| | `error: [R008] copy_from_user_iter passes iter_from in space user to a parameter of access_ok declared user` | **gone** |
| | `error: [R002] iter_from is written, but the pointer carries no w` | *(same)* |
| **total** | **7 items, 4 errors, 0 hints** | **7 items, 2 errors, 0 hints** |

Both `R008` hits are exactly the defect: `iter_from : ptr<user, r> u8` reaches
`mask_user_address(p : ptr<user, r> u8)` and `access_ok(p : ptr<user, r> u8, ...)` -- the
*same* named space, refused against itself. **They are gone, and nothing else moved.** `E005`
and `R002` are unrelated, pre-existing authoring gaps the first reading already attributes to
itself (missing effect on a write, a parameter declared `r` where the C's own logic writes
through it) -- not to Gabbro, and not touched here.

### K08 `test_func`, renamed copy

| | unchanged checker | repaired checker |
|---|---|---|
| | `error: [P002] u64 is a word of the vocabulary` (line 271, `u64(ktime_us_delta(...))`) | **gone** |
| | `error: [P002] u64 is a word of the vocabulary` (line 279, `u64(test_repeat_count)`) | **gone** |
| | `error: [M119] test_case_array is declared nowhere` (line 259) | *(same)* |
| | `error: [M119] delta is declared nowhere` (line 282) | **gone** |
| | 10 further errors + 1 hint (`M129`, `M104`×3, `M101`×3, `S006`×2, `K003`) | *(same, unrelated)* |
| **total** | **31 items, 16 errors, 1 hints** | **31 items, 13 errors, 1 hints** |

Three lines move, not two: the second `M119` (*"`delta` is declared nowhere"*) was a
**cascade**, not an independent finding -- `let mut delta = u64(ktime_us_delta(...));` never
parsed, so `delta`'s own declaration never registered, and its use three lines later read as an
undeclared name. Repairing the parse removes the cascade with it. *A reader refusal that stops
a body from parsing hides everything downstream of it, including a second diagnostic that
looks unrelated until the first one is gone -- the same shape `CLAUDE.md` already names for a
measurement that stops at the first hit.*

**One new, real finding appeared and was then closed by the same repair, and that is worth its
own line.** An early version of the conversion's typing rule answered every `u64(x)` with the
FULL range of `u64`, discarding whatever `M1` had already proved about `x`. Against this exact
line --

```gabbro
static mut test_repeat_count : u32 in 1 .. 4294967295 = 1;
...
delta = delta / u64(test_repeat_count);
```

-- that produced `error: [M102] the denominator has range u64 and does not exclude zero`: a
correct refusal by the rule as first written, and an avoidable one, because
`test_repeat_count`'s declared lower bound of `1` already excludes zero and a WIDENING
conversion (`u32` into `u64`) cannot lose that fact. The typing rule was corrected to keep the
source's proved range across a conversion that provably cannot lose information (source bounds
fit inside the target's), and falls back to the target's full range only where they might not
-- the same conservative answer `M1` already gives float arithmetic that mixes widths and an
`opaque` carrier's hidden representation, now used only where it is actually needed. With that
correction, `M102` does not fire and the count above (13, not 14) is the one that stands.

## 3. The corpus-wide sweep this reading rests on

Every one of the 658 `.gab` files this branch carried before the repair (`beispiele/`,
`beispiele/gift/`, `messung/fragmente/`, `messung/proben/`, `messung/k3-fragmente/`, and
every other tracked corpus) was run through the unchanged checker and the repaired one, and
the two runs were diffed by file:

```
vorher=658 nachher=663 gemeinsam=658
NEU (nur nachher): 5       -- the two new pass tests and three new poison probes this repair added
WEG (nur vorher): 0
GEAENDERT (in beiden, anderes Ergebnis): 0
```

**Zero of the 658 previously-existing files changed verdict, in either direction.** No poison
probe's expected code moved, no clean example gained an error, and no fragment -- K3's own
eight included -- read differently than before. The only files whose numbers moved are the
five new ones this repair added on purpose (two pass tests, three poison probes -- see the
commit message for their names and expected codes). *A repair that is truly this narrow should
leave a sweep this wide unchanged, and reporting that it did is the measurement, not an
assumption standing in for one.*

## 4. What this settles and what it does not

**It settles that both repairs are real, work exactly as described against the actual K3
material, and cost nothing measurable elsewhere.** The renamed-copy comparisons in §2 are not
a different corpus -- they are the SAME eight files «K3» cut, with the ONE identifier each that
collides with the vocabulary renamed out of the way, exactly as the first reading's own §3
already did to see past that collision. Measured against that view, `R008`'s false refusal on
K03 and the conversion's `P002` on K08 are both gone, with nothing new broken.

**It does not settle, and was never going to, the headline in §1.** «K3» is 0 of 8 before this
repair and 0 of 8 after it, on the files as frozen, because the fragments that would show
either repair are gated by a third, different, and still-unrepaired defect -- the vocabulary
collision `K3-BEFUND.md` §3 measured and did not fix. **Two defects out of thirty-seven walls,
each hidden behind a third, were never going to move a denominator of eight.** Reporting that
the number did not move is the result this section exists to state, not a disappointment to
explain away.
