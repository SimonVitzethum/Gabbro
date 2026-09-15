# A guardian that runs LEAN over every export

**Opus lane `waechter-export`. 2026-09-15.** Branch `worktree-agent-a0b37ba4c68c8380f`, base
`efaa4db3`. Every `cargo`, `lake` and `lean` run below was measured on `ki-pc-fisch-101`,
directory `gabbro-opus-wex`.

## 0. Files touched — the whole list, at the top

| file | why |
|---|---|
| `instrumente/pruefe-exportlean.py` | **new** — the guardian |
| `grammatik/Grammatik/Export108.lean` | the stale partial paste refreshed, and given a marker so a guardian can see it |
| `grammatik/Grammatik/GenOblig104.lean` | **regenerated** — it was stale, and `pruefe-genlean.py` had been arriving at `master` RED over it |
| `grammatik/Grammatik/GenOblig108.lean` | the same |
| `README.md` | the guardian row: 43 → 44, 69/72 → 70/73 |
| `messung/RUECKLAUFWERTE.md` | the two figures `pruefe-zahlen.py` binds to `pruefe-waechter.py`: 66/72 → 67/73, 414 → 427 exit sites, with the measured baseline beside them |
| `messung/muse/OPUS-BERICHT-WAECHTER-EXPORT.md` | this report |

**Nothing else.** In particular `crates/` was **not touched at all** — not `lean_g.rs`, not
`obligations_g.rs`, not `m1.rs`, not `saetze.rs`, not `MARKE_EMIT`, not one test. `Parser/`
untouched. No diagnostic code and no gift number was taken. The two `GenOblig*.lean` are
**generator output**, replaced by exactly what `gabbro obligations --g` writes today — not
edited by hand, and `pruefe-genlean.py` says so byte for byte.

---

## 1. THE HEADLINE

| | |
|---|---|
| exports the guardian checks today | **24 of 24 elaborate** (12 programs × 2 generators) |
| corpus programs swept | **113**, of which `lean-g` accepts 12 and refuses 101; `obligations --g` the same 12 |
| committed partial pastes compared | **1** (`Export108.lean`) — and it had **drifted** |
| cost | **10,1 s wall, 807 MB peak RSS** with the model built; the `lake build` of `grammatik/` is the precondition, 0,1 s warm and 2 min 20 s / 6,4 GB cold |
| where it belongs | **`abnahme.py --schnell`** — it needs no entry anywhere, the cast comes from the directory |

**The tree is green today, and that is a statement about today.** The four exports that never
typechecked were repaired by the lane before this one (`messung/muse/OPUS-BERICHT-EXPORT.md`
§2.4); what was missing was the instrument that notices when the next one breaks. The red
direction below puts that defect back and measures the guardian finding it — 8 findings over
4 programs — and then restores the source byte for byte.

---

## 2. What the guardian does, and why it is not the guardian next door

`instrumente/pruefe-genlean.py` (yesterday's) holds every **committed generated** Lean file
against its generator **byte for byte**. That closes the staleness loop and it is text all the
way down by design.

**This one asks the other half, and it is the only reader in the tree that runs the
elaborator over the exporter's output.** For every corpus program it runs both generators,
writes what they hand out into a scratch tree, and puts each file through `lake env lean`:

```
beispiele/*.gab ──► gabbro lean-g          ──► scratch/*.lean ──► lake env lean ──► green
                └─► gabbro obligations --g ──┘
```

**A refusal is not a finding.** 101 of 113 programs are refused, and the exporter is required
to refuse a form it has no G counterpart for. What is a finding is what the generator
**handed out** and Lean will not take. Four shapes, and three of them survive a bare exit-code
test:

1. an accepted export that Lean answers with an `error:` line;
2. an export that elaborates only through a `sorry` — Lean's exit code is **0** for that;
3. an export that decides something by `native_decide` — exit code 0 as well;
4. a generator that leaves with **0 and writes nothing**: an empty file elaborates green, and
   an emitter that swallows a program looks exactly like one that refuses it.

A generator exit outside `{0, 1}` is a finding too — *a crash is not a refusal.*

### 2.1 The five requirements, each in its place

| # | requirement | how |
|---|---|---|
| 1 | **deadline** | `FRIST=120` per generator run, `LEAN_FRIST=300` per `lake env lean`, `BAU_FRIST=1800` for the model build. Every one of them leaves with **2**, never with a silent pass |
| 2 | **two-way speech test** | 16 text directions + **3 through the elaborator**, on invented files — §3 |
| 3 | **red on abort** | six preconditions (no binary, stale binary, no Lean, model red, empty population, nothing accepted) each print `ABBRUCH` and return **2**; `1` is reserved for a finding. `abschnitt.fahre` announces a cut mid-run |
| 4 | **work quantity beside the verdict** | `24 of 24 exports checked, 0 Lean errors, 1 pasted block(s) compared, 0 findings in all, 212437 bytes elaborated or compared`, with the accepted/refused split per generator above it. An empty population is an **ABBRUCH**, not a green run |
| 5 | **pinned locale** | `LC_ALL=C` on every subprocess — this guardian reads a foreign tool's *message*, and a translated `error:` is an error that does not exist |

`./instrumente/pruefe-waechter.py` reports `ok pruefe-exportlean.py` on the static half.

### 2.2 Four things that cost a run each, and are written into the file

* **`lake env lean`, not a bare `lean`.** Measured: the `lean` on `PATH` is a different
  toolchain from the one that wrote the `.olean`, and it answers `incompatible header` for
  every export alike — *twelve identical failures that say nothing about the exports.*
* **The model is built FIRST, and a model that does not build is an ABBRUCH.** Otherwise every
  export falls for the model's reason and the run reads as twelve findings about the exporter.
* **The scratch tree is neither `/tmp` nor inside `grammatik/`.** `/tmp` is RAM on the
  orchestrator; a `.lean` dropped under `grammatik/` is a module `lake` builds — the same class
  as a scratch `.gab` inside `beispiele/`. It lives in a `mkdtemp` under the gitignored
  `.claude/` and is removed at the end, so two runs cannot read each other's files.
* **An abort names itself on STDERR as well as on stdout.** `abnahme.py` reads an abort's
  reason from stderr and otherwise quotes the guardian's LAST stdout line — which here is the
  shared cut notice, a pointer to a document. Measured in a collective run the same day: the
  row read *`ABBRUCH pruefe-exportlean.py [2] messung/RUECKLAUFWERTE.md, Abschnitt …`* while
  the real reason (a binary older than its sources, after an `rsync`) stood four lines above.
  **And the `return 2` stays spelled out at every call site** rather than folded into the
  helper: `pruefe-waechter.py`'s cut sieve looks for a literal `return 2`, and *a tool that
  hides its exits from the tool that counts them measures itself smaller.*

---

## 3. The speech test, and BOTH directions on the real object

### 3.1 In the guardian, every run

```
== Speech test -- on invented output, in both directions ==
  probe: ok   an `error:` line is read as a finding
  probe: ok   an `info:` line is NOT -- a model that prints its axioms is green
  probe: ok   the word 'error' in PROSE is not an error line
  probe: ok   the scratch path is stripped -- the finding names the EXPORT, not a temp dir
  probe: ok   a `sorry` is a finding although Lean leaves with 0
  probe: ok   and with the OTHER quoting too -- the toolchain picks it, not this reader
  probe: ok   `native_decide` in the export is a finding
  probe: ok   exit 0 with text is an ACCEPTED export
  probe: ok   exit 0 with NOTHING is a finding, not an export
  probe: ok   exit 1 is a REFUSAL and not a finding
  probe: ok   any other exit is a finding -- a crash is not a refusal
  probe: ok   a PASTE marker names its generator, its program and its block
  probe: ok   and a file without one is not a paste
  probe: ok   the block is cut at its OWN `end`, not at the first one
  probe: ok   a block that is not there comes back as absent, not as empty
  probe: ok   one line changed is a DIFFERENT block

== Speech test through the ELABORATOR -- the defect of 2026-09-15, both ways ==
  probe: ok   an export that IS well formed goes through (both halves parenthesised)
  probe: ok   and the defect of 2026-09-15 FALLS -- `nomatch` swallowing the second field
  probe: ok   a `sorry` falls although Lean leaves with 0
```

The Lean half is the defect of 2026-09-15 spelled out on invented text: a two-field structure
over `Empty`, built once with both halves parenthesised (must go through) and once without
(must fall, and fall with *`Insufficient number of fields`* and not with something else).
*One direction alone passes with an elaborator that refuses everything, and the other alone
with one that is never asked.*

> **A defect found on the way, in the guardian's own reader.** Lean 4.33 writes
> ``declaration uses `sorry` `` with **backticks**; the first pattern knew only the
> apostrophe form and the `sorry` probe went red. A pattern that knows one of the two would
> have stopped matching at the next `lean-toolchain` bump — **silently**. Both spellings are
> matched now, and both have a direction of their own.

### 3.2 RED on a planted broken export, and green after restoring it

The plant is the historical defect itself, put back into `lean_g.rs` **on the server copy
only** (the local worktree's `lean_g.rs` was never edited — another lane holds that file):

```
def gSp0 : Speicher gD :=
-  ⟨({slots}), ({globs})⟩          the repair
+  ⟨{slots}, ({globs})⟩            the defect of 2026-09-15
```

`cargo build`, then the guardian:

```
rc=1
  BEFUND  130-derived-contract-pure.gab   lean-g           LEAN: …:138:2: error: Insufficient
          number of fields for `⟨...⟩` constructor: Constructor `Speicher.mk` has 2 explicit
          field, but only 1 was provided
  BEFUND  130-derived-contract-pure.gab   obligations --g  LEAN: … (the same)
  BEFUND  62-grenzwort-im-ausdruck.gab    lean-g / obligations --g
  BEFUND  69-integer-conversion.gab       lean-g / obligations --g
  BEFUND  73-sugar-widths.gab             lean-g / obligations --g
pruefe-exportlean: 24 of 24 exports checked, 8 Lean errors, … 8 findings in all
== EXPORTLEAN: 8 BEFUNDE ==
```

**Eight findings over exactly the four table-less programs** the original defect hit, each with
the program, the generator and the first thing Lean said. The source was then restored and
verified byte for byte:

```
1340de29621aac955cac71da5a479c8d09d9658a54641a83b9423386e3d9ce44  lean_g.rs   (restored)
1340de29621aac955cac71da5a479c8d09d9658a54641a83b9423386e3d9ce44  lean_g.rs   (before)
```

and the next run is `== EXPORTLEAN: GRUEN ==`, `rc=0`.

*The same two directions were driven over the paste half as well — §5.3.*

---

## 4. What it costs, and where it belongs

Measured with `/usr/bin/time -v` on `ki-pc-fisch-101`, whole run, model already built:

| | |
|---|---|
| wall clock | **10,1 s** (10,14 s and 9,95 s in two runs) |
| CPU | 126 % of one core |
| **peak RSS** | **807 MB** |
| work | 226 generator runs, 24 `lake env lean` runs, 3 speech-test elaborations, 1 block comparison |

**It belongs in `abnahme.py --schnell`, and it needs no entry to get there** — the cast is read
from the directory, so a new `pruefe-*` is in the collective run on the day it is written. It
is deliberately **not** put into `pruefe-waechter.py:SCHWER`:

* 10 s is a fifth of `pruefe-emission.sh` (13,7 s) and a twentieth of `pruefe-lean-beweis.sh`
  (194 s), and both of the Lean guardians already in the quick run do a `lake build` of their
  own;
* 807 MB stays under the 1-GB line `CLAUDE.md` draws for a local run;
* it writes into no source, so two runs cannot destroy each other.

**And the precondition is named rather than hidden.** The guardian needs `lake` and a
`grammatik/` that builds. On a machine without Lean — the orchestrator `ubuntu` is one, it has
no Lean at all — it prints `ABBRUCH: NO LEAN … NOTHING was measured` and returns **2**, which
makes the acceptance red with a named reason. *That is the state `pruefe-lean-beweis.sh`,
`-programm.sh` and `-pflichten.sh` are already in there;* the acceptance belongs on `fisch`,
as `CLAUDE.md` says. **A cold `lake build` costs 2 min 20 s and 6,4 GB peak** — that is the
model build, not this guardian, and it is paid once per tree by whoever builds `grammatik/`
first.

---

## 5. The tree as it stands today — the honest answer

### 5.1 Every accepted export elaborates

```
   `gabbro lean-g`:          12 accepted, 101 refused of 113 programs
   `gabbro obligations --g`: 12 accepted, 101 refused of 113 programs
pruefe-exportlean: 24 of 24 exports checked, 0 Lean errors, 1 pasted block(s) compared,
                   0 findings in all, 212437 bytes elaborated or compared
== EXPORTLEAN: GRUEN ==
```

The twelve: `104-referenz`, `108-disjoint-start-locks`, `109-lockfree-entry-roots`,
`118-sperrinvariante-erhaltung`, `119-sperrinvariante-bloecke`, `124-two-threads-private`,
`130-derived-contract-pure`, `15-own-traegt-beide-rechte`, `16-by-ops-am-feld`,
`62-grenzwort-im-ausdruck`, `69-integer-conversion`, `73-sugar-widths`.

**`obligations --g` accepts exactly the same twelve** — measured, not assumed: the sweep runs
it over all 113 and counts, and the accepted sets are identical. So "where it applies" is not
a judgement call this guardian has to make.

**Nothing was repaired in the exporter, because nothing was broken in it today.** The one
export defect this tree has ever had was found and fixed yesterday; this lane is the
instrument that keeps it found.

### 5.2 THE FINDING: `Export108.lean` had drifted, and nothing could see it

This is the one real defect this lane measured, and it is exactly the surface
`messung/muse/OPUS-BERICHT-PFLICHT.md` §8.4 named as uncovered:

> *"`pruefe-genlean.py` measures only files that carry the generator's first line.
> `Export108.lean` (a partial paste) is therefore NOT covered — deliberately, since it is not
> byte-comparable, but it is a real uncovered surface."*

**Measured, not supposed.** The file's own header said the block below it was *"pasted verbatim
from the output of `gabbro lean-g beispiele/108-disjoint-start-locks.gab`"*. Held against
today's output, the pasted block differed in **four places**:

| | paste | generator today |
|---|---|---|
| `requires` | `fun _ => .wahr` | a per-function match (`\| .read_a => .wahr \| .read_c => .wahr`) |
| `gLs` | absent | `def gLs : List gD.Lock := []` |
| `gCs` | absent | `def gCs : List (gD.Tab ⊕ gD.Glob) := [(.inl GTab.T)]` |
| `gSp0`, `gE` | absent | the declared initial memory and the `Einheit` |

*The sentence in the header had quietly become false.* None of it made a theorem wrong — the
three theorems in the file are true of the pasted `gP` either way — but the file claims to be
the exporter's output and was not, which is word for word the failure `pruefe-genlean.py`
exists against, one class further along.

### 5.3 The decision on `Export108.lean`: a MARKER, not a deletion — and the measurement that says so

The assignment asked for one of the two, with the measurement. **Delete as superseded was
measured and rejected:** `GenOblig108.lean` is indeed the same program exported whole, byte-
guarded, and it proves the same two checks (`programmImFragmentG`, `fussOrtGB`) plus
`gCheck` and `gP_gabbro` — but the NAMESPACE of `Export108.lean` is load-bearing in **three
other files**:

```
grammatik/Grammatik/ZeugnisKorpus.lean          c108_read_a / c108_read_c and 4 examples
grammatik/Grammatik/Nichtinterferenz/Korpus.lean k108L, k108Cs and 2 flow theorems
grammatik/Grammatik/Parser/UebersetzeAllg2.lean  the T3 chain holds its parsed declaration
                                                 against this one
```

Deleting the file means editing all three, and the third is `Parser/`, which a Muse lane holds.
*A deletion that costs an edit in a reserved file is not a cheap deletion.*

**A `pruefe-genlean.py` marker is impossible**, and that guardian says so itself: a partial
paste is not byte-comparable to a whole generated file, and claiming otherwise "would be worse
than not measuring".

**So the third option, and it is the one the measurement supports:** a marker of its own kind,
naming the BLOCK instead of the file —

```
-- PASTED from `gabbro lean-g beispiele/108-disjoint-start-locks.gab` block `G108_disjoint_start_locks`
```

— and `pruefe-exportlean.py` holds that one namespace against the same namespace of today's
output, byte for byte. **The comparison is exactly as well defined as the one next door**, one
namespace against one namespace, and the marker cannot be confused with `pruefe-genlean.py`'s:
that one counts only on line 1, this one stands anywhere else.

The drift was then repaired: the block was replaced with today's output (which needs the one
extra `import Grammatik.Zielsatz.Spec` the generator writes), the header rewritten to say what
the file is and why it is not simply replaced by `GenOblig108.lean`, and the three theorems and
the CUTS section below it kept unchanged. **`lake build` green, 254 jobs**, including all three
dependants.

**Both directions of the paste half, on the real object:**

* *red* — one word changed inside the pasted block (a comment, so that the model still builds):

  ```
  BEFUND  grammatik/Grammatik/Export108.lean: the pasted block `G108_disjoint_start_locks`
          is NOT what `gabbro lean-g beispiele/108-disjoint-start-locks.gab` writes today
          committed 4171 bytes, generated 4171 bytes, first difference at byte 3801
          committed …'every slot at ZERO,\n-- every globa'
          generated …'every slot at zero,\n-- every globa'
  rc=1
  ```

* *green* — after restoring (`sha256sum -c`: OK), `block G108_disjoint_start_locks is
  byte-identical … (4171 bytes)`, `rc=0`.

> **And one thing the plant taught, which is worth keeping:** the first attempt changed
> `count := fun | .T => 4` to `5` inside the block. That is a **semantic** change, and the
> guardian came back `2`, not `1` — because `lake build` of the model fails first, and the
> model failing is an ABBRUCH and not a finding. *The paste check catches drift the compiler
> cannot see; the compiler catches drift the paste check would only report. Neither replaces
> the other, and the ordering is the honest one: apparatus first, tree second.*


### 5.4 A SECOND finding, and it is not this lane's: the two committed generated files were stale

The collective run that was supposed to show the new guardian in place showed something else
as well:

```
  gruen          pruefe-exportlean.py         10.1 s [0]
  ROT            pruefe-genlean.py             0.0 s [1]  == GENLEAN: 2 BEFUNDE ==
```

**`pruefe-genlean.py` had been arriving at `master` RED**, over both files it guards, and
nothing had read it since it was written. What it found:

| | committed at `efaa4db3` | `gabbro obligations --g` today |
|---|---|---|
| the ledger comment | `pub` alone | `pub` **and `opaque`** |
| `gSig_einzahlen.boden` (104) | `none` | **`some 1`** |
| the `hb` proof beside it | `… cases h` | `… cases h; exact ⟨1, rfl, by decide⟩` |
| `gSp0` | `⟨fun t _ f => match …, (fun g => nomatch g)⟩` | both halves parenthesised |

The middle two are **the lock-floor repair** of the lane before this one
(`OPUS-BERICHT-EXPORT.md` §2.3) and the last is its `gSp0` repair — *the exporter moved and
the committed files did not, which is the exact sentence `pruefe-genlean.py` was written for.*
The committed text still typechecked and `Pflicht104.lean` still proved against it, so nothing
went red in the build; the file had simply stopped being about this tree.

**Repaired, because the measurement said it was free.** Both files replaced by exactly what
the generator writes today — `gabbro obligations --g > file`, no hand editing — and then:

| | |
|---|---|
| `lake build` over the whole library | **254 jobs, exit 0**, no error |
| `sorryAx` in the build log | **0** |
| `#print axioms gabbro_ziel` | `[propext, Classical.choice, Quot.sound]` — unchanged |
| `#print axioms p108_ziel`, `gabbro_ziel_zeuge` | the same three |
| `pruefe-genlean.py` | **`2 of 2 generated files byte-identical, 18927 bytes`, GRUEN** |

*A regeneration that needed a proof repair would have been the other lane's to make, and it
would have been named here instead. It needed none, so it is made.*

> **And it will go red again at the next exporter merge, by design.** The Opus lane widening
> `lean_g.rs` for `linear`/`tagged` types will change what these two files should contain;
> `pruefe-genlean.py` will say so on the day of the merge, and the resolution of a conflict in
> a generated file is to run the generator. *That is the guardian working, not a defect.*

---

## 6. Everything measured, and where

All on `ki-pc-fisch-101`, directory `gabbro-opus-wex` (`cp -a ~/gabbro-muse/stage/lake3` seed,
`lake` through `~/gabbro-muse/bin/lean-slot` for the cold build).

| measurement | result |
|---|---|
| `pruefe-exportlean.py --probe` | **19 of 19 directions ok**, exit 0 |
| `pruefe-exportlean.py` (full) | **24 of 24 exports, 0 Lean errors, 1 pasted block, 0 findings**, exit 0 |
| the same with the `gSp0` defect planted | **8 findings**, exit 1; source restored against SHA-256, green again |
| the same with one byte changed in the paste | **1 finding**, exit 1; restored (`sha256sum -c` OK), green again |
| `/usr/bin/time -v` over the full run | **10,1 s wall, 807 MB peak RSS**, 126 % CPU |
| `lake build` over `grammatik/` (cold, from the seeded cache) | 254 jobs, exit 0, **2 min 20 s, 6,4 GB peak** |
| `lake build` (warm, and after the `Export108.lean` repair) | 254 jobs, exit 0, 52 s then 0,1 s |
| `cargo test --no-fail-fast` (whole workspace) | **30 suites, 0 failed**, exit 0 |
| `./instrumente/pruefe-emission.sh` | **ALL PASS — 37 durchgestochen, 264 of 264 translate, 2 reverse probes**; ASan over 36 units, no finding. `MARKE_EMIT`/`_G`/`_M` untouched |
| `./instrumente/abnahme.py` (quick run, on `fisch`) | `gruen  pruefe-exportlean.py  10.1 s [0]` — it is in the cast without an entry anywhere. The run as a whole is red over the tree's own standing findings (17 ROT, 3 TEILMESSUNG, 5 ABBRUCH), which this lane did not touch; the one it did touch, `pruefe-genlean.py`, went from ROT to green (§5.4) |
| `pruefe-genlean.py` | ROT (2 findings) at the base, **GRUEN** here |
| `lake build` after the regeneration | 254 jobs, exit 0, `#print axioms gabbro_ziel` unchanged |
| `pruefe-waechter.py` | `ok pruefe-exportlean.py` — all static requirements; **70 of 73** carry them (was 69 of 72) |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none** — this lane wrote no Lean proof at all, and the Lean it did write is the generator's own output |

### 6.1 Guardian figures that moved, with their reason and their baseline

Measured in BOTH trees — `git archive HEAD` into a throw-away directory, the same guardian run
there — because booking one's own increment leaves a wrong number that looks booked.

| figure | baseline (`efaa4db3`) | here | reason |
|---|---|---|---|
| `pruefe-waechter.py` / instruments with all requirements | 69 of 72 | **70 of 73** | the new guardian |
| `pruefe-waechter.py` / can abort mid-run | 66 of 72 | **67 of 73** | the new guardian |
| `pruefe-waechter.py` / exit sites behind the first | 414 | **427** | its thirteen preconditions, each leaving with a spelled-out `return 2` |
| `pruefe-*` guardians | 43 | **44** | the new guardian |
| `abnahme.py` cast | 69 | **70** | read from the directory, no entry needed |

All five are booked — `README.md` and `messung/RUECKLAUFWERTE.md` — and `pruefe-zahlen.py`
reports **no finding** on any of them here.

**And one thing the baseline tree cannot do, named rather than glossed over:** a
`git archive HEAD` tree has no `.git`, so `korpus.py` fails open there and every guardian that
asks `git` measures a different population — `pruefe-todo.py` aborts at its own speech test in
that tree (*"README: '17' als saubere Beispiele — es sind 113"*, the untracked count) and
`pruefe-zahlen.py` reports nine findings that are the throw-away tree's, not the tree's. **So
the baseline comparison above was taken only with `pruefe-waechter.py`**, which reads
`instrumente/` as text and asks `git` nothing. *A baseline that measures the copying is not a
baseline.*

*Not booked, and named instead:* `pruefe-zahlen.py` reads **551** files for the revocation
guardian where `KENNZAHLEN.md` books 299, and this report makes it 552. **That figure was
already red at the baseline** (549 two lanes ago, 550 one lane ago); this lane moves it by +1
and does not re-cut the ledger, for the same reason the two lanes before it did not: writing
the number there would book a jump whose history this lane did not measure.

---

## 7. What this lane did NOT do, by name

* **It did not touch the exporter.** No `lean_g.rs`, no `obligations_g.rs`, no test. The
  widening lane running beside it owns those files.
* **It does not say the export is the RIGHT term.** Lean answers *"this is a well-formed
  `Einheit gD`"*, never *"this is the meaning of that `.gab`"*. That question is the chain
  count's (`zaehle-kette.py` sieve (a)), and this guardian sits upstream of it: a term that
  does not typecheck cannot be the right one.
* **It does not cover a paste that carries no marker.** The run prints that as a hole with a
  name — *a paste without a marker is seen by nothing, here or in `pruefe-genlean.py`.*
  `Export108.lean` was the only one in the tree; the next one has to ask for its marker.
* **It does not run the model's own proofs.** `lake build` is a precondition here, not a
  measurement, and a model that does not build is an ABBRUCH with that word.
* **It did not regenerate anything else.** Only the two files `pruefe-genlean.py` names, and
  only with the generator's own output.
* **It was not merged and not pushed.**
