# The obligation manifest — the completeness half, measured before anything was built

**Running report.** Every finding is committed with the run that produced it.

Measured on `master` @ `94c9ac5`, built on `ki-pc-fisch-101:gabbro-mf`
(`cargo build --offline`, 5.04 s).

---

## 1. The question that had to come first

`messung/gabbrov/manifest-lage.sh` established on 2026-09-03 that **four of ten fragments
emit no manifest at all** and that **10 obligation lines stand against a population of 63**.
It did not say *which* of the two causes each missing line has, and the two are not one
defect:

| cause | whose defect |
|---|---|
| the checker refuses the file, so there is no register to emit | **not the manifest.** Another lane is repairing exactly these four for `H = 0` |
| the file checks clean, the register is emitted, and the obligation is not in it | **the manifest drops it** |

A number that mixes the two is worth nothing. So: the split, with its denominator.

## 2. The split — 63 = 43 + 15 + 5

Search path, three commands, all re-runnable:

```
./messung/gabbrov/manifest-lage.sh                    # per fragment: register or not
./instrumente/zaehle-pflichten.py --spalten           # `L` rows per fragment
./instrumente/zaehle-pflichten.py --gabbrov           # the three rebooked `progress` rows
```

| fragment | population (`L` rows − rebooked) | register? | obligation lines | of the population, lines |
|---|---|---|---|---|
| F01 | 17 | **no** — 3 checker errors | — | 0 |
| F02 | 5 | yes | 5 | **5** |
| F03 | 13 | **no** — 27 checker errors | — | 0 |
| F04 | 7 − 1 = 6 | yes | 1 | 0 |
| F05 | 10 − 1 = 9 | **no** — 4 checker errors | — | 0 |
| F06 | 5 | yes | 1 | 0 |
| F07 | 1 | yes | 0 | 0 |
| F08 | 2 | yes | 1 | 0 |
| F09 | 4 | **no** — 1 checker error | — | 0 |
| F10 | 2 − 1 = 1 | yes | 2 | 0 |
| | **63** | | **10** | **5** |

```
population                                             63
  blocked upstream -- the fragment emits no register    43   (F01 17, F03 13, F05 9, F09 4)
  in a fragment that DOES emit a register               20
      of these, an obligation line exists                5   (F02, all five)
      of these, the manifest DROPS it                   15   (F04 6, F06 5, F07 1, F08 2, F10 1)
```

**43 + 15 + 5 = 63.** The three rebooked `progress` rows (`F04`:886, `F05`:981, `F10`:1656)
leave the population as assumptions, not as obligations —
`instrumente/zaehle-pflichten.py --gabbrov` names all three.

**So the manifest's own defect is 15 of 20, not 53 of 63.** The larger number is somebody
else's repair, and booking it here would be the `W16` shape at the bookkeeping layer: a
measurement that counts a neighbour's hole as its own.

## 3. The reverse direction, and it is the sharper half

The ten emitted lines are not ten of the population. Mapped by hand against
`dokumente/PFLICHTEN.md`, whose anchors point at **`FRAGMENTE.md` at `708beed`** (1 686
lines) and not at today's file:

| emitted line | its clause | row at `708beed` | class |
|---|---|---|---|
| `Vtd :: transition setze_rtp requires` | `requires GSTS…` | F2 454–455 | **L** |
| `Vtd :: transition scharf_te requires` | `requires GSTS…` | F2 457–458 | **L** |
| `Vtd :: transition setze_irtp requires` | `requires GSTS…` | F2 460–461 | **L** |
| `Vtd :: transition scharf_ire requires` | `requires GSTS…` | F2 463–464 | **L** |
| `Vtd :: transition scharf_qie requires` | `requires GSTS…` | F2 466–467 | **L** |
| `VirtioPci :: reg QUEUE_SIZE requires` | `requires QUEUE_SIZE <= QMAX` | F4 764 | K |
| `unberuehrt :: ensures #1` | `ensures result <= s.len` | F6 1084–1085 | K |
| `toeten :: aufloesen requires #1` | `requires Held(SCHEDS, shared)` | F8 1421 / 1436 by text; 1427–1430 by anchor | K, and see below |
| `naechstes_token :: ensures #1` | `ensures result <= 9` | **no row** | — |
| `kerne_zaehlen :: loop invariant #1` | `invariant tiefe <= MAXTIEFE` | **no row** | — |

**Five of ten state an obligation the population contains. Not one of the other five does.**

### The F8 line is the instructive one — an anchor without a text identifies as little as an ordinal without one

`toeten :: aufloesen requires #1` sits at `messung/fragmente/F08.gab`:21, which is frozen
line 1429 — **inside** the `L` row `1427–1430`. By anchor alone it looks like a hit. Its
clause is `requires Held(SCHEDS, shared)`, and that row's obligation is *"the revalidation —
the thread may have vanished between selection and deed"*. **The two are different
statements.** What the clause says is what `PFLICHTEN.md` books at rows 1421 and 1436, both
`K`, both discharged by `H001`/`H006`/`E006`.

*So the anchor field alone would not have settled this line, and the ordinal field settles
nothing at all.* **The text is the field that decides**, and this is the measured argument
for it — the same shape as `O3`'s ordinal defect, one field further out.

### The two F10 lines stand in no row at all — the two sources have drifted

`ensures result <= 9` and `invariant tiefe <= MAXTIEFE` are **not in `FRAGMENTE.md`
at `708beed`**; they were added to `messung/fragmente/F10.gab` afterwards (the file says why
at `:26` and `:46`). The manifest is emitted from `messung/fragmente/F*.gab`; the population
is counted from the frozen `.md`. **They are two coordinate systems, and a line can exist in
one and in no row of the other.**

*That is not an argument against either file.* It is the reason a completeness check has to
name which side it counts — and why the guard prints both sides rather than a ratio.

## 4. Which fifteen are dropped, and why the emitter cannot see ten of them

| fragment | dropped rows | the clause | why no line |
|---|---|---|---|
| F04 | 773, 774, 775–776, 777–779 | `transition ack \| drv \| featok \| drvok` | the register books a `transition` only when it carries a `requires`; these four carry `effects` and none |
| F04 | 780–782 | — | **gap «B26»**: no placeholder for the pre-state, the clause is not writable |
| F04 | 836 | — | no clause says it |
| F06 | 1070–1072 | — | **gap «B14»** |
| F06 | 1094 | — | a `return` inside a `traverse`; no clause |
| F06 | 1129–1141, 1145–1158 | `check … claim "…"` | a `claim` produces no obligation |
| F06 | 1160 | `counterprobe … expects …` | no obligation line |
| F07 | 1289–1291 | — | a property of the PHASE; no clause states it |
| F08 | 1427–1430, 1439–1442 | `match` over `aufloesen` | the correctness of the branch carries no clause |
| F10 | 1631–1632 | `magie : u32 where magie == MAGIE` | a `format … where` produces no obligation line |

**Ten of the fifteen have no clause in the source at all.** For those a manifest line would
have to be *invented* — refused, and named here instead. **Five have a clause the checker
reads and the register does not book**: the four `transition`s without `requires`, and the
`format … where`. Those five are a separate decision from this lane's — a `transition`
without `requires` states a protocol step, not a promise, and booking it would change what
the `D` count means.

*The distinction is why this section stands here rather than a single number: fifteen reads
as fifteen repairable drops, and at most five are.*

---

## 5. The reader census — taken before the writer moved

`AUFTRAG-GABBROV.md` §4 puts the order of a format change in three steps and calls it *half
the rule*. Step zero is counting the readers, because the failure `CLAUDE.md` records is not
a loud one: **seven guards read a document, four went silently blind when it moved.**

**Three readers parse the plain register text.** Counted by sweeping the tree for every
distinctive string the emitter writes (`Obligation register`, `What a HUMAN still owes`,
`no generated proof obligation`, `obligations:`, each of the eight kind headings, the ` :: `
entry form, `has errors -- no register`):

| reader | what it reads | what a silent format change would do |
|---|---|---|
| `crates/gabbro-check/tests/beispiele.rs`:535 | three substrings of the F04 register | red, loudly — a test |
| `instrumente/pruefe-zahlen.py`:71 (`PFLICHTEN_SUMME`) | the `== N obligations: …` header, summed over `beispiele/*.gab` | **silent**: the pattern stops matching, the sum becomes `0`, and `0` travels to a green report |
| `messung/gabbrov/manifest-lage.sh`:39,44 | `no register` and `^== N obligations` | **silent**: every fragment reads as `0 obligations` — the very number this script exists to report |

**Two of the three go silently wrong**, and both in the direction that makes the manifest
look *emptier* than it is.

**Six tools and one test module read the SAME register through a different serialisation**
and are untouched by a change to `pflichten::zeige` — `refinement::verdicts` (`--isabelle`)
and `lean::verdicts` (`--lean`) both walk `pflichten::sammle`:

`instrumente/zaehle-p6.py` · `instrumente/pruefe-p6-beweis.sh` · `instrumente/zaehle-lean.py`
· `instrumente/pruefe-lean-beweis.sh` · `instrumente/miss-lean-gegen-isabelle.py` ·
`instrumente/miss-lean-reichweite.py` · `crates/gabbro-check/tests/rechenwerk.rs`

**Two registries know the subcommand and its flags** without reading the format:
`crates/gabbro-cli/tests/fahnen.rs`, `crates/gabbro-cli/tests/erstnamen.rs`.

*So: **3** readers to prepare, **7** siblings that share the register but not the text, **2**
registries. The number that mattered was three, and it was small enough that the ordering
rule cost almost nothing — which is the argument for keeping it, not against it.*

### Step 1 — the version field, and both silent readers now refuse

`pflichten::MANIFESTFASSUNG` writes `-- manifest-version 1` as **line one**, before the file
name. All three readers gained a gate on the same day, and the two silent ones were
speech-tested against a fabricated `-- manifest-version 99`:

```
GABBRO=/tmp/fakegabbro ./messung/gabbrov/manifest-lage.sh      -> exit 2, "NOTHING was measured"
<the awk of PFLICHTEN_SUMME over the same input>               -> exit 3, "nothing summed"
```

`cargo test --offline --no-fail-fast`: **401 passed, 0 failed** (400 at `94c9ac5`, plus the
new `das_register_traegt_seine_fassung_auf_zeile_eins`). `pruefe-zahlen.py` green.
