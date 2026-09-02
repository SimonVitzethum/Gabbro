# GabbroV V2 — the three rebookings, and the vacuity half

*Measured 2026-09-03 from tree `4e53df3`. `messung/GABBROV-V1.md` §6 costed two things and
built neither: a rebooking of three rows that are entered twice, and the cheap half of the
V2 gate. This file carries both. Every count below names the command that produced it.*

## The answer, up front

*(filled in as the run proceeds — this file exists from the first measurement, not from the
last one.)*

---

## 1. The three rebookings — verified, not taken over

`GABBROV.md` §5 and `GABBROV-V1.md` §6 claim that the ten fragments' three `progress` names
are **already** `assume` declarations, and that `PFLICHTEN.md` books each a **second** time as
a logic obligation. The claim was checked at three places rather than read.

### 1.1 The rule: a `progress` name MUST resolve to a declared `assume`

`SYNTAX.md`:1074, at the `forever` form:

> ***"`progress` names WHO ends it — an assumption about the environment, with a falsifier.
> The watchdog IS the falsifier."***

**And it is not only prose — the checker enforces it.**
`crates/gabbro-check/src/schleifen.rs`:221, `fortschritt_pruefen`:

```rust
match lg.annahmen.get(&z.text) {
    None        => absagen.schiebe(Absage::fehler("S003", …)),  // no declared assumption
    Some(false) => absagen.schiebe(Absage::fehler("S004", …)),  // unfalsifiable
    Some(true)  => {}
}
```

`S003` — *"`progress` names no declared assumption"* — is a hard error, and its note repeats
the rule: *"otherwise it is a hope with a keyword in front"*. `S004` adds that the assumption
must be falsifiable. **So the set of legal `progress` names is a subset of the declared
assumptions, by construction of the checker.**

### 1.2 Exactly THREE, and the count is against the FROZEN text

`PFLICHTEN.md`'s population is *"the ten ```gabbro blocks of `FRAGMENTE.md` @ `708beed`"*.
Counting `progress` in today's file gives **five** — and two of the five were written after
the freeze and are outside the population. The count has to be taken where the population is:

```
git show 708beed:dokumente/FRAGMENTE.md | grep -n "progress"
```

| frozen line | clause |
|---|---|
| 887 | `progress    device_completes_or_faults` |
| 981 | `progress    client_calls_or_endpoint_revoked` |
| 1656 | `progress token_verbraucht` |

*(884, 1239 are prose about the keyword, not clauses.)* **Three. The claim holds — but only
because it was checked at `708beed`; the same grep on `HEAD` answers five.**

| the `assume` in the source | `progress` at | `PFLICHTEN.md` row | anchor |
|---|---|---|---|
| `messung/fragmente/F04.gab`:33 `device_completes_or_faults` | :887 | **L42** (line 237) | 886 |
| `messung/fragmente/F05.gab`:87 `client_calls_or_endpoint_revoked` | :981 | **L46** (line 260) | 981 |
| `messung/fragmente/F10.gab`:62 `token_verbraucht` | :1656 | **L66** (line 383) | 1656 |

The `L42`/`L46`/`L66` numbering was **read off** rather than taken over: the `L` rows of
`PFLICHTEN.md` enumerated in file order with the tree's own `_zellen` parser put the three
progress rows at ordinals 42, 46 and 66 exactly. *`GABBROV-V1.md` gives L42's anchor as 887;
the row's own anchor is **886** — the `forever` head, not the `progress` line. One line, and
it is corrected here rather than carried.*

`F10.gab`:60 states the rule in its own words as the reason its `assume` is there at all:
*"`progress` nennt eine Annahme mit Falsifikator; ohne `assume` steht der Name in keinem
Manifest."*

### 1.3 The measurement nobody asked for: the EMITTED manifest does not double-book

`GABBROV.md` §2 rests the whole design on one sentence — ***"GabbroV does not read the Gabbro
program. It reads the manifest."*** So the question that decides what needs correcting is not
what `PFLICHTEN.md` says, but **what the binary emits.**

```
./target/debug/gabbro annahmen  messung/fragmente/F04.gab
./target/debug/gabbro pflichten messung/fragmente/F04.gab
```

| fragment | `gabbro annahmen` | `gabbro pflichten` |
|---|---|---|
| F04 | `A1 device_completes_or_faults  assume  ungedeckt` | **1 obligation**: `VirtioPci :: reg QUEUE_SIZE requires`. *No progress row.* |
| F05 | `A1 client_calls_or_endpoint_revoked  assume` | *no register — the fragment has errors (`N041`, `M134`)* |
| F10 | `A1 token_verbraucht  assume  ungedeckt` | **2 obligations**: `naechstes_token :: ensures #1`, `kerne_zaehlen :: loop invariant #1`. *No progress row.* |

> **So the double-booking is not in the manifest at all. It is only in the hand-kept
> document.** The assumption channel carries all three names; the obligation channel carries
> none of them. **The tool already holds the opinion the rebooking argues for** — what is
> wrong is `PFLICHTEN.md`, and nothing that GabbroV would ever read.
>
> *That sharpens `GABBROV.md` §5, which says the three are booked twice "here and under
> `obligation`". They are booked twice in `PFLICHTEN.md`'s `L` column and in the assumption
> manifest. `obligation`, as the binary emits it, was never one of the two places.*

**Verdict on claim 1: VERIFIED, and by a stronger witness than the one offered.**

### 1.4 `PFLICHTEN.md` is HAND-KEPT, so the file is the right place to edit

The mandate's caution — *if a tool produces it, the tool is what needs the change* — was
answered by search before any edit:

```
grep -rn "PFLICHTEN" --include=*.py --include=*.rs --include=*.sh .    # 14 files
```

Every one of the fourteen is a **reader**. No `write_text`, no `open(…, "w")`, no shell
redirection into `dokumente/PFLICHTEN.md` exists in the tree. **The file is hand-kept, and an
edit to it stands.**

### 1.5 The counts, re-measured and NOT subtracted

```
./instrumente/zaehle-pflichten.py --spalten
```

| | |
|---|---|
| anchored | 229 = **163 K** + **66 L** |
| lowering rows | 10 = 10 K + 0 L |
| **total** | **239 = 173 K + 66 L** |

> **The re-measurement caught a number that was already wrong, before any rebooking.**
> `GABBROV.md` §1 says ***"164 K against 66 L"***. The tree measures **163 K** anchored and
> **173 K** in total. `164` is neither. *It is, however, exactly what the counter's own speech
> probe produces when an escaped-pipe row is miscounted:* `Sprechprobe: ok (eine Zeile mit
> maskierter Pipe zaehlt mit: K 163 -> 164)`. **The mandate said re-measure rather than
> subtract; this is the row that shows why.**

### 1.6 And the `L` count does NOT move — the tree's own convention says so

The obvious move is to take the three rows out of the `L` column, and it is the wrong one.
**`PFLICHTEN.md`'s third column is not "obligation vs assumption".** Its own legend:

> **K / L** — plumbing / logic, by the criterion of `BEWEIS.md`: *mentions only the MACHINE →
> K; mentions the SUBJECT → L*

These three mention the device, the client, the token — the **subject**. They are `L` by the
criterion, and rebooking who *discharges* them does not change what they *mention*.

**And the file already has the rule for a discharged row**, stated in the counter's own
docstring:

> *"A struck-through class counts too — `~~K~~ **zu**` is a CLOSED obligation, not a removed
> one. That is the opposite rule from `gap:`, and on purpose: **a withdrawn gap is no
> obligation, a discharged obligation still is one.**"*

So: **239 / 173 / 66 stands after the rebooking, and that is a measurement, not a
preservation.** Re-run of `zaehle-pflichten.py --spalten` after the edit is in §1.8.

**What moves is the fourth column**, and it moves *into* the schema rather than out of it.
Column four's legend is *"a refusal code of a **present-day** pass, or a named gap"* — and
`S003`/`S004` are refusal codes of a present-day pass. The neighbouring row is already written
that way:

```
| 885–889 | the poll terminates and the overflow is NAMED | K | `S001`/`S002` |
| 886     | it ends because **the device** completes or faults | L | the human — … |
```

*Two adjacent rows about the same `forever` loop, one discharged by a pass and one by "the
human" — and the second has a pass too.*

### 1.7 So what does "10 → 8" mean, measured rather than asserted

It is **not** a statement about `PFLICHTEN.md`'s columns. It is a statement about **GabbroV's
obligation population**, which is the `L` rows minus the rows that are not obligations:

| | | source |
|---|---:|---|
| `L` rows of the ten fragments | 66 | `zaehle-pflichten.py --spalten` |
| of these, discharged by the assumption layer | 3 | L42, L46, L66 — §1.2 |
| **GabbroV's obligation population** | **63** | |
| of the 63, not sayable in the fragment | **8** | L11 L12 L13 · L24 L34 L50 L52 · L57 |
| of the 63, sayable | **55** | |

Read off `programmlogik/gabbrov/V1.lean`'s own census block rather than subtracted:
`nichtSagbar` lists ten in four classes; the class *"environment liveness — an `assumption`
(§5), not an `obligation`"* holds `["L42", "L46"]` and is the class that leaves. **8 remain,
in three classes.** L66 leaves from the *sayable* side, so the sayable count moves 56 → 55.

> **And the finding `GABBROV-V1.md` put under the ten survives intact.** The four ordering
> rows — L24, L34, L50, L52 — are untouched by any of this. *The rebooking makes the number
> smaller and the gap exactly as wide as it was.*

### 1.8 The edit, and the re-measurement AFTER it

The three rows now carry the rebooking in their fourth column, struck through rather than
overwritten (`~~the human~~ — **REBOOKED 2026-09-03** …`), each naming the `assume`, its
`falsifier`, `S003`/`S004`, and the two binary channels that disagree with the old entry.

```
./instrumente/zaehle-pflichten.py --spalten     # AFTER the edit
  verankert  229 = 163 K +  66 L
  insgesamt  239 = 173 K +  66 L
```

**Unchanged, and that is the result rather than a relief** — the class column was never the
thing that was wrong.

> **And a guard moved, from my own report file rather than from the rebooking.**
> `pruefe-zahlen.py` went red:
>
> ```
> BEFUND  TODO.md: „Dateien, die der Widerrufwaechter liest" steht als 182, der Lauf sagt 183
> ```
>
> **Cause measured by removing the file and re-running**, not guessed: `pruefe-widerruf.py`
> globs `messung/*.md` (`:263`) as well as `dokumente/*.md` (`:243`), so *this file* moves the
> count. `TODO.md`:556 carries it as a guarded number; corrected 182 → 183, and
> `pruefe-zahlen.py` is exit 0 again.
>
> *`GABBROV-V1.md` §2 hit the same thing one directory over, and wrote it down as the reach of
> a new `dokumente/*.md`. It is wider than that: **a new `messung/*.md` does it too.** The
> guard for the document you are adding is a number about a different guard's reach.*

---

## 2. Vacuity — the cheap half of V2

*(in progress)*
