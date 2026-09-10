# What the manifest carries per obligation kind — the text field, measured

**Running report, Lane M, 2026-09-10.** The mandate was *"every emitted obligation
line carries name + class + TEXT"*. Measured first: the field already exists —
`pflichten.rs::zeige` writes Fassung 2 since 2026-09-03
(`obligation<TAB>name<TAB>class<TAB>anchor<TAB>state<TAB>text`), and
[`MANIFEST-COMPLETENESS.md`](MANIFEST-COMPLETENESS.md) §5–§7 carries the build.
What this file adds is the per-kind record: **where each kind's text comes from**,
one verbatim example line each, and today's completeness figure.

Search path (all re-runnable, all against the prebuilt binary):

```
for f in beispiele/*.gab messung/fragmente/F*.gab; do ./target/debug/gabbro pflichten "$f"; done
./instrumente/pruefe-manifest.py            # E1 outer: 43 of 63 reach no manifest line
./instrumente/pruefe-manifest.py --sprechprobe
```

## 1. One line, six fields

```
obligation<TAB>name<TAB>class<TAB>anchor<TAB>state<TAB>obligation text
```

`name` is `function :: subject`; `class` is the kind letter below; `anchor` is
`file:line` of where the obligation ARISES; `state` is `open` (the only value —
GabbroV writes `passed`/`refuted` back); `text` is the predicate/contract wording,
cut from the source by `zeremonie::schnitt_bis` (whitespace folded to single spaces,
hard stop at 400 characters with `...`). The folding lives in one routine shared
with the assumption manifest — one cut, two limits, never two routines.

## 2. Per kind: where the text comes from

| class | kind | name shape | text source | anchor |
|---|---|---|---|---|
| `R` | refinement | `f :: refines g` | body of the `spec fn` `g` names (`spezpraedikate` lookup) | the `refines` clause |
| `E` | preservation | `f :: <invariant>` | body of the named `spec fn`, else of the `table`/`group` `invariant` it names | the `maintains` clause |
| `N` | postcondition | `f :: ensures #n` | the `ensures` clause itself | the clause |
| `F` | foreign duty | `f :: ensures #n` | the `ensures` clause itself (at a body Gabbro never sees) | the clause |
| `V` | precondition at call site | `caller :: callee requires #n` | the CALLEE's `requires` clause — the one kind where text and anchor differ | the CALL SITE |
| `D` | device promise | `dev :: reg <r> requires` | the `requires` clause | the clause |
| `D` | device promise | `dev :: transition <t> requires` | the `requires` clause (the GUARD) | the clause |
| `D` | device promise | `dev :: transition <t>` | the `transset` first-to-last step (the MOVE, e.g. `GCMD.SRTP: 0 -> 1`) | the item |
| `S` | loop invariant | `f :: loop invariant #n` | the invariant predicate | the clause |
| `W` | unowned invariant | `w :: down` | node type through guard end (`roh when !it.PS` — the type is half the statement) | the `down` clause |
| `W` | unowned invariant | `w :: leaf` | the leaf predicate | the `leaf` clause |
| `W` | unowned invariant | `w :: invariant <name>` / `<t> :: invariant <name>` | the invariant predicate | the clause |

Examples, verbatim from today's runs (tabs rendered as two spaces):

```
obligation  unlink :: cdt_wohlgeformt  E  messung/fragmente/F01.gab:266  open  forall s in slots of c : c.slots[s] reaches WURZEL via parent
obligation  unlink :: ensures #1  N  messung/fragmente/F01.gab:263  open  c.slots[s].parent == None
obligation  boot_ende :: ensures #1  F  beispiele/07-eintritt-und-boot.gab:135  open  !exists m in mappings of kern_wurzel : m.rahmen >= BOOT_RAHMEN_UNTEN && m.rahmen < BOOT_RAHMEN_OBEN
obligation  einsammeln :: blatt_loeschen requires #2  V  beispiele/01-tabelle.gab:140  open  c.slots[s].benutzt
obligation  freigeben :: refines ist_frei  R  beispiele/50-verfeinerung.gab:47  open  !Buch.slots[p].belegt
obligation  Vtd :: transition setze_rtp requires  D  messung/fragmente/F02.gab:79  open  GSTS.TES == 0 || GSTS.RTPS == 1
obligation  Vtd :: transition setze_rtp  D  messung/fragmente/F02.gab:78  open  GCMD.SRTP: 0 -> 1
obligation  einsammeln :: loop invariant #1  S  beispiele/01-tabelle.gab:138  open  c.slots[s].benutzt
obligation  Seitenabstieg :: down  W  messung/fragmente/F09.gab:118  open  roh when !it.PS
obligation  CapSpace :: invariant wurzel_ohne_vorgaenger  W  messung/fragmente/F01.gab:236  open  forall s in slots of Self : Self.slots[s].parent == None => Self.slots[s].prev_sibling == None
```

Two rows worth a second look, because the text is NOT cut from the line that
names it: `E`/`R` carry a NAME (`maintains baum_wohlgeformt`), and cutting it
would print the name twice and leave the reader in the dark. The wording is
resolved behind the name — first in the unit's `spec fn`s, then in its
`table`/`group` invariants. And `V`'s anchor is the call site while its text is
the callee's clause: two calls to the same callee yield byte-identical names,
and the anchor is the field that tells them apart.

## 3. Completeness, measured 2026-09-10

124 obligation lines over `beispiele/*.gab` + `messung/fragmente/F*.gab`:

| | |
|---|---|
| lines with an anchor | **124 of 124** |
| lines with a text | **124 of 124** (no `--`, no empty field) |
| texts truncated | **0** (longest 131 characters; the limit is 400) |
| header-vs-body divergence (inner E1) | **0** (`pruefe-manifest.py` reports none) |

`--` stays a possible value with a named reason beside the closing count: a run
with no source (anchor and text unknowable — inventing either would be worse
than saying so), or a `maintains`/`refines` name that resolves to no `spec fn`
and no `table`/`group` invariant in the unit. Neither occurs in the corpus
above. *An empty field with a reason is a statement; the name printed twice to
fill the column would be a guess.*

## 4. What this lane did NOT move, and why

E1 outer stands at **43 of 63** — unchanged, and the five `DROPPED` rows of
[`PFLICHTEN-KORRESPONDENZ.md`](PFLICHTEN-KORRESPONDENZ.md) §6 are none of them a
missing text field:

| row | clause | price, and why it is not emission work |
|---|---|---|
| 15 | F01's own `requires`, no caller | a fourth `Material` variant — `Material`'s docstring makes that a compile error at every goal site, and `lean.rs` matches `Art` with no wildcard (verified at `lean.rs:3811-3903`): it breaks files this lane must not touch. REPORTED |
| 53–55 | F06 `claim` / `counterprobe` | a ninth `Art` — same compile error in `lean.rs` — and the population's own rule points the other way: a `claim` with a `can_fail` block is an assumption with a falsifier, the shape `--gabbrov` books OUT of the 63. REPORTED |
| 63 | F10 `format … where` | DISCHARGED (`emit.rs` lowers it into the decoder) — a line for it would read `open` and be false. Correctly unbooked |

No new diagnostic code was added: no new refusal exists, so none is reported
either. The 13 `BLOCKED` rows belong to the F03 repair (another lane holds
`messung/fragmente/`); the 25 `NO CLAUSE` rows need language or fragment
changes. *Seven true lines were never on offer here, and five invented ones
would have made the gate greener and worth less.*
