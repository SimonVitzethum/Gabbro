# O3 — must the obligation NAME bind the obligation's CONTENT?

Running report. Lane: the subject of §15's ratchet (`SPRACHE.md` §15, `OFFEN.md` `O3`).
Worktree `.claude/worktrees/agent-adca48c751da1d8d3`. Started from `master` at `1cb66b0`;
**re-measured after merging `master` at `10856d8`** (the «B10» merge `e293a6c` plus the
unseen-port lane) — every figure below is from the MERGED tree, none carried across.
Built on `ki-pc-fisch-101:gabbro-nb` (`cargo build --offline`, 5.23 s); the sweeps run the
finished binary locally, `free -g` reading 31 GB total and 20 GB available.

- [x] 1. reachability — how many obligations carry an ordinal above 1, with the denominator
- [x] 2. has it already happened in this tree's history
- [x] 3. what the register itself relies on
- [x] 4. the options with their costs, the recommendation, and the cheap one built

---

## 1. Reachability — **28 of 113 for a swap, 79 of 113 for an insertion, 113 of 113 for an edit**

Measured 2026-09-03 at the merged `10856d8` over **every `.gab` in the tree bar
`beispiele/gift/`**: **184 units**, 135 of them emitting a register, **38 carrying at least
one obligation line**, and **113 obligation lines** in total.

> **The neighbouring 110 does not reconcile against the commit printed beside it, and that
> is worth saying rather than smoothing.** `messung/gabbrov/MANIFEST-COMPLETENESS.md` heads
> itself *"Measured on `master` @ `94c9ac5`"* and its field table says **110 of 110**. But
> `94c9ac5` is a **format-1** binary — built and swept for this report, it emits no
> `obligation` line at all, and its population is **100 lines over 36 units**. The
> difference from 100 to today's 113 is **exactly two files that gained a register**:
> `messung/fragmente/F01.gab` (+12) and `F09.gab` (+1), the `H = 0` lane's repair. *No
> other unit moved by a single line.* So the 110 was taken somewhere between the two,
> at a commit the document does not name — its header names the day's starting point, not
> each table's own stand. **This report's 113 is at the merged `10856d8`, and its
> search path is printed above it.**
>
> *`master`'s one new `.gab` since `1cb66b0`, `messung/proben/unseen-fat-reader2.gab`,
> checks clean and carries no obligation — so the 113 is unchanged by the merge, and only
> the unit count moved, 183 → 184.*

The name is built in `crates/gabbro-check/src/pflichten.rs`, and only three of the eight
kinds put an **ordinal** in it:

| kind | name shape | ordinal over |
|---|---|---|
| `N` / `F` | `<fn> :: ensures #n` | the function's `ensures` conjuncts (`pflichten.rs`:654) |
| `V` | `<fn> :: <callee> requires #n` | the **callee's** `requires` conjuncts (`pflichten.rs`:358) |
| `S` | `<fn> :: loop invariant #n` | the loops of the body, in source order (`pflichten.rs`:535) |
| `E`, `R`, `D`, `W` | `maintains I` · `refines g` · `reg X requires` · `invariant X` | — a NAME, no ordinal |

So there are three severities and they must not be reported as one number:

| | lines | what moves the mark |
|---|---:|---|
| **a swap of two siblings** | **28 of 113** | needs a sibling group of size ≥ 2 — there are **11 such groups over 6 files** |
| **an insertion or deletion among the siblings** | **79 of 113** | every ordinal-bearing line, *including the lone `#1`s*: write a new conjunct in front of `ensures #1` and `#1` now denotes the new one |
| **an edit of the text under an unchanged name** | **113 of 113** | also the four NAMED kinds — edit the body of the `spec fn` a `maintains I` points at, and `I` names something else |

The eleven permutable groups, in full:

```
3x  beispiele/01-tabelle.gab        aushaengen     :: ensures #
2x  beispiele/01-tabelle.gab        blatt_loeschen :: aushaengen requires #
3x  beispiele/01-tabelle.gab        einsammeln     :: blatt_loeschen requires #
3x  beispiele/09-ohne-zeiger.gab    einsammeln     :: blatt_loeschen requires #
2x  beispiele/53-zwei-orte.gab      treffen_oeffnen    :: ensures #
2x  beispiele/53-zwei-orte.gab      treffen_schliessen :: ensures #
2x  beispiele/56-auftragsring.gab   einreihen      :: ensures #
4x  messung/caprock/kapraum.gab     einsammeln     :: blatt_loeschen requires #
2x  messung/fragmente/F01.gab       delete_leaf    :: ensures #
2x  messung/fragmente/F01.gab       delete_leaf    :: unlink requires #
3x  messung/fragmente/F01.gab       unlink         :: ensures #
```

Class census of the 113: `N` 35, `V` 27, `D` 15, `E` 12, `F` 12, `W` 6, `S` 5, `R` 1.

**And the name IS a key today, just not a content-binding one:** no two lines inside one unit
carry the same name (0 of 113). The `V` duplicate `pflichten.rs`:55 warns about is still
latent, as that comment says.

**The number is not zero, in any of the three readings.** The cheapest reading (a swap) is
small — 28 of 113 — but the reading that matters for a ratchet is the middle one: an
obligation added to a contract renumbers every later one, and 79 of 113 lines carry a number
that an addition can move.

## 2. Has it already happened? — **No, and it could not have: the corpus has never edited a contract at all**

This is the question that outranks the rest, so it was measured exhaustively rather than
along `git log -- <path>` (which simplifies history and can drop a change that arrived
through a merge).

**Method.** `git rev-list --all` → **1091 commits** (the merged tree), each diffed against **every** parent,
every `.gab` on both sides parsed into per-function ordered conjunct lists, and consecutive
lists compared. Classification: `PERMUTATION` (same multiset, different order), `SHIFT` (an
ordinal that exists on both sides carries different text, both texts present on both sides),
`EDIT` (anything else).

```
modified-file pairs examined:  459
clause lists identical:        398
clause lists changed:            0

==== 0 distinct change(s) ====
```

**A detector that has never fired has measured nothing**, so it was driven in all three
directions against the very file `O3` uses — swapping `aushaengen`'s `ensures` conjuncts 1
and 3, inserting one at the front, and editing one in place:

```
base: ['c.slots[s].elter == None', 'c.slots[s].vorheriges == None', 'c.slots[s].naechstes == None']
  swap 1<->3        -> PERMUTATION
  insert at front   -> SHIFT
  edit conjunct #1  -> EDIT
SPRECHPROBE: ok
```

**Second, independent direction, with no parser in it.** A permutation must remove a line.
Over `git log --all -p --diff-filter=M -- '*.gab'` — every modification of every `.gab` file
that ever existed — there are **2 521 added lines and 282 removed ones**, and of the 282
**not one** contains `requires`, `ensures`, `maintains`, `invariant` or `refines`, and not
one is a bare conjunct continuation line either (they are `}`, `{`, `costs`, `traverse`,
`extern fn`, `lock`, `can_fail`, `return`). The removed lines are structural, never
contractual.

The two flagship carriers say the same thing one file at a time: `beispiele/01-tabelle.gab`
went through six revisions and `messung/fragmente/F01.gab` through five, and each carried
**exactly the same 11 and 16 conjunct slots, byte for byte, at every one of them.**

> **The finding, stated as it is:** in this tree's whole history no `requires`/`ensures`
> conjunct has ever been reordered, renumbered, or edited. A contract arrives with its file
> and never moves again. **So no `closed` mark stands on the wrong obligation today** — and
> no mark could have, because the write-back that would set one (`GABBROV.md` V4) is not
> built: `pflichten.rs::ZUSTAND` is the constant `"open"`, and all 113 lines say `open`.

*That is a statement about the past and about today, and about neither tomorrow nor the
corpus that V4 will be pointed at.* The corpus has been append-only because it is a
demonstration corpus; the moment an obligation is worked on rather than written down —
which is exactly what a `closed` mark implies is happening — the append-only habit ends.

## 3. What the register relies on today — one document does, and it names the most permutable line in the tree

**There is no ratchet.** `pflichten.rs::ZUSTAND` is the constant `"open"`; every one of the
113 lines says `open`, and `GABBROV.md`'s V4 — *"write-back into the manifest, ratchet over
names"* — is unbuilt. So the mechanism that would carry a `closed` mark across a swap does
not exist yet, and that is why the hazard has had no chance to show itself.

What does exist is a **hand-written verdict keyed on a manifest name**, and it happens to
be `O3`'s own example. `messung/GABBROV-V1.md` §4 tabulates five real manifest lines with
what each one means and where it stands, the first row being

> `aushaengen :: ensures #1` · `N` · *"…then `s'.world (.slot "c" f "elter") = .absent`.*
> **Carried today** — `duty_2` is a real theorem"

That row states the *content* (`elter`) beside the *name* (`#1`). Swap the conjuncts and the
row's two halves stop being about one thing. **This is not yet a soundness break** — see the
verdict measurement below — but it is the shape, standing in the tree, of exactly what a
ratchet would automate.

### The proof channel names goals by an ordinal too, and over a LONGER list

`refinement.rs`:134 and `lean.rs`:340 say it in the same words: *"`duty_7` — the number is the
position in the register `gabbro pflichten` prints."* So `duty_N` is an ordinal not over a
function's conjuncts but over the **whole unit's register**: adding any obligation of any kind
anywhere renumbers every later goal. *That is not a defect of those files* — both are
regenerated from the source on every run and carry the statement with them (`post_duty_2 :
Expr` is the term itself), so nothing there can go stale. It matters because it is where a
human reading a report picks up a name and writes it into a document that is **not**
regenerated. `messung/GABBROV-V1.md` is that document.

**How far that reaches, measured:** add ONE conjunct to `aushaengen` in
`beispiele/01-tabelle.gab` and **9 of 13 `duty_N` names denote a different obligation** —
across three functions and four kinds:

```
duty_5 : einsammeln :: baum_wohlgeformt          ->  aushaengen :: ensures #4
duty_6 : einsammeln :: loop invariant #1         ->  einsammeln :: baum_wohlgeformt
duty_7 : blatt_loeschen :: baum_wohlgeformt      ->  einsammeln :: loop invariant #1
duty_8 : blatt_loeschen :: ensures #1            ->  blatt_loeschen :: baum_wohlgeformt
duty_9 : einsammeln :: blatt_loeschen requires #1->  blatt_loeschen :: ensures #1
   … and duty_10 through duty_13 likewise
```

*The `#n` inside a name is the small ordinal; `duty_N` is the large one.* Both are
regenerated, so neither can go stale on its own — but a `duty_N` copied into prose ages the
moment anybody writes a clause above it.

### How much prose keys on a manifest name — 19 of 101, and 10 of those carry an ordinal

The 113 lines carry **101 distinct names**. Of those, **19 are quoted verbatim in
hand-written `.md` documents** — the ones nothing regenerates. **10 of the 19 carry an
ordinal, and 2 sit in a permutable sibling group.**

| | quoted in |
|---|---|
| **`aushaengen :: ensures #1`** — permutable, group of 3 | `AUFTRAG-GABBROV.md`, `GABBROV.md`, `OFFEN.md`, `GABBROV-AUDIT.md`, `GABBROV-AUFTRAG.md`, `GABBROV-V1.md` — **six documents** |
| **`einsammeln :: blatt_loeschen requires #1`** — permutable, group of 3 | `GABBROV-V1.md` |
| eight more with an ordinal, all `#1` in a group of one | `GABBROV-V1.md`, `GABBROV-V2.md`, `LEAN-REICHWEITE.md`, `RUMPFKANAL-ABSAGEN.md`, `MANIFEST-COMPLETENESS.md` |
| nine that carry a NAME and no ordinal | unaffected by a swap; affected by an edit of what the name points at |

*The two permutable ones are `O3`'s own examples, and one of them is written down in six
places.* That is not a live defect — no document claims a verdict a swap would falsify
today — but it is the surface a name-keyed ratchet would automate.

### And the neighbouring lane already measured the sharper half

`messung/gabbrov/MANIFEST-COMPLETENESS.md` §3: `toeten :: aufloesen requires #1` anchors at
`F08.gab`:21, which is frozen line 1429 — **inside** the `L` row `1427–1430`, whose obligation
is *"the revalidation"* while the clause says `Held(SCHEDS, shared)`. By anchor alone it looks
like a hit; it is not one. Their sentence is the one this lane arrives at from the other side:

> *An anchor without a text identifies as little as an ordinal without one.* **The text is
> the field that decides.**

### How much would a swap actually cost today? — 11 of 11 sibling groups are verdict-homogeneous

Measured over the six files that have a permutable group, reading the proof channel's verdict
per obligation (`gabbro pflichten --lean`): in **every one of the 11 groups all members carry
the same verdict** — three groups all `PROVED`, six all `refused:call-site`, one all
`refused:call-not-compositional`, one all `refused:carrier-not-a-table`. So a swap performed
today would move a mark onto an obligation of identical standing, and cost nothing.

**That is an accident of these six files, not a property of the mechanism, and it was checked
rather than assumed.** For a `V` group homogeneity *is* structural — `call-site` refuses the
kind and never looks at the conjunct. For an `N` group it is not: `Reason::NoTerm` and
`Reason::ArgumentNotStable` are decided by the conjunct's own term. One added line makes a
mixed group:

```
ensures   c.slots[s].elter == None,          -> PROVED
          c.slots[s].vorheriges == None,     -> PROVED
          c.slots[s].naechstes == None,      -> PROVED
          c.slots[s].zaehler <= 65535        -> refused: carrier-not-a-table
```

*So "harmless today" is a fact about six files that a fourth conjunct ends.*

## 4. The four options, priced — and the recommendation

Every figure below is from `./messung/gabbrov/ratschenschluessel.py`, which re-measures all of
it in one second and drives four speech tests first.

| | what it costs | verdict |
|---|---|---|
| **(a) a content hash in the name** | breaks on **exactly the same edits** as the text does — it is a hash *of* the text — and additionally destroys a readable name that **twelve documents and three instruments** already key on (counted: `grep -rl ':: ensures #' --include=*.md --include=*.py`, minus this report), the two proof channels' `duty_N … :: ensures #1` among them | **dominated by (b).** Same benefit, same breakage set, one loss more |
| **(b) name + class + text as the key** | nothing in the artefact — version 2 already carries the text. Priced in edits: **3 of 5** benign reformats leave every key standing | **recommended** |
| **(c) a stable identity written in the source** | §7's gate: a source word or a new clause slot, a pass slot, an Isabelle *and* a Lean counterpart, `exec` untouched, and the vocabulary ratchet **rises**. And it is **not sufficient**: a hand-given label stays put while the predicate under it is rewritten — the same transfer, one edit further out | **not built** — expensive *and* incomplete |
| **(d) nothing, with the hazard named at the ratchet** | free | **not available.** It is legitimate only at a reachability of zero, and the number is 28 / 79 / 113 depending on the edit. There is also no ratchet to name it at |

### Why (b) and not (c), stated once more because it is the load-bearing sentence

§15's own example is `revoke.functional` — an **authored** name, and it is (c). That is why the
sentence *"the ratchet runs over names; exchange is visible"* reads as true: with authored
names an exchange really would be visible, because the two names travel with their statements.
**The emitter does not write authored names**, it writes ordinals, and the sentence became
false without anyone editing it. So (c) is not a wrong idea — it is what §15 assumed all along.

**And §15's own example line already carries the text beside the name:**

```
obligation revoke.functional  "ensures !exists k in descendants of s: k.used"  offen
closed     consuming.schablone  "Ordnungserhaltung descendants, Erzeuger-Schablone"  Fundstelle
```

So the FORMAT §15 sketched has been (b)-shaped from the start; it is only the sentence
underneath it that says *names*. Version 2 of the manifest brought the format up to the
sketch on 2026-09-03. **What is left is one sentence, and correcting it against its own
example costs nothing.**

It is still not the answer, and for a reason that has nothing to do with cost: **(c) binds the
name to the SITE, not to the CONTENT.** Write `ensures unlinked: c.slots[s].elter == None`,
then later rewrite the predicate and leave the label — and `closed` transfers exactly as
before. A label is a better ordinal, not a binding. **Only the text binds the text**, and (b)
is the cheapest way to say so.

### The measured price of (b)

```
PRICE -- which edits move the key (name, class, text)?
  ok  MOVES  ( 2 of 13 keys)  the swap `O3` describes -- conjunct 1 against conjunct 3
  ok  STAYS  ( 0 of 13 keys)  re-indent, one conjunct per line, deeper
  ok  STAYS  ( 0 of 13 keys)  wrap ONE conjunct across two lines
  ok  STAYS  ( 0 of 13 keys)  a comment beside the first conjunct
  ok  MOVES  ( 1 of 13 keys)  redundant parentheses around one conjunct
```

`zeremonie::schnitt_bis` collapses every whitespace run to a single space, so **layout is
free**: indentation, line wrapping and a trailing comment leave the key alone. What moves it
is parentheses and any rewording — and every one of those is a case where a human should look
again, because the line the prover saw is no longer the line in the file. *The loss is in the
safe direction* (W10: it may oblige, it may not acquit) — a lost `closed` costs a re-proof, a
transferred one costs a false theorem.

### Why the anchor is not in the key, and where it is the last resort

```
ANCHOR -- one comment line at the top of a file
  anchors moved    13 of 13
  texts moved       0 of 13
```

**The anchor is the least stable field of the record.** It moves for every line below any edit
at all, contract or not. It stays for reading, and for one job the triple cannot do: two calls
to one callee with one `requires` produce two lines agreeing in name, class, state **and
text** — reachable in seventeen lines of Gabbro (`ratschenschluessel.py::DOPPELRUF`), and
`pflichten.rs`:55 already books it as latent. Today the triple is a key over the whole
population — **0 collisions of 113, 0 lines without a text.**

So the full rule, and the degenerate case is named rather than wished away:

> **key = (name, class, text), and where one unit carries that triple more than once, the
> k-th such line in SOURCE ORDER.** The occurrence index is stable under everything the
> anchor is not — a comment added at the top of the file does not move it.

### What was built

**Only the cheap half, because the expensive half is not mine and the cheap half is not the
ratchet.** There is no ratchet to key; what a lane can do today is fix the key *before* it is
written and leave a measurement that recomputes the argument instead of a paragraph that
remembers it.

* `messung/gabbrov/ratschenschluessel.py` — REACH, KEY, PRICE and ANCHOR in one second over
  184 units, with four speech tests ahead of the verdict: the degenerate double call must
  produce one triple over two anchors, the swap must move the text and **nothing else**, a
  reformat must move nothing, and the judgement itself must fall on a planted collision.
  Return `1` means the tree has to change, `2` that nothing was measured.
* `dokumente/GABBROV.md` V4 — *"ratchet over names"* struck, the key named at the milestone
  that will build it.
* `dokumente/OFFEN.md` `O3` — the decision with its numbers. **The entry stays open**, as the
  owner ruled: nothing keys on anything yet, and §15's sentence is still standing and still
  false as the emitter writes names.

**What was deliberately NOT built, with its price:** the tool sits in `messung/gabbrov/` beside
`manifest-lage.sh` and not in `instrumente/` as a `pruefe-*`. A new guardian is auto-discovered
by `abnahme.py` and `pruefe-waechter.py` and would move **three shared figures at once** — the
README's `59 of 59 instruments`, the acceptance station count, and the guardian register. The
merge-addition class is booked **seven** times in this tree now, §5 below being the seventh,
and every one of them is a lane moving a shared figure by one while git reports no conflict.
*One figure was unavoidable here; three more, chosen, would have been careless.*
Promoting it is one `git mv` plus those three cells, and that price belongs to whoever decides
to pay it, not to a lane that was asked a question about a key.

---

## 5. Re-measured on the merge, and one shared figure moved

`master` had gone from `1cb66b0` to `10856d8` under this lane (the «B10» merge `e293a6c`
plus the unseen-port lane). Merged in, and **every number above recomputed rather than
carried across** — the rule this tree has booked six times.

| | at `1cb66b0` | merged at `10856d8` |
|---|---|---|
| units swept (`*.gab`, no `gift/`) | 183 | **184** |
| obligation lines | 113 | **113** |
| swap / insertion / edit | 28 / 79 / 113 | **28 / 79 / 113** |
| key collisions, lines without a text | 0 / 0 | **0 / 0** |
| commits walked for the history scan | 1079 | **1091** |
| modified `.gab` pairs · clause lists compared · changes | 459 · 398 · **0** | 459 · 398 · **0** |
| contract lines ever removed from a `.gab` | 0 of 282 | **0 of 282** |

`master`'s one new unit, `messung/proben/unseen-fat-reader2.gab`, checks clean and carries
no obligation, so the population is unmoved.

### The one figure this lane did move — and the announced number was already stale

Adding a `.md` moves `pruefe-widerruf.py`'s file count, which `TODO.md` carries and
`pruefe-zahlen.py` guards. **This is the seventh booking of the merge-addition class in this
tree, and it has a new half:**

* on `1cb66b0` this lane measured **193 → 194** for its own one file, correctly;
* the coordination announced **194** for the merged `master`, correctly at the time;
* **both were wrong in the merged tree**, because `master` had meanwhile brought
  `messung/BERICHT-B10.md` and `messung/UNSEEN-PORT-FAT.md`.

Measured the way the entry demands — own file away, guard run, file back:

```
without messung/BERICHT-O3-RATSCHE.md   ==  13 Widerrufe, 195 Dateien
with it                                 ==  13 Widerrufe, 196 Dateien
```

**196 is the guard's own number in the merged tree**, and that is what `TODO.md` now says.
Not added, not chosen, and not taken from the instruction either. `pruefe-zahlen.py` is
green again (return code 0, 83 of 83 recomputed) — it had been this lane's one red.

### Out of bounds and left alone

`state` belongs to another instance this session. Nothing here touches the `state`
production in `SYNTAX.md`, `instrumente/pruefe-grammatiktafel.py`, or the `state` lines of
`SPRACHE.md`.

**And no obligation of the population can run over a `state` clause — read off the code, not
assumed.** `pflichten.rs::lauf` matches `ItemArt::Modul`, `Funktion`, `Device` and `Walk`,
and everything else falls through its `_ => {}`. `ItemArt::State` is one of the
*everything else*: a `state` declaration produces **no register line at all**, so the eight
kinds this report is about (`maintains`, `refines`, `ensures`, `requires` at a call,
`reg`/`transition requires` — the `transition` there is a **`device`** transition, from
`d.uebergaenge` — plus the loop and `walk` invariants) never reach that production.
`pruefe-grammatiktafel.py` is red on `state` in `master` and stays that way; it is not this
lane's, and this lane's five touched files are `TODO.md`, `dokumente/GABBROV.md`,
`dokumente/OFFEN.md`, this report and `messung/gabbrov/ratschenschluessel.py`.
