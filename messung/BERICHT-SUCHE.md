# The value-yielding, exitable search loop — the other half of «B10»

Lane started 2026-09-03 on `master` = `10856d8`. Every figure here was measured in this
lane; two foreign measurements were the starting point and both were re-run rather than
inherited.

`messung/BERICHT-B10.md` settled the *`mappings of`* half: **do not build it, demand is
zero.** Its §5 then named this half as the one *with* demand — "seven sites against zero" —
and left it. This report is that half, through the same gate.

> **Verdict: criterion 2 falls, and it falls twice.** The construct that fits in one pass
> slot serves neither of the two sites that are actually broken; the construct that serves
> them needs a second slot **and falsifies a discharged Isabelle theorem**. And the two
> problem sites turn out to want different things: one is repairable today with no construct
> at all (and was, in this lane), the other is not a search-loop problem but a
> `by consuming` problem.

---

## 0. The state of the tree at the start

    git log --oneline -1                 # 10856d8
    free -g                              # 31 total, 16 available, 20 cores, ulimit -v unlimited
    ssh … 'cd gabbro-suche && cargo test --offline --no-fail-fast'
    # 402 passed, 0 failed  (31 result lines summed -- a single `tail` truncates the log)

The task named `master` = `e293a6c`; `master` had moved one commit to `10856d8` by the time
this lane started, and this lane ran against `10856d8`. *A branch three commits behind
measures against a state that no longer exists* — so the newer one was taken, and it is
named here rather than assumed.

---

## 1. Spot-check (a) — `arp_suchen` returns the LAST match: **CONFIRMED, and repaired**

`messung/netz/udp-echo.gab`:167 declared itself a search and was not one.

    let mut treffer : u32 = 0;
    traverse s over slots of a by unvisited touches reads a {
        if a.slots[s].belegt && a.slots[s].ip == ip { treffer = a.slots[s].mac_hi; }
    }
    return treffer;

**Not read — run.** `gabbro emit`, then `cc`, then a table with two entries carrying the
same IP at slots 3 and 9:

    ARP_PLAETZE=16
    first  match (slot 3) mac_hi = 0xAAAA1111
    last   match (slot 9) mac_hi = 0xBBBB2222
    arp_suchen returns          = 0xBBBB2222        <- the LAST
    VERDICT: LAST match (defect confirmed)

And the checker is silent about it: `messung/netz/udp-echo.gab: 25 items, 0 errors, 0 hints`.

**Which entry wins is an accident of the workaround.** Not the first, and not the freshest
either — `alter` is the recency field and the loop never looks at it. The table's own
invariant (`belegt_hat_adresse`) says only *occupied ⇒ ip ≠ 0*; it does not say keys are
unique, and `arp_lernen` writes at a caller-chosen `platz` without searching, so duplicates
are producible through this file's own API.

### Should it be repaired independently of the construct? **Yes — and it needed no construct**

This is the part the demand argument turns on, so it was measured rather than assumed.

    traverse s over slots of a by unvisited touches reads a {
        if a.slots[s].belegt && a.slots[s].ip == ip { return a.slots[s].mac_hi; }
    }
    return 0;

`gabbro pruefe` → **25 items, 0 errors, 0 hints**. `gabbro emit` → C. Recompiled, re-run:
`arp_suchen returns = 0xAAAA1111` — the first match. **The repair is shorter than the defect**
(the `let mut` goes away), it actually stops walking on a hit, and the `costs <= 256 ops`
promise is untouched.

**`return` in a traverse body is not a trick — it is what four other corpus sites already
do**: `39-auftragsdienst.gab`:76 (`erster_dringender`), :95 (`buendel_von`),
`18-vorfahren.gab`:52 (`liegt_unter`), `43-gegenprobe.gab`:95.

> **So «B10» made the wrong shape plausible; it did not force it.** The right idiom was
> beside it and had been used four times in the same corpus. *That is a weaker claim than
> "the missing construct produces a wrong program", and it is the one the measurement
> supports.* Applied to the tree in this lane, with the reason at the site.

---

## 2. Spot-check (b) — the caprock original of `F03`:174: **CONFIRMED**

`../caprock-messbasis/crates/caprock-ipc/src/lib.rs`:625, `Endpoint::call`
(branch `arch/x86_64`, `a1bf707`):

    while let Some(server) = self.receivers.dequeue() {
        let Some(sframe) = ops.frame_of(server) else {
            continue;                       // dead receiver -> discard, try the next
        };
        …
        return if caprock_sched::owner_core(server) == Some(core) { … } else { … };
    }

It **returns at the first live receiver** and leaves every receiver behind it queued. The
same shape a second time at :675 (`Endpoint::recv`, over `senders`). Exactly what `F03`'s
«B10» comment says is lost:

> *"`traverse` yields no value and knows no `break` — with `by consuming` the WHOLE queue is
> emptied, including the receivers behind the one found. That is not verbosity, it is a
> different program: a rendezvous becomes a bloodletting."*

**Confirmed, and it is the strongest single piece of evidence in the file.** It also carries
a detail the census did not name: the loop is *consuming with a side effect* — dead entries
are permanently discarded on the way past, and the hit is dequeued too. Not "find", but
"drain-until-hit".

---

## 3. The three sub-demands, each with its own denominator

The census said three constructs were entangled under one marker. Separated and counted over
the **179-file corpus** (`beispiele/*.gab` + `messung/**/*.gab`, no `gift/` — the same
denominator `zaehle-wortschatz.py` uses):

| | |
|---|---:|
| loops in the corpus | **57** |
| `traverse` | 33 |
| `retry` | 13 |
| `forever` | 11 |
| **labelled** (`retry`/`forever` with an ident) | **24 — all of them** |
| `leave`/`next` statements | 15 |

### S1 — early exit (`break`): **already exists, on 24 of the 57 loops**

**`break` is not missing from Gabbro.** It is `leave <label>;`, it is used 15 times, and
every `retry` and `forever` in the corpus carries a label. What is missing is the label on a
`traverse` — the grammar gives it no place for one.

* denominator for the gap: **33 `traverse`**
* sites that want to stop early: **11 of 33 (33 %)** — the 10 in S2 plus
  `41-handschlag.gab`:193
* and `F05`:214-220, which the census calls "the loudest site", **is not one.** The file
  corrects itself in place: *"`leave <marke>` GIBT es … `gabbro pruefe` gibt darueber 0
  Fehler … «B11» schrumpft damit von 'die Dienstschleife ist nicht schreibbar' auf 'ihr
  Austritt ist unbenannt'."* F05 wants a **reason on the exit** (`leave EndpointGone`,
  shaped like `on_exceeded`) — a fourth demand, and a different one.

### S2 — a value out of the loop: **10 of 33, and 8 of the 10 are already correct**

| site | shape | correct today? |
|---|---|---|
| `39-auftragsdienst.gab`:69 `erster_dringender` | `return Some(i)` | yes |
| `39-auftragsdienst.gab`:94 `buendel_von` | body is only `return Some(v);` | yes |
| `18-vorfahren.gab`:50 `liegt_unter` | `return true` (flag) | yes |
| `43-gegenprobe.gab`:93 | `return false` (flag) | yes |
| `42-zaehlwerk.gab`:163 | `return …zaehler` | yes |
| `F06.gab`:197 | `return i * 8` | yes |
| `F01.gab`:423 | `let … else (e) { return e; }` | yes |
| `probe-elems.gab`:22 | `return n` | measuring apparatus, not demand |
| **`F03.gab`:174** | sentinel `picked`, **`by consuming`** | **no — different program** |
| **`udp-echo.gab`:172** | sentinel `treffer` | **was wrong; repaired in §1** |

**The whole gap is two sites, and they are the two that do not use `return`.** The other
eight escape through the enclosing function's `return`, which works, which the emitter
lowers, and which costs a dedicated helper function and nothing else. `buendel_von` is the
extreme — three lines of scaffolding around one `return Some(v);` — but it is *verbose*, not
*wrong*.

And the two exceptions do not want the same thing:

* **`udp-echo`** could have used `return` (it is the whole function body, exactly like
  `erster_dringender`). Measured, repaired, §1. **Not a demand for a construct.**
* **`F03`** cannot: the traverse sits in the middle of a function that continues afterwards,
  so `return` would leave the whole function. The sentinel is forced there — and so is
  `by consuming`, because the fastpath must *remove* the receiver. **This is the one real
  site, and it is a `by consuming` problem before it is a search problem.**

`messung/SCHLEIFENZUSAGEN.md`:91 lists five search loops; one of them, `F04 :: poll_used`,
is **not** a demand site — it is `retry warten until q.USED_IDX != von` with an *empty body*
and the value read after the loop. `retry … until` already serves that shape completely.
*Four of five, not five.*

### S3 — a named exit from a TRAVERSAL: **4 statements, 1 file, and it is deliberate**

A `traverse` carries no label, so `leave`/`next` inside one names the enclosing labelled
loop. Measured over all 15 exit statements:

    beispiele/41-handschlag.gab:201  next runde;   innermost=traverse  target=forever runde @163
    beispiele/41-handschlag.gab:202  next runde;   innermost=traverse  target=forever runde @163
    beispiele/41-handschlag.gab:206  next runde;   innermost=traverse  target=forever runde @163
    beispiele/41-handschlag.gab:210  leave runde;  innermost=traverse  target=forever runde @163

**Four of fifteen, all in one file, all in one traverse.** And that file's header says why:

> *"`leave runde;` im `else` eines `let … else` in einer Traversierung verlaesst die
> Schleife, die die Traversierung UMSCHLIESST — eine Traversierung selbst traegt keine
> Marke, und das ist Absicht."*

Three `traverse` of 33 sit inside a labelled loop at all (`04-schleifen.gab`:86,
`42-zaehlwerk.gab`:284, `41-handschlag.gab`:193). **The retargeting is not silent** — the
emitter lowers `leave`/`next` to `goto <label>_ende` and never to C's `break`, precisely so
that the innermost loop cannot be hit by accident, and it says so at `emit.rs`:7270.

**Demand: 0.** Nobody has wanted to leave a traversal *and stay in the enclosing loop*; the
one file that writes exits inside a traversal wants the enclosing loop and gets it.

---

## 4. The §7 cost gate, criterion by criterion

### Criterion 1 — no new source word: **HOLDS**

    python3 instrumente/zaehle-wortschatz.py
    == Die Zahl: 221 Woerter ==      212 reserviert · 9 kontextuell
    == Der Grund am Eintrag: 13 von 221 ==   208 ohne
    333 Stellungen (Terminal x Regel) auf 222 Terminale in 154 Regeln -- 1,50 je Terminal

**221 / 208 / 333**, the ratchet exactly. And it holds for the construct too, because the
language already has a **value-yielding block whose `return` means "yield"**:

```gabbro
let alt = GESENDET exchange update(v) bounded 64 ops on_exceeded zu_viel_streit {
    if v < 65534 { return v + 1; }
    return v;
} publishes nothing;
```

`beispiele/41-handschlag.gab`:216-224. That `return` yields the new CAS value; it does not
return from the function. So the search loop can be spelled with existing words in new
positions — the «B13» shape, which criterion 1 permits:

```gabbro
let treffer = traverse s over slots of a by unvisited
    touches reads a
{
    if a.slots[s].belegt && a.slots[s].ip == ip { return a.slots[s].mac_hi; }
} else { 0 };
```

`let`, `traverse`, `over`, `of`, `by`, `unvisited`, `touches`, `return`, `else` — all
present. `else <block>` already stands at `narrow … to … else { … }`. **221 → 221.**

*Criterion 1 is not what stops this either, and the cheap assumption is the opposite one.*

### Criterion 2 — one pass slot: **FALLS, and twice**

Measured against the **unchanged** checker, `messung/proben/probe-suchschleife-passfach.gab`
(W24 pre-run; the file carries its own literal output).

**Slot 1 — the not-found path creates the language's first unbound binding.** The question
was "is the yielded value bound on the not-found path?" and the answer is sharper than
expected:

    error: [P001] …:16:26: `=` expected, `;` found
       16 |     let mut treffer : u32;

`letstmt` (`SYNTAX.md`:961) has **no form without `=`**. An uninitialised binding is not an
error in this language — it is an unwritable shape. **There is therefore no definite
assignment pass today, because there is nothing for one to do.** A yielding loop creates the
first binding in the language whose value depends on a path. That is a real new obligation,
and it is a pass slot.

**Slot 2 — `by consuming` + exit falsifies a discharged theorem.** `beweise/Consuming.thy`
carries S2:

> *"Die erzeugte Zeugenmenge ist VOLLSTAENDIG: ist sie leer, ist die Domaene leer."*

An exit from a `by consuming` traverse means the witness set is **not** complete. This is not
a pass that would have to be extended — it is a theorem in the fifteen that build today, and
it is about exactly the loop form `F03`:174 uses. `SYNTAX.md`:1051 says the same thing from
the other side and calls it decided: *"«B10» is thereby answered … `by consuming` empties the
whole queue. The IPC fastpath wants the first live receiver and then stops — **that is a
different loop shape, not a different reading of this one**."*

**And the folder's own designed obligation for this construct already excludes the hard
cases.** `crates/gabbro-check/src/schablonen.rs`:711, `ops.suche`, `Stand::Entworfen`:

> *"The generated search returns the first hit in a generated, named enumeration order **and
> leaves the set unchanged**."*

"Leaves the set unchanged" rules out `by consuming` (F03, and caprock `Endpoint::call`/`recv`)
by its own text. Building the construct means rewriting that obligation first.

**What does NOT open a slot, measured:**

* **The cost pass — nothing.** The promise was tightened until `K001` fires, at two domain
  sizes:

      NSLOTS=16   costs <= 48 -> refused   costs <= 64 -> accepted
      NSLOTS=32   costs <= 96 -> refused   costs <= 128 -> accepted

  Four ops per element, doubling with the domain. **The worst case of a loop that may stop
  early is the loop that does not** — which is the promise already written. An early exit is
  free to the cost pass.

* **The effect pass — nothing.** Function (e) of the probe writes the found element inside
  the traverse and checks at 0 errors. `touches` already covers it.

* **The two-exit shape the caprock census warns about — nothing, because Gabbro already
  splits it across two loop forms.** Caprock caps loops with `if steps > limit { break }`
  because Rust gives it no domain bound. Gabbro's `traverse` takes its bound **from the
  domain declaration** (`K003` refuses a traverse whose domain has none), so it needs no step
  exit. And the caprock sites that have *no* domain — `find_rsdp` scanning physical memory,
  `dmar_unit_base` walking a TLV stream — are `retry` in Gabbro, where the bound exit is
  `bounded N ops` + `on_exceeded` and the hit exit is `leave`. **Both exits already exist,
  one per form.** What `retry` lacks is only the value.

* **Mutation of the found element — nothing.** `heap.rs`:112 sets `slot.bump` before
  returning the address; `pcie::find` writes the bus-master bit before returning the device.
  Probe function (e) does exactly this shape today, 0 errors. **The write is not the missing
  part** — but see `ops.suche` above: the template as written forbids it.

> **So the shape of the refusal is this.** A construct restricted to `by unvisited` fits in
> one slot and serves only sites that are already correct — the eight `return` sites, plus a
> `udp-echo` that this lane repaired without it. A construct that reaches `F03` and the two
> caprock IPC sites needs the second slot *and* contradicts a theorem that builds today. **The
> half with demand is the half that does not fit; the half that fits has no demand it uniquely
> serves.** That is the same shape that stopped the construct at `K001`, one report ago.

### Criterion 3 — the Isabelle counterpart builds: **baseline GREEN**

    rsync -rlpgoD --delete --exclude 'target/' … ./ ki-pc-fisch-101:gabbro-suche/
    rsync -a                                  beweise/ ki-pc-fisch-101:gabbro-suche/beweise/
    ssh ki-pc-fisch-101 'cd gabbro-suche/beweise && ~/Isabelle2025-2/bin/isabelle build -D . -o threads=12 -c -v'
    # 15 theories · Finished Gabbro (0:00:06 elapsed, 0:00:24 cpu, factor 3.92)
    # 0:00:08 elapsed time, 0:00:24 cpu time, factor 2.77
    # real 0m9.691s   user 0m43.459s   EXIT=0

Forced clean (`-c`) on purpose: the first, cached run reported `0:00:02` and named no theory,
which is a report about the heap store and not about the proofs.

**Is a counterpart statable? Yes, and half of it is already discharged.** The theorem about
the not-found path is `beweise/Option_Sonderwert.thy`: `option index into T` lowers to the
same machine word with `N` as `None`, and the encoding is injective — *"jeder gueltige Index
ist von `None` unterscheidbar"*. A search loop yielding `option index into T` inherits its
lowering theorem. What would be new is one statement — **the yielded binding is `None`
exactly on the path where no element satisfied the predicate** — and it is a real theorem,
not a formality.

**But the direction that matters here is the other one.** The construct would not merely need
a new theorem; in its `by consuming` form it **falsifies** `Consuming.thy` S2, which builds
today. *A construct whose first act is to break a standing proof is not covered by "a
counterpart is statable".*

### Criterion 4 — `exec` untouched: **HOLDS**

`dokumente/AUFTRAG-GABBROV.md`:295 hold list — *"`exec`s Großschrittigkeit. Sprachsemantik,
trägt die Isabelle-Beweise mit."* A loop form is a statement about a body's execution, and
big-step `exec` has no intermediate state to expose; nothing in this proposal reaches it.

---

## 5. Recommendation

**Do not build it — but not for the reason the census expected, and one thing WAS worth
doing.**

1. **The wrong ARP lookup is real, was confirmed by running it, and is repaired.** No
   construct was needed; `return` in the traverse body is what four other corpus sites do.
   *The gap made the wrong shape plausible, not necessary* — a weaker claim than the census
   made, and the one the measurement supports.
2. **`break` already exists.** `leave <label>` works on 24 of the corpus's 57 loops, 15 uses.
   The demand is for a label on `traverse`, and that is 11 sites of 33 — of which 8 are
   already correct with `return`.
3. **The named exit from a traversal has zero demand.** Four statements, one file, and the
   file says the current behaviour is what it wants.
4. **Criterion 2 falls**, and the version that would serve `F03` also falsifies
   `Consuming.thy` S2.

Rule A wants measured demand. Measured, the demand is **one site** — `F03`:174 — and it is
not a search-loop gap but a `by consuming` gap: *drain-until-hit* is a third run form beside
`unvisited` and `consuming`, and `SYNTAX.md`:1051 already says so in as many words. **If
anything is to be booked here, it should be booked under that name and against that site**,
not as "the value-yielding loop".

### The cheap half, worth having on its own

Two findings from this lane are repairs, not constructs, and neither needs the gate:

* **`retry` labels type-check and do not lower.** `schleifen.rs`:117 registers a `retry`'s
  label for `S001` — its own note even says *"`retry`/`forever` take one"* — but
  `emit.rs`:7821 pushes only `forever` labels. So:

      leave versuch;   inside   retry versuch until … { … }
      gabbro pruefe → 5 items, 0 errors, 1 hints
      gabbro emit   → error: [C001] …:34:13: no lowering: `leave`/`next` naming no enclosing loop

  **A program the checker accepts and the emitter refuses.** The emitter refuses by name, so
  no wrong C is produced — but the comment above the refusal says *"`S001` hat das schon
  entschieden; hier kann es nur ein Auszug sein"*, and that is not true for `retry`. All 15
  exits in the corpus name a `forever`, which reads as a style and is a constraint.
  `messung/ABSAGEFORMEN.md`:373 books this refusal as covered by
  `beispiele/gift/210-marke-ausserhalb-jeder-schleife.gab` `S001` — that is the
  *unresolvable-label* path; **the `retry` path reaches the same refusal with no checker
  error at all and is uncovered.**

* **A reason on the exit**, which is what `F05` actually asks for — `leave <label>` carrying a
  named cause the way `on_exceeded` does. One position on `leave`, no new word (`reason` is
  already a word). Two sites: `F05`:214 and `F05`:264. *That is a smaller item than this one
  and it is the one the loudest file wants.*

---

## 6. `messung/ABSAGEFORMEN.md` — the stale F09 lines, measured and corrected

`BERICHT-B10.md` §6 flagged two lines and left them for the owner. This lane measured which
site covers the rule and corrected the two that were named.

    gabbro pruefe messung/fragmente/F09.gab   # 9 items, 0 errors, 0 hints
    gabbro emit   messung/fragmente/F09.gab   # no error -- C is written

**F09 exercises no refusal at all any more.** The sweep, over every `.gab` under `beispiele/`
and `messung/` (621 files, `pruefe` for `K001` and `emit` for the refusal texts):

| question | answer |
|---|---|
| files raising `K001` | **15** — 11 in `gift/`, 3 `fnptr-proben`, 1 `probe-domaenenschatten` · **none is F09** |
| files reaching `no lowering: mappings of` | **1** — `beispiele/gift/571-walk-ebenen-laufen-um.gab`:52 |
| files reaching `device … at normal` | **0** |
| files reaching `walk … levels` not a number | **1** — `beispiele/gift/667-walk-levels-is-an-expression.gab` |

`gift/571` refuses at the checker with `K003` (the domain has no bound) and at the emitter
with `C001` at the `mappings of` site. **Corrected: :231 (the German table) and :401
(row `6532`)** now name it, with the measurement beside them.

**Three more rows carry the same stale citation and were left standing**, named rather than
edited — two lanes moving one line is the merge fault this week already produced six times:

| row | cites | measured today |
|---|---|---|
| `2487` / :230 `device … at normal` | F09 `K001`, *mit Fehler* | **no file in the tree reaches it** — the state is `ungemessen`, not `mit Fehler` |
| `7886` / :424 `walk … levels` not a number | F09 `K001`, *mit Fehler* | covered by `beispiele/gift/667-walk-levels-is-an-expression.gab` |
| :232 (German twin of `7886`) | F09 `K001` | same |

*A register that names a site which no longer exercises the rule reports coverage it does not
have* — and here it did so four times over one file.

---

## Summary

| question | answer | measured by |
|---|---|---|
| `arp_suchen` returns the last match | **yes** | emitted, compiled, run against two matching entries |
| …and is it a defect to repair today | **yes, and it needed no construct** | `return` idiom, checked + emitted + re-run |
| `F03`'s caprock original stops at the first live receiver | **yes**, `caprock-ipc/src/lib.rs`:625 and :675 | read on `arch/x86_64` `a1bf707` |
| S1 early exit — denominator | **already exists** on 24 of 57 loops; gap is 11 of 33 `traverse` | corpus census, comments stripped |
| S2 value out — denominator | **10 of 33**, 8 already correct, **2 real**, of which 1 repaired here | per-site classification |
| S3 named exit from a traversal — denominator | **4 statements, 1 file, and it is deliberate** | all 15 exits, innermost loop vs. target |
| criterion 1, no new source word | **holds** — 221 / 208 / 333; `exchange update` is the precedent | `zaehle-wortschatz.py` |
| criterion 2, one pass slot | **falls** — `P001` (no unbound binding exists) + `Consuming.thy` S2 | probe against the unchanged checker |
| criterion 3, Isabelle builds | baseline **green**, 15 theories, `EXIT=0`, 9.7 s wall / 43.5 s cpu | forced clean rebuild on the server |
| criterion 4, `exec` untouched | **holds** | `AUFTRAG-GABBROV.md`:295 |
| tree unbroken | `cargo test` **402 / 0** | `--offline --no-fail-fast`, 31 lines summed |
