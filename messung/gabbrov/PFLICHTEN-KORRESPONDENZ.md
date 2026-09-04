# The obligation correspondence — one row per obligation of GabbroV's population

**This file is READ BY A GUARD.** `instrumente/pruefe-manifest.py` parses the table in §3 and
checks every row against a live `gabbro pflichten` run. It is not a side note: the numbers
`pruefe-manifest.py` prints are derived from here, and a row that says something the run
contradicts turns the guard red.

> **Why it exists.** Until 2026-09-03 the split *"43 blocked upstream, 15 dropped by the
> manifest, 5 carried"* stood as a hardcoded sentence inside the guard. Three fragments were
> repaired that same day and **not one of the three numbers moved**, because none of them was
> derived from anything. *A blocker that no longer exists is not a blocker* — and a number
> that outlives its cause is worse than no number, because it reads like a measurement.

---

## 1. The two sides, and why a bare count cannot compare them

| | |
|---|---|
| **the population** | the `L` rows of `dokumente/PFLICHTEN.md`, anchored to `dokumente/FRAGMENTE.md` @ `708beed`, minus the three `progress` rows rebooked as assumptions. `./instrumente/zaehle-pflichten.py --gabbrov` → **63** |
| **the manifest** | the `obligation` records `gabbro pflichten` emits over `messung/fragmente/F*.gab`. `./instrumente/pruefe-manifest.py` → **39** lines today (27 before the three collection sites of 2026-09-04) |

**Subtracting the second from the first answers nothing**, and that was the guard's arithmetic
until today. The two sets are not nested: `PFLICHTEN.md` books **`K` (plumbing) and `L`
(logic)** rows and GabbroV's population is the `L` half alone, while the manifest emits a line
for every obligation the checker finds — `K` and `L` together. Measured on 2026-09-03: of the
27 manifest lines, **16 carry a `K` row or no row at all**. So `63 − 27 = 36` counted sixteen
lines as if each had closed a logic obligation, and not one of them had.

*The eleven that remain carry THIRTEEN rows*, because two lines do double duty — see §5.
`27 = 11 + 16` and `13 CARRIED rows = 11 lines`; both facts are printed by the guard, and
neither is a coincidence worth resting on.

**Re-measured 2026-09-04, after the three new collection sites:** `39 = 18 + 21`, and
`20 CARRIED rows = 18 lines` — two pairs of rows share a line (§5). *The 21 unclaimed grew by
five, and not one of them is a defect:* they are the five `transition` STEPS of F02, whose
guards `PFLICHTEN.md` books and whose moves it does not.

*The comparison that means something is a MAPPING, obligation by obligation, and a mapping is
a judgement.* This file is that judgement, written down where a guard can hold it against a
run.

## 2. The four states, and the test that decides between them

`SPRACHE.md` §15 names the addressee: *"Nothing is silently lost"*, for **"the programmer OR
AN EXTERNAL TOOL"**. So the question at every row is not whether a human could reconstruct the
obligation from the fragment — it is **whether a tool reading only the manifest could.**

| state | meaning | what it would take to move it |
|---|---|---|
| `CARRIED` | a manifest line states it. The row names that line, and the guard checks the line is really in the run | — |
| `BLOCKED` | the fragment carries checker errors, so it emits no register at all. **Not a defect of the manifest.** The guard checks the fragment really has no register | repair the fragment |
| `DROPPED` | **the clause stands in the source and the register does not book it.** The row names the clause and its line | a collection site in `pflichten.rs`, or a decision that the clause is not an obligation |
| `NO CLAUSE` | nothing in the fragment states it. A manifest line would have to be **invented** | a language construct, or a clause written into the fragment |

**The distinction between the last two is the whole value of this table.** A single number
reads as *n* repairable holes; measured on 2026-09-03, **12 of the 37 unblocked open rows had a
clause standing in the source** and 25 did not. **Measured 2026-09-04, after seven of the
twelve were booked: 5 of 30**, and §6 prices what each of the five would still cost.

## 3. The table

Anchors in column 3 are `dokumente/FRAGMENTE.md` line numbers (the frozen population); anchors
inside a reason are `messung/fragmente/F*.gab` line numbers (today's source).

| # | frag | anchor | obligation | state | manifest line / reason |
|---|---|---|---|---|---|
| 1 | F01 | 167–169 | a root has no predecessor | CARRIED | `CapSpace :: invariant wurzel_ohne_vorgaenger` — `pflichten::lauf` got its `ItemArt::Tabelle` arm on 2026-09-04. See §7: the refusal rested on a premise its own argument contradicts |
| 2 | F01 | 171–173 | the sibling chain is mutual | NO CLAUSE | «B14» — `pred` cannot resolve an `option index into`, so the statement is not writable |
| 3 | F01 | 174–177 | `refcount == count(s in slots : s.object == o)` | NO CLAUSE | «B13» — `count` is a reserved word with no production in `pred`/`expr` |
| 4 | F01 | 188–190 | `cdt_wohlgeformt` — every slot reaches the root via `parent` | CARRIED | `unlink :: cdt_wohlgeformt` |
| 5 | F01 | 197 | the CDT stays well-formed across `unlink` | CARRIED | `unlink :: cdt_wohlgeformt` |
| 6 | F01 | 201–213 | the four relink cases are exhaustive and each is correct | NO CLAUSE | `match` forces the cases; the correctness statement stands nowhere in the source |
| 7 | F01 | 236 | the cap has no children — `ist_blatt` | CARRIED | `revoke :: delete_leaf requires #4` |
| 8 | F01 | 244–245 | the refcount fell by exactly one | CARRIED | `delete_leaf :: ensures #2` |
| 9 | F01 | 246 | the CDT stays well-formed across `delete_leaf` | CARRIED | `delete_leaf :: cdt_wohlgeformt` |
| 10 | F01 | 273 | released exactly at zero | NO CLAUSE | a branch condition; no clause states that this condition is the right one |
| 11 | F01 | 277 | `Memory` — the region goes back to the RAM allocator | NO CLAUSE | the correctness of the arm carries no clause |
| 12 | F01 | 278 | `Dma` — released only after proof | NO CLAUSE | the correctness of the arm carries no clause |
| 13 | F01 | 279 | `Reply` — the caller is unblocked | NO CLAUSE | the correctness of the arm carries no clause |
| 14 | F01 | 292 | no reference survives | NO CLAUSE | no clause states it |
| 15 | F01 | 301 | the CDT is well-formed on entry to `revoke` | DROPPED | `F01.gab`:390 `requires … cdt_wohlgeformt(c)`. **A function's own `requires` reaches the manifest only through a CALL SITE**, and `revoke` has none: `grep -n revoke messung/fragmente/F01.gab` finds the `impl fn` at :384 and nothing but comments besides. **Measured MORE expensive than §6 priced it** — see §6 |
| 16 | F01 | 302 | it stays well-formed across `revoke` | CARRIED | `revoke :: cdt_wohlgeformt` |
| 17 | F01 | 337 | every `victim` is a leaf when `delete_leaf` sees it | CARRIED | `revoke :: delete_leaf requires #4` |
| 18 | F02 | 454–455 | `setze_rtp` — TE off or RTPS already set | CARRIED | `Vtd :: transition setze_rtp requires` |
| 19 | F02 | 457–458 | `scharf_te` — RTPS is set | CARRIED | `Vtd :: transition scharf_te requires` |
| 20 | F02 | 460–461 | `setze_irtp` — QIES is set | CARRIED | `Vtd :: transition setze_irtp requires` |
| 21 | F02 | 463–464 | `scharf_ire` — IRTPS set and CFIS clear | CARRIED | `Vtd :: transition scharf_ire requires` |
| 22 | F02 | 466–467 | `scharf_qie` — QIES is clear | CARRIED | `Vtd :: transition scharf_qie requires` |
| 23 | F03 | 587–589 | `caller` and `reply_owner` are set together or not at all | BLOCKED | F03 emits no register |
| 24 | F03 | 592–603 | the two places are written in one step | BLOCKED | F03 emits no register |
| 25 | F03 | 609–611 | the message arrived — `msg_kopiert` | BLOCKED | F03 emits no register |
| 26 | F03 | 630–631 | postconditions may speak about the return value | BLOCKED | F03 emits no register |
| 27 | F03 | 633 | `antwortpflicht_paarig` is maintained | BLOCKED | F03 emits no register |
| 28 | F03 | 642 | a quiescing endpoint starts no new transaction | BLOCKED | F03 emits no register |
| 29 | F03 | 648–651 | the fastpath takes the FIRST live receiver and stops | BLOCKED | F03 emits no register |
| 30 | F03 | 656 | the chosen receiver is alive | BLOCKED | F03 emits no register |
| 31 | F03 | 662–667 | a full queue is REFUSED by name, not blocked | BLOCKED | F03 emits no register |
| 32 | F03 | 668 | the caller is blocked | BLOCKED | F03 emits no register |
| 33 | F03 | 671 | the message arrives at the right thread | BLOCKED | F03 emits no register |
| 34 | F03 | 676–677 | the invariant does not hold between the two assignments | BLOCKED | F03 emits no register |
| 35 | F03 | 678 | a same-core rendezvous switches directly | BLOCKED | F03 emits no register |
| 36 | F04 | 773 | `ack` — from 0 to ACK | CARRIED | `VirtioPci :: transition ack` — the STEP is booked since 2026-09-04, `requires` or not. The from-state is never read: see §8 |
| 37 | F04 | 774 | `drv` — ACK to ACK or DRIVER | CARRIED | `VirtioPci :: transition drv` |
| 38 | F04 | 775–776 | `featok` | CARRIED | `VirtioPci :: transition featok` |
| 39 | F04 | 777–779 | `drvok` | CARRIED | `VirtioPci :: transition drvok` |
| 40 | F04 | 780–782 | a reset applies from EVERY state | NO CLAUSE | «B26» — no placeholder for the pre-state, so the transition table cannot be complete |
| 41 | F04 | 836 | a buffer belongs to exactly one side | NO CLAUSE | no clause states it |
| 42 | F05 | 954–960 | every startup failure is named and leaves the program | NO CLAUSE | six `let … else` arms; the statement is the SHAPE of the code and no clause |
| 43 | F05 | 964–967 | never read yet is distinguishable from zero | NO CLAUSE | no clause states it |
| 44 | F05 | 969–976 | the service loop has a NAMED exit | NO CLAUSE | no clause states it |
| 45 | F05 | 983 | a revoked endpoint ends the service | NO CLAUSE | no clause states it |
| 46 | F05 | 985–991 | `Info` — capacity is reported and cached | NO CLAUSE | no clause states it |
| 47 | F05 | 992–993 | `Read`/`Write` — the request lies inside the client's range | NO CLAUSE | no clause states it |
| 48 | F05 | 994–997 | `Flush` — the flush completed before the reply | NO CLAUSE | no clause states it |
| 49 | F05 | 998 | `Scan` — the partition table is read or refused | NO CLAUSE | no clause states it |
| 50 | F05 | 999–1006 | `Stop` — the reply still goes out before the service ends | NO CLAUSE | no clause states it |
| 51 | F06 | 1070–1072 | never measured is distinguishable from zero | NO CLAUSE | «B14», the same as F05 |
| 52 | F06 | 1094 | the first untouched word marks the depth | NO CLAUSE | a `return` inside a `traverse`; no clause |
| 53 | F06 | 1129–1141 | the measuring instrument reports the known depth | DROPPED | `F06.gab`:240 `check kstack_eichung { claim "…" }` — a `claim` produces no obligation line. **Measured MORE expensive than §6 priced it**: it fits none of the eight kinds, and its shape is the one the population itself books OUT — see §6 |
| 54 | F06 | 1145–1158 | at the foot of every EL0 kernel stack an eighth stays untouched | DROPPED | `F06.gab`:256 `check kstack { claim "…" }` — as row 53 |
| 55 | F06 | 1160 | the check can go RED | DROPPED | `F06.gab`:286 `counterprobe "…" expects erschoepft_waechst` — produces no obligation line, **and no pass reads the clause at all** (`namen.rs`:1262: where the `ident` is declared *„steht nirgends"*). As row 53 |
| 56 | F07 | 1289–1291 | before the MMU the console is lock-free | NO CLAUSE | a property of the PHASE; no clause states it |
| 57 | F08 | 1427–1430 | the revalidation — the thread may have vanished between selection and deed | NO CLAUSE | the `match` over `aufloesen` carries no clause. *The one emitted F08 line looks like a hit by anchor and is a different statement — see §5* |
| 58 | F08 | 1439–1442 | both exits are forced | NO CLAUSE | `match` forces them; the correctness carries no clause |
| 59 | F09 | 1531 | a non-leaf entry points at a next level | CARRIED | `Seitenabstieg :: down` — booked as `W` since 2026-09-04; the emitter compiles the clause into a CLASSIFIER and nothing decides it |
| 60 | F09 | 1532 | `PS == 1` marks a leaf | CARRIED | `Seitenabstieg :: leaf` |
| 61 | F09 | 1543 | the leaf level is reached | NO CLAUSE | `walk … levels` bounds the descent; that the leaf level is REACHED is stated nowhere |
| 62 | F09 | — | W^X over the page table | CARRIED | `Seitenabstieg :: invariant wx_getrennt` |
| 63 | F10 | 1631–1632 | the buffer is a device tree — `magie == MAGIE` | DROPPED | `F10.gab`:9 `magie : u32 where magie == MAGIE` — a `format … where` produces no obligation line, **and it should not**: `emit.rs`:4331 lowers the clause into the decoder and `gabbro emit` writes `if (!(DtbKopf_magie(v) == MAGIE)) return false;`. *A DISCHARGED duty booked `open` is a false line* — see §6 |

## 4. The split, derived

```
population                                                63
  CARRIED    a manifest line states it                    20   F01 8, F02 5, F04 4, F09 3
  BLOCKED    the fragment emits no register               13   F03, 18 checker errors
  DROPPED    a clause stands in the source, unbooked       5   F01 1, F06 3, F10 1
  NO CLAUSE  nothing in the fragment states it            25
```

**`13 -> 20` on 2026-09-04, and it is SEVEN of the twelve `DROPPED` rows, not twelve.** The
three collection sites are in `pflichten.rs` and each books a clause that already stood in
the source:

| rows | clause | kind | why that kind and not a ninth |
|---|---|---|---|
| 1 | a `table`/`group` `invariant` no `maintains` names and no `ops` carries | `W` | §7 — the refusal rested on a premise its own argument contradicts |
| 36–39 | `transition <n> { <place>: a -> b }`, `requires` or not | `D` | §8 — the from-state is never read; that is a promise at hardware Gabbro never sees |
| 59, 60 | a `walk`'s `down` and `leaf` | `W` | the emitter compiles both into CLASSIFIERS and nothing decides them |

**The five that stayed are the finding of this run, and §6 is re-priced around them.** Two of
the five turned out MORE expensive than §6 had them (rows 15, 53–55), and one turned out to be
a duty that is already DISCHARGED, so a line for it would be a false one (row 63).

> **The `18` above is not a typo for `27`.** §6 and the table both said F03 carries 27 checker
> errors; `./instrumente/pruefe-manifest.py` reads **18** in its own run today. The row state
> does not depend on it -- `BLOCKED` asks whether the fragment emits a register, and it does
> not -- but *a number that stands beside a state it does not decide still has to be true.*

**Against the sentence this replaces — `43 blocked upstream, 15 dropped, 5 carried`** — every
one of the three has moved, and only part of one move is this lane's work:

| | then | now | why |
|---|---|---|---|
| blocked | 43 | **13** | F01, F05 and F09 were repaired by other lanes on 2026-09-03. Only F03 still carries checker errors, and it is **frozen at 27 with a named reason** |
| carried | 5 | **20** | +5 because F01 now emits a register at all; +2 because a `let … else` call site was invisible to `pflichten::rufe_im_block` (rows 7 and 17); +1 because F09's walk invariant emits; **+7 on 2026-09-04 from three new collection sites** |
| dropped | 15 | **5** | the old figure counted only fragments that emitted a register. With F01, F05 and F09 unblocked the base is a different one, so the two halves are re-derived above and not carried over; **−7 on 2026-09-04** |

**The old split summed to 63 and so does this one; neither fact is evidence.** The three terms
are the thing to check, and the guard now checks two of them mechanically: a `BLOCKED` row
whose fragment DOES emit a register turns it red, and a `CARRIED` row whose line is not in the
run turns it red.

## 5. Two rows that look like hits and are not — and two pairs that share a line

**Row 57 (F08).** `toeten :: aufloesen requires #1` is anchored at `F08.gab`:31 and its text is
`Held(SCHEDS, shared)`. By anchor it lands inside the frozen `L` row `1427–1430`; by TEXT it is
what `PFLICHTEN.md` books at 1421 and 1436, both `K`, both discharged. *The anchor alone would
not have settled this line, and the ordinal settles nothing at all* — the text is the field
that decides, and this row is the measured argument for it.

**Rows 7 and 17 (F01) share ONE manifest line.** `revoke :: delete_leaf requires #4` carries
both `236` (*the cap has no children*) and `337` (*every `victim` is a leaf when `delete_leaf`
sees it*): the frozen text books the predicate twice, once at the declaration and once at the
call, and there is exactly one call. **One line, two rows** — the table says so rather than
counting the line twice.

**And so do rows 4 and 5**, which is why `20 CARRIED rows` come to `18 lines` and not to
twenty. `unlink :: cdt_wohlgeformt` carries both `188–190` (*`cdt_wohlgeformt` — every slot
reaches the root via `parent`*) and `197` (*the CDT stays well-formed across `unlink`*): the
first is the STATEMENT and the second is the DUTY at this function, and one `maintains`
clause is the only place either of them stands. *Two rows onto one line is not a defect of
the mapping; a mapping that hid it by counting twice would be.*

## 6. What the remainder costs, priced from this table

**Seven of the twelve were paid on 2026-09-04.** What follows is the re-pricing, and three of
the rows are priced DIFFERENTLY than they were — twice upward, once out of the table.

| what | rows | the price |
|---|---|---|
| repair F03 | 13 | 18 checker errors today (§4), **frozen deliberately with a named reason**; another lane holds `messung/fragmente/` |
| ~~book `table`/`group` invariants~~ | ~~1~~ **PAID** | *Was priced at a ninth `Art`. It cost none* — the statement IS `W`'s, and §7 below is the argument in full. One collection site, 14 new lines over the corpus |
| ~~book `transition` without `requires`~~ | ~~4~~ **PAID** | *Was priced as "a protocol STEP, not a promise". Measured: it is a promise* — the from-state is never read (§8). One collection site, and it books the step at EVERY `transition`, not only the ones without a guard |
| ~~book `walk`'s `down`/`leaf`~~ | ~~2~~ **PAID** | correctly priced: a collection site. Two lines per `walk` |
| book a function's own `requires` | 1 | **MORE than "a DECISION".** The decision stands: at the definition a `requires` is an assumption, at a call it is an obligation. But *executing* the other decision has a code price too: `V`'s anchor IS the call site (`Pflicht::span`) and `Material::Call` carries the actual arguments a prover substitutes. A declaration-site `V` has neither, so it needs a new `Material` variant — and `Material`'s own docstring makes that *"a compile error at every site that turns one into a goal"*: `refinement.rs` and `lean.rs` both. **A ninth `Art` or a fourth `Material`; not a collection site** |
| book `claim` / `counterprobe` | 3 | **MORE than "a DECISION", and the decision may already be made against it.** A `claim` fits none of the eight kinds: not an `ensures` at a body seen or unseen, not a call site, not a promise at hardware, not an invariant of a declaration. So it needs a ninth `Art`. *And the population's own rule points the other way:* `zaehle-pflichten.py --gabbrov` takes the three `progress` clauses OUT of the 63 because they are *"assumptions with a falsifier, and a falsifier is a promise that someone COULD refute them"*. A `claim` with a `can_fail` block is exactly that shape. **Booking it as an `open` proof obligation would put a thing in the register the population's own rule says is not one** |
| book `format … where` | 1 | **NOT a decision — measured, and it is already DISCHARGED.** `emit.rs`:4331 lowers every `where` into the decoder; `gabbro emit messung/fragmente/F10.gab` writes `if (!(DtbKopf_magie(v) == MAGIE)) return false;`. The register's second line is *"What a HUMAN still owes here"* and `ZUSTAND` is the constant `open`. *A discharged duty booked `open` is a false line, and a false line is worse than a missing one* |
| the 25 `NO CLAUSE` rows | 25 | **not reachable from the manifest at all** without either a language construct («B13», «B14», «B26») or a clause written into a fragment. *A manifest line for these would have to be invented, and an invented line is the silent loss §15 forbids, wearing the opposite coat* |

**So the honest reach today is 20 of 63, and the remaining 5 `DROPPED` rows are NOT the cheap
half of the twelve — they are the expensive half, and one of them should never be bought.**

> **The guard prints `Reachable without a language change: 25 of 63` and this table says 24.**
> That is not a disagreement to be papered over: the guard computes `CARRIED + DROPPED`, which
> is the right arithmetic over the states it knows, and `DROPPED` means *a clause stands in the
> source and the register does not book it* — which row 63 satisfies. **The extra judgement is
> that row 63's clause is DISCHARGED**, and the four states have no word for that. *A fifth
> state is a change to what the guard measures, and this lane does not make one* — so the
> difference stands here in writing instead of being legislated into the gate. The other four need a ninth
`Art`, which is `AUFTRAG-GABBROV.md` §4's third step and not a bookkeeping run's business.

*`pruefe-manifest.py` stays red at 43 of 63 missing, and the number it prints is derived from
this table. **A guard left honestly red is the deliverable** — the alternative was seven true
lines and five invented ones, and the invented five would have made it greener and worth less.*

---

## 7. The one row that turned into a corpus-wide finding — and the refusal that was lifted

Row 1 (`F01` `167–169`, *a root has no predecessor*) was `DROPPED` because
`messung/fragmente/F01.gab`:236 carries

```gabbro
invariant wurzel_ohne_vorgaenger cost O(n) runs offline :
    forall s in slots of Self :
        Self.slots[s].parent == None => Self.slots[s].prev_sibling == None;
```

and `pflichten::lauf` had no `ItemArt::Tabelle` arm. **The `Art::Walkinvariante` docstring said
this cannot happen** — *"at a `table` without `ops` it becomes an `E` per `maintains`"* — and
that half of the sentence does not hold. It now has an arm, and the row is `CARRIED`:

```
$ ./target/debug/gabbro pflichten messung/fragmente/F01.gab
obligation	CapSpace :: invariant wurzel_ohne_vorgaenger	W	messung/fragmente/F01.gab:236	open	forall s in slots of Self : Self.slots[s].parent == None => Self.slots[s].prev_sibling == None
```

### Why the refusal did not hold

Yesterday this section refused the repair with one sentence: **"a ninth `Art` moves the header
line."** *The premise is contradicted by the argument standing three paragraphs above it in the
same section*, which reads:

> **This is the exact argument the `W` kind was built on, one construct over** […] *"an `E` is
> owed by a FUNCTION that names the invariant in `maintains`. A walk invariant is owed by no
> function at all."* A table invariant that no function names is owed by no function either.

**If it is the same obligation, it needs no new kind to be booked under.** What a ninth `Art`
would have bought is a separate LETTER, not a separate duty — and the letter was never the
thing that was missing. `W` is not *"the invariant of a `walk`"*; it is **the invariant no
function owes**, which is the sentence the variant's own docstring gives as its reason for
standing beside `E`.

So the repair is the one `D` got on 2026-09-02, verbatim: **the kind stayed, the HEADING was
corrected to name what stands under it.** `Art::name()` now reads *"Invariant owed by NO
function — a `walk`, or a `table`/`group` that no `maintains` names"*, and the closing count
says `unowned invariant` where it said `walk invariant`.

**And that is not a format change**, which was checked before the word moved rather than
after. The three readers of the closing line are `pruefe-manifest.py` (`^== (\d+) obligations: `),
`manifest-lage.sh` (`^== [0-9]+ obligations`) and `pruefe-zahlen.py`, whose awk pattern is a
PREFIX ending at `precondition` and whose sum takes fields 2–12. **None of them reads the last
word of the line.** `MANIFESTFASSUNG` stays at `2`; `AUFTRAG-GABBROV.md` §4's three steps are
for a change a reader can misread, and this one no reader can see.

### The rule has two conditions, and each names a discharge

A `table`/`group` invariant is booked as `W` when **no `maintains` of the unit names it** — else
it is already an `E` at that function, and the same debt twice is worse than once — and when
**the table carries no `ops`** — else the generated mutations preserve it under the
machine-checked template `table.ops.erhaltung` (`beweise/Table_Ops_Erhaltung.thy`), and a
discharged duty is not open. *Neither condition hides a hole; both say where the duty went.*

### The census, re-measured — and every one of its five numbers had moved

Over the **145 of 196** `.gab` files under `beispiele/` and `messung/` that emit a register at
all (2026-09-04):

```
  named `table`/`group` invariants                       22   (was 19)
    a function `maintains` it   -> booked as `E`          4   (was  2)
    under a `table … ops`       -> carried by U-3          4   (was  2)
    NOTHING maintains it        -> booked NOWHERE         14   (was 15)
  (`walk` invariants, booked as `W` since 2026-08-31:      6   (was  4))
```

The fourteen: `beispiele/01-tabelle.gab`:69 and :76 · `09-ohne-zeiger.gab`:42 ·
`17-gruppe-ueber-zwei-sperren.gab`:47 (a `group`) · `18-vorfahren.gab`:37 ·
`39-auftragsdienst.gab`:38 · `messung/caprock/kapraum.gab`:72 and :76 ·
`messung/fragmente/F01.gab`:236 · `messung/proben/probe-stellungen.gab`:37, :41, :47, :52, :57.

**Three of yesterday's fifteen were MAINTAINED and one file was missed twice.**
`53-zwei-orte.gab`:47, `55-kindkette.gab`:72 and `messung/netz/udp-echo.gab`:135 each have a
`maintains` naming them — all three already at `340ef3c`, the commit that wrote the census, so
this is not a tree that moved underneath it. *And `pflichten.rs` said so in its own words on
the same day:* `spezpraedikate`'s docstring names `antwortpflicht_paarig` (twice),
`kind_zeigt_zurueck` and `belegt_hat_adresse` as **the four `maintains` lines whose wording sat
at a `table`/`group` invariant.** Two registers over one set, written the same day, and they
disagreed.

Missing from it: `messung/caprock/kapraum.gab`:72 and :76.

> **The two figures are measured twice and agree.** Once from the SOURCE
> (`invariant <name>` at a `table`/`group` against every `maintains` of the same unit) and
> once from the ARTEFACT (`W` lines of `gabbro pflichten` that are not a `walk`'s). Both say
> **14**, and the fourteen anchors are the same fourteen. *A census taken with the parser
> instead of a regex is the one that decides* — the regex reading over the same corpus said
> 15, and the extra one is `messung/race-proben/gruppe-unbekannter-traeger.gab`:10, in a file
> that emits no register at all.

## 8. `transition` — the from-state is never read, and that is the whole argument

Rows 36–39 were `DROPPED` with the price *"a decision about what the `D` count means — a
`transition` without `requires` states a protocol STEP, not a promise."* **Measured, the step
IS the promise.** `messung/fragmente/F04.gab`:91 carries

```gabbro
transition ack { DEVICE_STATUS: 0 -> ACK } effects { writes DEVICE_STATUS }
```

and `gabbro emit messung/fragmente/F04.gab` lowers it to

```c
static inline __attribute__((unused)) void VirtioPci_ack(VirtioPci *d) {
    (*(volatile uint8_t *)(d->basis + 20)) = (uint8_t)1u;
}
```

**The `0` on the left of the arrow is never read and never checked.** That the register was in
the from-state, and that writing the word puts the device in the to-state, is a promise at
hardware Gabbro never sees — which is `Art::Geraetezusage`'s defining property in its own
words (*"A foreign duty sits at CODE Gabbro does not see; this one sits at HARDWARE Gabbro
does not see"*) and not a widening of it.

*The step is booked at EVERY `transition`, not only at the ones without a guard.* A rule that
books a clause only when a DIFFERENT clause is absent is not a rule about the clause. So F02's
five guarded transitions now carry two lines each — `Vtd :: transition scharf_te requires` and
`Vtd :: transition scharf_te` — because a guard and a move are two statements, and a register
that merged them could not say which one a prover had taken up.
