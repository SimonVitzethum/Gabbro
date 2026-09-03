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
| **the manifest** | the `obligation` records `gabbro pflichten` emits over `messung/fragmente/F*.gab`. `./instrumente/pruefe-manifest.py` → **27** lines today |

**Subtracting the second from the first answers nothing**, and that was the guard's arithmetic
until today. The two sets are not nested: `PFLICHTEN.md` books **`K` (plumbing) and `L`
(logic)** rows and GabbroV's population is the `L` half alone, while the manifest emits a line
for every obligation the checker finds — `K` and `L` together. Measured on 2026-09-03: of the
27 manifest lines, **16 carry a `K` row or no row at all**. So `63 − 27 = 36` counted sixteen
lines as if each had closed a logic obligation, and not one of them had.

*The eleven that remain carry THIRTEEN rows*, because two lines do double duty — see §5.
`27 = 11 + 16` and `13 CARRIED rows = 11 lines`; both facts are printed by the guard, and
neither is a coincidence worth resting on.

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
reads as *n* repairable holes; measured today, **12 of the 37 open rows have a clause standing
in the source** and 25 do not.

## 3. The table

Anchors in column 3 are `dokumente/FRAGMENTE.md` line numbers (the frozen population); anchors
inside a reason are `messung/fragmente/F*.gab` line numbers (today's source).

| # | frag | anchor | obligation | state | manifest line / reason |
|---|---|---|---|---|---|
| 1 | F01 | 167–169 | a root has no predecessor | DROPPED | `F01.gab`:236 `invariant wurzel_ohne_vorgaenger` at the `table`. `pflichten::lauf` has no `ItemArt::Tabelle` arm — a table invariant that no function `maintains` and no `table … ops` carries is booked by nothing |
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
| 15 | F01 | 301 | the CDT is well-formed on entry to `revoke` | DROPPED | `F01.gab`:390 `requires … cdt_wohlgeformt(c)`. **A function's own `requires` reaches the manifest only through a CALL SITE**, and `revoke` has no caller in this unit — so the contract a stranger has to satisfy stands in no line |
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
| 36 | F04 | 773 | `ack` — from 0 to ACK | DROPPED | `F04.gab`:91 `transition ack { … }` **without a `requires`**. The register books a `transition` only when it carries one |
| 37 | F04 | 774 | `drv` — ACK to ACK or DRIVER | DROPPED | `F04.gab`:92 `transition drv { … }` without a `requires` |
| 38 | F04 | 775–776 | `featok` | DROPPED | `F04.gab`:93 `transition featok { … }` without a `requires` |
| 39 | F04 | 777–779 | `drvok` | DROPPED | `F04.gab`:95 `transition drvok { … }` without a `requires` |
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
| 53 | F06 | 1129–1141 | the measuring instrument reports the known depth | DROPPED | `F06.gab`:240 `check kstack_eichung { claim "…" }` — a `claim` produces no obligation line |
| 54 | F06 | 1145–1158 | at the foot of every EL0 kernel stack an eighth stays untouched | DROPPED | `F06.gab`:256 `check kstack { claim "…" }` — a `claim` produces no obligation line |
| 55 | F06 | 1160 | the check can go RED | DROPPED | `F06.gab`:286 `counterprobe "…" expects erschoepft_waechst` — produces no obligation line |
| 56 | F07 | 1289–1291 | before the MMU the console is lock-free | NO CLAUSE | a property of the PHASE; no clause states it |
| 57 | F08 | 1427–1430 | the revalidation — the thread may have vanished between selection and deed | NO CLAUSE | the `match` over `aufloesen` carries no clause. *The one emitted F08 line looks like a hit by anchor and is a different statement — see §5* |
| 58 | F08 | 1439–1442 | both exits are forced | NO CLAUSE | `match` forces them; the correctness carries no clause |
| 59 | F09 | 1531 | a non-leaf entry points at a next level | DROPPED | `F09.gab`:118 `down : roh when !it.PS` — a `walk`'s `down` clause produces no obligation line |
| 60 | F09 | 1532 | `PS == 1` marks a leaf | DROPPED | `F09.gab`:119 `leaf : it.PS` — a `walk`'s `leaf` clause produces no obligation line |
| 61 | F09 | 1543 | the leaf level is reached | NO CLAUSE | `walk … levels` bounds the descent; that the leaf level is REACHED is stated nowhere |
| 62 | F09 | — | W^X over the page table | CARRIED | `Seitenabstieg :: invariant wx_getrennt` |
| 63 | F10 | 1631–1632 | the buffer is a device tree — `magie == MAGIE` | DROPPED | `F10.gab`:9 `magie : u32 where magie == MAGIE` — a `format … where` produces no obligation line |

## 4. The split, derived

```
population                                                63
  CARRIED    a manifest line states it                    13   F01 7, F02 5, F09 1
  BLOCKED    the fragment emits no register               13   F03, 27 checker errors
  DROPPED    a clause stands in the source, unbooked      12   F01 2, F04 4, F06 3, F09 2, F10 1
  NO CLAUSE  nothing in the fragment states it            25
```

**Against the sentence this replaces — `43 blocked upstream, 15 dropped, 5 carried`** — every
one of the three has moved, and only part of one move is this lane's work:

| | then | now | why |
|---|---|---|---|
| blocked | 43 | **13** | F01, F05 and F09 were repaired by other lanes on 2026-09-03. Only F03 still carries checker errors, and it is **frozen at 27 with a named reason** |
| carried | 5 | **13** | +5 because F01 now emits a register at all; +2 because a `let … else` call site was invisible to `pflichten::rufe_im_block` (rows 7 and 17); +1 because F09's walk invariant emits |
| dropped | 15 | **12** | the old figure counted only fragments that emitted a register. With F01, F05 and F09 unblocked the base is a different one, so the two halves are re-derived above and not carried over |

**The old split summed to 63 and so does this one; neither fact is evidence.** The three terms
are the thing to check, and the guard now checks two of them mechanically: a `BLOCKED` row
whose fragment DOES emit a register turns it red, and a `CARRIED` row whose line is not in the
run turns it red.

## 5. Two rows that look like hits and are not

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

## 6. What the remainder costs, priced from this table

| what | rows | the price |
|---|---|---|
| repair F03 | 13 | 27 checker errors, **frozen deliberately with a named reason**; another lane holds `messung/fragmente/` |
| book `table`/`group` invariants | 1 here, **15 over the corpus** | a ninth `Art`, and that moves the header line — so `AUFTRAG-GABBROV.md` §4's three steps apply and this would be the third of them. **Named and refused in this lane; the measurement is in §7 below** |
| book a function's own `requires` | 1 | not a collection site but a DECISION: at the definition a `requires` is an assumption, at a call it is an obligation. The manifest carries the second and not the first, so a stranger's contract is not in it |
| book `transition` without `requires` | 4 | a decision about what the `D` count means — a `transition` without `requires` states a protocol STEP, not a promise |
| book `claim` / `counterprobe` | 3 | a decision about whether an executed check owes a proof obligation |
| book `walk`'s `down`/`leaf` | 2 | a collection site; both are predicates the checker already reads |
| book `format … where` | 1 | a decision: the `where` is CHECKED by the decoder, so the obligation is discharged rather than open |
| the 25 `NO CLAUSE` rows | 25 | **not reachable from the manifest at all** without either a language construct («B13», «B14», «B26») or a clause written into a fragment. *A manifest line for these would have to be invented, and an invented line is the silent loss §15 forbids, wearing the opposite coat* |

**So the honest reach today is 13 of 63, and the next 11 are decisions rather than code.** Even
granting every one of the 12 `DROPPED` rows, the gate stops at **25 of 63** while the 25
`NO CLAUSE` rows and F03's 13 stand where they are. *`pruefe-manifest.py` stays red, and the
number it prints is now derived from this table instead of from a sentence somebody typed.*

---

## 7. The one row that turned into a corpus-wide finding — and is refused by name

Row 1 (`F01` `167–169`, *a root has no predecessor*) is `DROPPED` because
`messung/fragmente/F01.gab`:236 carries

```gabbro
invariant wurzel_ohne_vorgaenger cost O(n) runs offline :
    forall s in slots of Self :
        Self.slots[s].parent == None => Self.slots[s].prev_sibling == None;
```

and `pflichten::lauf` has no `ItemArt::Tabelle` arm. **The `Art::Walkinvariante` docstring
says this cannot happen** — *"at a `table` without `ops` it becomes an `E` per `maintains`"*.
That is the half of the sentence that does not hold, and the measurement says so:

```
python3 <count `invariant <name>` at a table/group against every `maintains` of the unit>
  named `table`/`group` invariants, clean corpus       19
    a function `maintains` it   -> booked as `E`        2
    under a `table … ops`       -> carried by U-3        2
    NOTHING maintains it        -> booked NOWHERE       15
  (`walk` invariants, booked as `W` since 2026-08-31:    4)
```

The fifteen: `beispiele/01-tabelle.gab`:69 and :76 · `09-ohne-zeiger.gab`:42 ·
`17-gruppe-ueber-zwei-sperren.gab`:47 (a `group`) · `18-vorfahren.gab`:37 ·
`39-auftragsdienst.gab`:38 · `53-zwei-orte.gab`:47 · `55-kindkette.gab`:72 ·
`messung/fragmente/F01.gab`:236 · `messung/netz/udp-echo.gab`:135 ·
`messung/proben/probe-stellungen.gab`:37, :41, :47, :52, :57.

**This is the exact argument the `W` kind was built on, one construct over and at fifteen
times the surface**: *"an `E` is owed by a FUNCTION that names the invariant in `maintains`.
A walk invariant is owed by no function at all."* A table invariant that no function names is
owed by no function either — and the register is silent about it.

### Why it is not built here

**A ninth `Art` moves the header line**, and `AUFTRAG-GABBROV.md` §4 puts a format change in
three steps of which this is the third: version field, then every reader on both formats, then
the format. Today's readers know `1` and `2`; a ninth kind needs a `3` and the two silent
readers (`pruefe-zahlen.py`, `manifest-lage.sh`) prepared for it **before** the emitter moves.
*A reader taught the new format after the writer moved has a window in between in which it
reports a number out of a format it cannot read* — and `CLAUDE.md` holds the measured cost of
that window: seven guards read a document and four went silently blind.

**So: measured, priced, and left standing with a name on it.** It is one row of the 63 and
fifteen sites of the corpus, and *a hole with a name is not green* — but the alternative here
was a format change bolted onto the end of a bookkeeping run, which is how the window opens.
