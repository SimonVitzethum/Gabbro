# Gabbro — the proof obligations of the ten fragments, one by one

> **Newly assigned 2026-08-17, not reconstructed.** This file replaces the aggregate
> **74 / 17 / 57 / 19 / 1** of 2026-08-14, whose assignment was never in the folder
> (`MESSUNGEN.md`, W7 sweep: *"Found: ONE"* site). It does not continue it — the two are
> **not convertible**, because the old one counted at a coarser granularity.
>
> **Protocol, gate and result** stand in [`MESSUNGEN.md`](MESSUNGEN.md) (*VORAB — NEUZUWEISUNG*
> and the result section beneath it). **This file is the source list.** *A number without one
> does not belong in the folder — W7.*

**Population:** the ten ```gabbro blocks of [`FRAGMENTE.md`](FRAGMENTE.md) @ `708beed`,
1 104 lines. The file carries its own freeze sentence, so the line numbers are stable.

**Reading the columns**

| | |
|---|---|
| **Line** | `FRAGMENTE.md:NNN` — the anchor of the obligation |
| **K / L** | plumbing / logic, by the criterion of [`BEWEIS.md`](BEWEIS.md): *mentions only the MACHINE → K; mentions the SUBJECT → L* |
| **discharged by** | a refusal code of a **present-day** pass, or a **named gap**. **A gap in a K row is a breach of the thesis at that site** and is set in bold. |

> **The classification is against TODAY's grammar, not against the frozen text.** Where
> `FRAGMENTE.md` records a finding that has since been closed, the row says so — «B2»
> (`atomicdecl`/`lockdecl` unreachable) is closed, `item` lists both (`SYNTAX.md`:169).
> *The fragment is a record of 2026-08-14; the question is what carries today.*

---

# F1 — Cap space (`FRAGMENTE.md`:92–349)

**Origin:** `crates/caprock-cap/src/space.rs:1062` · `:1044` · `:991` · `:619`

## Declarations

| Line | Obligation | | discharged by |
|---|---|---|---|
| 101 | every `SlotIdx` lies in 0 ..< 80256 | K | `M101`/`M104` |
| 102 | every `Refcount` lies in 0 ..< 80256 | K | `M101`/`M104` |
| 110–118 | every failure path names one of the six reasons | K | `exhaustive`, name pass |
| 128–131 | an object is exactly one `ObjectKind` | K | `tagged type` |
| 136 | CAPS is held at every access to `plaetze`/`cdt`, in rank order | K | `H001`–`H006`, `E006` |
| 137 | MEM likewise, rank 9 | K | `H001`–`H006` |
| 142–149 | every `index into CapObjects` lies below 4 096 | K | `M103` |
| 145 | the wraparound at `CapObjects.gen` is intended | K | `wrapping` («B32») |
| 151–162 | every `index into CapSpace` lies below 80 256 | K | `M103` |
| 154 | the wraparound at `CapSpace.gen` is intended | K | `wrapping` |
| 167–169 | a root has no predecessor | L | `D001` schedules it, the human proves it |
| 171–173 | `slots[s.next].prev == s` — the sibling chain is mutual | L | **gap: «B14» — `pred` cannot resolve an `option index into`** |
| 174–177 | `refcount == count(s in slots : s.object == o)` | L | **gap: «B13» — `pred` knows no aggregation and no cross-table domain.** *The core of the capability system's bookkeeping.* |
| 184–186 | `ist_blatt` is pure | K | `E009` |
| 188–190 | `cdt_wohlgeformt` — every slot reaches the root via `parent` | L | the formulation is the human's |

## `unlink` (192–218)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 193 | CAPS is held on entry | K | `H001`/`E006` |
| 193 | the slot is occupied | K | declared, checked at every call site |
| 194–196 | afterwards parent, prev and next are `None` | K | declared · *borderline: it names three places, not the tree — hence K, per `delete_leaf` row 3* |
| 197 | the CDT stays well-formed | L | the human |
| 198 | nothing outside `c.slots` is touched | K | `E005`/`E006`/`E008`/`E010` |
| 199 | `<= 40 ops` | K | `K001` |
| 201–213 | the four relink cases are exhaustive and each is correct | L | `match` forces the cases, the correctness is the human's |
| 202–217 | `c.slots[p]`, `c.slots[par]`, `c.slots[n]` in range | K | `M103` |

## `release_slot` (220–229)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 221 | CAPS is held | K | `H001` |
| 222 | the slot is free afterwards | K | declared |
| 223 | nothing else is touched | K | `E005`/`E006` |
| 224 | `<= 20 ops` | K | `K001` |
| 226 | the wraparound at `gen` is intended | K | `wrapping` |

## `delete_leaf` (231–294) — **the R14 calibration set**

*The eleven rows marked ✔ are the published breakdown of 2026-08-15 (`BEWEIS.md`:1078–1092),
found again at their Gabbro anchor. The unmarked rows are obligations the Gabbro fragment
carries and the Rust original did not — because it does not write them down.*

| Line | Obligation | | discharged by |
|---|---|---|---|
| 233–234 | the `own` values are neither duplicated nor dropped | K | `L101`–`L105` |
| 236 | CAPS is held | K | `H001` |
| 236 | MEM is held | K | `H001` |
| 236 | the slot is occupied | K | declared |
| 236 | the cap has no children — `ist_blatt` | L | the human |
| 243 ✔ | the slot is free afterwards | K | declared |
| 244–245 ✔ | the refcount fell by exactly one | L | **gap: «B31» — `old` hangs under `atompred`, not under `primary`. No difference statement is writable — and that hits every "after against before".** |
| 246 ✔ | the CDT stays well-formed | L | the human |
| 247 | only the named places change | K | `E005`/`E008`/`E010` |
| 248 | `<= 200 ops` | K | `K001` |
| 250 ✔ | `c.slots[s]` in range | K | `M103` |
| 251 ✔ | `unlink`'s precondition holds here | K | call graph, `E008` |
| 252 ✔ | `release_slot`'s precondition holds here | K | call graph, `E008` |
| 268 | `o.slots[obj]` in range | K | `M103` |
| 268/271 ✔ | no underflow at `refcount -= 1` | K | **gap: `narrow … else` is a HAND-WRITTEN check.** *The folder counts these separately («B29», `zaehle-bereichspflichten.py`) — it is the same quantity.* |
| 273 ✔ | released exactly at zero | L | the human |
| 277 ✔ | `Memory` — the region goes back to the RAM allocator | L | the human |
| 278 ✔ | `Dma` — released only after proof | L | the human |
| 279 ✔ | `Reply` — the caller is unblocked | L | the human |
| 291 ✔ | the wraparound at `gen` is intended | K | `wrapping` |
| 292 ✔ | no reference survives | L | the human |

## `revoke` (296–339)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 301 | CAPS is held | K | `H001` |
| 301 | MEM is held | K | `H001` |
| 301 | the CDT is well-formed on entry | L | the human |
| 302 | it stays well-formed | L | the human |
| 303 | only the named places change, `c.slots` is consumed | K | `E005`/`L101` |
| 328 | `<= 16 452 480 ops` | K | `K001` — **and the pass caught the declared 200 here: five orders of magnitude** |
| 334 | the traversal terminates | K | `S001`/`S002` + witness ordering |
| 334 | `descendants of` is bounded by the table | K | `kosten.rs`, `count NSLOTS` |
| 337 | every `victim` is a leaf when `delete_leaf` sees it | L | the human — *the load-bearing statement of `revoke`* |

## Callee declarations (344–346)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 344–346 | every callee names its effects and its bound | K | `K003` refuses otherwise — *it says so instead of silently estimating* |

**F1: 59 obligations — 42 K, 17 L. Hanging: 4** (three L, one K).

---

# F2 — VT-d (`FRAGMENTE.md`:397–530)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 397 | every access goes to the `mmio` space | K | `R001` (placement rule) |
| 400 | a write to GCMD carries the state bits from GSTS | K | `mirrors` — **one line for trap 4's x86 form** |
| 402–419 | every field access lies inside its register | K | `M101`, `bitpos` |
| 403–419 | a `class r` register is never written, a `class w` never read | K | `R002`/`R003` |
| 425–426 | FSTS is MIXED: 7:0 are RW1C, 15:8 (FRI) are r | K | **gap: «B23» — `regdecl` carries ONE class. FRI is untypable, and FRI is how the driver finds the record at all** |
| 436 | the computed bank location lies inside the register file | K | `M103` via `count 256` |
| 438–442 | a bit position beyond 64 — which word does it mean? | K | **gap: «B24» — `bitpos` says nothing about it, nor about the interaction with `endian`** |
| 444 | IOTLB likewise | K | `M103` |
| 450–453 | the pre-state of a `transition` at `GCMD.TE` comes from `GSTS.TES` | K | **gap: «B26» — half resolved; `mirrors` says where the carried bits come from, not whether it also supplies the pre-state** |
| 454–455 | `setze_rtp` — TE off or RTPS already set | L | the human — *the remapping unit's protocol* |
| 457–458 | `scharf_te` — RTPS is set | L | the human |
| 460–461 | `setze_irtp` — QIES is set | L | the human |
| 463–464 | `scharf_ire` — IRTPS set and CFIS clear | L | the human |
| 466–467 | `scharf_qie` — QIES is clear | L | the human |
| 454–468 | every transition writes only GCMD | K | `E005` |
| 471–482 | every failure path names one of the nine reasons | K | `exhaustive` |
| 489–491 | the fault address is page-aligned | K | `format` `where` |
| 493–499 | the reason code lies in 0x01..0x0c | K | `M101` — **and only because the codes happen to be contiguous: «B25», `intty` carries an interval, not a value set** |
| 498 | an empty fault register is REFUSED, not reported empty | K | **gap: «B22-near» — `format` knows only refusal. In the original that is the difference between "no fault" and "record unreadable"** |
| 505–510 | the second-level PTE layout | K | `format` |
| 512–518 | the context entry layout, `AW @[66:64]` crosses the word | K | `format`; «B24» again |
| 520–522 | TE arms translation; DMA without a context entry faults | K | `assume` **with a falsifier** |
| 524–526 | GCMD is written whole | K | `assume` — **expressly `unfalsifiable`, with the reason: a probe would have to open the very window the mechanism is built against** |
| 528–530 | after FSTS.PFO further faults are dropped | K | `assume` **with a falsifier** |

**F2: 24 obligations — 19 K, 5 L. Hanging: 4, all K.**

---

# F3 — IPC fastpath (`FRAGMENTE.md`:554–704)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 560–566 | every result names one of the four reasons | K | `exhaustive` |
| 570–575 | every queue index lies in range | K | `M101` |
| 577–585 | every `index into Endpoint` lies below 64 | K | `M103` |
| 587–589 | `caller` and `reply_owner` are set together or not at all | L | the human |
| 592–603 | the two places are written in **one** step | L | **gap: «B17» — `transition` writes exactly ONE `place`. The whole statement of the fragment, and it is not writable** |
| 609–611 | the message arrived — `msg_kopiert` | L | **gap: «B12» — no numeric-range domain; the substitute `elems of` has two readings and the grammar fixes neither** |
| 610 | `msg_kopiert` is pure | K | `E009` |
| 613–624 | the callback's contract stands at the pointer type | K | **gap: «B9» — `fnptr` carries no `requires`, no `ensures`, no `effects`** |
| 630–631 | postconditions may speak about the return value | L | **gap: «B6» — `fndecl` binds no name for it; `old(place)` exists, a `result` does not** |
| 632 | EPS is held | K | `H001` |
| 632 | the endpoint slot is occupied | K | declared |
| 633 | `antwortpflicht_paarig` is maintained | L | the human |
| 638–639 | only the named places change, `dienste` included | K | `E005`–`E010` — **the `reads dienste` half became visible only through `E008`** |
| 640 | `<= 2000 ops` | K | `K001` |
| 642 | a quiescing endpoint starts no new transaction | L | the human |
| 642 | `e.slots[core]` in range | K | `M103` |
| 646 | `current_id`'s contract holds | K | `E008`/`K003` |
| 648–651 | the fastpath takes the FIRST live receiver and stops | L | **gap: «B10» — `traverse` yields no value and knows no `break`; `by consuming` drains the whole queue. Not verbosity: a different program** |
| 653–659 | the receiver traversal terminates | K | `S001` |
| 656 | the chosen receiver is alive | L | the human |
| 662–667 | a full queue is REFUSED by name, not blocked | L | D11 literally — **carried, and the best move in F3** |
| 668 | the caller is blocked | L | the human |
| 671 | the message arrives at the right thread | L | the human |
| 676–677 | the invariant does not hold between the two assignments | L | **gap: «B17» at its site** |
| 678 | a same-core rendezvous switches directly | L | the human |
| 687–703 | every callee names its effects and its bound | K | `K003` |

**F3: 26 obligations — 13 K, 13 L. Hanging: 6** (five L, one K).

---

# F4 — virtio driver (`FRAGMENTE.md`:753–896)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 753 | every access goes to the `mmio` space | K | `R001` |
| 754–769 | register classes are respected | K | `R002`/`R003` |
| 764 | the device's `QUEUE_SIZE` lies below QMAX | K | **gap: «B26» — `regdecl` carries a `requires` but no named exit. "Too big" yields no `reason` value** |
| 773 | `ack` — from 0 to ACK | L | the human — *the virtio protocol* |
| 774 | `drv` — ACK to ACK\|DRIVER | L | the human |
| 775–776 | `featok` | L | the human |
| 777–779 | `drvok` | L | the human |
| 780–782 | a reset applies from EVERY state | L | **gap: «B26» — no placeholder for the pre-state, so the transition table cannot be complete** |
| 785–792 | `used` belongs to the device — the register class per phase | K | **gap: «B18» — `device` knows no phases. And this site carries a PAID-FOR trap: in a reused region the `used` ring holds the previous driver's end state** |
| 796–800 | the five barriers of the real driver follow from the declaration | K | **gap: «B19» — `publishes` sits at `atomicdecl`, not at a device register. The most safety-critical publication in the tree is not an atomic at all** |
| 802 | `dma` space, and `n >= 1` | K | `R001` + `M101` |
| 803–817 | every ring index lies below 256 | K | `M103` |
| 810 | the avail index wraps at 65 536 by design | K | `wrapping` at the declaration («B32», closed) |
| 828 | the setup token exists exactly once | K | `L101`–`L105`; **notation gap «B3»: `typedecl` demands `params` in the parentheses — which hits `Held(Lock)` in every `requires` of the file** |
| 830–831 | `queue_reset` writes only `q` | K | `E005` |
| 833–834 | after `queue_arm` no path can write `USED_IDX` | K | `L101` — **carried, and it replaces the phases without a new mechanism** |
| 836 | a buffer belongs to exactly one side | L | the human |
| 838–841 | the unproven reason is named | K | `reason` |
| 843 | `head` lies below 256 | K | `M101` |
| 844 | only `q` changes | K | `E005` |
| 847 | `<= 9 ops` | K | `K001` — **the declared 4 was wrong; read off with `gabbro kosten`, not estimated (W2)** |
| 850 | the divisor is not zero | K | `n : u16 in 1 .. QMAX` |
| 851 | `q.AVAIL_RING[platz]` in range | K | `M103` |
| 872–876 | the V rules do not narrow a REGISTER place after a comparison | K | **gap: «B33» — undecided. Either intent (a register may change between check and use) or a hole. If it is intent, the reason belongs written down** |
| 877 | the ring counter wraps intentionally | K | `wrapping` |
| 880–881 | `poll_used` reads only `q` | K | `E010` |
| 885–889 | the poll terminates and the overflow is NAMED | K | `S001`/`S002` — **carried unchanged, and the clause order matches the production** |
| 886 | it ends because **the device** completes or faults | L | the human — *the borderline case the criterion decides: not "over a finite set" but "because the device makes progress"* |
| 891 | the divisor is not zero | K | `n : u16 in 1 .. QMAX` |
| 892–894 | a function may PRODUCE a compound | K | **gap: «B7» — no struct literal in `primary`. Here a scalar instead of the compound** |
| 895 | `q.USED_RING[s].id` in range | K | `M103` |

**F4: 30 obligations — 24 K, 6 L. Hanging: 7** (six K, one L).

---

# F5 — Userspace service loop (`FRAGMENTE.md`:919–1018)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 921–934 | every status and every exit names its reason | K | `exhaustive` |
| 936 | every request decodes to exactly one op | K | `tagged type` |
| 938–949 | the syscall register assignment | K | **gap: «B27» — `arch ident` exists, the register assignment does not. The one place where 168 measured `asm!` sites should converge has no carrier: the trusted surface does not shrink, it moves into a `prim` declaration without content** |
| 951–952 | `run` diverges and touches only the named world | K | `E005`/`E010`; `-> never` lets the passes see the error branches do not fall through |
| 954–960 | every startup failure is named and leaves the program | L | the human — six `let … else` |
| 964–967 | "never read yet" is distinguishable from zero | L | **gap: «B14» — `option` stands only in `slottype`, not in `typeexpr`. Exactly the reading the fragment was written against** |
| 969–976 | the service loop has a NAMED exit | L | **gap: «B11» — no `leave`, no `break`, no `continue`. The difference between "D0 falls by construction" and "the service loop is not writable". F5 breaks here** |
| 977–980 | each pass is bounded and the overflow is named | K | `S001`/`S002` |
| 981 | it makes progress because a client calls or the endpoint is revoked | L | the human |
| 983 | a revoked endpoint ends the service | L | the human |
| 984 | the six ops are exhaustive | K | `tagged type`, `match` |
| 985–991 | `Info` — capacity is reported and cached | L | the human |
| 988–990 | a reply may be a compound | K | **gap: «B7» — four arguments instead of one field** |
| 992–993 | `Read`/`Write` — the request lies inside the client's range | L | the human |
| 994–997 | `Flush` — the flush completed before the reply | L | the human |
| 998 | `Scan` — the partition table is read or refused | L | the human |
| 999–1006 | `Stop` — the reply still goes out before the service ends | L | **gap: «B11» — without `leave` only `exit()`, so the cleanup promise moves to two places. Literally the class C8 paid for** |
| 1014–1016 | `exit`/`signal`/`watchdog` name their effects | K | `E008` — **without `-> never` six `S002` arose from this alone** |

**F5: 18 obligations — 8 K, 10 L. Hanging: 5** (three L, two K).

---

# F6 — Test scaffold (`FRAGMENTE.md`:1047–1163)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1049–1053 | the stack kind is named | K | `exhaustive` |
| 1056 | every `Bytes` lies in 0 .. 65536 | K | `M101` |
| 1058 | the reserve divisor is not zero | K | `M101` — **`u32 in 1 .. 64` is what makes `g / MIND_RESERVE_NENNER` legal** |
| 1061–1064 | the ten `atomic` declarations are reachable from `program` | K | `item` (`SYNTAX.md`:169) — **«B2» is CLOSED; the frozen text records it as hanging** |
| 1065–1069 | the high-water mark is writable | K | **gap: «B21» — no `accumulates max`/`min`/`+`. 213 RMW sites tree-wide, 19 of them `fetch_max`/`fetch_min`. The measurand of this fragment is not writable, and `SYNTAX.md` names it the first candidate for "two demanded properties contradict each other"** |
| 1070–1072 | "never measured" is distinguishable from zero | L | **gap: «B14», the same as F5** |
| 1073–1082 | the ten counters carry no payload | K | `V001`–`V004`, `publishes nothing relaxed` |
| 1084–1085 | the returned depth does not exceed the stack | K | **notation gap «B6» — the line helps itself with the function name, and that is guessed, not written** |
| 1086 | `unberuehrt` reads only `s` | K | `E010` |
| 1088 | the counter stays in 0 .. 65536 | K | `M101` |
| 1091–1092 | the traversal terminates | K | `S001` — **notation wart «B30»: `touches` takes an `efflist` without braces while `effects` is braced everywhere else** |
| 1094 | the first untouched word marks the depth | L | the human |
| 1094/1103 | `i * 8` does not overflow | K | `M101`/`M104` |
| 1100 | the counter stays below 65 536 | K | **gap: the bound falls out of the domain, but M1 does not see it — the counter is an ordinary local. `narrow … else` is hand-written, and its else branch CANNOT BE TAKEN and must stand there anyway** |
| 1106–1112 | a function may return a pair | K | **gap: «B7» + «B6» block each other — hence two functions and a double traversal** |
| 1113–1114 | `s.len >= 8` | K | `M101` |
| 1115 | only the named atomics change | K | `E005`/`E010` |
| 1121 | `s.len - frei` does not underflow | K | the callee's `ensures` — **not a flow rule. Costs one line of postcondition, no proof.** *The best-carried K in the corpus* |
| 1126–1128 | a claim may be written precisely | K | **gap: «B22» — `claim` takes one string and `char` excludes `newline`. All three real claims are multi-line. A claim that must fit one line gets written shorter, not more precisely** |
| 1129–1141 | the measuring instrument reports the known depth | L | the human — **R14 as a language construct** |
| 1142 | the calibration ran at least once | K | `floor` |
| 1145–1158 | at the foot of every EL0 kernel stack an eighth stays untouched | L | the human |
| 1151–1155 | an `option`-valued `place` can be unpacked | K | **gap: «B14» — `let … else` demands a `call` on the right, and an atomic is a `place`** |
| 1157 | `(g - f)` does not underflow | K | **gap: `f < g / N` gives `f < g` only through the division; the V rules do no arithmetic** |
| 1159 | the measurement has a floor | K | `floor` |
| 1160 | the check can go RED | L | `counterprobe` — **the speech test as a language construct** |

**F6: 26 obligations — 21 K, 5 L. Hanging: 8** (seven K, one L).

---

# F7 — Loader / bringup (`FRAGMENTE.md`:1280–1333)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1285 | the boot token arises once, travels and is consumed | K | `L101`–`L105` |
| 1289–1291 | before the MMU the console is lock-free — **a property of the PHASE** | L | the human |
| 1293–1299 | "cap tables before the first cap" | K | **gap: «B37» — the token carries the order as LINEARITY, not as ORDER. `mmu_an` separates before/after the MMU; the four ordering constraints WITHIN one phase need either a token per boot step (the vocabulary grows with every step) or an order on tokens, and there is none** |
| 1300–1318 | every boot step consumes the token and returns it | K | `L101` |
| 1300–1318 | every boot step names its effects and its bound | K | `E005`/`K003` |
| 1317–1318 | after the root task no path can do what only boot allowed | K | `L101` — **carried, and it is the fragment's win** |
| 1320–1323 | `hochlauf` costs at most the sum of its steps | K | `K001`/`E008` |
| 1325–1330 | every step happens exactly once | K | `L101` |
| 1325–1330 | the steps happen **in this sequence** | K | **gap: «B37» at its site** |

**F7: 9 obligations — 8 K, 1 L. Hanging: 2, both K** — *and they are the same gap.*

---

# F8 — Scheduler (`FRAGMENTE.md`:1409–1461)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1414–1415 | every `KernIdx`/`FadenId` lies in range | K | `M101` |
| 1417–1419 | every `index into Laufliste` lies below 1 024 | K | `M103` |
| 1418 | the priority lies in 0 .. 255 | K | `M101` |
| 1421 | SCHEDS is taken in rank order | K | `H006` — **recomputed since 2026-08-16, not merely declared** |
| 1422 | SCHEDS is held at most 300 ops | K | `K002` |
| 1423 | shared at most 32 ops | K | `K004` — **its own computed quantity (N3)** |
| 1427–1430 | the revalidation — the thread may have vanished between selection and deed | L | the human — *without `aufloesen`, `toeten` would be a race* |
| 1432–1434 | only the named places change, `<= 340 ops` | K | `E005`/`E006`/`K001` |
| 1436 | the critical section covers resolve **and** write | K | `E006`/`H001` |
| 1439–1442 | both exits are forced | L | `match` forces them, the correctness is the human's |
| 1440 | `l.slots[i]` in range | K | `M103` |
| 1447–1451 | `masks IRQ` carries the value across the lock boundary | K | **gap: «B38» — the effect exists, but it is not tied to the lock boundary. The reason already stands in the language and cannot be used. `Stale(T)` in the proposed form is REFUTED at this site** |
| 1452–1455 | `beenden` holds SCHEDS, masks IRQ, `<= 16 ops` | K | `H001`/`E006`/`K001` |
| 1457 | `l.slots[k]` in range | K | `M103` |

**F8: 14 obligations — 12 K, 2 L. Hanging: 1, K.**

---

# F9 — MMU / page tables (`FRAGMENTE.md`:1503–1550)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1509–1510 | every `Idx`/`Ebene` lies in range | K | `M101` |
| 1514–1516 | the entry is ONE word with two readings; the frame is bits 51..12 × 4096 | K | `embeds` — **the construct that closes "pointer AND bitfield". Without the line the address would be a bare number and `& MASK` a convention** |
| 1520–1524 | `A`/`D` are `reserved` — a write by us would be an error | K | `R002`/`R003` |
| 1529–1533 | the descent terminates after at most 4 levels | K | `walk levels` — *the bound falls out of the declaration instead of a count in the body* |
| 1531 | a non-leaf entry points at a next level | L | the human |
| 1532 | `PS == 1` marks a leaf | L | the human |
| 1536–1538 | `<= 4096 ops` | K | `K001` — 4 levels × 512 entries, **computed, not promised** |
| 1540–1541 | the traversal terminates and visits each mapping once | K | `S001`, `by unvisited` |
| 1543 | the leaf level is reached | L | the human |
| 1558–1567 | **the MMU itself writes `A` and `D`** | K | **gap: «B39» — a writer no `effects` line names. The frame statement *"only what stands there changes"* is FALSE here, and not because of a checker hole but because the hardware is a participant. The honest form is `assume … falsifier …`, which puts the case in the axiom layer** |
| — | **W^X over the page table** | L | **gap: not in the fragment at all.** The 2026-08-14 report named it *"a real property falls out of all seven domains"*; F9's verdict is *"the finding is what did NOT show up"*. **Per R3 it is counted as an attempt, not as evidence** |

**F9: 11 obligations — 7 K, 4 L. Hanging: 2** (one K, one L).

---

# F10 — DTB parser (`FRAGMENTE.md`:1624–1668)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1631–1632 | the buffer is a device tree — `magie == MAGIE` | L | `format` `where` checks it, the human states it |
| 1634–1635 | every offset lies inside the buffer | K | `format` `offset_into` — **after that not a single access needs a length check** |
| 1641–1642 | the nesting depth is bounded at 64 | K | `M101` — *a DTB with 2^32 nested nodes is not a tree but an attack* |
| 1644–1645 | `naechstes_token` reads only `k` and costs at most 4 | K | `E010`/`K003` |
| 1647–1649 | `<= 65 540 ops` | K | `K001` |
| 1651 | `tiefe` stays in 0 .. 64 | K | `M101` |
| 1652 | `zahl` stays in 0 .. 1024 | K | `M101` |
| 1654–1658 | the parse terminates and the overflow is NAMED | K | `S001`/`S002` |
| 1656 | it ends because **a token is consumed** | L | the human — *the algorithm's progress measure, not the machine's finiteness* |
| 1660 | the depth stays below 64 | K | **gap: `narrow … else` is hand-written — but here the else branch is REACHABLE (a hostile DTB). Unlike F6:1100, this one is a real check, not a ritual** |
| 1666 | `baum_unlesbar` diverges | K | `S002` |

**F10: 11 obligations — 9 K, 2 L. Hanging: 1, K.**

---

# The tenth event — the lowering, one per fragment

| Fragment | Obligation | | discharged by |
|---|---|---|---|
| **F7** | **the generated C computes what the fragment says** | K | **carried, measured by execution.** `pruefe-emission.sh` cuts F7 out of the frozen corpus, emits, compiles with `cc -std=c11 -Wall -Wextra -Werror`, runs it and compares: **`123456`** — six boot steps, in order, each exactly once. The `linear ghost type` leaves **no trace** in the C |
| F1–F6, F8–F10 | same | K | **gap, for nine.** `C001` refuses for every form they need: loops, `match`, `locks`, `publish`, `exchange`, `format`, `walk`, every generated operation |

**+10 obligations, 10 K, 9 hanging** *(updated 2026-08-17, after F7)*.

> *That is the honest connection to the emitter work.* The differential test now shows that
> **two** lowerings hold for **two** files, measured by execution — and F7's is the first over a
> **fragment** rather than an example. **Refinement is a statement about every lowering**, and
> against this corpus it stands at **one of ten**.
>
> **What F7 buys is a statement about cost, and it is the first one this folder can make:** the
> boot phase is threaded as a linear ghost token through six steps, carries the whole safety
> argument of the fragment — and lowers to *nothing*. The obligation was discharged at compile
> time; at run time the six calls stand there and the token does not.
>
> **And the danger was measured, not assumed.** The erasure has to hold in the signature, at the
> call site and at the `let` binding. Made to fail at the third — dropping the whole statement
> instead of only the binding — the C **compiles cleanly** and prints `6`: five of six boot
> steps gone without a warning. *That is why stage 4 of the guardian exists.*

---

# The totals

| | | |
|---|---:|---|
| **Obligations in total** | **238** | 228 anchored at a line + 10 lowering (one per fragment) |
| **Plumbing (K)** | **173** | 73 % |
| **Logic (L)** | **65** | 27 % |
| **hanging** | **45** | of which **31 are K** — every one a breach of the thesis at its site. *(The run booked 50/36; five K were closed on 2026-08-17, each with its reason — see below.)* |
| **disputed** | **1** | `unlink`:194–196, argued in the row (the gate allows up to 10 %) |

**L : K = 0,38 : 1.**

## Per fragment

| | total | K | L | hanging | of which K |
|---|---:|---:|---:|---:|---:|
| F1 Cap space | 59 | 42 | 17 | 4 | 1 |
| F2 VT-d | 24 | 19 | 5 | 4 | 4 |
| F3 IPC | 26 | 13 | 13 | 6 | 1 |
| F4 Driver | 30 | 24 | 6 | 7 | 6 |
| F5 Userspace | 18 | 8 | 10 | 5 | 2 |
| F6 Test scaffold | 26 | 21 | 5 | 8 | 7 |
| F7 Loader | 9 | 8 | 1 | 2 | 2 |
| F8 Scheduler | 14 | 12 | 2 | 1 | 1 |
| F9 MMU | 11 | 7 | 4 | 2 | 1 |
| F10 Parser | 11 | 9 | 2 | 1 | 1 |
| Lowering | 10 | 10 | 0 | 7 | 7 |
| | **238** | **173** | **65** | **45** | **31** |

## Die hängenden Klempnereipflichten — nachgezogen 2026-08-17, Posten für Posten

**Der Lauf buchte 36. Fünf sind seither geschlossen, und jede mit ihrem Grund** — drei durch
Ausführung, eine durch die Absenkung selbst, eine durch ein Argument, das der Ordner
ausdrücklich verlangt hatte.

### Geschlossen

| Pflicht | wodurch |
|---|---|
| **Absenkung F7 · F8 · F10** | **an der Ausführung gemessen** — `123456`, `1 1 1 0 0 1 1 1`, `1 0 0 0 0 65` |
| **«B26» — der Vorzustand einer `transition`** | *„ob `mirrors` auch den Vorzustand einer `transition` an `GCMD.TE` aus `GSTS.TES` bezieht, sagt `SYNTAX.md` nicht"* — **der Erzeuger beantwortet es mit ja und misst es**: `1 1 1 1`, und die zweite und vierte Zahl sind die Falle. *Die Antwort gehört jetzt in `SYNTAX.md`, nicht in den Erzeuger* |
| **«B33» — die V-Regeln verengen keinen Registerort** | Der Ordner schrieb: *„Ob das Absicht ist (ein Register kann sich zwischen Prüfung und Rechnung ändern!) oder eine Lücke, entscheidet der Ordner. **Wenn es Absicht ist, gehört die Begründung aufgeschrieben** — sie wäre ein starkes Argument."* **Sie ist es, und sie steht jetzt im erzeugten C:** ein Registerzugriff wird `volatile`, und `volatile` IST die Aussage *„dieser Ort kann sich zwischen zwei Lesungen ändern"*. Eine Verengung wäre an dieser Stelle falsch, nicht bloß fehlend |

### Offen — **31**, und die Spalte rechts sagt, wem sie gehören

| Ursache | # | wem |
|---|---:|---|
| **die Absenkung** | 7 | F1–F6, F9 — davon **fünf durch Befunde gesperrt**, nicht durch Arbeit |
| **Gerätenotation** | 5 | «B23» gemischte Registerklasse · «B24» Bitlage jenseits des Wortes (×2) · «B26» `QUEUE_SIZE` ohne benannten Ausgang · «B18» Phasen am `device` |
| **handgeschriebenes `narrow`** | 3 | F1:268 · F6:1100 (**Zweig unerreichbar**) · F10:1660 (**Zweig erreichbar**) — *und der Unterschied wird von keiner Messung gesehen* |
| **`format`/Verbund** | 4 | «B25» Wertemenge statt Intervall · «B22-nah» Absage statt Abwesenheit · «B7» Verbundliteral (×2) |
| **die Reihenfolgezusage** | 2 | «B37» — *Linearität ist keine Ordnung* |
| **«B19»** Barrieren am Geräteregister | 1 | die sicherheitskritischste Veröffentlichung im Baum ist kein Atomic |
| **«B21»** `accumulates` | 1 | 213 RMW-Stellen |
| **«B38»** `masks IRQ` an der Sperrgrenze | 1 | die Wirkung existiert und ist nicht an die Grenze geknüpft |
| **«B39»** die MMU schreibt `A`/`D` | 1 | ein Schreiber, den keine `effects`-Zeile nennt |
| **«B27»** Registerbelegung | 1 | 168 `asm!`-Stellen ohne Träger |
| **«B22»** mehrzeiliges `claim` · **«B14»** `let … else` auf einem `place` · **«B6»** Rückgabebindung · **«B3»** `Held(Lock)` | 4 | Notation |
| **V-Regeln rechnen nicht** | 1 | F6:1157 — `f < g/N` liefert nicht `f < g` |

> **Von den 31 sind 24 Notations- oder Befundposten der SPRACHE**, nicht des Prüfers. *Die
> Klempnerei hängt nicht daran, dass ein Pass fehlt — sie hängt daran, dass sich sieben Dinge
> nicht sagen lassen.*
