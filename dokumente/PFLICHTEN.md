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
| 174–177 | `refcount == count(s in slots : s.object == o)` | L | **gap: «B13» — `pred` knows no aggregation.** *The core of the capability system's bookkeeping.* ~~*and no cross-table domain*~~ — **the second half was BERICHTIGT on 2026-08-28 and it never carried.** A predicate names places, a foreign table name is a place, and `pred` never restricted that: measured through the unchanged checker, the connecting statement passes at a `group` invariant **and at a plain `table … invariant`** with 0 errors. *What `group` brought on 2026-08-16 is not the form but its checked home* (`U002`, `U003`, `U005`–`U007`). **The gap is ONE thing, and its cause is narrower still: `count` is a reserved word** (`kw.rs`:168) with no production in `pred`/`expr` — `anzahl(o)` parses at the same site, `count(o)` does not. *It would therefore cost no new word.* Demand, measured and separated (W23): 2 clean corpus sites, F1, and Caprock's K2, which `cap_space.rs` carries by hand in Verus. **Not built, and not for lack of demand** — the tail is a cost rule, a generator template and an Isabelle counterpart, and `PLAN.md`:946 sorted «B13» *out* on the K/L line. Measurement, both forms and the refusal: `messung/AGGREGATION.md` |
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
| 244–245 ✔ | the refcount fell by exactly one | L | ~~**gap: «B31» — `old` hangs under `atompred`, not under `primary`. No difference statement is writable**~~ — **BERICHTIGT am 2026-08-28 für die SPRACHE, und der Rest steht:** `oldexpr` hängt unter `primary` (`SYNTAX.md`:572), und `SYNTAX.md`:41 führt genau diesen Fehler als behoben auf. `ensures b.slots[i].zaehler <= old(b.slots[i].zaehler)` geht durch den unveränderten Prüfer mit **0 Fehlern**. **Was bleibt, ist der RUMPFKANAL:** `old(x)` ist ein Prädikat über ZWEI Zuständen, und alles dort spricht über einen — `old-state`. *Gemessener Bedarf im Register: null*, die acht `old`-Fundstellen sind zu fünf `exchange … when old(X)` (die atomare Vergleichsform) und zu drei Fragmentzeilen. Regel A: benannt abgesagt, nicht gebaut (`messung/VIER-LUECKEN.md` §3) |
| 246 ✔ | the CDT stays well-formed | L | the human |
| 247 | only the named places change | K | `E005`/`E008`/`E010` |
| 248 | `<= 200 ops` | K | `K001` |
| 250 ✔ | `c.slots[s]` in range | K | `M103` |
| 251 ✔ | `unlink`'s precondition holds here | K | call graph, `E008` |
| 252 ✔ | `release_slot`'s precondition holds here | K | call graph, `E008` |
| 268 | `o.slots[obj]` in range | K | `M103` |
| 268/271 ✔ | no underflow at `refcount -= 1` | K | **LOGIC, rebooked K100.1 (2026-08-17).** *The folder counts these separately («B29»); the sharpened measurand asks whether the else branch can be TAKEN — here it can, and then the check is the human's business, not plumbing residue.* |
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

**F1: 59 obligations — 42 K, 17 L. Hanging: ~~4~~ 3** (~~three~~ two L, one K) *(nachgezählt 2026-08-30 an der vierten Spalte: «B31» ist seit dem 2026-08-28 durchgestrichen, und ein durchgestrichener `gap:` zählt nicht mit — so liest ihn auch `zaehle-pflichten.py`)*.

---

# F2 — VT-d (`FRAGMENTE.md`:397–530)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 397 | every access goes to the `mmio` space | K | `R001` (placement rule) |
| 400 | a write to GCMD carries the state bits from GSTS | K | `mirrors` — **one line for trap 4's x86 form** |
| 402–419 | every field access lies inside its register | K | `M101`, `bitpos` |
| 403–419 | a `class r` register is never written, a `class w` never read | K | **`R005`/`R006`, built 2026-08-20 — and this cell said `R002`/`R003`, which check POINTER rights.** The note on `R003` even spoke the sentence (*"`class w` on a register means the same"*); no line of code did it, and `return d.NUR_W.A;` gave 0 errors. *A booking that points at a rule looking elsewhere is worse than an open line: it looks closed* (`gift/216`, `gift/217`) |
| 425–426 | FSTS is MIXED: 7:0 are RW1C, 15:8 (FRI) are r | K | **«B23» built 2026-08-20** — `regfeld = ident "@" bitpos [ "class" regklasse ]`; a field without a word of its own inherits the register's. No new terminal. `R006` bites at `FSTS.FRI` (`gift/218`), the clean shape is `beispiele/45` |
| 436 | the computed bank location lies inside the register file | K | `M103` via `count 256` |
| 438–442 | a bit position beyond 64 — which word does it mean? | K | `@[hi:lo]` in a `format` — **«B24» decided 2026-08-18.** A position lies inside the field's **own word**; beyond it there is **nothing to mean** (refusal, not a meaning). The word is read in the declared byte order **first**, then the bits are taken from the *value*. **And the tiling IS the word boundary**: a bit group ends when its bits are complete, a gap must be `reserved`. *A unification of two existing forms — `device` registers have carried this mechanic since 2026-08-14* |
| 444 | IOTLB likewise | K | `M103` |
| 450–453 | the pre-state of a `transition` at `GCMD.TE` comes from `GSTS.TES` | K | `mirrors` — **and the other half is answered, 2026-08-20.** It supplies the PRE-STATE too: `scharf_te` reads `GSTS` and writes `GCMD`, carrying every bit but the one the transition names. Measured at `beispiele/20`, written down in `SYNTAX.md`. *An answer that lives only in the generator is a promise that lives only in a tool invocation* |
| 454–455 | `setze_rtp` — TE off or RTPS already set | L | the human — *the remapping unit's protocol* |
| 457–458 | `scharf_te` — RTPS is set | L | the human |
| 460–461 | `setze_irtp` — QIES is set | L | the human |
| 463–464 | `scharf_ire` — IRTPS set and CFIS clear | L | the human |
| 466–467 | `scharf_qie` — QIES is clear | L | the human |
| 454–468 | every transition writes only GCMD | K | `E005` |
| 471–482 | every failure path names one of the nine reasons | K | `exhaustive` |
| 489–491 | the fault address is page-aligned | K | `format` `where` |
| 493–499 | the reason code lies in 0x01..0x0c | K | `M101` — **and only because the codes happen to be contiguous: «B25», `intty` carries an interval, not a value set** |
| 498 | an empty fault register is REFUSED, not reported empty | K | `format` `where` with a DISJUNCTION — **closed 2026-08-25, and the notation was never missing.** ~~*gap: «B22-near» — `format` knows only refusal*~~. `pred = orpred` has stood in the grammar all along (`SYNTAX.md`:614) and `N032` name-checks it; what was missing was a `match` arm — `PredArt::Oder` fell through `_ => return None` in `emit.rs::pred_c_format`, so the emitter refused with `C001`. **The discharge is EXECUTED, not booked:** `beispiele/51-abwesenheit-und-absage.gab` writes `where f_bit == 0 \|\| (grund >= 1 && grund <= 12)` and `instrumente/pruefe-emission.sh` runs it — `lauf "b22-abwesenheit"`, expected `1 0 1 0`: *empty* and *too short* are now two different answers, and the poison probe that cuts the `\|\|` out makes them one again. `EMISSION: ALL PASS — 22 durchgestochen` (was 21). **The frozen excerpt keeps its wording** — `f_bit : u64 in 1 .. 1` (`FRAGMENTE.md`:505) is what the human wrote when the language offered nothing else, and it stays; what changed is that Gabbro can now say the other thing |
| 505–510 | the second-level PTE layout | K | `format` |
| 512–518 | the context entry layout, `AW @[66:64]` crosses the word | K | **«B24» decided 2026-08-18 — and the decision REFUSES this notation.** A position lies inside the field's own word; `u64` has bits 0…63, so `@[66:64]` names nothing. *The layout stays writable — as a second `u64` field with `@[2:0]`.* **The programmer names the second word instead of the emitter guessing it**, and that is the point: a 128-bit entry is two words, and saying so is cheaper than a rule about crossing |
| 520–522 | TE arms translation; DMA without a context entry faults | K | `assume` **with a falsifier** |
| 524–526 | GCMD is written whole | K | `assume` — **expressly `unfalsifiable`, with the reason: a probe would have to open the very window the mechanism is built against** |
| 528–530 | after FSTS.PFO further faults are dropped | K | `assume` **with a falsifier** |

**F2: 24 obligations — 19 K, 5 L. Hanging: ~~2~~ ~~1~~ **0**** — *und die alte Fassung widersprach dieser Datei selbst.* Sie sagte «1, and it is the lowering», während die Absenkungstafel eine Seite weiter unten für F2 **carried, measured by execution (2026-08-25)** führt und `pruefe-emission.sh` ein `lauf "fragment2"` trägt. *Zwei Stellen, eine Pflicht, zwei Aussagen — berichtigt 2026-08-30* *(«B26»'s second half and «B23» closed 2026-08-20; **«B22-near» closed 2026-08-25, and the discharge is a differential test that RUNS**; and one cell that read as closed was NOT — see 403–419)*. **F2 therefore carries no anchored gap any more** — read off with `./instrumente/zaehle-pflichten.py --haengend`, which now prints no line for F2.

---

# F3 — IPC fastpath (`FRAGMENTE.md`:554–704)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 560–566 | every result names one of the four reasons | K | `exhaustive` |
| 570–575 | every queue index lies in range | K | `M101` |
| 577–585 | every `index into Endpoint` lies below 64 | K | `M103` |
| 587–589 | `caller` and `reply_owner` are set together or not at all | L | the human |
| 592–603 | the two places are written in **one** step | L | the human — **«B17» BERICHTIGT am 2026-08-28, a correction and not a booking.** ~~*gap: «B17» — `transition` writes exactly ONE `place` … not writable*~~ — the row was wrong on its own reason, and it had been wrong since 2026-08-14. **`transset = placeshift { "," placeshift }` stands in `SYNTAX.md`:1256** with the comment *„MEHRERE Orte in EINEM Zug"*, `parse.rs::transition` carries the comma loop, and **`beispiele/02-geraet.gab`:42 uses the form**: `transition irq_umlenken { GCMD.IRE: 0 -> 1, GCMD.SRTP: 1 -> 1 }`. Measured, and it reproduces (W24, unchanged checker): `state Rendezvous { transition open { caller : None -> Some(cl), reply_owner : None -> Some(sv) } }` → **0 Fehler, 0 Hinweise**; the ONE token that fails is `over` (`P001`). *And the folder contradicted itself:* `MESSUNGEN.md`:6198 has carried `transset` correctly all along — this row flattened it. **What is really carried today is not atomicity but the named REGION**: `breaking antwortpflicht_paarig { … }` (`SPRACHE.md` §8.3), whose subject `D013` now resolves and whose site drops out of the K count (`D009`). *Atomicity itself is NOT delivered and cannot be honestly promised* — `schablonen.rs::transition.transset` stands at `Entworfen` and says why: without a named observer the promise is empty on a multicore. **Same booking as the neighbouring row 587–589**, which has read *the human* from the first day. Work and weighing: `messung/ZWEI-ORTE.md`, `beispiele/53-zwei-orte.gab` |
| 609–611 | the message arrived — `msg_kopiert` | L | **gap: «B12» — no numeric-range domain; the substitute `elems of` has two readings and the grammar fixes neither** |
| 610 | `msg_kopiert` is pure | K | `E009` |
| 613–624 | the callback's contract stands at the pointer type | ~~K~~ **zu** | **«B9» BERICHTIGT am 2026-08-25 — eine Richtigstellung, keine Buchung.** ~~*gap: «B9» — `fnptr` carries no `requires`, no `ensures`, no `effects`*~~ — the row was wrong on all three of its points, and it had been wrong for four days. **`effects` and `costs` are MANDATORY at a `fn(…)` type since 2026-08-21** (`N035`); `N036` says which effect words carry through an indirect call; `requires`/`ensures` are refused **with a measured justification** (`N037`) — not forgotten. Measured, and it reproduces: `printf 'type T = { f : fn(u8), };' > /tmp/b9.gab && gabbro pruefe /tmp/b9.gab` → ``Fehler: [N035] /tmp/b9.gab:1:16: `fn(#1)` declares no `effects` and no `costs```. **The work is from 2026-08-21** (`messung/FNPTR.md`, all four halves; `beispiele/49-dispatch-tabelle.gab` with 0 errors) — *this row only failed to be carried along.* `H` falls from 11 to **10**, and it falls because an entry was FALSE, not because anything was built today. **A number lowered by rewording would be repotting; a false entry corrected is not** — and that difference is the whole reason this sentence stands here |
| 630–631 | postconditions may speak about the return value | L | ~~**gap: «B6» — `fndecl` binds no name for it; `old(place)` exists, a `result` does not**~~ — **BERICHTIGT am 2026-08-28: «B6» ist in der SPRACHE geschlossen, und diese Datei sagte es schon selbst** — Zeile 1106–1112 führt es als *„«B6» was already [closed]"*, **dieselbe Datei, entgegengesetzte Auskunft.** `primary` trägt `"result"` (`SYNTAX.md`:572), und der Korpus schreibt es an **acht Stellen** (`06-annahmen`:115, `03-format`:86, `39-auftragsdienst`:115, `22-bootstrecke`:80, `41-handschlag`:101, `udp-echo`:84, `F10`:31, `F06`:140). Die naheliegende Form durch den UNVERÄNDERTEN Prüfer: **0 Fehler** (`messung/VIER-LUECKEN.md` §1). *Was wirklich fehlte, lag im RUMPFKANAL* — und ist seit dem 2026-08-28 gebaut: der Satz bindet `result` als Namen an den zurückgegebenen Wert und verlangt zusätzlich, dass der Rumpf einen **erzeugt** hat (`finalValue`) |
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
| 676–677 | the invariant does not hold between the two assignments | L | the human — and since 2026-08-28 the region is **named**: `breaking antwortpflicht_paarig { … }`. ~~*gap: «B17» at its site*~~. The statement was writable all along (`breakstmt`, `SYNTAX.md`:882, `SPRACHE.md` §8.3); what it lacked was its SUBJECT — `breaking gibt_es_gar_nicht { … }` passed with **0 Fehler, 0 Hinweise** until `D013`. *The break now falls out of the count „K holds" at the carrier whose invariant it names* (`D009`, narrowed the same day: it used to name every `ops` table, including ones the block never touched). **What stays open is NOT «B17» and is not a language gap:** no pass looks at an `invariant … runs online` at a statement boundary — the two assignments pass with zero errors, with `breaking` and without it. *A rule for it would fire on 2 clean corpus files and is refused by name in `messung/ZWEI-ORTE.md` §4 (Regel A).* |
| 678 | a same-core rendezvous switches directly | L | the human |
| 687–703 | every callee names its effects and its bound | K | `K003` |

**F3: 26 obligations — 13 K, 13 L. Hanging: ~~6~~ ~~4~~ **3** (~~three~~ two L, one K)** — *«B17»'s two rows fell on
2026-08-28, and the arithmetic is spelled out because a number that moves without one is
repotting.* **Row 592–603 fell because its reason was FALSE** (`transset` has carried several
places since the first day, corpus site `beispiele/02`:42) — that is the «B9» move of
2026-08-25, not a build. **Row 676–677 fell because the form it needed already existed and
only its subject was missing** (`D013`). Nothing about the two hanging counts of
`zaehle-pflichten.py --haengend` moves: both rows are **L**, and that tool counts K.
*The remaining three L are «B12», «B6» and «B10»; the one K is the lowering.*

---

# F4 — virtio driver (`FRAGMENTE.md`:753–896)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 753 | every access goes to the `mmio` space | K | `R001` |
| 754–769 | register classes are respected | K | `R002`/`R003` |
| 764 | the device's `QUEUE_SIZE` lies below QMAX | K | **closed 2026-08-28 — `requires … else`, and it LOWERS («B26»).** The clause now carries a FALSIFIER: `requires QUEUE_SIZE <= QMAX else Geraetelug::ZuGross` makes the READ fallible, a plain read is refused (`R011`), the `else` must name a declared reason case (`R010`), and `emit.rs::fehlbare_lesung` emits **ONE** volatile read whose condition is checked on the BINDING. *No fact was made out of the promise* — the register is volatile and a hostile device may report anything, so what is held is that the PROGRAM looks, not that the device is honest; assuming it would have been the «B33» error one level up. Probes `beispiele/gift/405` (`R011` — the site that passed with 0 errors until today) and `406` (`R010`); the clean side is `beispiele/44-register-einmal-lesen.gab`, «B33»'s own file, and it goes through `cc` under `-Werror`. Decision with both rejected forms: `messung/GERAETEVERSPRECHEN.md` <br>~~**gap: «B26» — HALF closed on 2026-08-24, and the row says which half.** *no pass reads `RegDecl::requires` at all; the clause parses and is then dropped* — **the silent drop is gone:** the clause is now COUNTED as a device promise (`gabbro pflichten` prints `D  Device promise at a register`), the same answer `ensures` at an `extern fn` got. *A clause nobody reads became a duty with a name and a number.* **What is still open is the half that would close it:** the promise carries **no falsifier** and does not LOWER. `requires … else <reason>` would make the read fallible, and `let q = d.REG else (e) { … }` is a form the emitter already carries. **A fact from the clause would be the «B33» error again** — the register is volatile, and a hostile device may report anything. *`H` therefore does NOT fall by one: a booking is not a discharge, and buying a decrement with bookkeeping is exactly what K100's second gate exists to prevent*~~ |
| 773 | `ack` — from 0 to ACK | L | the human — *the virtio protocol* |
| 774 | `drv` — ACK to ACK\|DRIVER | L | the human |
| 775–776 | `featok` | L | the human |
| 777–779 | `drvok` | L | the human |
| 780–782 | a reset applies from EVERY state | L | **gap: «B26» — no placeholder for the pre-state, so the transition table cannot be complete** |
| 785–792 | `used` belongs to the device — the register class per phase | K | **closed 2026-08-28 — the register class PER PHASE («B18»).** `reg USED_IDX : u16 wrapping @0x202 class rw in setup, r in live` parses, and the stages are those of a declared `linear ghost type … order { … }` («B37») — **no second mechanism, and no new word.** The PAID-FOR trap keeps its answer: `class rw in setup` allows exactly the zeroing a reused ring needs, and `class r` alone would have forbidden it. `R009` holds the declaration; the access keeps `R005`/`R006` and names the stage. Decision with both rejected forms: `messung/PHASENKLASSE.md` <br>~~**gap: «B18» — `device` knows no phases. And this site carries a PAID-FOR trap: in a reused region the `used` ring holds the previous driver's end state**~~ |
| 796–800 | the five barriers of the real driver follow from the declaration | K | **AXIOM LAYER, rebooked K100.2 (2026-08-17)** — `assume` with a named falsifier. *What the machine guarantees and no pass can check is carried by name, not by silence (`gabbro annahmen`, 19 entries)* |
| 802 | `dma` space, and `n >= 1` | K | `R001` + `M101` |
| 803–817 | every ring index lies below 256 | K | `M103` |
| 810 | the avail index wraps at 65 536 by design | K | `wrapping` at the declaration («B32», closed) |
| 828 | the setup token exists exactly once | K | `L101`–`L105`; **notation gap «B3»: `typedecl` demands `params` in the parentheses — which hits `Held(Lock)` in every `requires` of the file** |
| 830–831 | `queue_reset` writes only `q` | K | `E005` |
| 833–834 | after `queue_arm` no path can write `USED_IDX` | K | **closed 2026-08-28 — and by the WEAKER half, which is why it holds («B18»).** The correction of 2026-08-26 stands: `L101` never carried this, because a linear mark is a permission nobody is obliged to hold. **Nothing was built that obliges anyone to carry it.** What was built says what follows WITHOUT it: *where the stage is not determined, what holds is what EVERY stage permits* — and the intersection of `rw in setup` and `r in live` is `r`. `heimlich`, the reproduced site with no mark anywhere in its signature, therefore falls at `R006` (`beispiele/gift/401-registerklasse-ohne-marke.gab`), and the write AFTER `queue_arm` falls with the stage named (`402`). *The raise this row asked for is thereby paid back in the same run it was booked in* <br>~~**gap: «B18» — BOOKED AS CARRIED AND IT DOES NOT CARRY (measured 2026-08-26).** `L101` — carried, and it replaces the phases without a new mechanism. The excerpt's own sentence names the mechanism: *"nicht weil ein Wächter es verbietet, sondern weil die Marke verbraucht ist"* (`FRAGMENTE.md`:837) — **and a consumed mark forbids nothing to a function that never mentions it.** `L101` holds that whoever HAS the mark passes it on and does not duplicate it; *it does not hold that whoever WRITES must have it.* A linear mark is a permission nobody is obliged to hold. Reproduced — a function with no `QueueSetup` anywhere in its signature: <br>``impl fn heimlich(q : ptr<dma, rw> Virtq) effects { writes q } costs <= 4 ops { q.USED_IDX = 7; }`` → `8 Items, 0 Fehler, 0 Hinweise`. <br>**What would close it is the phase-dependent register class**, and F4 asks for it in its own words two lines further up: `reg USED_IDX : u16 wrapping @0x202 class rw in Setup, r in Live` — written as a COMMENT because `device` knows no phases. *This row is therefore «B18»'s second corpus site, and the load-bearing one: `class r` alone would be WRONG here — it would forbid the very zeroing that disarms the paid-for trap.* <br>**And the correction RAISES `H` by one.** That is the same move as «B9» on 2026-08-25, with the sign reversed: *a number lowered by rewording would be repotting; a false entry corrected is not — in either direction.*~~ |
| 836 | a buffer belongs to exactly one side | L | the human |
| 838–841 | the unproven reason is named | K | `reason` |
| 843 | `head` lies below 256 | K | `M101` |
| 844 | only `q` changes | K | `E005` |
| 847 | `<= 9 ops` | K | `K001` — **the declared 4 was wrong; read off with `gabbro kosten`, not estimated (W2)** |
| 850 | the divisor is not zero | K | `n : u16 in 1 .. QMAX` |
| 851 | `q.AVAIL_RING[platz]` in range | K | `M103` |
| 872–876 | the V rules do not narrow a REGISTER place after a comparison | K | **decided and BUILT, 2026-08-20 — and the folder had it backwards.** The V rules DID narrow one; `if d.ST.IDX < 8 { … d.ST.IDX … }` went through with 0 errors, and the C indexed 8 slots with a value the hardware may reset between the two volatile reads. It is intent: `volatile` IS *"this may change between two reads"*. Now enforced (`SPRACHE.md` beside V1–V3, `gift/213`+`214`, two mutations), with the door open — `let i = d.ST.IDX;` lowers (`beispiele/44`) |
| 877 | the ring counter wraps intentionally | K | `wrapping` |
| 880–881 | `poll_used` reads only `q` | K | `E010` |
| 885–889 | the poll terminates and the overflow is NAMED | K | `S001`/`S002` — **carried unchanged, and the clause order matches the production** |
| 886 | it ends because **the device** completes or faults | L | the human — *the borderline case the criterion decides: not "over a finite set" but "because the device makes progress"* |
| 891 | the divisor is not zero | K | `n : u16 in 1 .. QMAX` |
| 892–894 | a function may PRODUCE a compound | K | `P(a: …, b: …)` — **«B7» closed 2026-08-17.** No braced literal: it would have been the first expression form continuing with `{`, and 76 corpus sites have a `{` right after an expression. The marks are mandatory (`M106`/`M107`), because two same-typed fields in a positional list are swappable with no type objecting |
| 895 | `q.USED_RING[s].id` in range | K | `M103` |

**F4: ~~30~~ 31 obligations — 24 K, ~~6~~ 7 L. Hanging: ~~6~~ 1** (one L, ~~five~~ **no** K) *(«B33» decided and built 2026-08-20)*.

> **Zwei Berichtigungen an einer Zeile, 2026-08-30.** Die Tabelle darüber hat **31** Zeilen, nicht 30: 24 mit `K`, **sieben** mit `L` (773, 774, 775–776, 777–779, 780–782, 836, 886). Die Kopfzeile führte sechs. *Die Gesamtzahl stimmte trotzdem — 24 + 6 = 30 —, und genau deshalb fiel sie nicht auf: eine Summe, die zu ihren Summanden passt, sieht richtig aus, auch wenn beide falsch sind.* Und die hängende Zahl: von F4s sechs steht heute **eine** da, «B26» an 780–782; «B18» ×2 und «B26» an 764 sind seit dem 2026-08-28 durchgestrichen, und die Absenkung ist seit dem 2026-08-26 **gemessen** (`lauf "fragment4"`).

---

# F5 — Userspace service loop (`FRAGMENTE.md`:919–1018)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 921–934 | every status and every exit names its reason | K | `exhaustive` |
| 936 | every request decodes to exactly one op | K | `tagged type` |
| 938–949 | the syscall register assignment | K | **CORRECTED 2026-08-28 — a FALSE entry, measured through the unchanged checker (W24).** The register assignment EXISTS, and has since 2026-08-20: an `asm` FUNCTION BODY carries `in { p : "a" }`, `out { result : "=a" }` and `clobbers { … }` next to `arch`, and `beispiele/36-asm.gab` writes a **syscall** with it. F5's own `invoke`, written as an `asm` body instead of a `prim` declaration, checks with **0 errors** and lowers to correct inline asm — the measured C stands in `messung/EINTRITTSBELEGUNG.md`. **What is TRUE and stays, as a named residue and not as a `gap:` row:** the assignment is spelled in C CONSTRAINT LETTERS and not in architecture register names, so Gabbro DELEGATES it to `cc` instead of checking it; and a `prim fn … arch x;` really does lower to an empty forward declaration — *which is what `prim` MEANS, not a missing carrier.* The fragment reached for the wrong construct. **Corrected, not painted over: `H` falls by one WITHOUT work, the same move as «B9» on 2026-08-25** <br>~~**gap: «B27» — `arch ident` exists, the register assignment does not. The one place where 168 measured `asm!` sites should converge has no carrier: the trusted surface does not shrink, it moves into a `prim` declaration without content**~~ |
| 951–952 | `run` diverges and touches only the named world | K | `E005`/`E010`; `-> never` lets the passes see the error branches do not fall through |
| 954–960 | every startup failure is named and leaves the program | L | the human — six `let … else` |
| 964–967 | "never read yet" is distinguishable from zero | L | ~~**gap: «B14» — `option` stands only in `slottype`, not in `typeexpr`. Exactly the reading the fragment was written against**~~ — **BERICHTIGT am 2026-08-28: `option index into T` steht an allen drei Stellen** — Parameter, `let`-Typ und Rückgabetyp. Gemessen am unveränderten Prüfer: **0 Fehler**, und der Rumpfkanal trägt **alle** Rümpfe der Probe (`bodies 4, refused 0`). *Auch der zweite Halbsatz trifft nicht mehr:* das Modell unterscheidet `absent` von `present n` seit `Body.lean` §1, und `.someOf` ist der Erzeuger. `messung/VIER-LUECKEN.md` §1.4 |
| 969–976 | the service loop has a NAMED exit | L | ~~**gap: «B11» — no `leave`, no `break`, no `continue`. The difference between "D0 falls by construction" and "the service loop is not writable". F5 breaks here**~~ — **BERICHTIGT am 2026-08-28: «B11» ist GESCHLOSSEN, und diese Zeile stand länger als sie wahr war.** `leave` und `leaves` stehen im Wortschatz (`kw.rs`:121/122), `forever … leaves identlist` in der Grammatik (`SYNTAX.md`:994), und der Ausgang hat **sieben Leser**: `schleifen.rs`:61 hält `leave <marke>` gegen die Marken der umgebenden Schleifen, `gruppe.rs`:401 bucht ihn als `Ereignis::Austritt`, `kosten.rs`:529 gibt ihm Kosten 0, `m2.rs`:451 und `lib.rs`:875 zählen ihn zu den Anweisungen, die immer enden, dazu `pflichten.rs` und `phasen.rs`. **Der Korpus schreibt genau diese Dienstschleife zweimal** — `beispiele/04-schleifen.gab`:80/94 (`leaves marke` + `leave dienst;`) und `beispiele/39-auftragsdienst.gab`:156/174. Die naheliegende Form durch den UNVERÄNDERTEN Prüfer: **0 Fehler, 0 Hinweise** (W24-Vorlauf, `messung/AUSSETZUNG.md` §1.1). *Diese Berichtigung ist keine Arbeit und wird so gebucht* (§1.8) |
| 977–980 | each pass is bounded and the overflow is named | K | `S001`/`S002` |
| 981 | it makes progress because a client calls or the endpoint is revoked | L | the human |
| 983 | a revoked endpoint ends the service | L | the human |
| 984 | the six ops are exhaustive | K | `tagged type`, `match` |
| 985–991 | `Info` — capacity is reported and cached | L | the human |
| 988–990 | a reply may be a compound | K | `P(a: …, b: …)` — «B7» closed 2026-08-17. *Four arguments become one record, and the field names survive into the C as designators* |
| 992–993 | `Read`/`Write` — the request lies inside the client's range | L | the human |
| 994–997 | `Flush` — the flush completed before the reply | L | the human |
| 998 | `Scan` — the partition table is read or refused | L | the human |
| 999–1006 | `Stop` — the reply still goes out before the service ends | L | ~~**gap: «B11» — without `leave` only `exit()`, so the cleanup promise moves to two places. Literally the class C8 paid for**~~ — **BERICHTIGT am 2026-08-28, dieselbe Ursache wie 969–976:** `leave` gibt es, und die Aufräumzusage bleibt an einer Stelle. Nachzurechnen an `beispiele/04-schleifen.gab`:94 |
| 1014–1016 | `exit`/`signal`/`watchdog` name their effects | K | `E008` — **without `-> never` six `S002` arose from this alone** |

**F5: 18 obligations — 8 K, 10 L. Hanging: ~~5~~ 1** (~~three L, two K~~ — **nur noch die Absenkung, K**) *(nachgezählt 2026-08-30: «B14», «B11» ×2 und «B27» sind seit dem 2026-08-28 durchgestrichen; F5 trägt keine verankerte Lücke mehr)*.

---

# F6 — Test scaffold (`FRAGMENTE.md`:1047–1163)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1049–1053 | the stack kind is named | K | `exhaustive` |
| 1056 | every `Bytes` lies in 0 .. 65536 | K | `M101` |
| 1058 | the reserve divisor is not zero | K | `M101` — **`u32 in 1 .. 64` is what makes `g / MIND_RESERVE_NENNER` legal** |
| 1061–1064 | the ten `atomic` declarations are reachable from `program` | K | `item` (`SYNTAX.md`:169) — **«B2» is CLOSED; the frozen text records it as hanging** |
| 1065–1069 | the high-water mark is writable | ~~K~~ **zu** | **«B21» geschlossen — und bis zum 2026-08-19 hier weitergezählt.** `accumulates hoch : u64 merge max;` geht mit **0 Fehlern** durch, `pruefe-notation.py` bucht B21 als geschlossen, und `Accumulates_Monoid.thy` beweist die Schablone. *Das Konstrukt kam mit `accumulates`; diese Zeile wurde nicht mitgenommen.* **Dieselbe Klasse wie die sechs Zeilen vom 2026-08-17, nur spiegelverkehrt:** dort wurde die Summe gepflegt und die Quelle nicht, hier blieb die Quelle offen, während das Werkzeug, das sie prüft, grün meldet. `H` fällt damit von 18 auf **17** |
| 1070–1072 | "never measured" is distinguishable from zero | L | **gap: «B14», the same as F5** |
| 1073–1082 | the ten counters carry no payload | K | `V001`–`V004`, `publishes nothing relaxed` |
| 1084–1085 | the returned depth does not exceed the stack | K | **notation gap «B6» — the line helps itself with the function name, and that is guessed, not written** |
| 1086 | `unberuehrt` reads only `s` | K | `E010` |
| 1088 | the counter stays in 0 .. 65536 | K | `M101` |
| 1091–1092 | the traversal terminates | K | `S001` — **notation wart «B30»: `touches` takes an `efflist` without braces while `effects` is braced everywhere else** |
| 1094 | the first untouched word marks the depth | L | the human |
| 1094/1103 | `i * 8` does not overflow | K | `M101`/`M104` |
| 1100 | the counter stays below 65 536 | ~~K~~ **zu** | **«H2.1» gebaut 2026-08-19.** Ein Zähler, der in einer beschränkten Traversierung höchstens einmal je Durchgang wächst, erbt die Schranke seiner Domäne: an der Zuwachsstelle `n <= c + (B-1)*k`. *Die einzige Ausnahme von `SPRACHE.md`:657 — der Unterschied zwischen Ausnahme und Loch liegt in der Richtung: die Tatsache kommt aus der Schleifenform selbst.* Das `narrow` ist an beiden Fundstellen ENTFERNT. **Und der Ausschnitt musste dafür seinen Träger nennen** — `Stack` war benutzt und nie erklärt, wie `STACK_MAX` am 2026-08-15; die Wortzahl ist aus `i * 8` und `STACK_MAX` ABGELEITET |
| 1106–1112 | a function may return a pair | K | `P(a: …, b: …)` + `ensures result` — **both closed**; «B6» was already, «B7» on 2026-08-17. *The double traversal was the price of two gaps that met* |
| 1113–1114 | `s.len >= 8` | K | `M101` |
| 1115 | only the named atomics change | K | `E005`/`E010` |
| 1121 | `s.len - frei` does not underflow | K | the callee's `ensures` — **not a flow rule. Costs one line of postcondition, no proof.** *The best-carried K in the corpus* |
| 1126–1128 | a claim may be written precisely | K | adjacent string literals — **«B22» closed 2026-08-17.** *The one-line rule (`L001`) stays: a string ends on its line, and three of them become one claim* |
| 1129–1141 | the measuring instrument reports the known depth | L | the human — **R14 as a language construct** |
| 1142 | the calibration ran at least once | K | `floor` |
| 1145–1158 | at the foot of every EL0 kernel stack an eighth stays untouched | L | the human |
| 1151–1155 | an `option`-valued `place` can be unpacked | K | `let … else` on a `place` — **«B14b» closed 2026-08-17.** *An unpacked place calls nothing:* the call graph sees no edge, M2 consumes nothing, the cost pass counts one |
| 1157 | `(g - f)` does not underflow | ~~K~~ **zu** | **«H2.2», 2026-08-19 — und die alte Begründung beschrieb den FALSCHEN ZWEIG.** Sie lautete, `f < g / N` gebe `f < g` nur über die Division; der Vergleich steht aber in einem `if`, das ZURÜCKKEHRT, und auf dem Weg zur Subtraktion gilt `f >= g / N` — eine UNTERE Schranke, wo eine obere gebraucht wird. **Keine schärfere V-Regel schließt das.** Die Aussage ohne Subtraktion (`irq + g/N <= f`) ist unter `f <= g` äquivalent und hat keine Unterlaufpflicht: *die Pflicht war ein Artefakt der Schreibweise, nicht der Sprache* |
| 1159 | the measurement has a floor | K | `floor` |
| 1160 | the check can go RED | L | `counterprobe` — **the speech test as a language construct** |

**F6: 26 obligations — 21 K, 5 L. Hanging: ~~8~~ 2** (one L — «B14» an 1070–1072 —, one K — die Absenkung) *(nachgezählt 2026-08-30)*.

---

# F7 — Loader / bringup (`FRAGMENTE.md`:1280–1333)

| Line | Obligation | | discharged by |
|---|---|---|---|
| 1285 | the boot token arises once, travels and is consumed | K | `L101`–`L105` |
| 1289–1291 | before the MMU the console is lock-free — **a property of the PHASE** | L | the human |
| 1293–1299 | "cap tables before the first cap" | K | `order { … }` + `advances a -> b` — **«B37» closed 2026-08-17.** The folder took the second way **the row itself named**: *an order on tokens.* The stages are identifiers in ONE declaration, so the vocabulary grows by two words, once. `O003` refuses a step that meets a token on the wrong stage — **before this, all 720 orderings of the six boot steps type-checked** |
| 1300–1318 | every boot step consumes the token and returns it | K | `L101` |
| 1300–1318 | every boot step names its effects and its bound | K | `E005`/`K003` |
| 1317–1318 | after the root task no path can do what only boot allowed | K | `L101` — **carried, and it is the fragment's win** |
| 1320–1323 | `hochlauf` costs at most the sum of its steps | K | `K001`/`E008` |
| 1325–1330 | every step happens exactly once | K | `L101` |
| 1325–1330 | the steps happen **in this sequence** | K | `advances` at the site — **«B37» closed 2026-08-17**; `beispiele/22-bootstrecke.gab` carries F7's shape with the order *and* the seven stated obligations. *`FRAGMENTE.md` stays untouched — a report of 2026-08-14 is not made right afterwards* |

**F7: 9 obligations — 8 K, 1 L. Hanging: ~~2, both K~~ 0** — *and the gap they were is measured:* `lauf "fragment7"` in `pruefe-emission.sh` emits, compiles, RUNS and compares `123456` *(berichtigt 2026-08-30)*.

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
| 1447–1451 | `masks IRQ` carries the value across the lock boundary | K | **AXIOM LAYER, rebooked K100.2 (2026-08-17).** *`Stale(T)` stays refuted at this site; what carries is a named assumption, not a mechanism that does not hold* |
| 1452–1455 | `beenden` holds SCHEDS, masks IRQ, `<= 16 ops` | K | `H001`/`E006`/`K001` |
| 1457 | `l.slots[k]` in range | K | `M103` |

**F8: 14 obligations — 12 K, 2 L. Hanging: ~~1, K~~ 0** — the lowering is measured, `lauf "fragment8"`, `1 1 1 0 0 1 1 1` *(berichtigt 2026-08-30)*.

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
| 1558–1567 | **the MMU itself writes `A` and `D`** | K | **AXIOM LAYER, rebooked K100.2 (2026-08-17)** — the honest form was named in the row itself: `assume … falsifier …`. *The hardware is a participant, and the frame statement is false here, not incomplete* |
| — | **W^X over the page table** | L | **gap: not in the fragment at all.** The 2026-08-14 report named it *"a real property falls out of all seven domains"*; F9's verdict is *"the finding is what did NOT show up"*. **Per R3 it is counted as an attempt, not as evidence** |

**F9: 11 obligations — 7 K, 4 L. Hanging: 2** (one K — die Absenkung —, one L) *(2026-08-30 nachgezählt und **unverändert richtig** — die einzige Fragmentzeile, die es war)*.

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
| 1660 | the depth stays below 64 | K | **LOGIC, rebooked K100.1 (2026-08-17)** — the row said it itself: *the else branch is REACHABLE (a hostile DTB), a real check and not a ritual.* A reachable branch is the human's business |
| 1666 | `baum_unlesbar` diverges | K | `S002` |

**F10: 11 obligations — 9 K, 2 L. Hanging: ~~1, K~~ 0** — the lowering is measured, `lauf "fragment10"`, `1 0 0 0 0 65` *(berichtigt 2026-08-30)*.

---

# The tenth event — the lowering, one per fragment

| Fragment | Obligation | | discharged by |
|---|---|---|---|
| **F7** | **the generated C computes what the fragment says** | K | **carried, measured by execution.** `pruefe-emission.sh` cuts F7 out of the frozen corpus, emits, compiles with `cc -std=c11 -Wall -Wextra -Werror`, runs it and compares: **`123456`** — six boot steps, in order, each exactly once. The `linear ghost type` leaves **no trace** in the C |
| **F8**, **F10** | same | K | **carried, measured by execution** — booked in `pruefe-emission.sh` beside F7 |
| **F2** | same | K | **carried, measured by execution** *(2026-08-25)*. The first one that was NOT already a program: five `reserved` fields were missing, and without them no `format` says which bits exist. `pruefe-emission.sh` runs it against `messung/fragmente/F02.gab` and compares **`4096 153 7 3 256 1 6 2 1 1 0 9`** — the record bank's address computed from a READ register field (`CAP.FRO * 16`), the stride, the same computation with `ECAP.IRO`, **trap 4** (`mirrors GCMD from GSTS` carries `RTPS` into the `TE` write; the poison probe reads `2` there), five bit positions out of the fault record, the `where` clause in both directions, and the DECLARED number of a `reason`. **And the completion itself is now checked, not asserted:** the guard cuts the frozen block and refuses if a single excerpt line is missing — *adding is allowed, leaving out is not.* Without it the yardstick could be moved instead of the obligation discharged |
| ~~F1, F3–F6, F9~~ **F1, F3, F5, F6, F9** | same | K | ~~**gap, for six**~~ **gap, for five** *(F2 left this row on 2026-08-25, **F4 on 2026-08-26** — measured, not rebooked; the row still named F4 on 2026-08-30, four days after `lauf "fragment4"` stood in `pruefe-emission.sh`)* *(re-measured 2026-08-20; the row said "nine" long after F8 and F10 were measured)*. And the seven are not one class. ~~**Three are open DECISIONS** — «B10» (`by consuming` drains the whole queue), «B12» (`elems of` binds an element or an index; `SYNTAX.md` uses both readings), `mappings of` (a path or the leaf set — seven orders of magnitude apart).~~ **BERICHTIGT am 2026-08-25 — alle drei sind seit dem 2026-08-20 ENTSCHIEDEN, und diese Zeile stand fünf Tage länger als sie wahr war.** `TODO.md` Stufe 3 trägt die Überschrift *„AUSGEFÜHRT am 2026-08-20, ohne ein neues Terminal und ohne eine neue Schablone“* und führt Entscheid **und** Begründung für alle drei; `dokumente/SYNTAX.md`:635 trägt «B12» in der Grammatik. Nachzurechnen mit `grep -n 'decided 2026-08-20' dokumente/SYNTAX.md` (→ ``"elems" "of" place  (* «B12», decided 2026-08-20: binds an INDEX into the array *)``) und `grep -n 'AUSGEFÜHRT am 2026-08-20' TODO.md`. Die Entscheide: **«B12» `elems of`** bindet einen **INDEX** — *aus dem Index bekommt man das Element, aus dem Element den Index nicht*; **`mappings of`** ist die **Blattmenge** — *W^X ist eine Aussage über die Menge; über einen Pfad ist sie sinnlos*; **«B10» `by consuming`** leert die **ganze** Schlange, *und das ist die Bedeutung*. **Damit ist «B10» kein Lesartenposten mehr, sondern ein KONSTRUKTposten** — *„das ist eine andere SCHLEIFENFORM, keine andere Lesart dieser“* — eine Schleifenform, die einen Wert liefert und verlassen werden kann. Er fällt unter Regel A (kein Konstrukt ohne gemessenen Bedarf) und unter Tor 2: **gebucht, nicht gebaut.** *Diese Richtigstellung senkt keine Zahl — `H` liest die vierte Spalte der Fragmenttabellen, nicht diesen Satz; sie nimmt nur einer Zeile den falschen Grund weg.* **Two are the axiom layer** — which barrier a `dma` access needs. **And ALL SEVEN carried a corpus-side blocker** *(counted 2026-08-20, one hour after the line below first said "two"; **F2's is closed since 2026-08-25** — the five `reserved` fields stand in `messung/fragmente/F02.gab`, and the file emits, compiles under `-Werror -O2`, runs and compares)*: 41 sites name 20 constants and types nobody declares (`MAX_POLL`, `EP_BADGE`, `SYSNO_RESULT`, `Fehler`, `NTFN`, …), nine `let … else` call bodies this unit does not declare, six bit positions left unnamed, one `table` with no `tree`, one callee with no `or <reason>`. *An EXCERPT is not a program, and `FRAGMENTE.md` carries a freeze sentence* — see the note below |

**+10 obligations, 10 K, ~~6~~ 5 hanging** *(re-measured **2026-08-30** with `./instrumente/zaehle-fragmente.py`: ~~6~~ **7** of the ten check clean, ~~**4 lower and run**~~ **6 lower and 5 run** — F02, F04, F07, F08, F10)*. **Alle drei Zahlen dieses Klammersatzes waren falsch, und alle drei in dieselbe Richtung: zu pessimistisch.** *Eine Buchführung, die nur in eine Richtung altert, ist nicht vorsichtig — sie ist ungemessen.*

> **Und am 2026-08-31 ist die erste dieser Zahlen GEFALLEN, von ~~7~~ auf 6 — mit Grund an der
> Marke.** `N041` weist einen Namen ab, den C schon vergeben hat, und `messung/fragmente/F05.gab`
> trägt einen: `extern fn exit()`. **Die 7 war ein falsches Grün** — die Datei prüfte sauber,
> emittierte 199 Zeilen C und wurde vom fremden Übersetzer zurückgewiesen. *Eine Marke, die fällt,
> weil eine Blindstelle einen Namen bekommen hat, ist keine Verschlechterung; sie ist die erste
> ehrliche Ablesung.* Gemessen in `messung/C-NAMEN.md`, entschieden in `messung/F05-UNERREICHBAR.md`.
> **Die Absenkungsspalte bewegt sich davon NICHT:** `F05` war nie unter denen, die absenken —
> `C001` stand davor. Sie steht heute bei *6 lower and 6 run*, und der Zuwachs kommt von `F06`,
> das am 2026-08-31 durchgestochen wurde.

> **And the column is no longer kept by hand.** `instrumente/zaehle-pflichten.py` used to carry
> `ABSENKUNG_OFFEN = ["F1", "F2", …]` in its source; it now reads the `lauf "fragmentN"` lines out of
> `pruefe-emission.sh`. **Whoever builds a differential test lowers `H`; whoever removes one raises it**, and
> a speaking probe holds both directions. *An entry without a run is no longer writable* — which is the
> same sentence this file already carries about the anchored half.

> ### The gate `H = 0` has a floor, and it is not made of work
>
> **Two of the seven are unreachable in principle.** The tenth-event obligation reads *"the
> generated C computes what the fragment says"* — **measured by execution**. F5 calls three
> functions it never declares; F2 and F9 leave bit positions unnamed. Neither is a gap in
> Gabbro: they are the marks of an EXCERPT, and `FRAGMENTE.md` opens with *"a report from
> 2026-08-14, and it stays untouched."*
>
> *An excerpt cannot be run.* Closing them would mean editing a frozen file — which is not
> closing an obligation but moving the yardstick.
>
> **This is the same move K100.1 made and did not finish.** That phase separated a check
> from a ritual among three hand-written `narrow`s and said: *a yardstick that cannot tell
> them apart measures the wrong thing.* The lowering column carries the same confusion one
> level up — it counts *"Gabbro cannot lower this"* and *"this text is not a program"* in one
> number.
>
> ### And the split is not five-two. It is seven-to-all — measured, after the first reading was wrong
>
> **The first version of this note said *"five of the seven are Gabbro's, two are the
> corpus's"*, and the floor `H = 2`. Both were wrong**, and an hour later the count said so:
> **every one of the seven carries at least one corpus-side blocker.** F4 — the one that
> looked purest — needs exactly one line, `MAX_POLL`, and without it the `bounded` clause
> names nothing.
>
> | | Gabbro's half | the corpus's half |
> |---|---|---|
> | F1 | field / parameter / `tagged` payload type (9 sites) | `Fehler` is declared nowhere; the `table` names no `tree` |
> | ~~F2~~ | — | ~~five bit positions unnamed~~ — **closed 2026-08-25**, and it was the only blocker: F2's Gabbro half was empty, which is why it is the first of the seven to fall |
> | F3 | field / parameter type (6), ~~«B10» to decide~~ **«B10» decided 2026-08-20** *(and what follows is a CONSTRUCT, not a reading — booked, not built)* | five names; one callee with no `or <reason>` |
> | F4 | `let` type (2), the `dma` barrier (axiom layer), `bounded … ops` with no fixed per-pass cost | `MAX_POLL` |
> | F5 | `match` over something other than `option index into T` | ten names, seven call bodies |
> | F6 | ~~parameter type, `let` type, expression form, «B12» to decide~~ **2026-08-25: `lenof` outside a `format` — and nothing else.** The parameter type (a `reason` IS a C type), the `let` type (read from the callee's signature) and the `static` of a record (`S19`, proved) lower since 2026-08-25; «B12» was decided on 2026-08-20 | three names, two call bodies — **and no pass reports them:** a `check … can_fail` is not entered by the name, effect and cost passes |
> | F9 | `walk … levels` that is not a number, ~~`mappings of` to decide~~ **`mappings of` decided 2026-08-20 (the leaf set)**, the `dma` barrier | one bit position |
>
> **Therefore: the floor of `H` from Gabbro's side alone is `7`, not `2`.** The five anchored
> obligations can be closed by building; **the lowering column cannot fall by a single
> point** without writing into a file that says it is a report and stays untouched.
>
> *And that is the sharper form of the same finding: the number does not measure what it is
> read as measuring. It was quoted as "how much plumbing is left in Gabbro"; seven twelfths
> of it are the corpus's completeness, not Gabbro's coverage.*
>
> *The second corpus is where the number can go to zero, and it is the one no one looked at
> while building.* `./instrumente/zaehle-pflichten.py` counts it since 2026-08-20.
>
> ### And since 2026-08-20 the obligation has a corpus that CAN carry it
>
> [`messung/fragmente/`](../messung/fragmente/) — the same ten, byte-identical, plus exactly
> the lines that make them **programs**. Per file the head says what was added and what was
> not; **`FRAGMENTE.md` stays the frozen report.** *The same move as «K2»: rebuilt, not
> translated — and said so out loud.*
>
> ```
> $ ./instrumente/zaehle-fragmente.py
> 7 von 10 pruefen sauber        (over the excerpts: 5)
> 4 von 10 senken ab             (over the excerpts: 3)
> ```
>
> **And the yield is three findings the frozen corpus could not show**, because they only
> appear once the missing declarations are there:
>
> 1. **`A::B` parses and never resolves.** The name pass reads the FIRST segment of a path
>    and looks it up as a value — `IpcResult::Ok` falls as `M119` whether `IpcResult` is a
>    `module`, a `reason` or a variant type. All three measured.
> 2. **A `reason` value has no producer.** `primary` (`SYNTAX.md`:405) has no production for
>    it, and **every `-> T or R` in the corpus sits on an `extern fn`** — a body Gabbro never
>    sees. *The error channel exists at the declaration and has no way to be written.*
>    **The same shape as «B9» at `fnptr`.**
> 3. A line *I* added does not lower: `static irq : IrqMarke = IrqMarke(…)` — a `static` of a
>    record with an ordinary initial value. *That stands there instead of leaving the line out.*

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
| **Obligations in total** | ~~238~~ **239** | ~~228~~ **229** anchored at a line + 10 lowering (one per fragment) |
| **Plumbing (K)** | ~~171~~ **173** | 72 % |
| **Logic (L)** | ~~67~~ **66** | 28 % |
| **hanging** | ~~31~~ **12** | of which **`H = 5` are K** — **0 anchored at a line, 5 lowerings** *(«B9» corrected 2026-08-25 — a FALSE entry removed, not a discharge: the work is from 2026-08-21, `N035`/`N036`/`N037`)* *(F2's lowering measured 2026-08-25)* *(«B21», «H2.1», «H2.2» closed 2026-08-19; «B26»'s second half, «B33» and «B23» 2026-08-20)*. ~~**All three remaining are NOTATION gaps: not one is a hand-written proof.**~~ **BERICHTIGT 2026-08-30 — dieser Halbsatz widersprach seiner eigenen Zelle.** Sie sagt zwei Zellenhälften weiter vorn **`0 anchored at a line`**; „die drei verbleibenden" gab es beim Schreiben dieses Satzes schon nicht mehr. Was verbleibt, sind **sieben verankerte `L`-Zeilen** (F1 ×2, F3 ×2, F4, F6, F9) und ~~fünf~~ ~~vier~~ **fünf Absenkungen** *(F6s Durchstich stand am 2026-08-31 — und fiel am selben Tag wieder: `N043` nimmt `messung/fragmente/F06.gab` an `measures eich` nicht mehr an, damit emittiert es nicht und der Durchstich ist WEG. **BERICHTIGT 2026-08-31, und zwar von der Messung und nicht von einem Leser:** `zaehle-pflichten.py` las die Absenkungsspalte am QUELLTEXT von `pruefe-emission.sh` ab — an der blossen Anwesenheit einer `lauf`-Zeile, nicht daran, ob der Lauf haelt. `F06` steht seit `N043` (`measures eich`, ein Traeger, den es nicht gibt) und emittiert nicht mehr; der Waechter war deswegen zu Recht ROT, und `H` sagte weiter 4. *Dieselbe Familie wie `W25`, eine Stufe weiter: dort trug eine richtige Zahl eine ungemessene BESCHRIFTUNG, hier trug eine Zahl eine ungemessene VORAUSSETZUNG.* **`H` ist keine Ratsche, sondern eine Messung** — sie steigt, weil eine Einloesung weggefallen ist.)* — und keine einzige davon ist Klempnerei. *(«B22-near» closed 2026-08-25 — and NOT by prose: `lauf "b22-abwesenheit"` in `pruefe-emission.sh` emits, compiles under `-Werror` at `-O0` and `-O2`, RUNS and compares `1 0 1 0`.)* Every one a breach of the thesis at its site. *Read off with `./instrumente/zaehle-pflichten.py --haengend`, not carried forward — see the note below.* |
| **disputed** | **1** | `unlink`:194–196, argued in the row (the gate allows up to 10 %) |

**L : K = 0,38 : 1.** *(2026-08-30 nachgerechnet — und hier liegt der Fall genau andersherum: **die Verhältniszahl war richtig, beide Operanden waren es nicht.** 66 / 173 = 0,381; die gebuchten 67 / 171 ergeben 0,392, also 0,39. Der Quotient stand seit jeher auf dem Wert der WAHREN Spalten. Ein Verhältnis ist keine Probe auf seine Operanden — aber ein Verhältnis, das nicht zu ihnen passt, ist eine Frage.)*

## Die Zahl war nicht mehr aus ihrer Quelle ableitbar — nachgezogen 2026-08-17

**Der Handgang unten IST der Suchweg zu `H`.** Am 2026-08-17, beim Schliessen von «B7»,
stellte sich heraus: **sechs Zeilen standen noch als `gap:` da, die in den Summen längst
geschlossen waren** — K100.1 buchte zwei nach *Logik* um (F1:268, F10:1660), K100.2 drei in
die Axiomschicht (B19, B38, B39), «B22» schloss eine. *Die Summe wurde gepflegt, die Quelle
nicht.*

> **W7 sagt: eine Zahl ohne Suchweg gehört nicht in den Ordner.** Eine Zahl, deren Suchweg
> ihr widerspricht, ist schlimmer — **sie sieht belegt aus.**

Die sechs Zeilen tragen jetzt ihren Grund, und die Zahl wird nicht mehr fortgeschrieben,
sondern **abgelesen**:

```
./instrumente/zaehle-pflichten.py --haengend
```

**Und die zweite Unstimmigkeit ist am 2026-08-20 aufgelöst — durch Streichen, nicht durch
Rechnen.** Die Tabelle unten führte zwei Spalten `hanging` und `of which K`. Die eine summierte
sich zu **47** bei einer Summenzeile von **34**, die andere zu **33** bei **18** — und die
Fußnoten der Fragmentabschnitte sagten ein Drittes.

> **Drei Register über derselben Sache** (W7), und keins davon abgeleitet. *Eine Zahl, deren
> Suchweg ihr widerspricht, ist schlimmer als eine ohne — sie sieht belegt aus.*

Die beiden Spalten sind fort. **`./instrumente/zaehle-pflichten.py --haengend` druckt sie jetzt je
Fragment**, aus den `gap:`-Zeilen dieser Datei abgeleitet plus der einen bekannten
Absenkungszeile (F1–F6 und F9 offen, F7/F8/F10 gemessen). *Was bleibt, ist der Handgang —
`total`, `K`, `L` —, und der ist eine Auszählung und keine Summenpflege.*

## Per fragment

| | total | K | L |
|---|---:|---:|---:|
| F1 Cap space | 59 | 42 | 17 |
| F2 VT-d | 24 | 19 | 5 |
| F3 IPC | 26 | 13 | 13 |
| F4 Driver | ~~30~~ **31** | 24 | ~~6~~ **7** |
| F5 Userspace | 18 | 8 | 10 |
| F6 Test scaffold | 26 | 21 | 5 |
| F7 Loader | 9 | 8 | 1 |
| F8 Scheduler | 14 | 12 | 2 |
| F9 MMU | 11 | 7 | 4 |
| F10 Parser | 11 | 9 | 2 |
| Lowering | 10 | 10 | 0 |
| | ~~238~~ **239** | ~~171~~ **173** | ~~67~~ **66** |

> **Die Summenzeile widersprach ihrer eigenen Spalte — gefunden 2026-08-30.** Die elf
> Zeilen darüber addieren sich zu **173 K** und **65 L**; die Zeile darunter führte
> **171 / 67**. Beide Fassungen ergeben 238, und *deshalb* stand es sechzehn Tage da:
> **eine Aufteilung, deren Summe stimmt, wird nicht nachgerechnet.**
>
> Und die Nachzählung fand einen zweiten Fehler eine Ebene tiefer: **F4 hat 31 Zeilen,
> nicht 30** — 24 `K` und **sieben** `L`. Damit ist die wahre Aufteilung **173 / 66**,
> und keine der beiden bis heute gebuchten Zahlenpaare war es. *Die Spaltensumme ist
> nicht die Wahrheit, sie ist nur der nächste Zeuge; der letzte sind die Zeilen.*
>
> Nachzurechnen ohne Werkzeug: `grep -c` geht nicht, weil eine Zeile mit `\|` in der
> Zelle beim naiven Zerlegen zerfällt (F2:498 tut das). Der Suchweg steht seit heute im
> Register von `./instrumente/pruefe-zahlen.py` — `./instrumente/zaehle-pflichten.py --spalten`.

*Die hängenden Zahlen je Fragment stehen nicht mehr hier, sondern im Befehl:*
`./instrumente/zaehle-pflichten.py --haengend`.

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

### Offen — **`H = 5`** *(~~10~~ ~~9~~ ~~5~~ ~~4~~ — 2026-08-25 zweimal, 2026-08-26 durch F4s Absenkung; **2026-08-28 von 9 auf 5**: «B18» ×2 und «B26» durch BAU, «B27» durch BERICHTIGUNG — und damit ist keine einzige verankerte Zeile mehr offen; **2026-08-31 von 5 auf 4 durch F6s Durchstich**, `lauf "fragment6"` in `pruefe-emission.sh` — **und am selben Tag zurück auf 5**, weil derselbe Durchstich an `N043` gefallen ist und der Zähler ihn bis dahin nicht gelesen hat)*, abgelesen mit `./instrumente/zaehle-pflichten.py --haengend` — und die Zahlenspalte ist am 2026-08-20 GESTRICHEN

**Dieselbe Auflösung wie einen Abschnitt weiter oben, und aus demselben Grund.** Die Spalte
`#`, die hier stand, war ein **viertes** Register neben dem Handgang, der Summenzeile und dem
Befehl:

| | |
|---|---:|
| die Überschrift sagte | **15** |
| die Spalte darunter summierte sich zu | **17** |
| `./instrumente/zaehle-pflichten.py --haengend` sagt | **12** |

> **Drei Zahlen über einer Sache — und die, die einen Suchweg nannte, war die falsche.** *Eine
> Zahl, deren Suchweg ihr widerspricht, ist schlimmer als eine ohne: sie sieht belegt aus.*

Gefunden am 2026-08-20 durch `./instrumente/pruefe-zahlen.py`, das die Überschrift seither gegen den Befehl
hält. **Die Ursache ist nicht Nachlässigkeit, sondern Fortschreibung:** «B21», «B23», «B33» und
«B26»s zweite Hälfte sind seit dem 2026-08-19 geschlossen, «B19»/«B38»/«B39» durch K100.2 in die
Axiomschicht umgebucht — und jede Schließung wurde in der Summenzeile eingetragen und in dieser
Liste nicht.

**Die ~~zwölf~~ *(2026-08-25: elf, dann zehn)* stehen jetzt nur noch an einer Stelle: im Befehl.** Er druckt sie je Fragment und
mit der Zeile, an der sie hängen. Was hier bleibt, ist, **wem** sie gehören:

| verankert — ~~fünf~~ ~~vier~~ ~~drei~~ **null** *(2026-08-25 zweimal, 2026-08-28 dreimal — die Überschrift blieb bei drei stehen)* | wem |
|---|---|
| ~~`F2`:498~~ **zu** | ~~**«B22-nah»** — `format` kennt nur die Absage~~ — **GESCHLOSSEN am 2026-08-25.** Die Notation fehlte nie (`pred = orpred`, `SYNTAX.md`:614); es fehlte ein `match`-Arm in `emit.rs::pred_c_format`. *Und die Entlastung ist AUSGEFÜHRT*: `beispiele/51-abwesenheit-und-absage.gab` unter `lauf "b22-abwesenheit"`, erwartet `1 0 1 0` — „leer" und „unlesbar" sind zwei Antworten, und die Giftprobe, die das `\|\|` herausschneidet, macht wieder eine daraus |
| ~~`F3`:613–624~~ **zu** | ~~**«B9»** — `fnptr` trägt kein `requires`, kein `ensures`, kein `effects`~~ — **BERICHTIGT am 2026-08-25.** `N035` macht `effects` **und** `costs` am `fn(…)`-Typ zur Pflicht (seit 2026-08-21), `N036` trägt die Wirkungswörter durch den indirekten Ruf, `N037` weist `requires`/`ensures` **mit gemessener Begründung** ab. Nachgerechnet: ``printf 'type T = { f : fn(u8), };' > /tmp/b9.gab && gabbro pruefe /tmp/b9.gab`` → ``[N035] … `fn(#1)` declares no `effects` and no `costs```. *Die Zeile fiel durch eine Richtigstellung, nicht durch Arbeit von heute — die Arbeit ist vom 2026-08-21 (`messung/FNPTR.md`)* |
| ~~`F4`:764~~ **zu** | ~~**«B26»** — `RegDecl::requires` wird von KEINEM Pass gelesen; die Klausel zerfällt nach dem Parsen~~ — **GEBAUT am 2026-08-28**: `requires … else <grund>` macht die Lesung fehlbar (`R010`/`R011`), und die Zeile in F4 sagt es selbst |
| ~~`F4`:785–792~~ **zu** | ~~**«B18»** — `device` kennt keine Phasen~~ — **GEBAUT am 2026-08-28**: `class rw in setup, r in live` steht in der Grammatik, `R009` hält die Erklärung |
| ~~`F5`:938–949~~ **zu** | ~~**«B27»** — `arch ident` gibt es, die Registerbelegung nicht~~ — **BERICHTIGT am 2026-08-28**: die Belegung gibt es seit dem 2026-08-20 (`asm`-Rumpf mit `in`/`out`/`clobbers`), der Eintrag war falsch |

> **Diese Tafel war am 2026-08-30 GANZ leer, und ihre Überschrift führte drei.** Alle drei Zeilen tragen in ihrem eigenen Fragmentabschnitt seit dem 2026-08-28 ein `~~gap:~~ … closed`/`CORRECTED`; `./instrumente/zaehle-pflichten.py --haengend` druckt `verankert 0` und tut das seither. **Und die Datei sagte es selbst** — zwei Absätze weiter unten steht *„seit dem 2026-08-28 hängt davon NICHTS mehr"*. *Dieselbe Sache, zwei Stellen, zwei Aussagen: die Schlussfolgerung wurde nachgezogen, die Tafel darüber nicht.*


**Und die anderen ~~sieben~~ fünf sind die Absenkung** — eine Zeile je Fragment für
~~F1–F6~~ **F1, F3, F5, F6** und F9; ~~F7/F8/F10~~ **F2/F4/F7/F8/F10** sind an der
Ausführung gemessen (`4096 153 7 3 256 1 6 2 1 1 0 9`, F4s Reihe, `123456`,
`1 1 1 0 0 1 1 1`, `1 0 0 0 0 65`). *Sie ist keine Sprachfrage, sondern Arbeit.*
*(Nachgezogen 2026-08-30; F2 ist seit dem 2026-08-25 gemessen, F4 seit dem 2026-08-26 —
abzulesen an den fünf `lauf "fragmentN"`-Zeilen in `instrumente/pruefe-emission.sh`.)*

> **Alle ~~fünf~~ ~~vier~~ verankerten waren NOTATION, keine einzige war ein handgeschriebener Beweis** — *und seit dem 2026-08-28 gibt es keine mehr.* Und
> die alte Liste führte daneben noch «B21», «B38», «B39», das handgeschriebene `narrow` und
> *„V-Regeln rechnen nicht"* — **fünf Zeilen für Posten, die schon zu waren.** Eine Liste, die
> nur wächst, ist kein Register.

> **Und der Satz, der hier ein Jahr lang stand, gilt nicht mehr:** *„die Klempnerei hängt
> nicht daran, dass ein Pass fehlt — sie hängt daran, dass sich sieben Dinge nicht sagen
> lassen."* **Sie lassen sich jetzt alle sagen.** ~~Was hängt, sind zwei Gerätestellen («B18»,
> «B26»), ~~drei~~ ~~zwei~~ **eine** einzelne Notationslücke (~~«B9»~~, ~~«B22-nah»~~, «B27»)~~ — **und seit dem
> 2026-08-28 hängt davon NICHTS mehr:** die zwei Gerätestellen sind gebaut, die letzte
> Notationslücke war ein falscher Eintrag. **Was bleibt, ist die Absenkung — und die ist
> keine Sprachfrage, sondern Arbeit.**
