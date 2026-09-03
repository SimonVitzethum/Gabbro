# The fifth mark, with its categories — the second pass

*Measured 2026-09-03. The working behind `dokumente/PLAN-HARDWARE.md` §50 #6.*

The item stood at **75 %** with a note against its own number:

> *Not measured:* whether the remaining transport capabilities (`poll_used`, `reclaim`,
> `kick` at a computed offset) are writable in Gabbro — they merely do not stand in the
> file, and **unwritten is not inexpressible.** This separation needs a second pass, and
> without it the figure 75 % is still a quotient without categories.

This is that pass. **The method is one sentence: write it in Gabbro and run the checker.**
Not grep — the previous pass committed `W16` inside its own decomposition tool, and the only
reason it was caught was reading a body instead of believing a number.

---

## 0. What is NOT measured here, and by whom

**The ownership handover is a parallel lane's, taken 2026-09-03.** That is
`reclaim(buf : Owned<Device>) -> Owned<Driver>` (`lib.rs`:311), `reclaim_unproven`
(`lib.rs`:326) and the `Owned<Driver>`/`Owned<Device>` typestate itself (`owned.rs`:55, 60) —
three capabilities, one question, and `R004`/`R007` under it. They appear in the enumeration
below **named and unmeasured**, and nothing in this document decides them.

*Naming a capability without measuring it is correct here; measuring it twice is not.*

---

## 1. The enumeration — capabilities, not lines

Object: `messung/treiber/virtio-net.gab` against `../caprock-messbasis/crates/caprock-virtio`
(`net.rs`, `lib.rs`, `owned.rs`; branch `arch/x86_64`, at `a1bf707`). `blk.rs` and
`VirtioRng` are excluded — they are other devices.

**A capability is a thing the driver can DO.** A line ratio between two languages measures
verbosity, and the previous pass says so in its own text.

| # | capability | caprock | in the `.gab`? | verdict |
|---|---|---|---|---|
| 1 | ECAM capability-list walk, guarded against a circular list | `lib.rs`:173 | no | **unwritten** |
| 2 | BAR base, 64-bit assembled from two registers, I/O BAR rejected | `lib.rs`:217 | no | **unwritten** |
| 3 | the transport as a value; `has_device_cfg` | `lib.rs`:396, 407 | no | **unwritten** |
| 4 | reset: write 0, bounded wait for 0, then ACK + DRIVER | `lib.rs`:437 | half (ACK/DRIVER are `transition`s) | **unwritten** |
| 5 | offered features — 64 bits through a 32-bit window | `lib.rs`:453 | no | **unwritten** |
| 6 | negotiate, and READ `FEATURES_OK` BACK | `lib.rs`:468 | half (`stufe_merkmale` waits on it) | **unwritten** |
| 7 | queue setup: select, clamp, zero BOTH ring halves, three addresses, `notify_off`, enable; absence as its own finding | `lib.rs`:486 | no | **unwritten** |
| 8 | `driver_ok` | `lib.rs`:532 | **yes** — `stufe_laeuft` | — |
| 9 | kick at `notify_base + notify_off * notify_mul` | `lib.rs`:540 | no | **unwritten** |
| 10 | device config space, guarded against "there is none" | `lib.rs`:550, 561 | no | **unwritten** |
| 11 | the memory barrier | `lib.rs`:422 | **yes** — `publishes`/`awaits` | — *(settled 2026-09-02)* |
| 12 | write a descriptor / arm a buffer | `lib.rs`:275, 295 | **yes** — `armieren` | — |
| 13 | publish: head into the avail ring, then the index | `lib.rs`:334 | **yes** — `armieren`, `AVAIL_IDX` | — |
| 14 | read the used index | `lib.rs`:346 | half (`USED_IDX` is declared and never read) | **unwritten** |
| 15 | the used entry at `slot % size`, as a completion | `lib.rs`:354 | no | **unwritten** |
| 16 | **`poll_used`** — bounded wait, then the completion | `lib.rs`:363 | no | **unwritten** |
| 17 | **`reclaim`** — the buffer back against the device's receipt | `lib.rs`:311 | no | **category C — parallel lane** |
| 18 | `reclaim_unproven` — the named way back without one | `lib.rs`:326 | no | **category C — parallel lane** |
| 19 | `Region::carve` — monotone, fail-closed | `owned.rs`:200 | no | **unwritten** |
| 20 | zero a RUN-TIME byte range | `owned.rs`:164 | no | **unwritten** |
| 21 | typed access into a buffer | `owned.rs`:133–155 | **yes** — `format`/`table` fields | — |
| 22 | device address and length of a buffer | `owned.rs`:91, 95 | **yes** — record fields | — |
| 23 | `retarget_device_view` — move only the device view | `owned.rs`:127 | no | **unwritten** |
| 24 | **the two axes stay apart — nobody may pick the wrong view** | `owned.rs`:62–77 | no | ~~carried at a PARAMETER, not at a FIELD~~ **carried — §3, closed 2026-09-03** |
| 25 | `Owned<Driver>` / `Owned<Device>` typestate | `owned.rs`:55, 60 | no | **category C — parallel lane** |
| 26 | the completion as a value: id and length, separately | `owned.rs`:218 | no | **unwritten** |
| 27 | the whole ARP exchange, rx armed BEFORE tx | `net.rs`:135 | no | **unwritten** ¹ |
| 28 | the whole ARP frame, all sixteen fields | `net.rs`:273 | quarter (4 of 16) | **unwritten** |
| 29 | a result with seven separately checkable fields | `net.rs`:66 | no | **unwritten** |
| 30 | two queues with DIFFERENT notify offsets | `net.rs`:170–179 | no | **unwritten** |

¹ **#27 is composition, and it is the one row not separately measured.** Every constituent
below it is; the orchestration was not assembled as one function. It is marked *unwritten*
because each part checks and emits, and that is a weaker claim than a measurement — *it is
written here so the row can be argued with.*

```
30 capabilities      6 already in the file
                    21 unwritten and measured writable
                     3 ownership handover — parallel lane
                     0 not carried            <- was 1 until §3 was repaired
```

---

## 2. The twenty, with the output that decided each

Every probe was run through the **unchanged** checker and the **unchanged** emitter, and
where it lowered, the C went through `cc -std=c11 -Wall`. *Three of these went green at the
checker and were still wrong; only the emitter, or `cc`, said so.*

| probe | checker | emitter | `cc` |
|---|---|---|---|
| `probe-transport-poll-used.gab` | `10 items, 0 errors, 0 hints` | writes C | passes |
| `probe-transport-kick-berechneter-versatz.gab` | `4 items, 0 errors, 0 hints` | writes C | passes |
| `probe-transport-merkmale-aushandeln.gab` | `8 items, 0 errors, 0 hints` | writes C | passes |
| `probe-transport-warteschlange-aufsetzen.gab` | `11 items, 0 errors, 0 hints` | writes C | passes ² |
| `probe-transport-ruecksetzen.gab` | `6 items, 0 errors, 0 hints` | writes C | passes |
| `probe-ecam-faehigkeitenlauf.gab` | `17 items, 0 errors, 0 hints` | writes C | passes |
| `probe-region-schnitt-und-nullen.gab` | `18 items, 0 errors, 0 hints` | writes C | passes |
| `probe-netz-rahmen-und-ergebnis.gab` | `9 items, 0 errors, 0 hints` | writes C | passes |

² **and this footnote was WRONG for half an hour, which is the reason it says so.** The
first version of that probe read `tx.weckversatz` straight off a `let … else (e)` binding,
`cc` refused it (§4, finding 3), and the row said *passes* because the compile had been run
BEFORE the edit and not after. *The same class as the pattern that could not find the
barrier: a number carried forward past the change it was measuring.* The comparison now
goes through a helper taking the record as a plain parameter, and `cc` is silent.

### `poll_used` — #16, and it is unwritten

```
messung/proben/probe-transport-poll-used.gab: 10 items, 0 errors, 0 hints
  M1 saw 9 expressions, 0 of them without a type (100 % coverage)
```

The emitted body, read and not grepped:

```c
{
    uint32_t _r1 = 0;
    while (!(USED_IDX != von)) {
        if (_r1 >= 682u) { geraet_antwortet_nicht(); }
        _r1++;
    }
}
/* awaits { usedring_gesehen } -- paired at compile time (V001-V004) */
uint16_t stand = atomic_load_explicit(&USED_IDX, memory_order_acquire);
return (Abschluss){ .kopf = u->slots[i].kopf, .laenge = u->slots[i].laenge };
```

**One difference to caprock, and it is Gabbro's way round.** Caprock returns
`Option<Completion>` and lets the caller decide what a timeout means. Gabbro's `retry` sends
the overrun to a **named** `on_exceeded` function that must be `-> never`. *The absence is
not one shape of nothing; it has a name, and the name is in the manifest.*

### `kick` at a computed offset — #9, and it is unwritten

The claim under test was that a `device … at mmio` block carries CONSTANT offsets and the
notify address is computed. It does, and the runtime half goes into the device **base**:

```c
uint64_t adresse = notify_basis + notify_versatz * notify_faktor;
Weckfenster f = (Weckfenster){ .basis = (volatile uint8_t *)(uintptr_t)adresse };
(*(volatile uint16_t *)(f.basis + 0)) = warteschlange;
```

> **And the checker was green before this body was correct.** The first version wrote
> `let adresse = …` without a type; `pruefe` said `4 items, 0 errors, 0 hints` and `emit`
> said
>
> ```
> error: [C001] …:31:5: no lowering: `let` without a resolvable type
> ```
>
> *A verdict of "expressible" taken at the checker alone would have been wrong here.*
> One observation for whoever writes the real driver: `notify_versatz * notify_faktor` is
> `uint16_t * uint32_t` and therefore multiplies at 32 bits before widening. Caprock casts
> both to `u64` first. Gabbro can say the same by declaring the parameters `u64`; nothing
> forces it to.

### The `Option`-shaped returns — #7, #16, #19

Three caprock capabilities return an `Option`. The direct transliteration is a `tagged type`,
and **it falls** — see §4, finding 1. Gabbro's own form for the same job is the error
channel, and it says more:

```gabbro
impl fn warteschlange_aufsetzen(…) -> Warteschlange or Aufsatzfehler
…
    if qmax == 0 {
        return Aufsatzfehler::GibtEsNicht;
    }
```

`let … else (e) { … }` at the caller, and the `else` branch must return or diverge — so
"this queue does not exist" cannot be dropped, which is what the exhaustive `match` would
have bought. **The absence carries a name instead of being one shape of nothing**, and
caprock's own comment asks for exactly that: *"das unterscheidet 'Queue 1 gibt es nicht' von
'Queue 1 antwortet nicht'."*

### Where the language refused, and was right

Four refusals in this run were the checker doing its work, not a limit:

| written | fell at | what caprock does instead |
|---|---|---|
| `g.TREIBERMERKMAL = wunsch;` (`u64` into `u32`) | `M101` | `want as u32` — a **silent truncation** |
| `dev_basis + 256` | `M104` | wraps without a word |
| `if nieder & 1 != 0` | `M136` | groups the other way in C; caprock parenthesises by habit |
| a second name for register `0x14` | `N009` | — |

**`M136` is worth naming.** `x & y != z` groups as `(x & y) != z` in Gabbro and as
`x & (y != z)` in C, and the checker refuses to let the reader guess. That is a class of bug
this exact driver family is famous for.

### And one semantic difference that is easy to walk into

`bounded N ops` counts **ops, not passes.** Caprock's `guard < 48` counts iterations; the
Gabbro bound is a total budget, and `K006` says so with the figure in hand:

```
error: [K006] …:106:5: one pass of this loop costs 105 ops, the loop promises `bounded 48 ops`
```

*A capability-list walk written with `bounded 48 ops` ends after one entry.* The bound is
`48 * 105`.

---

## 3. ~~The one that is NOT carried — and it is a SECOND item, not the first~~ — **it is carried since the same afternoon**

> **Read this section as the working that produced a repair, not as a standing gap.**
> Everything below was measured against the unchanged checker; the paragraph at the
> end of the section says what happened next and what it cost.

**Capability #24: the two axes of a DMA buffer stay apart.**

Caprock holds both addresses of one buffer in `Owned` (`owned.rs`:62–77) and its own note
names the bug it exists against:

> *"beide Adressen in einer Struktur zu halten, aus der man sich je nach Zweck die passende
> greift, ist genau die Bequemlichkeit, die aus zwei Achsen eine macht: bis ext-36 trugen sie
> denselben Wert, mit einem IOVA-Fenster ≠ 0 fallen sie auseinander, und ein Treiber, der sie
> vermischt, programmiert dem Gerät eine Adresse, die es nicht auflösen kann."*

It buys the guarantee with **field privacy**: `cpu` is unreadable outside the crate, so there
is no getter that hands out the one where the other was meant.

Gabbro has no field privacy. What it has is `opaque`, and `opaque` is the **stronger**
instrument at exactly this point — it makes the mixing a type error rather than a convention
about which getter to call. Measured, `messung/proben/probe-opak-am-feld.gab`:

```
error: [N030] …:48:24: `c` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
messung/proben/probe-opak-am-feld.gab: 11 items, 1 errors, 0 hints
```

**One error, and the file holds four wrong sites.** `N030` fires at a bare **parameter** of
the wrong view. It stays silent at

* the same mistake read out of a **pointer field** — `deskriptor_stellen(p.cpu, p.laenge)`;
* and out of a **local binding** taken from that field.

Both `0 errors, 0 hints`, in the same run, so this is *which* fire and not *whether any*.

**And the obvious way out is not there either.** If the RECORD were `opaque`, its fields would
have to be reached through accessors — and an accessor takes the view at parameter position,
which is exactly where `N030` bites. That would buy the guarantee back. It does not:
`opaque` on a record does not close its fields, and site 5 of the same probe reads `p.cpu`
straight out of an `opaque type OpakerZweiachser` with `0 errors, 0 hints`.

> **A field is where the two axes actually live.** The shape caprock guards is a record
> holding both; the one position `N030` reads is the one position that shape never uses.

**And the bundling cannot simply be dropped.** The obvious objection — *pass the two views as
separate parameters and the check bites* — gives up the thing `Owned` exists for: that these
two numbers are the two views of the **same** buffer. `Region::carve` has to hand back one
value, not three loose ones, or the pairing is back in the caller's head, which is where
caprock found it and took it out. *A guarantee that only holds while you refuse to put the
pair in a record is not the guarantee.*

**And this is a CHECKER gap, not `S2`.** The type is in the language and the type is right —
`opaque` says the thing. A pass reads one position and not another. *That is the shape of
`R008` and `R013` in `messung/PASSREGISTER.md`*, where the space was compared and the rights
in the same struct were not, and it is attributable there rather than to the language.

### And it was closed the same day, after the claim was re-measured — 2026-09-03

**The claim above was verified before anything was built on it.** *One error in a run that
did not stop* is the shape of a masked measurement, and this tree has that class booked in
its own instructions. So each of the five sites was cut out into its **own file** and run
alone:

| site | alone | what it should say |
|---|---|---|
| 1 `richtig` — `p.dev` at a `Geraetesicht` | `6 items, 0 errors, 0 hints` | nothing — and it says nothing |
| 2 bare parameter `c` | `6 items, 1 errors` `[N030]` | the refusal — and it fires |
| 3 `p.cpu` at a pointer field | `6 items, 0 errors, 0 hints` | a refusal — **silent** |
| 4 `let c = p.cpu` then the call | `6 items, 0 errors, 0 hints` | a refusal — **silent** |
| 5 `p.cpu` out of an `opaque` record | `7 items, 0 errors, 0 hints` | a refusal — **silent** |

**Silent alone, so nothing was masking anything.** And the run does not stop either: a file
with three bare-parameter mistakes reports `7 items, 3 errors` — three `N030`s, not one.
*The two failure modes were separated by measurement and not by reading the code.*

**What the rule's subject actually was:** a **bare, unsuffixed binding** — a parameter, or a
`let` with a written type or a call whose declared return type is nominal — compared at four
positions (`let` initialiser, `return`, `==`/`!=`, call argument). `namen.rs` said so twice
in one function, `if !o.suffixe.is_empty() { continue; }`, and a field access has suffixes.

**The repair walks `.f`/`->f` from the binding's declared record**, gives up at an `[i]`
(W10), and reads the **write** end too — `p.dev = c` is `retarget_device_view`'s own shape
(`owned.rs`:127), and a rule that guards the read and not the write leaves standing the half
that corrupts the record for every later read.

```
error: [N030] …:54:24: `c` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
error: [N030] …:62:24: `p.cpu` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
error: [N030] …:72:24: `c` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
error: [N030] …:94:24: `p.cpu` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
messung/proben/probe-opak-am-feld.gab: 11 items, 4 errors, 0 hints
```

*The line numbers moved against the block at the top of this section because the probe's own
header grew by six lines when it was marked closed; site 2 is `:48` there and `:54` here, and
it is the same call.*

**What it newly refuses over the whole corpus: nothing.** All 635 `.gab` files were run
before and after, file by file, and compared on exit code, error count and identifier list —
`0 newly refused`, `0 newly accepted`, and the single file whose verdict moves is the probe
itself (1 error to 4). The 438 poison files of that baseline are unchanged as a block;
the two written for this repair (`669`, `670`) came after it and take the corpus to 440.

> **And the denominator is said with the numerator, because it is small.** Three of 635 files
> hold a nominal type in a record field at all: `F01.gab` (four such records, no read),
> `probe-opak-am-feld.gab`, and `probe-region-schnitt-und-nullen.gab` — the last of which
> makes **six** such reads and one such write, is a working programme, and stays green under
> the extended rule. *A rule that refuses nothing because nothing exercises it is a different
> result from one that refuses nothing because every site is right.* Here it is a little of
> both, and saying only the first number would be the flattering half.

**The other half of the finding is NOT repaired, and it is not a pass.** An `opaque` record
still does not close its fields. It is no longer needed to catch the mixing — the check bites
at the field itself — but `opaque` on a record promises a privacy it does not have, and that
is a construct through §7's cost gate. It stays in `dokumente/OFFEN.md` under `O7`.

Probes: `beispiele/gift/669-the-wrong-view-out-of-a-field.gab` (read),
`beispiele/gift/670-the-wrong-view-into-a-field.gab` (write). Mutations:
`ein-feld-traegt-keinen-namen`, `in-ein-feld-darf-jede-sicht`.

---

## 4. Five findings that fell out of the attempts, four of them not about the mark

They are recorded because a probe that produced them exists in the tree, and because three
of them sit in a file this lane does not own.

**1. A `tagged type` value has NO CONSTRUCTOR.** `messung/proben/probe-tagged-wird-gebaut.gab`.
**Fifteen `tagged type` declarations stand across nine corpus files**, every one of them
taken apart by `match`. **Not one is put together anywhere** — and the reason is not habit:
no spelling exists. Four of them, each measured on its own, so no refusal masks another:

```
Keine                        error: [M119] `Keine` is declared nowhere
Aufsatz::Keine               error: [M126] `Aufsatz` is not a declared `reason`
Keine()                      error: [K003] `f` promises costs, but `Keine` is not declared here
let x : Aufsatz = Keine;     error: [M119] `Keine` is declared nowhere
```

**This is the «B9» shape a third time** — *a form that exists at the declaration and has no
way to be written.* Its second instance is named in `dokumente/PFLICHTEN.md`:483, in the same
list whose finding 1 (*"`A::B` parses and never resolves … whether `IpcResult` is a `module`,
a `reason` or a variant type"*) is still standing. The `reason` half was closed by adding a
producer (`reasonval`, `SYNTAX.md`:591); the variant half never was. **It did not block a
single capability here** — the error channel does the same job — so it belongs in
`dokumente/OFFEN.md`, not in the 25 %.

**2. `leave`/`next` at a `retry` label CHECKS and does not LOWER.**
`messung/proben/probe-marke-an-retry-und-traverse.gab`, `6 items, 0 errors, 0 hints`, then:

```
error: [C001] …:59:13: no lowering: `leave`/`next` naming no enclosing loop
gabbro emit: … has errors -- no C written
```

`retry [ident]` and `forever [ident]` both carry a label (`SYNTAX.md`:1000, 1008);
`traverse ident` does not — there the `ident` is the loop variable, and `next i` falls at
`S001`, correctly. So this is about two forms. The checker resolves both. **`emit.rs`'s
`forever` writer holds the only `schleifen.push` in the whole file** — line 7821 on
2026-09-03, and the COUNT is the durable half of that, not the line. The corpus hides it by
construction: every `leave`/`next` in `beispiele/41` names `runde`, `bootlauf` or `leerlauf`,
and all three are `forever` labels.

*It cost this measurement a detour*: the ECAM walk wants `next lauf` in the `else` of a
`narrow`, and `M105` will not let that `else` fall through either. The walk was written with
plain comparisons instead, V1/V2 carried the range into the branch, and it emits — **so this
is an emitter gap the capability went around, not a language limit.**

**3. `let x = f() else (e) { … }` binding a RECORD lowers to `x->field`.**
`messung/proben/probe-fehlerkanal-verbundwert.gab`, `5 items, 0 errors, 0 hints`, and the
emitter declares the binding as a value and then dereferences it:

```c
static uint16_t liest(void) {
    W w;
    { Fehlt e; (void)e; if (!liefert(true, &w, &e)) { return 0; } }
    return w->a;
}
```

```
error: invalid type argument of '->' (have 'W')
```

Found by **reading** the body. The checker is silent because the fault is not in the source.

> Findings 2, 3 and 4 sit in `crates/gabbro-check/src/emit.rs`, which another lane owns.
> They are reported here and **not fixed here.**

**4. A narrowing M1 has PROVED reaches C as an implicit conversion.**
`messung/proben/probe-transport-merkmale-aushandeln.gab`. `BEWEIS.md` §2 line 7 says
*"none, but to be checked mechanically"*; `zaehle-c-formen.py --uebersetzer` is that check,
and until this run it reported **zero hits over the whole corpus**:

```
(*(volatile uint32_t *)(g->basis + 12)) = wunsch >> 32;
warning: conversion from 'uint64_t' to 'uint32_t' may change value [-Wconversion]
```

`M101` accepts the assignment because `w >> 32` on a `u64` provably fits — and gcc cannot
reproduce that proof, so it arrives as a bare narrowing. **Three ways of writing it, one
emission, no cast in any of them.** The corpus had simply never contained a program that
narrows through a proved range; a 64-bit feature word reached through a 32-bit register is
the first. *A guard is only as strong as the programs it has been shown.*

The mark was raised to 67/32 with a named exit written at the mark, the way the same file's
own precedent for `D1` did it, and booked as `O9`. **The repair is in `emit.rs` and belongs
to another lane.**

**5. `N030` at a field** — §3 above. It is the one of the five that touches the mark, and **the only one of the five that was closed on the day it was found**: a pass change, no new word, nothing newly refused over the corpus.

---

## 5. The recomputed mark

```
                                        capabilities   of 30
  in Gabbro today                             6         20 %
  unwritten, measured writable               21         70 %
  ------------------------------------------------------------
  IN GABBRO                                  27         90 %

  beside it                                   3         10 %
      A  plumbing (B1/B2)                     0          0 %
      B  hardware instructions (B5)           0          0 %
      C  what Gabbro does not carry           3         10 %
             ownership handover (3) — parallel lane
```

> **This block read 26 / 87 % / 4 until the afternoon of the same day.** `C2` was a pass gap
> and the pass was extended, so capability #24 moved from *not carried* to *unwritten and
> measured writable* — it is right in the language, and it still does not stand in
> `virtio-net.gab`. **The mark moves because a checker learned to read one more position, and
> the honest sentence is that and not "the language got better".**

**A is zero because `B1` closed on 2026-09-02** and virtio-net wants no string output.

**B is zero, and that is measured over the object rather than assumed.** `caprock-virtio`
contains no `asm!`, no `in`/`out`, no port I/O — the four sources were read for it. Its
`fence` is a function pointer the caller supplies, and the previous pass established that
`publishes`/`awaits` lower it to C11 acquire/release. **The `B5` items — legacy PCI
`0xCF8`/`0xCFC`, `invlpg`, `TLBI`, shootdown — are not in this driver at all.** They are real,
and they are somewhere else in caprock.

### And the two zeroes say something about the FIRST pass

If A and B are both zero for this driver, then the 25 % of 2026-09-02 was **entirely
category C** — which its own text denies, since it put C at *"genau ein Posten"*. Both
cannot hold. **What the first pass counted as "beside Gabbro" was in large part
capabilities that were merely unwritten**, and that is precisely what its closing note
suspected and could not settle: *unwritten is not inexpressible.*

*The correction is therefore not that the language got better in a day. It is that the
first quotient had no categories, said so, and was right about itself.*

### The two numbers are not comparable, and that is said rather than hidden

**75 % and 87 % rest on different enumerations.** The pass of 2026-09-02 did not write its
denominator down; this one does, above, row by row with a `file:line` against each. *The
honest statement is not "the mark rose by twelve points" but "the mark now has a denominator
someone can argue with."*

### The answer to the question the item asked

> *Is the third bucket a bucket of one?*

**It was a bucket of two for about an hour, and then it was a bucket of one again — because
the second item was priced and paid, not because the question was re-asked.**

| | what it is | where it is booked |
|---|---|---|
| **C1** | ownership handover | `R004`/`R007`; a parallel lane, 2026-09-03 — **still open, still not this lane's** |
| ~~**C2**~~ | ~~the two axes of a DMA buffer stay apart~~ | **closed 2026-09-03** — `N030` reads the field, and the write into it (§3) |

**The intermediate answer was right when it was given, and saying so is the point.** `C2`
had no name before that run; naming it is what made it cheap enough to price. **And C2 was
never `S2`:** `S2` is the item no verification heals — a property the language cannot
*state*. `opaque` states this one correctly and a pass did not read it, which put it in the
`R008`/`R013` family, and that family is repaired by extending a pass. *It was, on the same
day, for zero new words and zero newly refused programs.*

### So what is the third bucket, stated plainly

**One item, three capabilities, and it belongs to another instance.** Everything else in the
enumeration is either in the file or measured writable. The sentence the fifth mark can now
carry is:

> *Of thirty capabilities of a real virtio-net driver, **27 are in Gabbro** — six written and
> twenty-one measured writable against the unchanged checker and emitter. The three that are
> not are one question — the ownership handover — and it is open, not answered.*

**Two cautions travel with that sentence and are not decoration.** *Measured writable* is a
claim about probes that check and lower, not about an assembled driver; row #27, the
orchestration, is the one row not separately measured and says so. And 90 % is not comparable
with the 75 % of 2026-09-02, for the reason given two headings up: that quotient had no
written denominator.

*A bucket of one that turned out to be a bucket of two, and was a bucket of one again by
evening, is the finding — and the middle step is the part that made the last one possible.*
