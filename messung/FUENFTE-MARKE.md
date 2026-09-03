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

## 0. ~~What is NOT measured here, and by whom~~ — **it was measured the same evening, and §6 re-measures it**

> **This section was true when it was written and is not the standing state.** The parallel
> lane closed `C1` at `7455b0f`, two commits before the merge that carries this document, so
> the two lanes could not see each other. §6 takes the handover up, reproduces both verdicts,
> and attacks the empty bucket the arithmetic produces.

**The ownership handover was a parallel lane's, taken 2026-09-03.** That is
`reclaim(buf : Owned<Device>) -> Owned<Driver>` (`lib.rs`:311), `reclaim_unproven`
(`lib.rs`:326) and the `Owned<Driver>`/`Owned<Device>` typestate itself (`owned.rs`:55, 60) —
three capabilities, one question, and `R004`/`R007` under it. They appeared in the enumeration
below **named and unmeasured**, and nothing in *this* pass decided them.

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
| 17 | **`reclaim`** — the buffer back against the device's receipt | `lib.rs`:311 | no | ~~category C~~ **unwritten — §6, closed 2026-09-03** |
| 18 | `reclaim_unproven` — the named way back without one | `lib.rs`:326 | no | ~~category C~~ **unwritten — §6, closed 2026-09-03** |
| 19 | `Region::carve` — monotone, fail-closed | `owned.rs`:200 | no | **unwritten** |
| 20 | zero a RUN-TIME byte range | `owned.rs`:164 | no | **unwritten** |
| 21 | typed access into a buffer | `owned.rs`:133–155 | **yes** — `format`/`table` fields | — |
| 22 | device address and length of a buffer | `owned.rs`:91, 95 | **yes** — record fields | — |
| 23 | `retarget_device_view` — move only the device view | `owned.rs`:127 | no | **unwritten** |
| 24 | **the two axes stay apart — nobody may pick the wrong view** | `owned.rs`:62–77 | no | ~~carried at a PARAMETER, not at a FIELD~~ **carried — §3, closed 2026-09-03** |
| 25 | `Owned<Driver>` / `Owned<Device>` typestate | `owned.rs`:55, 60 | no | ~~category C~~ **unwritten — §6, closed 2026-09-03** ³ |
| 26 | the completion as a value: id and length, separately | `owned.rs`:218 | no | **unwritten** |
| 27 | the whole ARP exchange, rx armed BEFORE tx | `net.rs`:135 | no | **unwritten** ¹ |
| 28 | the whole ARP frame, all sixteen fields | `net.rs`:273 | quarter (4 of 16) | **unwritten** |
| 29 | a result with seven separately checkable fields | `net.rs`:66 | no | **unwritten** |
| 30 | two queues with DIFFERENT notify offsets | `net.rs`:170–179 | no | **unwritten** |

¹ **#27 is composition, and it is the one row not separately measured.** Every constituent
below it is; the orchestration was not assembled as one function. It is marked *unwritten*
because each part checks and emits, and that is a weaker claim than a measurement — *it is
written here so the row can be argued with.*

³ **#25 is the row the whole third bucket rested on, and §6 re-measures the artifact behind
it.** The capability goes; the probe `C1` closed it with keeps caprock's *order* and not its
*exclusion*, and a second probe was written for the difference. The row is *unwritten and
measured writable* either way — but by the second probe, not the first.

```
30 capabilities      6 already in the file
                    24 unwritten and measured writable
                     0 ownership handover     <- was 3 until `7455b0f`, re-measured in §6
                     0 not carried            <- was 1 until §3 was repaired
```

**Re-derived here rather than inherited, 2026-09-03.** All thirty `file:line` citations above
were opened in `../caprock-messbasis` at `a1bf707` and each points at what its row claims —
`#17` at `pub fn reclaim(&self, buf: Owned<Device>, _done: &Completion)`, `#25` at
`pub enum Driver {}` / `pub enum Device {}`, and so on for the other twenty-eight. The six
*yes* rows were checked against the object: `stufe_laeuft`, `publishes`/`awaits`, `armieren`,
`AVAIL_IDX` all stand in `messung/treiber/virtio-net.gab`, and `USED_IDX` stands there **once**,
at line 212, declared and never read — which is exactly what row #14's *half* says.

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
  unwritten, measured writable               24         80 %
  ------------------------------------------------------------
  IN GABBRO                                  30        100 %

  beside it                                   0          0 %
      A  plumbing (B1/B2)                     0          0 %
      B  hardware instructions (B5)           0          0 %
      C  what Gabbro does not carry           0          0 %
```

> **This block read 26 / 87 % / 4, then 27 / 90 % / 3, and now 30 / 100 % / 0 — all on one
> day, in three lanes that could not see one another.** `C2` was a pass gap and the pass was
> extended (#24). `C1` was measured and closed at `7455b0f` (#17, #18, #25), two commits
> before the merge that carries this document, which is why §0 still called it unmeasured.
> **The mark moves because a checker learned to read one more position and because a question
> nobody had asked got asked — the honest sentence is that, and not "the language got
> better".**
>
> **100 % is a strong claim and §6 attacks it rather than banking it.** The attack does not
> overturn the number; it overturns one of the artifacts underneath it.

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

**It was a bucket of two for about an hour, then a bucket of one, and by the end of the same
day a bucket of none.** Each step was priced and paid; the question was never re-asked, and
no step was arithmetic.

| | what it is | where it is booked |
|---|---|---|
| ~~**C1**~~ | ~~ownership handover~~ | **closed 2026-09-03** at `7455b0f`, `beispiele/66-transport-rueckgabe.gab` — and **re-measured in §6**, where the capability holds and the artifact is replaced |
| ~~**C2**~~ | ~~the two axes of a DMA buffer stay apart~~ | **closed 2026-09-03** — `N030` reads the field, and the write into it (§3) |

**The intermediate answers were right when they were given, and saying so is the point.** `C2`
had no name before that run; naming it is what made it cheap enough to price. **And neither
was ever `S2`:** `S2` is the item no verification heals — a property the language cannot
*state*. `opaque` states `C2` correctly and a pass did not read it, which put it in the
`R008`/`R013` family, repaired by extending a pass. `C1` the language states in two different
ways, and §6 shows that the two are not equally strong — *which is a statement about the
probe, not about the vocabulary.*

### So what is the third bucket, stated plainly

**It is empty.** Everything in the enumeration is either in the file or measured writable.
The sentence the fifth mark can now carry is:

> *Of thirty capabilities of a real virtio-net driver, **all thirty are in Gabbro** — six
> written and twenty-four measured writable against the unchanged checker and emitter. There
> is no capability of this driver that the language cannot express.*

**Three cautions travel with that sentence and none of them is decoration.**

1. *Measured writable* is a claim about probes that check and lower, **not about an assembled
   driver**. Row #27, the orchestration, is the one row not separately measured and says so.
2. **100 % is not comparable with the 75 % of 2026-09-02**, for the reason given two headings
   up: that quotient had no written denominator. It is not comparable with 87 % or 90 % either
   — those are this same denominator at three times of day.
3. **And the sentence is about *this driver*.** Thirty capabilities of `caprock-virtio` are
   not the kernel; `B5`'s legacy port I/O and TLB shootdown are real and are simply not in
   this object. *An empty bucket over one enumeration is not an empty bucket.*

*A bucket of one that turned out to be a bucket of two, was a bucket of one again by evening
and empty by night, is the finding — and every middle step is the part that made the next one
possible.*

---

## 6. The empty bucket, attacked — and one probe did not survive it

*Measured 2026-09-03 against the merged tree at `9b5c067`, binary built on `ki-pc-fisch-101`.*

An empty third bucket is the strongest claim this document makes, and it rests on two
verdicts taken in lanes that could not see each other. Both were re-run here, unchanged, and
then the question behind them was asked once more: **does *writable in a probe* mean the same
thing as *expressible*?**

### Both verdicts reproduce exactly

| | command | result |
|---|---|---|
| `C1` | `./target/debug/gabbro pruefe beispiele/66-transport-rueckgabe.gab` | `11 items, 0 errors, 0 hints` |
| `C1` | `./target/debug/gabbro emit …` then `cc -std=c11 -Wall -Wextra -c` and `-O2 -c` | emits; `rc=0` at both |
| `C2` | `./target/debug/gabbro pruefe messung/proben/probe-opak-am-feld.gab` | `11 items, 4 errors, 0 hints`, four `N030` at `:54`, `:62`, `:72`, `:94` |

**Nothing in §3 or in `7455b0f` is withdrawn.** What follows is a second question about the
`C1` artifact, and the answer moves the artifact rather than the row.

### `beispiele/66` keeps the ORDER — and that part is real

Three attacks, each in its **own file**, because one error in a run that did not stop is the
shape of a masked measurement:

```
b1 consumed twice        ->  error: [L104] `b1` is consumed a second time
b1 consumed on no path   ->  error: [L107] `b2` is created here and consumed on no path
arm on an armed token    ->  error: [O003] `arm` presupposes `fahrer`, `b1` stands at `geraet`
```

That is a genuine linear typestate with an order on it, and it is what caprock's `Owned`
buys with move semantics and `transition`.

### It does not keep the EXCLUSION, and that is what `owned.rs` is for

`owned.rs`:60 states the guarantee in one line at the type: `pub enum Device {}` carries
*"Dieser Typ hat **keine** Zugriffsmethode. Das ist die ganze Zusicherung."* The write methods
sit on `impl Owned<Driver>` alone (`owned.rs`:133–155), `arm` takes the buffer **by value**
(`lib.rs`:295), and `Owned` is deliberately not `Copy` — a point caprock measured against a
mutation and wrote down: with a hand-written `impl<S> Copy for Owned<S>`, *"armiert und
trotzdem weiter beschrieben"* compiles again.

In `beispiele/66` the linear thing is the **ghost token**; the buffer goes in beside it as
`h : ptr<normal, rw> Puffer`, unconsumed. Nothing ties the two together:

```gabbro
let b1 = arm(h, i, b);
h.slots[i].belegt = false;   -- the device owns it, and the driver writes
let b2 = hole(h, i, b1);
```

```
8 items, 0 errors, 0 hints
```

**Two further losses, one cause.**

* **`hole` has no stage precondition.** It carries no `advances` — deliberately; `advances
  geraet -> fahrer` falls at `O002`, and the file's own header says so. But a function with
  no `advances` has nothing to presuppose either, so reclaiming a token still at `fahrer` is
  `8 items, 0 errors, 0 hints`. Caprock's `reclaim(buf : Owned<Device>, …)` cannot be handed
  an `Owned<Driver>`: **the precondition is the parameter type.**
* **The receipt is read by no pass.** `requires geraet_fertig()` is an obligation nothing
  checks at a call site. Measured on three files: `requires 1 == 0` at a call site is
  `4 items, 0 errors, 0 hints`, while `requires x > 10` called with `0` **does** fall —
  `error: [M115] … the argument lies in 0 .. 0`. **`M115` reads range statements about
  arguments and nothing else**, and the register says as much of `D012` in its own
  reservation: *"It does not PROVE a premise, and it cannot."* Caprock's receipt is a
  **value** whose constructor is `pub(crate)` with exactly one production site outside the
  tests — `lib.rs`:356, inside `used_entry`. A `Completion` cannot be made anywhere but at
  the used ring.

And `hole` and `hole_unbelegt` emit **byte-identical C** — three functions, one body each,
`h->slots[i].belegt = false;`. That much is honest: the file says the unproven path rides its
NAME, and it does. Caprock additionally marks `reclaim_unproven` `unsafe`, so a block stands
at its call site; here both are ordinary calls.

### The gate that would rescue the ghost form does not exist

A buffer write happens **at** `fahrer` without advancing anything. Three spellings of that
precondition, each measured alone:

```
advances fahrer -> fahrer  ->  error: [O002] `schreibe` goes from `fahrer` to `fahrer` -- that is not a step forward
requires fahrer            ->  error: [D021] `fahrer` in `requires` is not declared here
requires b == fahrer       ->  error: [D021] `fahrer` in `requires` is not declared here
```

**`order`/`advances` gates a function that MOVES the stage, and only that.** The standing
precondition has no spelling.

### But the LANGUAGE keeps the guarantee — the probe chose the weaker of two forms

`beispiele/66`'s header named the two-type route and ruled it out:

> *"`Owned<Fahrer>` -> `Owned<Geraet>` as TWO NOMINAL types with a value moving between them:
> `N030` (nominal) refuses `let g: GeraetBesitz = b`."*

**That tested the ASSIGNMENT spelling, and caprock never uses it.** `owned.rs`:102 moves
between the two states with a **function** — `pub(crate) fn transition<T>(self) -> Owned<T>`.
Both spellings, each in its own file:

```
let g : GeraetPuffer = b;   ->  [N030] the binding: a `FahrerPuffer` where a `GeraetPuffer` is required
                                [L101] `b` is listed under `consumes` but is consumed on no path
let g = arm(b);             ->  6 items, 0 errors, 0 hints
```

With two `linear type`s and the write path declared over the driver side alone, all three
losses come back — **with no new word, no pass change and no rule change**:

| | file | result |
|---|---|---|
| the round trip | `messung/proben/probe-besitz-zwei-typen.gab` | `22 items, 0 errors, 0 hints`; emits; `cc -Wall -Wextra` silent at `-O0` and `-O2` |
| write while armed | `beispiele/gift/673-writing-while-the-device-owns-it.gab` | `8 items, 1 errors` — `[N030] b1 is a GeraetPuffer, and schreibe takes a FahrerPuffer there` |
| reclaim without arm | `beispiele/gift/674-reclaiming-a-buffer-that-was-never-armed.gab` | `7 items, 1 errors` — `[N030] b is a FahrerPuffer, and hole_unbelegt takes a GeraetPuffer there` |
| receipt from thin air | `beispiele/gift/675-a-receipt-made-out-of-thin-air.gab` | `6 items, 1 errors` — `[D004] the return value silently converts gift::beleg_transport::Beleg` |

**The receipt comes back too, and it needs a door that was already built and never used.**
`pub(crate)` has a spelling in Gabbro: an `opaque type` whose one producer stands inside the
declaring module cannot be built from its carrier anywhere else. So the probe puts the
transport and the driver in **two modules**, and a driver that invents a `Beleg` out of a
`u64` falls at `D004` — measured above, not assumed.

> **And that measurement moves a line in the sentence register.** `d.undurchsichtig`
> (`D003`/`D004`, `saetze.rs`:843) carries the reservation *"On today's corpus this sentence
> has ZERO bite: all twelve opaque declarations declare and use in the same module"* and
> its `gemessen_an` reads *"NO corpus site exercises it."* Both halves are now stale. Counted
> at the branch point `9b5c067`: **75 `opaque type` declarations in 50 of 639 `.gab` files**,
> not twelve (`grep -rhE '^ *(pub )?opaque type ' . --include=*.gab | wc -l`); and
> `probe-besitz-zwei-typen.gab` declares one in `c1v::transport` and uses it in `c1v::treiber`,
> so the boundary is crossed by a working programme for the first time — 77 in 52 of 643 with
> this commit's own two.
> *The register is not edited here — it belongs to the pass that owns it, and a stale
> reservation is a finding to hand over, not a number to overwrite in passing.*

The two `linear type`s reach C as two distinct structs, so even the emitted code separates
them:

```c
typedef struct { uint8_t nichts; } FahrerPuffer;
typedef struct { uint8_t nichts; } GeraetPuffer;
```

### What this changes, and what it does not

**Row #25 stays closed and the bucket stays empty** — the capability *is* expressible, and it
is expressible in the standing vocabulary. What changes is which artifact is entitled to say
so. *`beispiele/66` answered "can this be written?" and the question underneath was "does the
written thing carry what the original carried?"* Those came apart here, and only writing the
second probe separated them.

> **The general form is worth more than this instance.** A probe that checks green has
> demonstrated that a shape is admissible. It has not demonstrated that the shape carries the
> property the original was carrying — and *the checker cannot tell the difference*, because
> the dropped property was never written down for it to check. **The test is not "does it
> check", it is "does the thing it forbids still get forbidden".** Every one of the twenty-four
> *measured writable* rows above rests on the weaker question, and this document should be
> read with that in mind. **Booked as `O10` in `dokumente/OFFEN.md`**, with the size of the
> backlog counted: 24 rows, 8 with a positive probe recorded in §2, **none with a negative
> one** until `671`/`672`/`673` were written for row #25.

*And the finding is not that a lane was careless.* `beispiele/66` names its own refusals under
Rule A rather than papering over them; the note that ruled out the two-type route is a
measurement, taken on a spelling that turned out to be the wrong one. **A wrong answer with
its apparatus written down beside it is repairable in an hour. That is the whole reason the
apparatus is written down.**
