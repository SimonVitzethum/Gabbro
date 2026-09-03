# The pass register — 56 sentences over twelve passes

*Set up 2026-08-21 (PL.1 + PL.2). Every figure below names the command that recomputes it.*

> **The finding this started from:** `struct Pass` had no field for a sentence. Twelve
> passes decide about every program, 191 refusal codes — and **zero sentences**. Without the
> sentences, *"Gabbro formally verified"* is not even **formulable**: one would not know
> what there was to prove.

## The state, in figures

```bash
cargo build -q --bin gabbro && ./target/debug/gabbro paesse          # the register
./instrumente/pruefe-saetze.py                                       # the second tooth
```

| | | Command |
|---|---:|---|
| Sentences in the register | **94** | `gabbro paesse` |
| of those `measured` | **87** | a poison-probe case or a caught mutation |
| of those **`ARGUED`** | **2** | a correctness argument is written down — [`K001`](K001.md), [`H006`](H006.md). *The first found an undercount by a factor of 3; the third attempt ([`V2`](V2.md)) found, instead of a measurement, the [non-determinism](DETERMINISMUS.md) and stayed `CONJECTURED`* |
| of those `CONJECTURED` | **5** | nothing measures them |
| of those `PROVED` | **0** | **that is the figure PL.2 is about** |
| Passes with at least one sentence | **12 of 12** | `gabbro paesse` |
| Codes in the checker | **274** | `./pruefe-kennungen.py` |
| of those claimed by a sentence | **223** | `./instrumente/pruefe-saetze.py` |

> **The five figures above were carried on 2026-08-31, and the ratchet RISES — with reason.**
> The subject grew: `N042` came in (`namen.erzeugter_name_zweimal`,
> `messung/ERZEUGERNAMEN.md`), and `pruefe-zahlen.py` had reported 73 against 74. The four
> figures beside it stood there older still — `of those measured` at 48 instead of 67, `Codes`
> at 191 instead of 242. *A figure that stands too low looks like a held ratchet and is a
> forgotten one.*
>
> **And on the same day once more by one, for the same reason:** `N043`
> (`namen.berichtszeile`) — a `measures` name without a carrier, `messung/TORREICHWEITE.md`.
> 74 → 75 sentences, 242 → 243 codes, 197 → 198 claimed, 67 → 68 `measured`; the 45
> without a sentence stay standing. *The second tooth, for the second time in one day.*
>
> **2026-09-02, and this time the ratchet does NOT move.** `D021`
> (`d.praedikatsname`, the base name of a place in a predicate) and `N054`
> (`n.merkmalsform`, a feature demand names one bare name) came in **with their sentences in
> the same commit** — 92 → 94 sentences, 272 → 274 codes, 221 → 223 claimed, and **51
> without a sentence, unmoved.** `messung/PREDICATE-NAMES.md`.
>
> *The four figures beside them were stale again* — `measured` stood at 68 where the run
> says 87, `Codes` at 243 where it says 274, `claimed` at 198 where it says 223. They are
> recomputed here rather than incremented, because incrementing a forgotten figure carries
> the forgetting forward.
| **Codes without a sentence — the ratchet** | **51** | `./instrumente/pruefe-saetze.py` |

**The estimate in the plan was ~22 sentences; it became 43.** The reason is not
diligence but a measurement: several passes hold **two claims of different strength**,
and writing them into one sentence would have hidden the weaker under the stronger.
`kosten` is the example — see below.

## The 50 without a sentence are not an oversight but a drawn line

> **45 → 48 on 2026-09-01.** `N047`, `N048` and `N049` came out of the register-layout audit
> and stand without a theorem **on purpose**: `Device_Konstruktor.thy` proves
> `getrennte_register_treffen_getrennte_zellen` UNDER the premise `getrennt r s`, and
> `bankeintraege_ueberlappen_nicht` for the bank. **The three rules ESTABLISH those premises;
> they do not need one of their own.** A theorem apiece would be a fourth statement of the
> same fact — and the sixth class in pure form, one layer up: *a pass whose premise nothing
> needs has moved the trust base, not shrunk it.*
>
> **48 → 50 on 2026-09-02, and the reason is the one above, one layer DOWN.** `N050` and
> `N051` came out of the same audit method applied to the emitted C, and neither establishes a
> premise — **they keep the CONCLUSIONS true of the lowering.** `Device_Konstruktor.thy`
> reasons in an address space with no word width; the emitted bank accessor computes
> `i * stride` in `unsigned int`, so with a wide enough bank two distinct `i` name the same
> address. *The theorem still holds; the C stops being a model of it.* `N051` is the same
> sentence for `uintptr_t`: an offset above `u64::MAX` has no address to be separate from.
>
> A theorem apiece would have to be a theorem about C's integer widths, and that is not what
> the proof layer models. **Measured before it was written:** codes 263 → 265, sentence-less
> 48 → 50, and neither code is named in `saetze.rs` or under `beweise/` — the delta is exactly
> these two.

```
parse.rs   37     lex.rs   7     emit.rs   1
```

**All 45 lie outside the `passliste()`**: the parser is not a checking pass, nor is the
generator. *They stand as open nonetheless, and not as defined away* — a refusal text of the
parser asserts just as much about a program as one of the cost pass.

> **What does not work is making the figure smaller by changing the question.** Whoever wants
> it at zero writes the 45 sentences — or the register gets a second column for
> "no pass", and *that* is then a decision with a date.

## What the figure 43 does NOT say

> **A written-down sentence is not a proved one.** That is the whole reservation, and it is
> larger than the achievement.

1. **`PROVED` is empty.** None of the 56 sentences was ever in Isabelle. What the register
   delivers is the **list of the claims to be proved** — the subject of PL.2, not its
   result.
2. **`measured` measures the IMPLEMENTATION, not the RULE.** A falling poison probe shows that
   the Rust decides in *this* case the way the sentence says. It does not show that it does so
   everywhere, and certainly not that the rule is right (PLAN.md PL.3, path (c)).
3. **The guardian counts ASSIGNMENTS, it does not read the sentences.** A wrong sentence counts
   like a right one; a sentence that says less than its pass delivers is not noticed at all (W10).
4. **20 of the 146 claimed codes have NO poison probe** — of those 5 are hints, the
   remaining **15 are genuine refusals that nobody measures**:
   ```
   A002 A003 E004 H004 H008 K004 L105 M106 M107 M110 M114 U001 U002 U004 U005
   ```
   *The sentence above them stands on `measured` nonetheless, because other codes of the same
   sentence are measured. That is the coarsening of this register, and it stands here instead
   of in a footnote.*

## The precondition over all 56 sentences: a hint is not a refusal

`Stufe::Hinweis` does not count as an error, and only `Stufe::Fehler` makes the compiler
fail. **Five codes are hints: `E003`, `E009`, `V003`, `S007`, `N026`.**

> **A program that passes "without a refusal" can contain functions whose frame or pairing
> claim the checker has EXPRESSLY declared undecidable.** `E009` is the honest third state
> (R16) — visible, not green. **Every sentence of this register is weaker by exactly that
> amount**, and that is why the line stands in the head of `gabbro paesse`.

## The three with the greatest load-bearing (PL.2)

### `K001` — the summation, and its measured error stands IN the sentence

**The sentence was split because the two halves are of different strength:**

| | State | |
|---|---|---|
| `kosten.summation` | **measured** | statements add; branch = maximum; what stands behind an always-leaving `if` counts once; the comparison is made at the **smallest assignment** |
| `kosten.domaenenschranke` | **measured** | `traverse` costs body × bound, and the bound is an **UPPER** bound out of the declaration — since 2026-08-31 **each of the five domains** has a probe and a mutation |

> **The error, made visible instead of overwritten:** for `mappings of` the pass read
> `levels × node length` = **2 048**, where the domain is the **leaf set**,
> `node length ^ levels` = 512⁴ = **68 719 476 736**. **Seven orders of magnitude, carried for
> three days** — and found because the **generator** ran into it, not because a test fell.
>
> It is corrected (`umgebung.rs::walkschranken`). **The sentence stands on `CONJECTURED`
> nonetheless**, for `K003` has two poison probes and they measure that a **missing** bound is
> rejected — not that a **present** one is right. *In exactly this difference the error lived
> for three days, and every other domain bound of the pass has the same construction and the
> same check: none.*

### `H006` — the rank ordering

`sperren.rangordnung` is **measured**, and the sentence carries the classical argument: *every
lock has a rank fixed at compile time, on every path one is taken only under a strictly
smaller rank, hence no circular waiting is possible.* **Three conditions the sentence needs and
the pass does not fully deliver** stand in the `vorbehalt`: interprocedurality has existed only
since 2026-08-19, over an **incomplete hull** nothing is refused (R16), and covered are only
**declared** locks.

### V2 — relational narrowing: the sentence with the greatest load and the least measurement

**`v2.relationale-verengung` stands on `CONJECTURED`, and the reason is structural:**

> **V2 has no code of its own.** The rule **widens** what passes; where it does not carry, the
> refusal comes as `M104`/`M101` out of a different sentence. *With that it cannot be
> poisoned* — a probe would have to show a **pair** (without the fact it falls, with the fact
> it passes), and for that the harness has no form today.

54 relational occurrences of the 102 flow-sensitive ones hang on it. **That is the first
sentence PL.3 should buy.**

## What the writing-down cost and what it FOUND

*The most frequent single finding was not a missing sentence but a **module head that asserts
more than its code redeems** — five times, in five files, twice simply out of date.*

| Find | File | What |
|---|---|---|
| **the K condition is not enforced** | `kbedingung.rs` | `k_haelt()` demands `breaking.is_empty()`; the pass reports handwriting only. **`breaking` is collected, counted, printed — and never refused.** A program that passes pass 2 does **not necessarily** satisfy the K condition |
| **`N028`/`N029` key differently** | `namen.rs` | Map under the **short name**, lookup under the **full path**. `m::f()` never hits: `N029` stays silent, `N028` fires **wrongly** |
| **the pairing is global, not transitive** | `paarung.rs` | The head says "transitive set", the code unions over **all** functions of the tree. A `publishes` in module A pairs with an `awaits` in module B **without any call relation** |
| ~~**the address space is checked nowhere**~~ **— built 2026-08-24 (`R008`)** | `m3.rs` | Apart from `R001` there was **no** test on a space; a `ptr<normal, rw>` reached a `ptr<mmio, rw>` parameter with zero errors. *Now the space has to MATCH at the call site* — for arguments that are a bare parameter. **`code`, `boot`, `port` are still checked by nothing, and `Typ` loses `Raum` at type formation** |
| ~~**the pointer RIGHTS are checked nowhere either**~~ **— built 2026-09-02 (`R013`)** | `m3.rs` | `R008` read `z.raum` and stopped; **`z.rechte` sits in the same struct and no line compared it.** A `ptr<normal, r>` reached a `ptr<normal, rw>` parameter with zero errors, the emitter wrote `const Text *` into `Text *`, and `cc` said *discards `const` qualifier*. **Unlike the space, rights NARROW**: `rw` at an `r` parameter must stay silent. *Compared are `r`, `w`, `x`; `own` counts as read and write (the emitter's own answer), and whether OWNERSHIP may be handed over is still asked by nobody* |
| ~~**`M128` compares no parameter type and no result**~~ **— built 2026-09-02 (`M141`)** | `m1.rs` | `fnptr_passt` held arity, effects and cost and nothing else, so `&eng` with `eng(b : u8) -> u8` sat in a `fn(u32) -> u32` slot with **0 errors and `100 % coverage`** while `cc` refused the emitted `.f = &eng`. **A code of its own**: `M128` is a subsumption (*promise less, never more*), a signature is an EQUALITY — nothing converts at an indirect call. *The declared RANGE is still held by nobody there, and that half `cc` cannot see at all* |
| **`melden` is dead code** | `phasen.rs` | The switch that was to distinguish "a body without its own `advances` line does not report" is passed through six call sites and **never read** |
| **`O004` stays silent on an empty body** | `phasen.rs` | A function with `advances roh -> mmu` and an empty body gives **zero errors**. *"A stretch that stops on the way is no stretch" — one that never starts is mute* |
| ~~**recursive functions: no frame check**~~ **— fixed 2026-08-24** | `wirkungen.rs` | At the cycle, `E009` was set and it **returned before every `E008` check**; one unresolvable edge deep down devalued `E008` for the whole call chain. *The hull is a LOWER bound — everything in it really happens, so the check holds under incompleteness.* It now runs on; `E009` remains as the third state for **completeness**. Ten corpus sites were affected, probe 261 |
| ~~**`U005` falls wrongly**~~ **— fixed 2026-08-24, and it was WORSE** | `gruppe.rs` | The module path was empty: a rank as a **module constant** did not resolve at all, became `0`, and two locks with **different** ranks counted as equal. *A correct program fell — with a number that stands nowhere in its source.* `H014` stayed silent meanwhile, so the only report was the wrong one. Probe 262 (the first for `U005` at all) and test `ein_modulweiter_rang_loest_auf` |
| ~~**`by unvisited`/`by consuming`: no descent check**~~ **— half closed, 2026-08-24 (`S008`)** | `schleifen.rs` | `by consuming` must now name a `consumes` in its `touches`: *the promise that the domain shrinks needs a carrier.* **`by unvisited` needs nothing** — it visits every element of a finite domain at most once |

> **None of these nine finds was reported by a tool.** They came to notice because somebody
> had to write the sentence down and look up for it what the pass really does.
> *That is the achievement of this exercise, and it is greater than the list itself.*

### The `R008`/`R013` family got a third member on 2026-09-03, and it is NOT in the table

**Not in it because it was not found the same way** — the table is the record of one exercise,
and its closing sentence counts its own rows. This one a probe found.

`R008` read a pointer's SPACE and stopped at the rights; `R013` read the rights sitting in the
same struct; **`N030` read a bare binding and stopped at the FIELD** — which is the one
position a record holding two axes has. Caprock keeps the CPU view and the device view of one
DMA buffer in one record (`caprock-virtio/src/owned.rs`:70–77) and buys the guarantee with
field privacy; `opaque` is the stronger instrument and the pass did not reach it.

> **The shape of the family is worth naming:** in all three, the property was stated
> correctly and a pass read one position short of where it stood. *That is the cheapest class
> of defect this tree has* — no new word, no new identifier, and here **nothing newly refused
> over all 635 `.gab` files.** `N030` now walks `.f`/`->f` from the binding's declared record
> and reads the write into a field as well (`p.dev = c` is `retarget_device_view`'s own shape,
> `owned.rs`:127).

*Verified before it was repaired:* each of the five sites of `messung/proben/probe-opak-am-feld.gab`
was run in its OWN file, and the three that were silent were silent alone too — so it was the
rule's reach and not one refusal masking another. Booked at `dokumente/OFFEN.md` `O7` and
`messung/FUENFTE-MARKE.md` §3; probes `beispiele/gift/669` and `670`.

## The second tooth, and how it measures

```bash
./instrumente/pruefe-saetze.py [--je-satz] [--ohne-satz]
```

**Two directions, and the second is the sharper one:**

| | | |
|---|---|---|
| (a) | code in the checker, no sentence | the **ratchet** — mark **45**, it may fall, not rise |
| (b) | code in a sentence, not in the checker | **always red, without a mark** — a sentence about a rule that does not exist |

**Both directions are measured from outside, not only in the speech test** (R14/W17):

<!-- QUOTED RUN, in the tool's own language -- evidence, not prose. -->
<!-- Re-run 2026-09-01: the mark moved 45 -> 48 (`N047`/`N048`/`N049` from the register-layout
     audit stand without a theorem, on purpose -- they ESTABLISH the premise of
     `Device_Konstruktor.thy` rather than needing one). The transcript is re-taken rather than
     patched: a quoted run that nobody re-ran is prose with a monospace font. -->

```
Kennung "Z999" in kosten.rs eingefügt   -> RC 1, „49 Kennungen ohne Satz, gebucht sind 48"
Kennung "Z998" in einen Satz eingefügt  -> RC 1, „steht in einem Satz und wird von KEINER Datei vergeben"
sauberer Baum                           -> RC 0
```

> **The second probe found an error in the guardian itself on its first run**: the code survey
> read `saetze.rs` too, so the invented code turned up there again and counted as present.
> *A guardian that counts itself can never go red in this direction.* Fixed by the same
> exception `tests/` already had — **and the same error sat in `pruefe-kennungen.py`**, which
> after the register was set up reported 146 double assignments, of which none was one.
