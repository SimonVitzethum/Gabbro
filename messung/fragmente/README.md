# The completed fragment corpus

**These are the same ten fragments as in [`dokumente/FRAGMENTE.md`](../../dokumente/FRAGMENTE.md) — byte-identical, plus exactly the lines that make them programs.**

## Why this folder exists

K100's lowering obligation reads: *"the emitted C computes what the fragment says"* — **measured at execution.** Seven of the ten did not meet it, and on 2026-08-20 it was counted up why:

<!-- QUOTED RUN, in the tool's own language -- evidence, not prose. -->

```
41 Stellen nennen 20 Namen, die niemand deklariert
   (MAX_POLL · EP_BADGE · SYSNO_RESULT · Fehler · NTFN · IpcResult · …)
 9 `let … else` rufen Rümpfe, die diese Einheit nicht kennt
 6 Bitlagen sind unbenannt
 1 Tabelle nennt kein `tree`, 1 Gerufener kein `or <reason>`
```

**Each of the seven carried at least one corpus-side bolt.** F4 — the purest — needed exactly one line: `MAX_POLL`. Without it the `bounded` clause names nothing.

With that, the lowering column fell **by not a single point**, as long as `FRAGMENTE.md` stays untouched — and that file carries its freeze sentence: *"a report from 2026-08-14, and it stays untouched."*

> **An excerpt cannot be executed.** Closing the seven would mean changing a frozen file — that is not the discharge of an obligation, it is the moving of the yardstick.

## The rule of this folder

**Every file states in its head what was added — and what was not.** It is the same move as with «K2»: *reproduced, not translated, and expressly said so.* Whoever reads the figure sees beside it which part is measured and which is written.

Added are **only** declarations that the excerpt calls and does not name. Nothing is rewritten, nothing left out, no refusal defined away. **Where an error remains standing after completion, it belongs to Gabbro** — and that is precisely the yield.

## The state

<!-- QUOTED RUN of `zaehle-fragmente.py`, in the tool's own language. It is EVIDENCE:
     a translated transcript is no longer a transcript, and `pruefe-zahlen.py` reads two
     of these lines. Do not "fix" it into English -- it moves when the TOOL's output
     moves, and not before. -->

```
$ ./instrumente/zaehle-fragmente.py
9 von 10 prüfen sauber        (über den Ausschnitten: 5; am 2026-08-20 kurz 7;
                               ~~7~~ **6 seit dem 2026-08-31: `N041` nimmt `F05` heraus**,
                               und die 7 war ein falsches Grün — die Datei prüfte sauber,
                               emittierte 199 Zeilen C und wurde von `cc` zurückgewiesen)
9 von 10 senken ab            (über den Ausschnitten: 3)
9 von 10 sind DURCHGESTOCHEN  — F01, F02, F04, F05, F06, F07, F08, F09, F10
                               (F6 am 2026-08-31, am selben Tag an `N043` gefallen
                                und geheilt; F9, F1 und F5 am 2026-09-03)

**Und `F3` bleibt die eine, und zwar aus einem ENTSCHIEDENEN Grund** (Ordner, 2026-09-03).
Ein Durchstich fuer `F03` lag am 2026-09-03 vor -- emittiert, uebersetzt, GELAUFEN, gegen
eine Handschrift verglichen. **Er ist nicht angenommen worden, weil er die tragende
Anweisung des eingefrorenen Ausschnitts ausgetauscht hatte**: aus
`traverse cand over queue … by consuming` wurde `traverse i over elems of ….buf by
unvisited`, aus einem lokalen Sammler ein `static mut`, und **die Warteschlange wird nicht
mehr entleert** -- caprock entnimmt den gefundenen Empfaenger, diese Fassung laesst ihn
darin.

*Der Kern ist nicht die Ordnerregel, sondern was `H` misst.* `H` zaehlt Fragmente, die
Gabbro absetzen kann. Wird ein Fragment umgeschrieben, damit es absetzbar wird, zaehlt `H`,
was Gabbro **und der Umschreiber zusammen** koennen -- und der Umschreiber erreicht jede
Zahl. **`H = 1` mit benanntem Grund ist mehr wert als `H = 0` ueber einem zurechtgelegten
Gegenstand.**

Die Neufassung steht vollstaendig unter
[`../proben/probe-ipc-fastpath-durchgestochen.gab`](../proben/probe-ipc-fastpath-durchgestochen.gab),
mit der Gegenueberstellung in ihrem Kopf. Der Ertrag daraus ist unberuehrt: der Durchstich,
das Treiberprotokoll und der Erzeugerbefund unterwegs (`narrow` schrieb `>= 0` ueber ein
`u32`, was `-Werror=type-limits` abweist -- in `emit.rs` repariert).
```

**The fourth figure came in on 2026-08-25, and it is the one K100's first gate stands on.**
The paragraph below has always said *"one that lowers is not executed"* — and then did not
count the executed ones. But the lowering obligation reads literally *"the emitted C computes
what the fragment says"*, **measured at execution**; whoever stops at `lowers` stops exactly
short of the claim.

> **F02 is the first of the seven to have fallen** — without a line of construct, without a
> new template. Five `reserved` fields were missing; afterwards it emits 157 lines of C,
> compiles under `-Werror` at `-O0` and `-O2`, runs under UBSan and yields
> `4096 153 7 3 256 1 6 2 1 1 0 9`. **The completion is itself checked in the process:**
> `pruefe-emission.sh` cuts the frozen block and rejects the file if so much as one line of
> the excerpt is missing from it. *Adding is allowed, leaving out is not* — otherwise the
> completion would be a moving of the yardstick.

| | added | what still falls afterwards |
|---|---|---|
| **F1** | `reason Fehler`, `or Fehler` on `delete_leaf` | **`N029`** — `revoke` calls `delete_leaf` and does not catch the failure. *(2026-08-31, P-d: the form EXISTS and is measured — with `let … else` + `or Fehler` at the caller exactly **one** refusal remains, `K001` with **+80 256 ops** = one op per pass. That makes **TWO** frozen lines, :337 and the `costs` line :328 — so a rewrite. And the reason lies deeper: in the original `delete_leaf` is not fallible at all; «B29» at :268 is what makes it fallible. Both halves stand in the same report. See [`../DREI-FRAGMENTABSAGEN.md`](../DREI-FRAGMENTABSAGEN.md).)* |
| **F2** | five `reserved` fields | — *checks clean, lowers, compiles — and has been **punched through** since 2026-08-25*|
| **F3** | four constants, `or EpVoll` on `enqueue`, `lock SCHEDS` *(2026-08-25)* | 3× `M124`, `M101` option special value, `H011` `locks SCHEDS` never taken, **5× `N035`** — the contract on the `fn(…)` type, obligatory since 2026-08-21. *(2026-08-31, P-c: the three `M124` are a **correct refusal**. The template in `caprock-messbasis` carries `pub const ERR_… : u64` at this place, not an enumeration type — **zero projections in the whole tree** — and the two number spaces already diverge today: `ErrBadCap = 2` against `ERR_BADCAP = 1`. What is missing is four `const` lines, and those would stand in excerpt lines.)* |
| **F4** | `MAX_POLL`, `assume`, `on_exceeded` target | — *checks clean*; lowering at the `dma` barrier. **Re-checked 2026-08-25 and BOOKED, not built:** the three `C001` are `device Virtq(…) at dma` (:79) and two `let` in `publish` — and both `let` stand BEHIND the first refusal, the device does not lower in the first place. *The `at dma` refusal is the axiom layer itself* (which barrier a DMA access demands is a claim about the memory model; M3 expressly does not build it). **Narrowing it would mean guessing**, and a generator that guesses annuls every pass ahead of it |
| **F5** | nine constants, five `extern fn` with a channel, one `assume` | — *checks clean (re-measured 2026-08-31: 26 items, 0 errors).* ~~3× `M124` — a reason value stands as an ARGUMENT~~ **closed by the FOURTH DOOR** (2026-08-25): an argument may be a reason if the parameter declares exactly that `reason`. *This line stood six days longer than it was true.* **Measured out on 2026-08-31: F5 would be ONE addition away from lowering** — five `extern fn`, all called by the service body and named nowhere, give 31 items, 0 errors, 0 hints and 199 lines of C. *It does not stand there:* `cc -Werror` falls in three places, and the first is `exit`, a name C has taken and which the FROZEN excerpt calls (`ABSAGEFORMEN.md` U10, `TODO.md`). **CORRECTED on 2026-08-31: F5 does NOT check clean any more, and that is the first honest reading.** `N041` rejects `extern fn exit()` — 558 names C has taken, in three measured classes ([`../C-NAMEN.md`](../C-NAMEN.md)). *The file checked clean, emitted 199 lines of C and was rejected by the foreign compiler; now it falls at the line that causes it.* **And it is unreachable, not merely open:** `exit` stands nine times in the frozen block, the rename would be nine omissions, and C carries `void exit(int)` against an `exit()` without an argument ([`../F05-UNERREICHBAR.md`](../F05-UNERREICHBAR.md)) |
| **F6** | two constants, `IrqMarke`+`static irq`, two channels, one gate | — *checks clean*; ~~lowering at «B12» `elems of`~~ *(«B12» has been decided since 2026-08-20)*. **2026-08-25: 4 × `C001` down to 2.** What remains: three names in the `check` body that nobody declares — **corpus-side**, and no pass says so (finding 7) — and `lenof` outside a `format`, whose only corpus site lies exactly behind it (rule A). ~~**2026-08-31 PUNCHED THROUGH** — `lauf "fragment6"`, eighteen figures, `-O0`/`-O2`/UBSan; `H` falls from 5 to 4~~ **FALLEN AND HEALED THE SAME DAY:** `N043` saw `measures eich.leer, eich.voll, eich.tiefe, eich.gelaufen` and found no carrier `eich` — `gabbro emit` wrote no more C, the punch-through was GONE, `H` stood at 5 again. *The `lauf` line stood there unchanged; until then the counter had read exactly that and not the run.* **Healed with `type EichMarke` + `static eich`** — the same move as `IrqMarke`/`irq` in the same file, `H` = 4. **And one finding remains that no rule sees:** the `can_fail` body reports four quantities and *writes none of them* — `N021` sees the reverse case, `N022` a one-sided threshold, a report line without a writer nobody sees |
| **F7 F8 F10** | nothing | — *were programs already* |
| **F9** | two `reserved` fields | **`K001`** — the promise `costs <= 4096 ops` has been recomputably **false** since stage 3 (137 438 953 472). See the head of the file. *(2026-08-31, P-a: the figure is recomputed and **sharp**, `body × node length^levels`; and `F9` is not blocked by the CHECKER but **three times by the generator** — none of the three `C001` hangs on `K001`. [`../K001-DOMAENENSCHRANKE.md`](../K001-DOMAENENSCHRANKE.md).)* |

## The yield: three findings the frozen corpus could not show

**1. `A::B` parses and is never resolved.** `path = ident { "::" ident }` stands in the grammar; the name pass reads the **first syllable** and looks it up as a value. `IpcResult::Ok` falls as `M119`, no matter whether `IpcResult` is a `module`, a `reason` or a variant type — all three checked.

**2. ~~A `reason` value has no producer.~~ — SUPERSEDED on 2026-08-21, re-measured on 2026-08-25.** Since stage 7, `return R::F;` stands settled as one of three permitted positions; the producer is built. What falls today at the six sites in F1/F3/F5 is **`M124`** — the POSITION, not the production: a reason value may stand only as a `return`, as the subject of a `match` and in `==`/`!=`, and all six are arguments. *The open remainder is thereby smaller and more precisely named: a `reason` lacks the NUMBER PROJECTION although it declares its numbers.* The original wording stays beside it — it is the finding of 2026-08-20:

> **2. (2026-08-20) A `reason` value has no producer.** `primary` (`SYNTAX.md`:405) knows no production for it. **Every `-> T or R` signature in the corpus stands on an `extern fn`** — on a body Gabbro never sees. *Not a single Gabbro function ever produces a reason.*

> **The same shape as «B9» at `fnptr`:** a form one can declare and cannot construct. First the producer, then the contract.

**6. Added on 2026-08-25: «B9» is likewise superseded — ~~and it still stands as an open gap in `PFLICHTEN.md`~~ *(corrected the same day; the line now carries `N035`/`N036`/`N037`, and `H` fell from 11 to 10)*.**

<!-- widerruf:aus -->
Der Kommentar in F3 sagt, `fnptr` trage „kein `requires`, kein `ensures`, kein `effects`“. *Der Satz steht hier ZITIERT — deshalb der `widerruf:aus`-Block: `WB3` in [`../../instrumente/pruefe-widerruf.py`](../../instrumente/pruefe-widerruf.py) sucht seit dem 2026-08-25 genau diesen Wortlaut.* **Er bleibt DEUTSCH: er zitiert einen Quellkommentar, und ein übersetztes Zitat belegt nichts mehr.**
<!-- widerruf:an -->

Since 2026-08-21 it carries `effects` **and** `costs`, and as an OBLIGATION at that: `N035` rejects an `fn(…)` type without both, `N036` says which effect words carry through an indirect call, and `beispiele/49-dispatch-tabelle.gab` writes all four halves down in one program (`messung/FNPTR.md` carries the measurement). `requires`/`ensures` are **rejected with a measured justification** (`N037`) — not forgotten. Recomputed on 2026-08-25:

```
$ printf 'type T = { f : fn(u8), };' > /tmp/b9.gab && gabbro pruefe /tmp/b9.gab
Fehler: [N035] /tmp/b9.gab:1:16: `fn(#1)` declares no `effects` and no `costs`
```

> **And it is a CORRECTION, not a decrement by bookkeeping.** The work is from 2026-08-21; what fell today is an entry that had been wrong for four days. *Lowering a figure by rewording would be repotting — correcting a wrong entry is the opposite of it.*

> *The yield is double-edged here:* the same rule makes **five new errors** in F3, because the five `fn(…)` lines of the 2026-08-14 excerpt would have to carry a contract that did not exist then. **A frozen corpus can go stale under a new refusal** — and that is not a regression but the price of the yardstick not moving along.

**5. Added on 2026-08-20 (stage 3): the decided reading COST a fragment, and that is the
yield.** `mappings of` has since meant the **leaf set**, and F9's line `costs <= 4096 ops` —
justified in the excerpt with *"`levels` times `node` length"* — is thereby recomputably
false: the body costs **137 438 953 472**.

> **The error had stood in the file since the cut and was invisible as long as the pass
> carried the same wrong reading as the human who wrote the line.** Two registers over one
> thing, and both wrong (W7). *A figure falls from 7 to 6 — and what falls is a promise
> nobody keeps.*

**4. Added on 2026-08-20 (stage 2): «B11» is out of date, and the correction stands in the
head of F5.** `forever` does indeed have an exit — `leave <mark>` stands in the grammar
(`SYNTAX.md`:658), checks with 0 errors and lowers to `goto marke_ende;`. What is missing is
an exit that carries a **reason**; `leaves` means something else in Gabbro (the linear values
that leave the scope). *«B11» shrinks from "the service loop is not writable" to "its exit is
unnamed".*

> **The wording of the excerpt stays standing nonetheless**, and the correction stands beside
> it with a date. An excerpt from 2026-08-14 is a report from that day — overwriting it would
> mean moving the yardstick instead of discharging the obligation.

**3. ~~And one line I added myself does not lower:~~ — CLOSED on 2026-08-25.** `static irq : IrqMarke = IrqMarke(…)` in F6 — a `static` of a record with an ordinary initial value. *That stood here instead of leaving the line out; today it lowers.*

> **Re-measured 2026-08-25: the refusal is WIDER than its reason.** `emit.rs`:1275-1281 refuses for every `static` whose type is a `tagged` or a record — but the text names the case "initialised with an ordinary number" (`= 0`) and justifies it by the declaration not saying **which variant the zero is**. Here it does say so: `IrqMarke(tiefe_max: 0, n: 1)` is the tagged call, hence exactly the form for which the template `S19 verbund.konstruktor` (**proved**) exists. *A rule whose scope and whose justification come apart* — the same shape this folder has already found four times.

> **Narrowed the same day, and `L` does not move in the process.** In the `static`, the tagged
> call becomes a braced initialiser with named designators —
> `static IrqMarke irq = { .tiefe_max = 0, .n = 1 };` — and not the compound literal that
> `emit::ruf` writes at an expression site: a `(P){…}` has static storage duration but is
> **not a constant expression**, and C11 6.7.9p4 demands one at this place. *Two positions,
> one template, two C forms* — the distinction stands in `verbundmarken` and not in the head.
>
> **What does NOT belong to it:** a `tagged` keeps its refusal. Which variant the zero is, the
> declaration still does not say, and a tagged call can name none. *The reason is unchanged
> and right; only its scope was not.*

**And what still falls at F6 afterwards — three refusals became two, and the second is rule A:**

| Line | before | today |
|---|---|---|
| `:54` `static mut irq` | `C001` | **lowers** (above) |
| `:134` `art : Stackart` | `C001 parameter type` | **lowers** — a `reason` IS a C type, `ItemArt::Reason` has always written its `typedef enum`; `ctyp` just did not know the name |
| `:142` `let benutzt = s.len - frei` | `C001 let without a resolvable type` | **lowers** — `frei` comes from `unberuehrt(s) -> u64`, and the type stood in the signature |
| `:155` `let f = eichfeld()` | `C001` | **open, corpus-side**: nobody declares `eichfeld`, `muster_schreiben` and `beruehre` — see finding 7 |
| `:160` `lenof(f.worte)` | `C001` | **open, rule A**: the refusal is justified by `sizeof(T)` and the layering; `lenof` of a declared `[u64; N]` is the declared FIGURE and has nothing to do with the layering. *The same shape as above — but the ONLY corpus site for it is this line, and it is locked behind the bolt above it. No construct without a program that needed it.*

**7. Added on 2026-08-25: a `check … can_fail` is NOT entered by the name, effect and cost passes — and F6 checks clean partly because of it.**

Measured against a purpose-built probe, both halves:

```
$ gabbro pruefe <check-Block mit `let x = gibtesnicht();`>
… 4 Items, 0 Fehler, 0 Hinweise

$ gabbro pruefe <derselbe Ruf in einem `impl fn`>
Hinweis: [E009] … the call effects of `t` are undecidable: `gibtesnicht` is unknown to the graph
Fehler:  [K003] … `t` promises costs, but `gibtesnicht` is not declared here
```

> **The same call, two answers** — and the quieter one stands in the block whose whole purpose
> is measuring. In F6 it is three names (`eichfeld`, `muster_schreiben`, `beruehre`), and
> **the only pass that notices them at all is the generator** (`C001`). *The line "6 von 10
> prüfen sauber" thereby carries less at this point than it reads.* Not built: a pass that
> enters the `can_fail` body costs its refusal code, its sentence and its poison probe — and
> it would lower a figure nobody asked it to.
