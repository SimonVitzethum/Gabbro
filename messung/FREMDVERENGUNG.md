# A foreign body's promise is a fact inside the checker — and it decides

> **Measured on 2026-08-21.** The subject is not whether an `ensures` line on a body-less
> `extern fn` *stands there*, but whether it **moves anything** at the caller. Those are two
> different figures, and until today only the first stood anywhere.

## The command

```
./instrumente/zaehle-fremdverengung.py                 -- the figure for the whole corpus
./instrumente/zaehle-fremdverengung.py --stellen       -- every site with file, line and clause
./instrumente/zaehle-fremdverengung.py --sprechprobe   -- only the speech test, in both directions
gabbro zeugnis <datei.gab>                 -- the same figure per file, section F
```

All of it belongs on `ki-pc-fisch-101` (`cargo run`, `CLAUDE.md`).

## The figure

<!-- QUOTED RUN, in the tool's own language -- evidence, not prose. -->

```
== 1 wirksame Fremdverengungen aus 10 ausgesprochenen Verträgen, 57 von 61 Dateien mit Zeugnis ==
   109 fremde Rümpfe insgesamt; 4 Dateien tragen Fehler und haben kein Zeugnis.
```

| | |
|---|---|
| **109** | foreign bodies in the corpus (`beispiele/*.gab` + `messung/*/*.gab`) |
| **12** | of those **state their duty** — `ensures` or `maintains` on a declaration without a body |
| **1** | of those **really narrows** something at the caller |

The one site:

```
F  FOREIGN CONTRACTS THAT NARROWED -- a foreign `ensures` became a FACT here
     127:   abarbeiten -> naechste_menge           range     result >= 1
            u32 in 0 .. 4096  ->  u32 in 1 .. 4096
```

## Why the other nine move nothing — and that is the yield of the measurement

**Six of ten do not name `result` at all.** `beispiele/22-bootstrecke.gab` says
`ensures mmu_an_zahl == 1`, that is, a claim about the **world state**. Out of a foreign
`ensures` the checker reads only `result <op> <number>` and `result <op> <place>`; everything
else is left lying (W10, and it stands as such in the module head).

**Two more name `result` and still move nothing** — because the bound already stands there.
The third line stands beside them for comparison:

| File | Clause | Result type | moves |
|---|---|---|---|
| `beispiele/41-handschlag.gab`:101 | `result >= 1` | `Laenge = u32 in 1 .. 4096` | nothing |
| `beispiele/06-annahmen.gab`:115 | `result >= 1` | `Stapelgroesse = u64 in 1 .. 1048576` | nothing |
| `beispiele/39-auftragsdienst.gab`:115 | `result >= 1` | `Rest = u32 in 0 .. 4096` | **`0 ..` → `1 ..`** |

> Three lines, word for word the same, on the same construction — and **one of them is trust
> surface with an effect, two are ornament.** Precisely for that reason the certificate counts
> the *effective* narrowing and not the present clause.

**And the fourth `result` clause is dead without anything being missing from it:**
`beispiele/22-bootstrecke.gab`:72
declares `melde_roh(...) -> u32 ensures result <= 4096` — the form that *would* narrow. The
function is called nowhere in the unit. *A narrowing without a call site is none.*

## Half (a): the surface is already carried — checked, not assumed

Hand probe on a real corpus file, `beispiele/22-bootstrecke.gab` — the file with the most
stated foreign duties in the corpus:

```
$ gabbro zeugnis beispiele/22-bootstrecke.gab
E  FOREIGN -- the generator writes the prototype, somebody else the body

     The bodies this unit does NOT write, and the contract
     the checker uses to reason about them:
       melde_roh                  effects { reads text }, mit `costs`, ensures (1)
       mmu_an                     effects { consumes p, writes mmu_an_zahl }, mit `costs`, ensures (1)
       …
     0 assumptions, 0 templates (0 of them UNPROVED), 4 direct forms,
     7 foreign bodies (7 state their duty), 0 narrowings from foreign contracts

$ gabbro pflichten beispiele/22-bootstrecke.gab
F  Foreign duty (7)
     melde_roh :: ensures #1
     …
== 7 obligations: 0 preservation, 0 postcondition, 7 foreign, 0 precondition ==
```

**So the surface really does stand there already**, in two places and by name: `zeugnis`
section E (what the checker believes) and `pflichten` class `F` (what a human owes).
*(a) was a booking and not a gap.* New is only the last figure of the finding line — and it
stands there because a surface and an effect are two different things.

## What this figure does NOT say

* **It is a LOWER bound on the surface.** Counted are only units out of which a certificate
  arises, and that arises only without errors. Four fragment files (`F01`, `F03`,
  `F05`, `F09`) carry errors today and are not measured; the 222 poison files are refused by
  construction and are not looked at in the first place.
* **In the other direction it is an UPPER bound on the facts USED.** What is booked is that a
  fact *arose* — not that any refusal later rests on it. For the relational half
  (`ensures result <= s.len`, `Fakt::Beziehung`) that holds especially: a relation nobody
  reads counts here nonetheless.
* **It says nothing about whether the promise is true.** It says that Gabbro believes it. A
  foreign body that promises `result >= 1` and delivers `0` makes the narrowing wrong —
  and this translation says nothing about that. *Whoever cannot check, exports.*
* **It says nothing about `impl fn`.** The same narrowing on a body Gabbro sees is a
  derivation Gabbro will one day recompute itself. It deliberately does not stand in this
  figure — otherwise the trust surface would be too large instead of too small.

## `M115` — the counter-direction, and why it is NOT the same class

`m1::requires_pruefen` reads the `requires` of the **foreign** callee and refuses at the call
site (`M115`) where the range of the argument excludes the precondition. There too a foreign
contract decides about the acceptance of a program. It still does not stand in section F:

| | `ensures` → narrowing | `requires` → `M115` |
|---|---|---|
| Direction | the checker believes **more** | the checker believes **less** |
| Consequence of an error | a wrong program passes | a right program is refused |
| Effect in the product | yes — a narrower range passes checks a wider one does not | no — no code arises, a refusal arises |

> **A wrong precondition on a foreign declaration can refuse a right program; it cannot let a
> wrong one through.** That is why it is ceremony and not a trust item. The sentence stands in
> the certificate too, under section F — so that the decision can be read up where somebody
> looks for it.

The *set* of open preconditions at the call site is already counted, in the right place:
`gabbro pflichten` carries them as `V` (`pflichten::Art::Vorbedingung`), with both of their
bounds beside them.

## Why it is ONE reader and not two

`crates/gabbro-check/src/fremdverengung.rs` answers the question *"does this `ensures` clause
narrow, and how?"* exactly once: `bereich_aus_ensures` yields the narrowed type **and** the
steps that led there. M1 takes the type and computes on with it, the certificate takes the
steps and prints them out.

> A certificate that searched the tree once more for `ensures` clauses would have been the
> second reader — and **precisely this construction lost a fact on 2026-08-20 that had two
> readers and of which only one read** (`verbundwert`, a `let` type that became `c->len`).
> That is why `zeugnis::zeige` gets the source text and the list of the **pass** since today,
> instead of a second reading of its own.

## The speech tests that can go red

| Where | What falls |
|---|---|
| `tests/beispiele.rs::eine_fremdverengung_steht_mit_namen_im_zeugnis` | the site disappears from the certificate |
| `tests/beispiele.rs::eine_klausel_ohne_wirkung_steht_nicht_unter_f` | a clause without an effect is counted |
| `tests/beispiele.rs::ein_eigener_rumpf_zaehlt_nicht_als_fremdverengung` | an `impl fn` lands in the trust surface |
| `tests/beispiele.rs::auch_die_relationale_nachbedingung_wird_gebucht` | the relational half drops out of the booking |
| `./instrumente/zaehle-fremdverengung.py --sprechprobe` | both directions on two units that differ in **one character** |

**And the counter itself can go red — measured, not asserted.** With the mutation
`fremdverengung-zaehlt-jede-klausel` in the checker:

<!-- QUOTED RUN, in the tool's own language -- evidence, not prose. -->

```
== Sprechprobe, in beide Richtungen ==
  verengende Klausel  (u32 in 0 .. 4096):  1  ok
  bindende Klausel ohne Wirkung (1 .. 4096): 1  GESCHEITERT -- erwartet 0
RC mit Mutation = 1        RC ohne Mutation = 0
```

And four mutations in `mutiere-pruefer.py`, all four **caught** (run individually on
`ki-pc-fisch-101`, 2026-08-21):

```
gefangen   fremdverengung-zaehlt-jede-klausel
gefangen   fremdverengung-ueberspringt-die-ruempfe-ohne-rumpf
gefangen   fremdverengung-vergisst-die-beziehung
gefangen   zeugnis-druckt-abschnitt-f-nicht
```

## Divergences from the bookkeeping, recomputed

The TODO item names **89 foreign bodies, 10 with `ensures`, "and M1 narrows out of every
one"**. Re-measured on 2026-08-21:

| booked | measured | Command |
|---|---|---|
| 89 foreign bodies | **80** in `beispiele/`, **109** over the whole `.gab` corpus | `./instrumente/zaehle-fremdverengung.py` |
| 10 with `ensures` | **10** — confirmed | `./instrumente/zaehle-fremdverengung.py` |
| "M1 narrows out of every one" | **1 of 10** | `./instrumente/zaehle-fremdverengung.py --stellen` |

*The third divergence is the one that matters.* It was not countable as long as no figure was
carried about the *effect* — and precisely that is why the item got a counter of its own
instead of a line in the assumption surface.
