# GabbroV §8 — which obligations fall in theories with a usable certificate path

*Measured 2026-09-09 from tree `1af516a`. `AUFTRAG-GABBROV.md` §8 asks for
a number, not a build: the share of the sayable obligations that fall in
theories with a usable certificate path. That share decides G2, and G2
decides between two unpleasant routes — Z3 in the trust base or weaker
automation. The decision is not an agent's; the number is.*

## The answer, with its derivation command

```
python3 messung/gabbrov/cert-theorien.py
```

| | |
|---|---|
| sayable obligations (66 L minus 10 `notSayable` minus rebooked L66) | 55 |
| of those, in QF_LIA/QF_BV shape — quantifier-free boolean/integer arithmetic over fixed places | **26** |
| of those, needing quantifiers, folds or reachability | 29 |

**26 of 55.** The criterion is §8's own sentence: for bitvectors there is
a usable path, for quantifiers and arrays practically none. A row counts
as QF only if none of the other three fire; `cdtWf` and helpers such as
`antwortpflichtPaarig` are expanded one level, so a row that quantifies
through a helper is not booked QF.

| class | rows |
|---|---|
| QF (26) | L10 L18 L19 L20 L21 L22 L26 L28 L30 L31 L32 L35 L36 L37 L38 L39 L44 L45 L47 L48 L51 L53 L55 L58 L63 L65 |
| QUANT (27, five of them also REACH, one also FOLD) | L01 L02 L03 L04 L05 L06 L07 L08 L09 L14 L15 L16 L17 L23 L25 L27 L33 L40 L41 L43 L49 L56 L59 L60 L61 L62 L64 |
| REACH (5) | L04 L05 L09 L15 L16 |
| FOLD (3) | L03 (`countD`), L29 L54 (`firstD`) |

## What the number does and does not say

**QF shape is necessary for a certificate, not sufficient.** A
quantifier-free goal can still resist proof, and "usable path" differs
between QF_BV and QF_LIA. So 26 of 55 is the **ceiling** for route C
(Z3 searches, Lean recomputes), not its yield: at most 26 obligations
could ever carry a recomputed certificate, and every one of the other 29
ends undecided under C unless the fragment or the solver side moves.

**Two of the 26 are degenerate.** L44 and L53 are tautologies
(`messung/GABBROV-V2.md` §2.5): their postcondition follows from the
precondition alone. They are in QF shape and would certify — while saying
nothing about any program.

**The shape of the 29 is not one gap.** 24 quantify over a table domain
(the commonest form among the 66 — `allD` over `slots of T`); 5 need
bounded reachability, whose unrolling is finite but not tractable at the
corpus bounds (`OFFEN.md` `O6`: answers at 21, silence at 20); 3 need
folds that are not yet fragment constructs. A certificate story for the
second and third classes is different work from the first.

## Gate 7 — reached, and this is where the mandate says to stop

| §8 asks for | |
|---|---|
| the share in theories with a usable certificate path | **26 of 55**, QF shape, ceiling not yield |
| derived by a command, not subtracted | `python3 messung/gabbrov/cert-theorien.py` |

**Reporting and stopping here**, as §9 and §8 both require. Route C
covers at most the QF half; whether that half is worth the
certificate-checking build (V3) is the owner's decision.
