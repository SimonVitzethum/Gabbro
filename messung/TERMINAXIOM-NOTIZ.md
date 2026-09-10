# Termination and axiom note

Measured on branch lane-20 at base 291c27b. This note records termination
per loop construct and the current axiom inventory. Every number names
the command or file that reproduces it. No new mechanism is built here.

## 1. Termination per construct

| construct | measure that carries it | checker rule | theorem in Passlogik Terminierung | status |
|---|---|---|---|---|
| traverse by unvisited | count of unvisited domain elements | domain bound is K003 business | unvisited_endet | proved, ends by construction |
| traverse by decreasing e | named measure e | S005, name is written by body | decreasing_endet, s005_ist_nicht_hinreichend | necessary, not sufficient |
| traverse by consuming | count of unconsumed witnesses | S008, touches names a consumes | consuming_endet, s008_ist_nicht_hinreichend | necessary, not sufficient |
| retry bounded N ops | remaining operation budget | K006 holds upper bound C body ≤ N | retry_endet, retry_ohne_kosten_endet_nicht | ends only if a pass costs at least one op, see Finding 3 |
| forever per_pass bounded N ops | per-pass cost only, no total | K003, per_pass not costs | forever_laeuft_ewig, forever_traegt_kein_mass | proved non-terminating as a whole, total per pass |
| recursion | decreases term | K008 at definition, K009 at call sites | induction over decreases in Body | necessary, not sufficient |

### 1.1 Forever is total per pass and proved endless as a whole

A `forever` loop carries `per_pass bounded N ops` with a named
`on_exceeded` arm. Each pass stays under N. That bound is total per
pass and is the only total claim the construct makes. The loop itself
has no total measure, and that is permitted by the language rule:
infinite is one of the forms. The theorem `forever_laeuft_ewig` exhibits
an infinite run in which every pass meets its bound, and
`forever_traegt_kein_mass` records that the form carries no descent
measure. The cost pass refuses a `costs` promise on a `forever` body
for the same reason: its promise is `per_pass`, not `costs`.

### 1.2 Traverse variants are necessary, not sufficient

S005 checks that a `by decreasing e` measure names the traversal
variable or a name the body writes. It does not check that the measure
falls, and the pass register says so in its own sentence. The theorem
`s005_ist_nicht_hinreichend` makes the gap a run: a loop that writes
the measure on every pass at constant value 7 satisfies the checked
predicate on every step and never satisfies the falling predicate.

S008 has the same shape. It requires that a `by consuming` traversal
names a `consumes` in its `touches` list, which is a statement about
the text. The theorem `s008_ist_nicht_hinreichend` makes the gap a run:
a state with witness count 3 and the flag set satisfies the checked
predicate on every step while the witness count never falls. That a
pass really shrinks on every pass stays the prover business in both
cases. The proved direction is conditional: under real shrinking,
`decreasing_endet` and `consuming_endet` close the run by the core
lemma `schleife_endet`, which is `kein_unendlicher_abstieg` applied
to runs.

### 1.3 Retry zero-cost hole, Finding 3

`retry` ends through `bounded`: each pass spends its cost, and on
exhaustion the loop leaves through `on_exceeded`. The theorem
`retry_endet` needs a positive hypothesis, namely that each pass costs
at least one operation. Without it the budget never falls and
`on_exceeded` never fires. The theorem `retry_ohne_kosten_endet_nicht`
exhibits the constant run at cost zero.

The specification states no lower bound. K006 holds the upper side
against the body and nothing holds the lower side, while the language
reference states that branch, match, return and leave cost nothing.
A body built only from zero-cost forms therefore meets the upper bound
and never consumes budget. This is Finding 3 of the pass logic: either
the specification states that a retry pass costs at least one
operation, or the table row that says retry ends through `bounded`
must be withdrawn. The decision is open and is recorded here, not made
here.

### 1.4 Recursion decreases

Recursion is the second source of non-termination beside loops. K008
requires that a function which reaches itself carries a `decreases`
term, and K009 requires that each recursive call site moves a named
size. Both check the necessary condition, namely that the measure names
a size the recursive call changes. That it falls stays the prover
business, exactly as at S005 and S008. The program logic wires direct
self-recursion by induction over the `decreases` term, and mutual
cycles by the same induction over the cycle measure.

## 2. Axiom inventory

| class | count | guardian |
|---|---|---|
| falsifiable assumptions, probe named by falsifier | 39 | pruefe-sondendeckung.py, share Ap |
| unfalsifiable clauses under written criteria | 6 | pruefe-unfalsifizierbar.py, population ratchet down |
| admitted | 1 | pruefe-unfalsifizierbar.py, admitted ratchet down, ipi_kommt_an under U2 |
| total declared | 46 | gabbro annahmen over beispiele plus checker generated entries |

Reproduce with:

```bash
./target/release/gabbro annahmen beispiele/*.gab
./instrumente/pruefe-sondendeckung.py
./instrumente/pruefe-unfalsifizierbar.py
```

The early census found 27 named probes with 0 standing as a runnable
program. That booking was correct in kind and too small in count. The
current quota counts programs that stand in `sonden/`: 6 of 39 meet it,
so 33 of 39 remain falsifiable with the probe missing. A name without a
program is a promise of refutability with no instrument behind it.

### 2.1 Probe classes P1 to P3

| class | what a probe would need | of falsifiable |
|---|---|---|
| P1 | ring 0, control register, page table, MSR, port IO | 14 |
| P2 | a device, VT-d, virtio, UART, timer, counter | 16 |
| P3 | a mechanism the generator does not emit, grace period, fetching reader, ending source | 4 |

A fourth class, P4, holds probes that need nothing but a C compiler on
the bench. All open P4 work is written, so the quota floor of one in
eight is met with earned share and cannot be met again by another
userland probe. The classification per name is an estimate carried by
`sonden/README.md`; the counts above are read from it.

### 2.2 Rebooking order

| order | move | reason |
|---|---|---|
| 1 | rebook release_stellt_sichtbarkeit_her from unfalsifiable to falsifier sonde_release_sichtbarkeit | the refusal reason is rejected under R1, the program already stands in sonden with a positive control, the change costs no probe and closes one orphan program |
| 2 | P3 before P1 and P2 | P3 needs an owner decision or a bound at the loop, no new apparatus, while P1 needs ring 0 and P2 needs a device bench |

The first move is free and independent of apparatus. The second move
orders the remaining work by apparatus cost: mechanism rows first,
privilege and device rows after. A refusal moves a row from
unfalsifiable to falsifiable and unprobed, which is the more expensive
place to stand, not the cheaper one.
