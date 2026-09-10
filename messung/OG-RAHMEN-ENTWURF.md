# OG frame draft: sequential contracts under interleaving (og_halbA sketch)

Status: DRAFT, not a theorem. Main tree, 2026-09-10. No implementation.
No number here is measured; every shape below cites its source file and line.

Goal: name the missing Owicki-Gries half step (`ZIEL-BEWERTUNG-2026-09-10.md`
section 2 item 2) as a sketch with checkable premises, so a later lane can
either build it or refute it. The claim to close is: per-body frames plus
pairwise disjoint frames imply sequential contracts survive interleaving.

## 1. Goal sentence (og_halbA, sketch)

If two bodies `f` and `g` each satisfy their sequential contract in isolation
(frame: each writes only what its own contract names), and their write frames
are pairwise disjoint (with the lock-shared, pairing, and atomic exemptions
of section 3), then every restricted interleaving of `f` and `g` preserves
each body’s sequential pre and post conditions at each of its own program
points.

The joint model is the declared pair set: only declared pairs share a run
(closed world, `nur_deklariert_teilt_lauf`, `Wettlauf.lean:540`).

## 2. Premise shapes (as they stand in the tree)

| item | shape | source |
|---|---|---|
| frame predicate | `Rahmen W G s s'` holds iff slots agree wherever `W` is false and globals agree wherever `G` is false | Satz.lean:193 |
| per-body frame | `exec_rahmen P O passes fuel hO b s r hh s'` : from `HeldGenau L s.haelt`, an output world `s'` of `exec` under contract `V` satisfies `Rahmen V.schreibt V.gschreibt s s'`; sole premise is `GutO O` | Satz.lean:1323 |
| full per-body good | `exec_gut` gives frame AND trace (`Gut = Rahmen + Brav`); og_halbA needs only the frame half | Satz.lean:1317, Satz.lean:303 |
| call fits | `RufPasst V S L` has four fields: hw (callee table writes imply caller writes), hg (same for globals), hk (consumed marks are a submultiset of `L`), hh (held locks in `L` iff in `S.haelt`, exact in both directions) | Syntax.lean:254 |
| held exact | `HeldGenau L h` : static held set equals dynamic held list; entry assumption of every per-body frame proof | Satz.lean:216 |
| foreign bodies | `GutR R` : each foreign body keeps the frame of its own writes; `GutO O` : hardware keeps its declared effects box and leaves locks and trace unchanged | Satz.lean:790, Satz.lean:794 |
| frame widen | `Rahmen.weiter` : a narrower contract keeps the wider frame; used to lift a callee frame into its caller via hw and hg | Satz.lean:206 |
| restricted run | `IstVerschraenkung` (observed trace is a suffix of each full trace) plus `BeschraenkteVerschraenkung Nb` (steps of distinct threads stand in the declared relation `Nb`) | Wettlauf.lean:482, Wettlauf.lean:527 |

## 3. Sketch (four steps, none built)

1. Per-body instances. Apply `exec_rahmen` to each body: `f` keeps
   `Rahmen Vf.schreibt Vf.gschreibt`, `g` keeps
   `Rahmen Vg.schreibt Vg.gschreibt`. The `RufPasst` hw and hg fields are what
   let a nested call frame lift into its caller via `Rahmen.weiter`, so the
   top-level frame already covers transitive callees.
2. Pairwise disjointness (checker side, from transitive effect hulls,
   `NEBENLAEUFIGKEIT-ENTWURF.md` section 2): writes of hull `f` and writes of
   hull `g` are disjoint as sets, for tables and for globals, except: shared
   writes under a common lock `L` in both hulls (order edge `gibt L` before
   `nimmt L`), `publishes` and `awaits` payload pairs (order via pairing,
   already checked), and `atomic` globals (machine orders, A10). Unshared
   carriers or rows written from two declared-concurrent bodies mean refuse.
3. Stability lemma (the unbuilt core). A step of `g` preserves every carrier
   that `f` relies on: by disjointness, what `g` may write is outside what
   `f` reads or writes, so `Rahmen` equality on `f`’s carriers survives. Form:
   `Rahmen` of `g` plus disjoint frames implies the pre state of `f`’s next
   step agrees with its post state of its last step on `f`’s frame.
4. Induction over the restricted interleaving. Walk the interleaving
   (`IstVerschraenkung` restricted by `BeschraenkteVerschraenkung Nb`); at each
   own step apply the sequential contract, at each foreign step apply the
   stability lemma. Closed world (`nur_deklariert_teilt_lauf`) confines the
   induction to declared pairs, so undeclared overlap never enters the case
   split.

## 4. Why W3-W5 cannot close it

W1 and W2 come from the bodies (`lauf_aus_brav`: consistency and good events
inherited over suffixes). W3-W5 are premises about the relation of the
threads to each other, and no sentence about one body at a time can close
them (`Wettlauf.lean:467`). More importantly, even granted as assumptions,
they prove the wrong sentence:

| premise | what it says | why it does not give stability |
|---|---|---|
| W3 exclusion | whoever takes `L` takes it while no other thread holds it (promise of the foreign lock primitive) | gives the sync order edge, says nothing about write sets; two bodies can exclude correctly and still overwrite each other’s carriers |
| W4 one thread per mark | no instruction passes a mark across threads, so two accesses guarded by the same mark are same-thread | covers mark-guarded access only, says nothing about table or global write disjointness, which is what og_halbA quantifies over |
| W5 unshared carrier in one thread | a carrier declared unshared is reached by one thread only | concludes same-thread for the unshared case; shared carriers, the case where interference is possible, are explicitly outside it |

Jointly, W1-W5 yield `kein_wettlauf`: guarded accesses of distinct threads
are happens-before ordered (program order plus `gibt L` before `nimmt L`), or
the global is atomic. That is an order statement. og_halbA is a stability
statement: assertions and frames preserved under foreign steps. Ordered writes
are still writes; without disjointness a foreign write between an assertion
and its use breaks the sequential proof while respecting happens-before. Race
freedom and logic preservation are therefore two unconnected sentences, and
`exec_rahmen` is the candidate premise for the second, not a consequence of
the first.

## 5. Open obligations (what would refute or complete this draft)

- The joint model of the declared pair set stands nowhere (`Wettlauf.lean`
  section 6 note); without it the induction in step 4 has no subject.
- The stability lemma (step 3) is unbuilt; its exact relied-on set (footprint
  vs full contract frame) is unknown.
- Lock-shared writes need a held-set analysis that the checker lacks
  (`NEBENLAEUFIGKEIT-ENTWURF.md` section 6 item 1).
- Guest bodies with unknown writes and same-table distinct-row writes are
  undecided (items 2 and 4 of the same list).
- Row-level disjointness for thread tables needs an index analysis the
  checker lacks; interim rule is refuse on same-table writes unless
  lock-shared.

## 6. How to kill this draft

Take the falsifier pair from `NEBENLAEUFIGKEIT-ENTWURF.md` section 5 (two
bodies writing one table, declared concurrent, must refuse; disjoint write
sets with shared read, must pass). If the stability lemma cannot separate
those two cases — if the passing pair needs a shared carrier the disjointness
check forbids, or the failing pair passes under some exemption — the sketch
is wrong in step 2, not merely unbuilt.
