# SYNTAX section draft: the general interference model (design only)

Status: DESIGN ONLY, no implementation. Worktree lane-34, base 2657f77,
2026-09-10. Companion to `grammatik/Grammatik/InterferenzAllgemein.lean`,
which owns the Lean shapes; this note owns the prose that `dokumente/SYNTAX.md`
will carry. Do NOT edit `SYNTAX.md` itself from this lane; a later lane moves
the text and proves against it.

## 1. Where the text goes

Two landing spots, both already shaped for it:

- §11 table, `concurrent { f, g }` row: today it reads "`Nebeneinander`
  premise in `Wettlauf.lean`". The general model keeps that cell and appends
  the second sentence drafted in section 2 below.
- §16.1 theorem list: after `kein_wettlauf`, a new row for `AllgemeinStabil`
  (statement SHAPE, explicitly not a theorem yet); §16.2 item 1 gains the
  booked cuts G1–G7 from section 4 below.

## 2. Draft prose for the §11 `concurrent` row

> `concurrent { f, g, … }` — the declared-concurrent bodies («SG-23»): pairwise
> non-interference over the transitive hulls — shared writes fall (`W001`),
> undeclared overlapping roots fall (`W002`), incomplete hulls refuse (`W003`).
> The joint run of N declared bodies is `GemeinsamerLauf`
> (`InterferenzAllgemein.lean`): one world chain, each step in its own body's
> frame (`exec_rahmen` per body), every pair declared, the run well-behaved
> (`Gesittet`) and restricted (`BeschraenkteVerschraenkung`). Lock-shared
> carriers are INCLUDED, not refused: each carrier carries an invariant
> predicate (`TraegerInv.inv`), every writer holds the carrier's guards
> (touch-only-while-holding, `TraegerInv.disziplin`), and any carrier written
> by two threads is shared and guarded by a lock both hold
> (`GeteiltGedeckt` over `GemeinsameSperre`). The main statement,
> `AllgemeinStabil`, has the SHAPE `context → coverage → per-thread frame
> dependence → per-thread entry validity → every assertion at the last world`
> — as a `def … : Prop`, not a theorem. Proofs are a later phase.

Lean cell for the same row: `GemeinsamerLauf`, `TraegerInv`,
`GeteiltGedeckt`, `AllgemeinStabil` (`InterferenzAllgemein.lean`); frame
premise per step `exec_rahmen` (`Satz.lean`), entry shape `RufPasst.hh` in
both directions (`EintrittPasst`), owed-invariant shape U003
(`SchuldnerHaelt` over `schuldet`), invariant-view shape
(`InvSichtHaelt` over `heldIn_invarianten`).

## 3. Defined names (all in `InterferenzAllgemein.lean`, all `def`/`structure`)

| name | kind | shape |
|---|---|---|
| `TraegerSchreibt` | def | per-carrier write switch of one body (`D.schreibt` / `D.gschreibt`) |
| `WaechterGehalten` | def | carrier guards held in the signature's entry resources (`darf` shape, static) |
| `Geteilt` | def | shared flag per carrier (`D.geteilt` / `D.ggeteilt`) |
| `GemeinsameSperre` | def | a lock both bodies declare, standing in the carrier's guard list |
| `TraegerInv` | structure | per-carrier predicate `inv` + touch-only-while-holding `disziplin` |
| `EintrittPasst` | def | entry holds exactly the declared locks (`RufPasst.hh` shape, both directions) |
| `SchuldnerHaelt` | def | owed invariant ⇒ locks of ALL its carriers held (U003 shape over `schuldet`) |
| `InvSichtHaelt` | def | invariant view read under held locks (`heldIn_invarianten` shape at entry) |
| `GemeinsamerLauf` | structure | N threads, entry worlds, world chain + step-thread list, `Lauf D`, closed-world pair premise, `Gesittet`, `BeschraenkteVerschraenkung`, entry/owed/view premises |
| `InvariantenKontext` | def | every carrier predicate at every chain world |
| `GeteiltGedeckt` | def | a carrier written by two threads is shared AND under a common lock |
| `StabilSchritt` | def | `stabil` as a `Prop` shape: foreign step in a disjoint frame preserves `Q` |
| `StabilKette` | def | the shape folded over the chain |
| `AllgemeinStabil` | def | MAIN STATEMENT SHAPE (`def … : Prop`, see section 2) |

No `theorem`/`lemma`/`example` commands anywhere in the file; no
`sorry`/`admit`/`axiom`; no proof terms at all (nothing needed them); no
mathlib.

## 4. Cuts booked (mirrors the file header G1–G7)

- G1: `AllgemeinStabil` is a shape, not a theorem; the induction folding
  `StabilSchritt` over the chain is future work, owned by the proof phase.
- G2: relied-on set is the full contract frame, not the syntactic footprint
  (same cut as `Interferenz.lean` S1); `HaengtAb` is a premise per thread.
- G3: `disziplin` is assumed, not checked — the checker has no held-set
  analysis (`NEBENLAEUFIGKEIT-ENTWURF.md` §6 item 1).
- G4: only lock-shared carriers are included; `atomic` (A10) and
  `publishes`/`awaits` pairing need their own exemptions beside
  `GeteiltGedeckt`.
- G5: `Gesittet` is carried, not consumed (same cut as S2); HB order from
  `kein_wettlauf` is unconnected to stability — ordered writes are writes.
- G6: per-thread entry worlds, no fork/join model — how threads start is
  unmodeled.
- G7: assertions speak about the world only, not `Env` (same cut as S6).

## 5. Self-check (this lane)

`lake env lean Grammatik/InterferenzAllgemein.lean` in `grammatik/`, exit 0,
no output. Build cache (`.lake/`, gitignored) copied from the main tree at
the same base commit — no build was run in this lane, full or otherwise.
`Grammatik.lean` index untouched; `SYNTAX.md` untouched.

## 6. What the next lane owns

Move the §11 prose, add the §16.1 row and the §16.2 cuts, then either prove
`AllgemeinStabil` (fold `StabilSchritt` over `hSchritt` under `GeteiltGedeckt`)
or refute the shape — the falsifier pair in
`NEBENLAEUFIGKEIT-ENTWURF.md` §5 separates the two cases the same way it does
for the two-thread sketch.
