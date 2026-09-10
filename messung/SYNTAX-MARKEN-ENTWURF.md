# Linear marks as a construction for W4 — design

Status: DESIGN ONLY, no implementation. Worktree lane-39, base 2657f77.
Not committed. This file is the SYNTAX.md section draft; SYNTAX.md itself is
untouched.

Goal: turn (W4) — "a mark is in one thread" (`Wettlauf.lean:18`, premise
`Gesittet.marke_eindeutig`, `Wettlauf.lean:188-190`) — from an assumed run
property into a construction. Mark ownership becomes explicitly threaded step
state (defs), creation/consumption becomes tight constructors with no forging,
and single-threadedness becomes Prop-valued defs shaped to feed the
`marke_eindeutig` premise verbatim. Companion Lean file (design only, defs, no
theorems): `grammatik/Grammatik/Marken.lean`.

## 1. Inventory (measured on this tree)

What the grammar already says about linear marks — every site read, none moved:

| site | content |
|---|---|
| `SYNTAX.md:256-260` | `typedecl … "linear" … [ markorder ]`; `order` says which steps are admissible on the value |
| `SYNTAX.md:321-325` | examples: `linear type Parked;`, `linear ghost type BootPhase order { roh, mmu, geraete };`, `linear ghost type Duty(farbtest);` |
| `SYNTAX.md:555-562` | head clauses: `advances a -> b` (mark at `a`, body leaves it at `b = a+1`), `retires m from s …` (mark leaves Λ, assumption named) |
| `SYNTAX.md:586-590` | "linear, not affine": `return` demands multiset EQUALITY between Λ and the `allocs` list |
| `SYNTAX.md:679-682` | `advstmt = "advances" ident "->" ident ";"`; Λ after the statement carries the mark at the next stage |
| `SYNTAX.md:722-730` | Λ table: head = `Held(L)` + consumed marks at stage; after call = Λ − consumes + allocs; after `advances` = Λ − marke(m,a) + marke(m,b); after `retires` = Λ − marke(m,s); at `return` ≡ signature `Held` + allocs |
| `SYNTAX.md:764-765` | statement table: `advances` needs mark at `a`, `b = a+1 < stages`; `retires` needs mark at stage `s` |
| `Syntax.lean:136-149` | `D.Marke`, `D.stufen`, `D.eigner`, and `eigner_nie_erzeugt`: no signature ever produces an owner mark |
| `Syntax.lean:206-219` | `Res.held` / `Res.marke (m) (stufe)`; `Res.von`, `Res.vonMarke` |
| `Syntax.lean:226-250` | `nachSig` (consumed erased, produced appended), `Signatur.anfang` (head Λ), `Vertrag.ende` (owed Λ) |
| `Syntax.lean:461-465` | `Stmt.advances` (`h : Res.marke m a ∈ Λ`, `hs : a + 1 < D.stufen m`), `Stmt.retires` (`h : Res.marke m s ∈ Λ`) |
| `Satz.lean:140` | a `return` hands back exactly the owed witnesses and marks — linear |
| `Satz.lean:186-188` | `stufe_steigt`: inversion at `advances` |
| `Wettlauf.lean:18-20` | (W4): one thread per mark; no instruction hands a mark to another thread; nobody creates owner marks |
| `Wettlauf.lean:188-190` | `marke_eindeutig` — exact shape (quoted in §4) |

What is missing (the gap this design closes): the grammar threads Λ through
*derivations* (`Stmt` indices), but no object says who owns a mark *between
threads at run time*. (W4) therefore travels as a premise about event traces
(`Res.marke m s ∈ ei.lambda`), with nothing on the construction side that
could discharge it. The honesty note at the end of `Wettlauf.lean` §5 books
exactly this: W4 stays a premise because it speaks about the relation of
threads to each other.

## 2. Rule sketch: the step state

One stand per run, threaded through every mark step:

- `Stand : Marke → Option (Faden × Nat)` — each mark is free or owned by
  exactly one thread at exactly one stage. A mark at two threads is not
  wrong; it is unwritable.
- `belebe` / `loesche` — the two state transitions, as defs.
- `MarkenSchritt κ σ σ'` — exactly three constructors, each carrying its
  premise (same style as the `Stmt` constructors, which carry `h : … ∈ Λ`):
  - `erzeuge`: only from void (`σ m = none`), only below the stage count,
    never an owner mark (`¬ κ.istEigner m` — the `eigner_nie_erzeugt` half).
  - `fuehre`: only in the hand of the SAME thread (`σ m = some (f, a)`),
    only to `a + 1 < stufen` (the `Stmt.advances` half: `h`, `hs`).
  - `verbrauche`: only from the hand into the void (the `Stmt.retires` half).
- `Verlauf κ σ` — runs over the stand, from `Anfang` (all void), step by step.
- Invariants as Prop-valued defs, no proofs: `Besitzt`, `StufenTreu`
  (owned ⇒ below stage count), `StandEinfaedig` (two owning threads agree).

There is no fourth constructor — no forging over an owned mark, no
duplication, no handoff to another thread. The tightness of the constructors
IS the no-forging discipline (W4: "keine Anweisung reicht eine Marke an einen
anderen Faden weiter, und Eigentumsmarken erzeugt niemand").

## 3. Proposed SYNTAX.md section text (paste-ready draft)

The following block is the draft for a new SYNTAX.md subsection (placement:
after the Λ table in §7, which it extends by one column — the run-time stand):

```markdown
### Linear marks at run time: the stand

The context Λ says what the derivation holds; the STAND says what the run
holds. One stand per run: every linear mark is free or owned by exactly one
thread at exactly one stage. A mark step is one of three — create (only from
void, only below the stage count, never an `owner` mark: owner marks are never
produced, `eigner_nie_erzeugt`), advance (only in the hand of the same thread,
only to the next stage below the count), consume (only from the hand into the
void). There is no fourth step: no forging, no duplication, no handoff to
another thread.

| derivation (Λ, §7) | run (stand) |
|---|---|
| head Λ = `Held` + consumed marks | initial stand: all void (`Anfang`) |
| call: Λ − consumes + allocs | the callee's produced marks appear in its own hand |
| `advances a -> b;` | the same thread advances the same mark `a -> a+1` |
| `retires` | the owning thread consumes the mark into the void |
| `return`: Λ ≡ `Held` + allocs | every produced mark is owned, every consumed mark is gone |

Single-threadedness (W4) is the shape every mark step preserves: two events
naming stages `s`, `s'` of the SAME mark name the SAME thread — stages may
differ (advance changes the stage, never the owner), threads may not.
```

## 4. Lean impact (`grammatik/Grammatik/Marken.lean`)

Defined names (all defs; no theorem/lemma/example; no sorry/admit/axiom; no
mathlib; no imports — standalone with a mirror table, same arrangement as
`Geteilt.lean`, because the lane forbids touching the `Grammatik.lean` index):

- abbrevs: `Marke`, `Faden`, `Lauf`
- `MarkDekl` (`stufen`, `istEigner`) — mirrors `D.stufen`, `∃ t, m ∈ D.eigner t`
- `Stand`, `Anfang`, `belebe`, `loesche` — ownership as threaded step state
- `MarkenSchritt` (`erzeuge`/`fuehre`/`verbrauche`), `MarkenSchritt.faden`,
  `Verlauf` — tight constructors, runs from `Anfang`
- `Besitzt`, `StufenTreu`, `StandEinfaedig` — structure invariants as
  Prop-valued defs
- `Einfaedig` — single-threadedness as a Prop-valued def with EXACTLY the
  `marke_eindeutig` shape (`Wettlauf.lean:188-190`, read-only):

```lean
marke_eindeutig : ∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
  l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
  Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g
```

`Einfaedig` repeats these binders and antecedents with the local mirrors
(`Lauf`, `Schritt`, `Ereignis`, `Marke`, `Res`, `Ereignis.lambda`) where the
original has `Lauf D`, `Schritt D`, `Ereignis D`, `D.Marke`, `Res D`,
`Ereignis.lambda`. Whatever `Gesittet` delivers therefore fits without
translation; the projection itself is booked as cut C2 (it needs the index
entry this lane must not add).

Self-check (only): `lake env lean Grammatik/Marken.lean` in `grammatik/` —
no full build, no cargo.

## 5. What it does NOT do (decided loudly)

- C1. No theorems: reachable stands satisfy `StufenTreu`/`StandEinfaedig` by
  induction over `Verlauf` — an induction is a theorem, and this design ships
  none. The defs name the shape the theorem will have.
- C2. No wiring: `Einfaedig` matches the W4 field verbatim, but consuming it
  inside `kein_wettlauf` (replacing the premise) is the wiring lane's work,
  together with the `Grammatik.lean` index entry.
- C3. No handoff, by absence: cross-thread mark passing is not refused by a
  rule — there is simply no constructor that could write it.
- C4. No initial ownership: where the FIRST ownership comes from (signature
  head, `Signatur.anfang`) is the derivation's business, not the stand's;
  the stand starts void.

## 6. Falsifier pair (must-fail / must-pass, to be added as `gift/` probes)

```gabbro
// MUST FAIL: forging an owner mark — no constructor admits it
linear type M;
table T count 4 { slot { x : u32 } owner M }
impl fn forge() effects { pure } {
  advances M -> M;   // expect: refuse — M is nowhere in hand, and owner marks are never created
}
// MUST PASS: advance in hand, consume at the head promise
linear ghost type Phase order { roh, fertig };
impl fn step() effects { consumes Phase, allocs Phase } advances roh -> fertig {
  advances roh -> fertig;   // expect: clean — same thread, next stage, below the count
}
```

## 7. Open questions with owners

1. Call-produced marks: `erzeuge` currently admits any non-owner mark below
   the stage count; should it demand `(m, s) ∈ (sigNr n).produziert` for some
   `n` (witnessed creation), or does the head-Λ (`Signatur.anfang`) already
   carry that? (Owner: proof-architecture lane.)
2. Ghost vs. physical marks: `Held(Lock)`-style ghost witnesses are never
   consumed (`locks` adds non-consumably) — does the stand track them, or do
   only `Res.marke` marks thread through it? (Owner: grammar lane.)
3. Stand ↔ Λ correspondence: which theorem ties `Stand` at run time to Λ at
   the derivation (`exec` recording `Res.marke` into `Ereignis.lambda`)? That
   is the missing joint statement C1 will need. (Owner: semantics lane.)
4. `Duty(farbtest)` parameters: the mark carries a `check` name — does the
   stand need the parameter, or is `(Marke × Nat)` enough as for `Res.marke`?
   (Owner: S3/error lane.)
