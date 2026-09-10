# V4 — Freshness as a fact-set discipline (design draft)

Status: design only, no implementation. Goal: alias analysis becomes
UNNECESSARY — the question "do these two names alias?" may never arise,
because freshness is answered from syntax alone (carriers are named at
every access by construction, SYNTAX.md §§3–4).

## 1. Rule sketch

Per function body the checker keeps a taint map beside the M1 fact set
(SPRACHE.md §3.2): each local holding carrier-derived data maps to its
source **carrier** (table/static name only — granularity §2a). The map
grows at exactly one place — a `let` whose RHS reads a carrier
(`T.slots[i].f`, `G`, `p->f`/`p[i].f` via `Expr.durch`) or calls a
function whose `effects` read one (return taint = callee reads-hull) —
and dies at writes, exactly like V1–V3 facts. A local killed by an
intervening write is **expired**. Re-binding it from a fresh read
revalidates — the re-read IS the refresh, no new spelling (§4).

An expired local may still be **stored/moved** (write RHS, passing it
on changes no belief) but may NOT be **acted on**: branch/match
condition, call argument, return value, `narrow` subject, index. Acting
on it is refused as `logik (veraltet x)` (§4). No may-alias lattice
anywhere: a write naming carrier C kills every C-tainted local,
whether the paths match or not.

## 2. Scope decisions (with measurements)

(a) Kill granularity: **carrier, not field path.** Field-path kill
would need path-overlap reasoning — a mini-alias analysis through the
back door, against the directive. Carrier kill asks only "which carrier
does this write name", which is syntax. Price: measured below (1 site).
(b) Own writes kill too. Exempting same-name writes would bless the
most common C staleness shape (`x = T[i]; T[i] = y; use x`) because it
"looks visible". The swap idiom survives anyway via the store/move
allowance (§1): `k.ziel = alt_quelle` is a move, not a decision.
(c) Loops: **kill all taints at the loop boundary** — the same sentence
as V1–V3 ("loops carry no facts inward"), same machinery, no new rule
to learn. A value needed across iterations is re-read inside; cost on
the corpus: 0 (no table-tainted local crosses a loop boundary, §3).
(d) Calls: **kill taints of carriers in the callee's writes-hull.**
`effects` is already mandatory and already lists carriers, so no new
annotation is consumed. Cost on the corpus: 0 (§3).
(e) Device registers **never taint.** A register read is volatile by
declaration (B33 already refuses V-facts through it); the mandated
single-read idiom (`let m = k.MERKMAL`) is fresh by construction.
Excludes 9 of 12 measured carrier-derived lets (§3) from the rule.

## 3. Ceremony estimate (mandatory) — measured, not guessed

Method: `let` with carrier-read RHS over 131 files (`beispiele/*.gab`,
`messung/proben/*.gab`, `messung/netz/udp-echo.gab`,
`messung/treiber/virtio-net.gab`), then hand-simulation of kill/use
per §1–2. Raw count: **12 carrier-derived lets**; 9 are register reads
(excluded per §2e); of the 3 table-derived ones:

| site | fate under §1–2 | refreshes |
|---|---|---|
| `udp-echo` `alt_quelle = k.quelle` (swap temp) | killed by `k.quelle = …`, used as write RHS → allowed | 0 |
| `39-erster_dringender` `p = q.slots[i].prio` | no write to `q` in body (`effects { reads q.slots }`) | 0 |
| `ipc-fastpath` `w → picked → p` from `e.slots[…]` | killed by `e.slots[core].caller = …`; `p` then passed to `owner_core`/`switch_to` (call args = decision-use) → **refused, needs re-read** | 1–2 |

Loops (§2c) and calls (§2d): 0 sites corpus-wide. **Total: 1–2 sites
against the `narrow` yardstick of 24 — no narrowed scope needed.**

LOUD STATEMENT (the one this section owes): the **literal**
`udp-echo.gab` still passes under V4 — and must. Its bug is an
OMISSION (checksum never recomputed after the `k` writes), and no local
holds the stale value, so no expiry can fire. V4 catches the
udp-echo SHAPE — a named stale use (§5) — not the missing recompute.
A rule that flagged the literal file would be flagging without a stale
name, i.e. guessing. Corpus corollary: with ~0 natural stale-use
sites, V4's teeth are proven by poison/gift probes plus mutation, not
by corpus bites — the same standing as `H013`/`H101`/`H017`.

## 4. Sugar, EBNF, Lean, outcome

No new production, no new word: refresh is re-binding, expiry is a
refusal of existing forms. A `refresh x = …` keyword was costed and
refused — vocabulary is closed (a new word costs the lexer plus every
vocabulary guardian), and at 1–2 ceremony sites sugar buys nothing
(Rule A: no construct without a program that needed it). Lean impact:
**no new constructor.** The taint map threads through `Block` beside
the fact set; `Stmt.assignSlot/assignDurch/assignGlob` (plus call/traverse
boundaries) kill; decision-vs-store is a position property of existing
`Stmt` constructors. Evaluation is untouched — only a new refusal.
Outcome stays **`logik (veraltet x)`**: a new refusal class would add a
third error constructor and break `zwei_fehler` plus the `Satz.lean`
induction; a named `logik` clause keeps the theorem whole.

## 5. Falsifier pair

MUST fail (udp-echo shape — read via `w`, write via `k`, act stale):
```gabbro
let sum = kopfsumme(w);   -- taint {IpKopf bytes}
k.ttl = 64;               -- write names the carrier -> sum expires
if sum != 0 { return Verwurf::Pruefsumme; }  -- REFUSED: decision on expired sum
```
Must pass (fresh read, no intervening write; re-read after write):
```gabbro
k.ttl = 64;
if kopfsumme(w) != 0 { return Verwurf::Pruefsumme; }  -- fresh read, no live taint
```

## 6. Open questions with owners

1. Return-taint precision (reads-hull over-taints pure wrappers?) —
   owner: checker (`m`-pass author). 2. `traverse` re-read cost if a
   hot loop ever needs a cross-iteration taint — owner: corpus (`39`
   is clean; first red loop decides). 3. Whether `veraltet` wants its
   own gift-probe family or rides the `H`-series numbering — owner:
   pass register keeper. 4. A2 (the alias question itself) stays open
   by design: V4 answers the EVENT half (A3) and leaves A2 unasked.
