# OG-NB draft: declared-pair restriction and the Rust-to-Lean handoff

Status: DESIGN ONLY, no implementation. Worktree lane-13, base 291c27b,
2026-09-10. Companion to `messung/NEBENLAEUFIGKEIT-ENTWURF.md`, which owns the
checker side; this note owns the Lean-side restriction and the seam between
the two, plus the statement that is still missing.

OG-NB names the Owicki-Gries step for declared concurrency: sequential
contracts (`requires`/`ensures`) stay valid under interleaving, for declared
pairs only, on the back of pairwise disjoint frames.

## 1. Restriction to declared pairs

Today `kein_wettlauf` and `kein_wettlauf_global` quantify over EVERY
interleaving (`IstVerschraenkung`) of well-behaved executions. The `concurrent`
declaration changes the quantifier, not the proof shape:

- `Nebeneinander : Faden -> Faden -> Prop` holds exactly for bodies named
  together in one `concurrent` set, closed under symmetry. It is a premise,
  populated from the declaration; the Lean model never guesses it.
- `BeschraenkteVerschraenkung` is `IstVerschraenkung` restricted to declared
  pairs: an interleaving counts only if every pair of bodies it interleaves
  satisfies `Nebeneinander`.
- `kein_wettlauf` and `kein_wettlauf_global` quantify over the restricted
  predicate. The statement is strictly stronger in its premise (fewer
  interleavings to cover) and matches the checker exactly: what stands in no
  `concurrent` set never runs concurrently in the model either.

Non-declared pairs are therefore not a gap in the proof; they are outside its
quantifier by construction. The proof obligation moves to the checker: every
pair that CAN overlap must either be declared (then checked) or be refused.
That obligation is the handoff below.

## 2. Rust-to-Lean handoff

Each Rust refusal establishes one Lean-side premise. The table reads
Rust check, Lean premise, probe:

| Rust check | Lean premise established | Probe |
|---|---|---|
| W001 disjointness: a declared pair whose transitive write hulls overlap is refused, exact places and same-table carriers, modulo the exemptions | any two bodies with `Nebeneinander` have disjoint write frames, so the frame premise of the joint theorem holds for every declared pair | gift 704 refused, clean side probe-nebeneinander-getrennt accepted |
| W002 closed world: two context roots (`entry`/`boot` dispatch) whose hulls overlap in writes and share no `concurrent` set are refused | `Nebeneinander` covers every overlapping pair: no concurrent pair runs outside the relation silently, so the restricted quantifier loses nothing | gift 705 refused with W002 alone |
| W003 fail-closed: a declared member that resolves to no body, or a pair with an incomplete hull (cycle, unknown callee), is refused | the disjointness premise is never vacuous: a pair the checker could not fully see never enters `Nebeneinander` silently | gifts 706 and 707 refused with W003 |

What the handoff does NOT carry (stays assumption or open question, owned by
`messung/NEBENLAEUFIGKEIT-ENTWURF.md` section 6):

- lock-primitive exclusion (W3, foreign body) and memory-model visibility
  (A10, hardware `sichtbarkeit`): the lock exemption in W001 assumes the edge
  `gibt L -> nimmt L` orders the pair;
- the lock exemption is pair-level, not site-level: a common `locks L` in
  both hulls clears the pair with no held-set analysis;
- table identity is the short name: two modules declaring the same short
  table name in one unit read as one carrier;
- `per cpu` cells are not exempt by shape (refused without a common lock
  although disjoint by core);
- `entrust` roots are skipped, not cleared: unknown guest writes never enter
  any hull;
- W002 is asymmetric by design: visible overlap refuses from the lower bound,
  while a pair with nothing visible stays silent; the fail-closed half lives
  in declared sets (W003).

## 3. Missing joint interleaving semantics statement

Stated loudly, following `messung/ZIEL-BEWERTUNG-2026-09-10.md` section 2:
`exec` and `exec_sicher` compute over one `World`, sequentially. That
sequential `requires`/`ensures` stay valid under interleaving does NOT follow
from happens-before order. Race freedom and the logic proof are two
unconnected sentences, and the restriction in section 1 does not connect
them; it only narrows the interleavings the connection must cover.

The missing statement has this shape (UNBUILT, no Lean text exists for it):

- premises: `exec_rahmen` per body (a body writes only what its contract
  names), plus pairwise disjoint write frames for every pair with
  `Nebeneinander` (exactly what W001 establishes, exemptions included);
- quantifier: every `BeschraenkteVerschraenkung` interleaving of executions
  that are well-behaved per body;
- conclusion: each body satisfies its sequential contract in the joint run;
  equivalently, the per-body `requires`/`ensures` survive the interleaving.

Until that sentence stands proved, the chain reads: Rust checks disjointness
of declared pairs (built), Lean quantifies only over declared pairs
(design, this note), and the theorem that disjoint frames preserve sequential
contracts under the restricted interleaving is missing. Booking the first two
as the third would repeat the withdrawn verdicts of 2026-09-09: shape of a
specification standing in for a proof.

## 4. Acceptance

- The restriction is real when `kein_wettlauf` quantifies over
  `BeschraenkteVerschraenkung`, both Lean trees build with no new axiom
  beyond `propext`, `Classical.choice`, `Quot.sound`, and 0 `sorry`.
- Falsifier for the handoff: a declared pair the checker accepts whose Lean
  frames overlap (exact place or same carrier outside the exemptions). Then
  the seam, not the theorem, is the finding.
- The missing statement is closed when the joint theorem of section 3 stands
  with 0 `sorry` and its premises name W001, W002, W003 line by line.

## 5. Risks

- A silent W002 pair (nothing visible in either hull, recursive callee, no
  declaration) enters neither `Nebeneinander` nor any refusal; the model
  then assumes sequential execution of bodies that share a hidden place.
- The pair-level lock exemption clears pairs no site-level analysis would
  clear; the joint theorem inherits that width silently unless its lock
  premise says pair-level.
- Short-name table identity can merge two carriers the model should keep
  apart; row-level disjointness inside one table stays refused until index
  analysis exists, which caps expressiveness, not soundness.
- `Faden` in Lean is a thread identity while the corpus threads are table
  rows; mapping rows to `Faden` is assumed in this note and unowned.
