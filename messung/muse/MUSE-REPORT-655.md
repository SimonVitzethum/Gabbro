# MUSE-REPORT-655: Review of author 654 (Derived target work bound)

Lane 655, clone `/home/simon/Dokumente/gabbro-muse/a655`, branch `muse/655`.
Report-only exact review of the pinned candidate. No source edits; this report
is the only owned file.

CANDIDATE: 654 34c89f7e37f7837ad40da7974755fe29410cca48
VERDICT: ACCEPT

## What was reviewed

Author 654 owns `grammatik/Grammatik/X86/DerivedWorkBound.lean` (new, 678 lines),
one appended import in `grammatik/Grammatik.lean`, and `MUSE-REPORT-654.md`.
Pinned snapshot (`.tmp/review/SNAPSHOT.json`): head
`34c89f7e37f7837ad40da7974755fe29410cca48`, base `24e625c0`, clean, 3 files.
I inspected the exact pinned PATCH, the owner task, and the full candidate
module, and resolved every reused definition in this clone before judging.

## Semantic checks (all passed)

- Real lowering, no second interpreter: work formulas (`senkAtom_laenge`,
  `senkFrag_laenge`, `senkAssign_laenge`) are derived from the actual
  `senkAtom`/`senkFrag`/`senkAssign` via the existing classifications
  (`istAtom_von_senkAtom`, `istFrag_von_senkFrag`, `senkAssign_ok`). The one
  `targetWork` (`CostSummary.lean`, `xs.length`) and the one `laufKosten`
  aggregation are reused untouched; `decodiertZu` is a plain map whose
  `laenge` field is cost-irrelevant (`schrittKosten` reads only `befehl`).
- No assumed Deckung/hWork: `Deckung` appears only as a conclusion.
  `deckung_fragment` derives it from the fragment admission equation plus the
  proved length bound; both premises (`hsenk`, `hsrc`) are used.
  `senkAssign_zeit_schranke` composes it with named per-form hardware costs
  via the existing `budgetAusfuehrung_transfer`; its cost premises (`hCost`,
  `hb`) are concrete aggregation facts instantiated in the witness
  (`hCost_wit`, `hb_wit` over the existing `profilZeuge`: 1+1+2+3 = 7), not
  hidden correspondence.
- No forged input, no vacuous joints: witnesses share the non-degenerate
  package (`Paket`: contract writes the table `witHw628`, fetched-byte run
  changes memory `witLaufAendert628` via actual `laufBytes`, source run moves
  slot 12 -> 42 via actual `execStmt`). Refusals are genuine: mul has no
  lowering (`senkAssign_verweigert_mul` in the base module), the retry-bound
  removal applies the existing `kein_freier_versuch` with proved `rfl`
  arguments, the below-2 bound contradicts the proved length formula.
- Optimiser connection is honest: `arbeit_nach_faltung` lowers both sides
  through actual `senkFrag` (work 3 vs 1, same value via `eval_foldAddLit`),
  proving costs must be recomputed, never inherited.
- No guarantee weakening: `ret` stays refused, stops stay loud, no CAS
  progress/fairness/stutter claim; CUTS names scheduling, all-source and
  timing-model fidelity as OPEN. No `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`, no `Prop`-typed premises, no unused premises found.

## Reproduced evidence (queued wrappers, this clone)

- `./lean-probe grammatik/Grammatik/X86/DerivedWorkBound.lean` (candidate file
  copied in, removed afterwards): `== 0 error(s) in the COMPLETE output`.
  All `#print axioms` within `[propext, Classical.choice, Quot.sound]`.
- `./lean-bau` with candidate file plus appended import on current master:
  `Build completed successfully (462 jobs).` Tree reverted afterwards;
  `git status` clean except this report.

## Accepted bounded claim

For the covered fragment (literals, variables, one bounded add/sub over
atoms, one slot store): generated work is 1 / 1-or-3 / 2-or-4 instructions;
`fragmentSummary` (uniform maximum 4, zero spill/fence, proved retry bound)
is admitted and yields `Deckung` by derivation; named per-form hardware time
composes to `t <= B * k`. Minimal repair: none.

## What remains open (per candidate CUTS, endorsed)

Scheduling across several assignments, all-source coverage beyond the
fragment, and timing-model fidelity (named bounds, never silicon) stay open.
Next useful task as the author states: a `Deckung` producer for the next
covered fragment reusing `senkFrag_laenge`/`arbeit_decodiert`.
