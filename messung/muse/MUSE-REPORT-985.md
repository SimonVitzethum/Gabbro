# MUSE-REPORT-985: Exact review of author 835 (work-transfer composition closing)

CANDIDATE: 835 e21c40da63fb2fe39a329f1f0b4ed0970b4f60d0
VERDICT: ACCEPT
Bound: explicit interface closure over the covered fragment only; no new hardware coverage beyond lanes 654/572.

## Identity and scope

- Review clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a985`, branch
  `muse/985`, HEAD `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, working tree clean.
  This matches the review SNAPSHOT base exactly.
- Candidate files (from pinned PATCH, 3 files only): `MUSE-REPORT-835.md`,
  `grammatik/Grammatik.lean` (one appended import line), and new file
  `grammatik/Grammatik/X86/ComposeWorkTransfer.lean` (227 lines, read in full).
- Scope clean: no source/checker/Spec/goal/emitter edits, no friend-reserved
  optimiser files, no diagnostic/gift/example/CLI numbers, no MARKE changes.
  The only PATCH mention of `MARKE_EMIT` is the report's own "no changes" sentence.

## What the candidate does

- `ComposeWorkTransfer_verbindung` (TARGET): plugs producer
  `DerivedWorkBound.deckung_fragment` (lane 654, derives `Deckung` from the
  fragment lowering) into consumer `BudgetExecution.budgetAusfuehrung_transfer`
  (lane 572, named per-form costs + `Deckung` into `t <= B * k`). Proof is the
  two-line composition; both producer and consumer are reused by name, nothing
  re-proved, no new interpreter/executor/cost model/IR.
- `ComposeWorkTransfer_geschlossen`: closed corollary `t <= B * (src * 4)` via
  `fragmentSummary_expand` (uniform maximum 4, zero spill/fence).
- Three refusals propagated by name: `verweigert_knapp` (via
  `arbeit_knapp_verweigert`), `verweigert_retry` (via
  `kein_freier_versuch_fragment`), `verweigert_ohneKosten` (via
  `zeitTransfer_verweigert_ohneKosten`).
- Joint witnesses `verbindung_zeuge`, `geschlossen_zeuge`,
  `verweigert_knapp_zeuge` on the shared non-degenerate `witD628` package with
  the `Paket` conjunct. The two syntax-free refusals need no `_zeuge` per rule 13.

## Independent checks performed

- Signature check: `deckung_fragment`, `budgetAusfuehrung_transfer`,
  `senkAssign_zeit_schranke`, `fragmentSummary_expand`, `arbeit_knapp_verweigert`,
  `kein_freier_versuch_fragment`, `zeitTransfer_verweigert_ohneKosten`, and all
  witness names (`witAbb628`, `witE628`, `witSenk628`, `witSenkAssign628`,
  `hCost_wit`, `hb_wit`, `paket_nicht_degeneriert`, `Paket`, `profilZeuge`) exist
  in this base with matching roles.
- Premise use: traced every binder of the main theorem into the proof
  (`hsenk`/`hsrc` via `deckung_fragment`, `hCost`/`hb` via the transfer;
  `abb`/`e`/`dst`/`tmp`/`baseR`/`disp`/`src`/`p`/`B`/`t`/`prog` all consumed).
  Same for `geschlossen` and all three refusals. No `Prop`-typed premise, no
  discarded premise, no contract quantification, no restated-premise conclusion.
- Forbidden forms: grep over the candidate shows no `sorry`, `admit`, `axiom`,
  `native_decide`, or `unsafe` (only `admit` as substring of "admitted"); no
  `intro _` / `have _ :=` pattern.
- Witness non-degeneracy: `Paket` = contract writes the table (`witHw628`) AND
  a memory-changing fetched-byte run (`witLaufAendert628`) AND a source
  `execStmt` run moving slot `12 -> 42` (`witQuelle_aendert`). Each `_zeuge`
  instantiates ALL premises jointly on the witness program and proves the
  conclusion through the composed step. Genuine reached memory-changing runs,
  not a conjunction of checks.
- Hardware-architecture review: the module introduces no byte forms, no decoder
  or execution rules, no REX/register/width/flag semantics, no memory-order or
  TSO/atomicity claims, no feature/MXCSR/interrupt gates, and no redefinition
  of canonical execution (`decodiertZu`, `laufKosten`, `schrittKosten`,
  `senkFrag`/`senkAssign` reused untouched). The architecture checklist is
  vacuous by construction, and the CUTS say so honestly: fragment-only coverage,
  named per-form bounds (never silicon latencies), scheduling/multiplicities
  and interleavings OPEN with owning lanes named.
- Queued wrappers (read-only, own clone untouched): `./lean-probe
  grammatik/Grammatik/X86/DerivedWorkBound.lean` -> `== 0 error(s)`, exit 0;
  `./lean-probe grammatik/Grammatik/X86/BudgetExecution.lean` -> `== 0
  error(s)`, exit 0. Candidate build evidence (`lean-probe` 0 errors, `lean-bau`
  509 jobs green, axioms `[propext, Quot.sound]` main / `+ Classical.choice`
  witnesses) is consistent with the reused base lemmas. No source files were
  modified for this review; per the own-only rule the candidate was verified
  from its pinned PATCH/review copy, not by staging it into this clone.

## Known thinness (bounded acceptance, not a defect)

- The author discloses, and I confirm by direct comparison, that
  `ComposeWorkTransfer_verbindung` coincides propositionally with the
  already-accepted `senkAssign_zeit_schranke` (DerivedWorkBound, lane 654):
  identical premises proved through the same two legs. The genuinely new
  checked content is: the named 572-OPEN-leg closure stated in one place, the
  closed declared-cost bound `t <= B * (src * 4)`, the three refusals propagated
  through the composed step, and the joint non-degenerate witnesses. That is
  what the owner task asked for ("compose already-accepted modules ... never
  re-prove their internals"), so the duplication is redundancy, not fake
  closure. No full source-to-final-bytes validation and no target-to-W/GX
  bridge is claimed; both stay OPEN as recorded.

## Conclusion

ACCEPT candidate 835 e21c40da63fb2fe39a329f1f0b4ed0970b4f60d0. Sound composition
with all premises used, real joint witnesses with memory-changing reached runs,
propagated (not weakened) refusals, standard axioms, precise CUTS with owners,
and no unsupported desired-correctness premises or weakened guarantees.
Bounded as stated above: closure of the `Deckung`-into-transfer interface over
the covered lowering fragment only.
