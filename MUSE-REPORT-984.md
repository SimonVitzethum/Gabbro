# MUSE-REPORT-984: Exact review of author 834 (Composition closing: budget-resumption closing)

CANDIDATE: 834 b1a78264bd1afe3b7e74461edcaf61fe73fbf93b
VERDICT: ACCEPT

Acceptance is bounded as stated in CUTS (see sections below).

## Task and scope verified

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a984`, branch `muse/984` (via `.git/HEAD`).
- Pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 834, head
  `b1a78264bd1afe3b7e74461edcaf61fe73fbf93b`, base
  `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4` (matches this clone's base),
  files: `MUSE-REPORT-834.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/ComposeBudgetResum.lean`, clean.
- Owner task (`.tmp/review/author-834/OWNER-TASK.md`): close source budget
  exhaustion to target work spent with ghost source-budget correspondence;
  exhaustion timing stays explicit OPEN cut; compose accepted modules only;
  ZEUGE `ComposeBudgetResum_verbindung` + `ComposeBudgetResum_verbindung_zeuge`.
- This review owns ONLY `MUSE-REPORT-984.md`. No source file was modified.

## What the candidate does (from exact PATCH text)

- New file `grammatik/Grammatik/X86/ComposeBudgetResum.lean` (202 lines) +
  one import line in `grammatik/Grammatik.lean`. No other file touched.
- New names, exactly:
  - `def GhostBudget (s : CostSummary) (ghost src : Nat) (xs : List Decodiert) : Prop`
  - `theorem expandBound_mono`
  - `theorem deckung_resum`
  - `theorem ComposeBudgetResum_verbindung`
  - `theorem ComposeBudgetResum_verbindung_zeuge`
- Interface closed: source over-budget head (`Budget.runOps` via
  `BudgetExecution.stoppReihenfolge`) to target work spent
  (`CostSummary.expandBound`/`targetWork` via `BudgetExecution.Deckung` and
  `budgetAusfuehrung_transfer`), plus ghost tracking (`ghost = src`) and
  resumption (`src <= src'` preserves coverage via
  `expandBound_keinVerlust`).

## Independent checks performed

1. PATCH text read in full (`.tmp/review/author-834/PATCH.diff` and the
   snapshot copy of `ComposeBudgetResum.lean`). No `sorry`, `admit`,
   `axiom`, `native_decide`, `unsafe` present. No `intro _` / `have _ :=`
   discard. Proofs use `rw`, `cases`, `omega`, `decide`, `obtain`, `exact`
   only.
2. Every referenced producer lemma confirmed to exist in this base clone:
   `expandBound_keinVerlust`, `blattSummary_schranke` (`CostSummary.lean`);
   `budgetAusfuehrung_transfer`, `stoppReihenfolge` (`BudgetExecution.lean`);
   `laufKosten_kopf_verweigert`, `profilZeuge`, `zeugeKosten` with
   `.ret => none`, `laufKosten_schranke_zeuge_hbound`
   (`HardwareAssumptions.lean`); `zeugeProg`/`zeugeZustand`/`lauf`/`zeige...`/
   `zeuge_speicher_aendert_sich` (`Ausfuehrung.lean`); `runOps`/`runOps_cons`/
   `fremdOp`/`fremdOp_kosten` (`Budget.lean`); `ziel_ort_einfaden_zeuge`
   (`ZielOrtEinfadenZeuge.lean`).
3. Proof logic verified by reading (not by re-execution of the author HEAD):
   - `expandBound_mono`: rewrites both bounds with `expandBound_keinVerlust`
     (`src * m + spill + fence`), then `Nat.mul_le_mul_right` + `omega`.
     Sound; spill/fence cancel correctly.
   - `deckung_resum`: `Deckung` unfolds to
     `forall k, expandBound s src = some k -> targetWork ... <= k`; replays
     accepted expansion on both sides, uses `hDeck _ e1` and monotonicity.
     Sound; same-`m` reuse is valid since `alleMax` is `src`-independent.
   - `ComposeBudgetResum_verbindung`: all 8 hypotheses used
     (`hGhost` for ghost deck; `hMax`/`hDeck`/`hResum` via `deckung_resum`;
     `hCost`/`hb`/`hDeck` via first transfer; same at `src'` for second;
     `hSrcOver`/`hTgtRef` via `stoppReihenfolge`). Conclusion is a genuine
     composition, not a premise restated and not an existential of one.
   - Witness `ComposeBudgetResum_verbindung_zeuge`: reuses accepted
     non-degenerate fixtures — `ziel_ort_einfaden_zeuge` (table-writing
     program, reached run slot `0 -> 5`), `zeuge_speicher_aendert_sich`
     (register and memory byte `0 -> 42`, start byte `0`), `hCost`/`hDeck`
     by `decide`, `hb` via `laufKosten_schranke_zeuge_hbound`, over-budget
     `fremdOp 3` (cost `3 + 1 = 4 > 3`, so `runOps 3 3 [fremdOp 3]` is a
     genuine `.budget` refusal), refused `ret` head (`schrittKosten
     profilZeuge ret = none` definitionally from `zeugeKosten`, so
     `laufKosten ... = none` is a genuine target refusal). Both transfer
     bounds (`src = 1`, resumed `src' = 2`) are exhibited jointly with both
     refusals. Joint, non-degenerate, memory-changing. Satisfies the ZEUGE
     requirement.
4. Architecture (byte forms, REX/register/width/flags, operands, pre-fault
   effects, memory order, TSO/atomicity, feature/MXCSR/interrupt gates,
   canonical execution): no new hardware form is introduced — the file
   composes accepted `lauf`/`laufKosten`/`runOps` equations untouched and
   adds no decoder, executor, cost model, or profile. `ret` refusal is a
   cost-model refusal (`none`, never silent zero); execution of `ret` remains
   modelled in `Ausfuehrung` (`probe_ruf_kehr`). No invented determinism, no
   zeroed/ignored defined effect, no reordering claim. Exhaustion TIMING is
   explicitly left OPEN in CUTS (scheduling/IR lanes), lowering
   correspondence stays carried `Deckung` data, no hardware-cycle,
   constant-time, or CAS-progress claim. Claim boundary is precise.
5. Scope compliance: no diagnostic/gift/example/CLI numbers, no MARKE_EMIT
   change, no source/checker/Spec/goal/emitter edit, no friend-reserved
   optimiser file. Import appended at end of `Grammatik.lean`. CUTS block +
   `#print axioms` for all five names present.
6. Queued wrapper sanity in THIS clone (source untouched):
   `./lean-probe grammatik/Grammatik/X86/BudgetExecution.lean` →
   `== 0 error(s) in the COMPLETE output; exit 0` (producer module green;
   confirms apparatus and the axiom footprints of the reused theorems).
   The exact author HEAD was NOT rebuilt in this clone (own-only +
   base-preservation constraint); build evidence for the candidate comes
   from its pinned `BUILD-EVIDENCE.json`: `lean-probe` on the new file
   `0 error(s)`, whole-project `./lean-bau` `Build completed successfully
   (509 jobs)`, `gabbro_ziel` family still
   `[propext, Classical.choice, Quot.sound]`, new theorems on
   `[propext, Quot.sound]` (main) / `[propext, Classical.choice,
   Quot.sound]` (witness) — all within standard goal axioms.

## Bounded acceptance notes (not repairs)

- `GhostBudget` is defined but the closing theorem states its content
  inline (`hGhost : ghost = src` + `Deckung s ghost xs`) rather than naming
  `GhostBudget` in the conclusion. The report's wording slightly overstates
  the use of the def. Semantically identical; no repair needed, noted for
  precision.
- `expandBound_mono` is proved but the main path uses `deckung_resum`
  (which replays the expansion) rather than calling it. Harmless auxiliary;
  all its premises are used by its own proof.
- Intel SDM reference (edition 093, September 2026, locally snapshotted in
  `.tmp/HARDWARE-REFERENCES/`) is inherited scope here: no new instruction
  form means no new manual-evidence obligation beyond the reused accepted
  `ret`-refusal and `zeugeProg` forms.

## What remains open (per file CUTS, endorsed)

Exhaustion timing, lowering/IR correspondence (`Deckung` carried data;
`DerivedWorkBound.deckung_fragment` covers only the fragment), hardware
cycles, constant-time/CAS-progress — all explicitly OPEN, none claimed.

## Conclusion

One candidate reviewed, decision as stated in the machine-readable header.
No guarantee weakened, no desired simulation assumed, no fake
closure. No repairs required.
