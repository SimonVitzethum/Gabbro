# MUSE-REPORT-551: Independent exact-candidate review of 545 PayloadResidue

Lane 551, review of author lane 545 (organisation plan N11
`X86/PayloadResidue.lean`, consumer C6 AtomicPayload + QUELLBRUECKE, DEP C6).
Clone `/home/simon/Dokumente/gabbro-muse/a551`, branch `muse/551` verified at
start. Owns only this report; candidate files were staged temporarily for
probing and removed afterwards.

CANDIDATE: 545 6256fe30e55d85ef190449556cefd0f3ad001b44
VERDICT: ACCEPT

## What was reviewed

- `.tmp/review/SNAPSHOT.json`: author 545, head
  `6256fe30e55d85ef190449556cefd0f3ad001b44`, base
  `3dce9fa2585d123c1ad546d520eaf8fe60f0125d`, files `MUSE-REPORT-545.md`,
  `grammatik/Grammatik.lean` (one additive import),
  `grammatik/Grammatik/X86/PayloadResidue.lean` (273 lines).
- `.tmp/review/author-545/OWNER-TASK.md` (N11 row), `MUSE-REPORT-545.md`,
  `BUILD-EVIDENCE.json`, `PATCH.diff`, and the exact candidate file under
  `.tmp/review/author-545/grammatik/`.
- N11 row in `dokumente/x86/NEXT-PROOF-WAVE.md` and QUELLBRUECKE section 3.3
  context; accepted dependencies in this clone: `FussSX` (AtomarReplay),
  `GeteiltA`/`GeteiltV` (Spec), `hb_uebergabe` (Speichermodell/Atomar),
  `nutzlast_braucht_restbeweis`/`nichtatomar_verweigert`/`pD`/`atomar_nichtleer`
  (AtomicPayload, lane 350 merged), `n1_konfig_geteilt` (AtomarAkzeptiertZeuge),
  `w_nicht_sc` (SchwachZeuge), NI fixture types.

## Independent reproduction (real evidence, not trusted logs)

- Staged the exact candidate file plus a trailing
  `import Grammatik.X86.PayloadResidue` in this clone (current master
  `ebdec41d`; candidate base `3dce9fa2` drifted, `Grammatik.lean` tail differs,
  so the PATCH hunk for the import no longer applies verbatim -- content is
  identical, only the anchor moved).
- `./lean-probe grammatik/Grammatik/X86/PayloadResidue.lean`: 0 errors in the
  COMPLETE output; `#print axioms` matches author evidence exactly:
  `payload_fuss_braucht_deckung [propext]`,
  `nutzlast_ohne_deckung_verweigert [propext]`,
  `flagge_ist_kein_schloss [propext, Quot.sound]`,
  `bewachte_uebergabe_ohne_rueckstand [propext, Classical.choice, Quot.sound]`.
- `./lean-bau`: green, `Build completed successfully (421 jobs)` (author saw 416
  on its older base; the delta is master drift, not the candidate).
- Exact forbidden-token scan
  (`\bsorry\b|\badmit\b|\baxiom\b|\bnative_decide\b|\bunsafe\b|intro _|have _ :=`):
  no hits (naive substring hits are only the English word "admitted" in docs).
  No edits to source Spec/checker/emitter or friend-reserved
  `OptimizationRules`/`OptimizationWitnesses`; `Grammatik.lean` diff is the one
  additive import.
- Premise-use checked by reading: every premise of all four mains is used
  (`hF/hmem/hpay/ha/hna` via `hpair`/`hno`; `hna` via `hB`; `ha/hpay/hna` via
  derived `hx`; all W-step premises into `hb_uebergabe`). No `Prop`-typed
  premise, no `forall rho/v` weakening, no discarded premise, no invented
  semantics: all steps/machines/views are actual `SchrittW`/`RufMaschineW`/
  `SchreibG`/`LiestG`/`ordVon` vocabulary.
- Restored the clone afterwards: candidate file removed,
  `grammatik/Grammatik.lean` reverted, `git status --short` clean except this
  report.

## Statement-by-statement check (semantics, not just elaboration)

1. `payload_fuss_braucht_deckung` -- generic footprint obligation over every
   declaration/program. Kills the shared-atomic disjunct via the accepted
   `nutzlast_braucht_restbeweis`, leaves local-or-guard-locked. Real
   `FussSX`/`fussOrteG`/`sigB`/`Bewacht` vocabulary. ACCEPT as stated.
2. `nutzlast_ohne_deckung_verweigert` -- non-atomic payload refused by
   `atomarFussB` and never admitted, via accepted `nichtatomar_verweigert`.
   This is the N11 WITNESS- (unguarded payload refused). ACCEPT as stated.
3. `flagge_ist_kein_schloss` -- concrete: admitted flag `konfig` is shared
   (`GeteiltA` from `n1_konfig_geteilt.1`) and guarded by no lock
   (`.1.2.1`). Destructuring verified against the `GeteiltA`/`GeteiltV` defs.
   A shared atomic flag is not a lock. ACCEPT as stated.
4. `bewachte_uebergabe_ohne_rueckstand` -- thin wrapper over accepted
   `hb_uebergabe`; payload premises discharge exactly the side inequality
   `x != c` (via `p = a` contradiction between `ha`/`hna`), nothing about
   release/acquire assumed beyond the accepted theorem. Conclusion (reader view
   at least writer view at payload; every later payload read at or above it)
   is exactly `hb_uebergabe`'s conclusion at `x := p`. ACCEPT as stated, with
   the scoping cut below.

## Witnesses

- Three mains have fully joint nondegenerate witnesses on `qP`/`pD`
  (`payload_fuss_braucht_deckung_zeuge`, `nutzlast_ohne_deckung_verweigert_zeuge`,
  `flagge_ist_kein_schloss_zeuge`): cover/membership/publication/flag/payload
  jointly, beside a decided written table (`q_schreibt`, `tabA` at `hauptA`)
  and the reached memory-changing run `atomar_nichtleer.2` (`konfig` 0 -> 3
  on `nP`, whose `NFn`/`NTab`/`NGlob` types `pD` shares by record update).
  The `lok := fun _ => true` in `q_fuss` trivialises that cover leg, but the
  main theorem is generic, so this is a valid instance, not a vacuous proof.
- `bewachte_uebergabe_ohne_rueckstand_zeuge` is SCOPED, as openly declared:
  it witnesses jointly the part the transfer adds over `hb_uebergabe`
  (atomic flag, publication, plain payload, derived separation `p != a`,
  written table, reached run), not fresh W-step premises. No in-tree run
  exhibits a fresh acquire read on a payload program (the in-tree run exhibits
  the complementary stale case); faking steps would be worse. The W-step
  premises are `hb_uebergabe`'s own, proved in-tree. This matches the lane-350
  precedent (checker-side witnesses with the run leg shared) and the task's
  honest-bound option. Not a silent gap: report open point 2 and file CUTS
  point 2 say exactly this.

## CUTS (accepted boundaries; full closure stays OPEN)

1. No per-access x86-TSO refinement: transfer is over source W steps, never
   target bytes. TSO bridge owns it.
2. No fresh acquire-read pair exhibited on a payload program; completing that
   leg is bridge work (e.g. via `schrittW_bau`).
3. No duty construction for payload-bearing units (`nutzerA_aus_quelle` is
   atomic-free only); this file audits the cover, it does not build duties.
4. No IR/validator/lowering/optimisation content; no language construct added;
   no atomic-rely duty relaxed.
5. N11 WITNESS+ end-to-end form (exhibited guarded handoff run on the payload
   program itself) is therefore met only in the bounded sense above, not as a
   closed handoff-run exhibit. No repair is ordered for this: it is the
   bridge's job, and the candidate claims nothing beyond the bounded theorem.

## Repair locations

None. No REPAIR items; the scoped transfer witness is disclosed and correct
for the residue-half row, and every other claim is fully proved and witnessed.
