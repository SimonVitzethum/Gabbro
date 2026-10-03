# MUSE-REPORT-1037: Exact review of author 887 (shift selection rule)

## CANDIDATE

CANDIDATE: 887 da65c2e6c2133f5c6f7ac17d6c87fa752cd09962

## VERDICT

VERDICT: ACCEPT

Scope: bounded — within the CUTS stated in the file, see below.

## What was done

Report-only exact review of the pinned snapshot in `.tmp/review/author-887/`
(SNAPSHOT.json pins head `da65c2e…`, base `b040b155…`, files
`MUSE-REPORT-887.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/OptShiftSel.lean`; PATCH.diff carries exactly those
three files). No source, control or live file touched; this report is the only
owned file. Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1037`
on `muse/1037`.

Reviewed definitions/theorems (all in `Gabbro.Grammatik.X86`, file
`OptShiftSel.lean`, 372 lines):
`ShiftSelCert`, `shiftSelZulassen`, `shiftSelVerweigert_zaehler`,
`shiftSelVerweigert_flaggen`, `shiftSelVerweigert_breite`,
`shiftSelVerweigert_pruefung`, `probe_shiftSelZulassen_ok`,
`probe_shiftSelZulassen_zaehler`, `probe_shiftSelZulassen_flaggen`,
`shiftSel_shl/shr/sar`, `probe_shiftSel_65`, `probe_shiftSel_33_schmal`,
`probe_shiftSel_null`, `shiftQuelle_shl/shr_wert`, `zahlShl_kongr`,
`OptShiftSel_verbindung`, `OptShiftSel_verbindung_zeuge`.

## Evidence (independently reproduced, not copied)

- `./lean-probe` on the exact snapshot file: `== 0 error(s) in the COMPLETE
  output; exit 0`. Axiom lines reproduced exactly as the author reported:
  admission none; four refusals `[propext]`; masking/source/congruence
  `[propext, Quot.sound]`; connection and witness
  `[propext, Classical.choice, Quot.sound]` — all within the `gabbro_ziel`
  standard set.
- `./lean-bau` on my untouched tree: `== exit 0; 0 error line(s) in the
  COMPLETE output`, `Build completed successfully (510 jobs)`.
- Architecture against the local official reference
  (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US): "The count is masked to 5 bits (or 6 bits if in
  64-bit mode and REX.W = 1)" with `COUNTMASK 1FH/3FH` — the reused
  `schiebeZaehler` (`c % 32`, `c % 64` at `.b64`, `Ganzzahl.lean:108`) matches
  exactly. OF "undefined" for masked count > 1; flags unaffected at masked
  count 0. The candidate never assigns the undefined OF: it refuses to fire
  whenever flags are live (`flaggenTot`, `shiftSelVerweigert_flaggen`) and
  cites the reused `SchiebeGueltig` relation instead of re-proving flag
  identity. Sound abstraction, no invented determinism, no ignored defined
  effect (CF/SF/ZF/PF/OF all covered by the liveness refusal).
- Reused names verified present in this tree: `schiebeZaehler`/`shlB`/`shrB`/
  `sarB`/`SchiebeGueltig` (`X86/Ganzzahl.lean`), `Expr.orte` `.shl` arm
  (`a.orte ++ b.orte`, `Semantik.lean:170`), `execEnd` `.bind` arm
  (`Semantik.lean:896-898`), witness fixtures `refEin_schreibt`
  (`ReferenzB.lean:123`), `refB_erreicht` (:987), `refB_schreibt` (:1007,
  slot `0 -> 100`). The `hOrte` footprint-equality premise follows the
  established `CarrierTraceBridge.lean` pattern.
- Proof substance (not vacuous): `shiftSel_shl/shr/sar` rewrite the reused
  canonical ops under the masked-count equation; `zahlShl_kongr` destructures
  all three numbers and substitutes the count equality; the connection proves
  `horte` by `rw [hOrte]` (genuine: `.shl` orte is append) and outcome
  equality by `simp only [execEnd, horte]` + value rewrite — the `.bind`
  outcome is fixed by read-set plus bound value plus shared `rest`, so stop
  classes, contracts at their place, call logs and footprints genuinely
  transfer. All premises used (`hz` via `hEq hz`; `hEq`, `hOrte` in both
  conjuncts); checked premises `hw1 hw2 h0 h0'` forwarded to both spellings;
  no `ensures` derived; IDIV/DIV untouched.
- Witness `OptShiftSel_verbindung_zeuge`: `3 << 2` vs `3 << (1+1)` on
  non-degenerate `refD` (writes via `refEin_schreibt`) beside reached,
  memory-changing run `MB` (`refB_erreicht`, `refB_schreibt`). All premises
  jointly inhabited with concrete values (`cert := <true,true,true,true>`,
  `hEq := fun _ _ _ _ => rfl`, `hOrte := rfl` — both `rfl`s elaborate, as the
  0-error probe confirms). The `_hz/_hEq/_hOrte` binder underscores only
  silence the linter; values are provided, so HARD RULE 13 joint
  inhabitation holds.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep hits are
  only "admission"/"admitted" prose and `#print axioms`); no new
  diagnostic/gift/example/CLI numbers; no MARKE_EMIT change; no
  source/checker/Spec/goal/emitter edits; friend-reserved optimiser files
  untouched; my tree's `Grammatik.lean` contains no `OptShiftSel` (candidate
  unmerged, review is pre-merge).

## Bounded acceptance (the CUTS match the file)

No byte codec/decoder claim; no lowering-side flag-identity proof (admission
cites reused `SchiebeGueltig`); `hEq`/`hOrte` name per-site recomputed
obligations (validator-decided side conditions per the DESIGN section 7 row,
not desired-correctness assumptions — all used, witness-discharged); only
`shl` gets the `Endblock` connection (`shr`/`sar` values only); no
level-(c) machine-work bound; no TSO/GX bridge beyond footprint equality; no
silicon correspondence. The conditional `hEq : zulassen → ∀…` shape is the
documented certificate pattern, consistent with the DESIGN row.

## Nits (not verdict-changing)

- Only three `decide` probes for four refusals: `breite` and `pruefung` have
  refusal theorems but no `probe_shiftSelZulassen_breite/pruefung` probe.
  Suggest adding them at merge or in a follow-up; coverage is complete at
  theorem level.

## What remains open

Nothing for this lane: report-only review is complete. Integration (merge +
fresh publication checks) belongs to the serial watch, not to this report.

## Task feedback

Nothing in the task appears wrong.
