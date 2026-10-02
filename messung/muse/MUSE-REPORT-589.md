# MUSE-REPORT-589: Independent exact-candidate connection review of 571

CANDIDATE: 571 ea00d1a8e427dc790d3aaa88814f6c4a3c0bf238
VERDICT: ACCEPT

## Scope and method

- Reviewed exact candidate `ea00d1a8` against base `8596f83e`: 3 files
  (`MUSE-REPORT-571.md`, `grammatik/Grammatik.lean` +1 import,
  `grammatik/Grammatik/X86/EntryExecution.lean` 375 lines). No other paths touched.
- Read full candidate file, its report, and all resolved producers in the
  local checkout: `Bild` (`wohlgeformt`, `geladen`, `laden*`),
  `EntryState` (`eintrittOk`, `eintrittRsp`, `stapelRW`,
  `eintritt_verweigert_unlisted`), `GateStub` (`torOkB`, `schreibTor`,
  `torAusClobber`, `torKlassifiziere`, `schreibTor_ok`,
  `torKlassifiziere_ebadf`), `Byteschritt` (`fetchDekodiert`,
  `byteschritt`, `byteschritt_weiter`, `ausgangRip`),
  `ValidatorSkeleton` (`valZeuge`, `valTore`), `VertragOrtB.ReqAmEintritt`,
  `FremdRuf.AufruferPflicht`, `ContractSites.vertragStandort_lauf_zeuge`,
  `Speicher.write_read_zeuge`. All names resolve to real accepted definitions.
- Reproduced mechanically: copied candidate file to
  `grammatik/Grammatik/X86/EntryExecution.lean` in this clone and ran
  `./lean-probe grammatik/Grammatik/X86/EntryExecution.lean`.
  Result: `== 0 error(s)`, exit 0. Removed the copy afterwards;
  this commit owns only this report (`git status` clean before write).
- Grep for forbidden tokens with word boundaries: no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`. No `intro _` / `have _ :=`.
  No premise typed `Prop` itself. CUTS block + `#print axioms` per main
  theorem present.

## Connection check (producer/consumer delivers new facts)

- `eintrittZulassung` conjoins three checked admissions (mapping AND entry
  state AND gates) as a `Bool`. The conjunction alone would be decorative,
  but the candidate derives genuinely new consequences from it:
  - `zulassung_rip_ausfuehrbar`: RIP executable through the CHECKED loaded
    mapping `(geladen bild bias).ausfuehrbar`, proved via the `hl` leg of
    `eintrittOk` — not the state's own permission function. Real loading fact.
  - `zulassung_stapel_rw`: entry stack word below `rsp` readable/writable,
    via `stapelRW` leg. Real memory fact.
  - `zulassung_erster_schritt`: from admission + `fetchDekodiert` + `schritt`,
    concludes mapping-executability AND `byteschritt = .weiter s'` by reusing
    `byteschritt_weiter`. No second executor, no duplicated fetch/decode.
  - `tor_grund_im_kanal`: raw answer decoding to `.grund g` through an
    admitted gate's table implies `g < t.gruende`, via `fehlerOkB` admission
    plus actual `torKlassifiziere` case analysis and proved `find?_tupel_mem`
    auxiliary. Kernel meaning of the table stays user logic. Real channel fact.
  - Generic refusals `zulassung_verweigert_unlisted` /
    `valTore_verweigert_bei` / `zulassung_verweigert_tor` reuse the missing
    listing / member refusal; planted `decide` witnesses for both directions.
- No forged input: witness image is the accepted `valZeuge` (one `ret` byte
  195 at 0x1000); `zulassung_fetch_ret` / `zulassung_schritt_ret` are `decide`
  over actual `fetchDekodiert` / `byteschritt` on the witness state, and they
  re-checked green here. No guessed ISA (uses existing `Decodiert.ret`,
  `Codec`), no new hardware assumption, no cost/time transfer, no
  checker/Spec/goal/emitter or friend-file edits.

## Statements, premises, witnesses, axioms

- Every premise is used: `h` in all admission theorems (via projections),
  `hf`/`hs` in `zulassung_erster_schritt` (via `byteschritt_weiter`),
  `htor`/`herr` in `tor_grund_im_kanal` (admission + decode), `hmem`/`h` in
  refusal pair. No conclusion restates a premise; projections
  (`zulassung_wohlgeformt`, `zulassung_eintritt`) are honest conjunction
  eliminations alongside the substantive derived theorems above.
- No contract quantification-away: `ReqAmEintritt` held at actual `(wP, rhoP)`
  from the reached run; `AufruferPflicht` reused as `torRuferPflicht`
  (def alias) at actual values, never discharged by declaration. The report
  honestly records `torRuferPflicht` as stated-only: fixture `eD` has
  `Ax := Empty`, so no gate inhabitant exists — a correct non-witness
  admission, not a hidden weakening.
- Joint non-degenerate witness `eintrittAusf_zeuge` (existential, honestly
  named): admitted entry (`zulassung_zeuge_ok`) + fetched `ret` +
  executed step to RIP 0 + reached source run from
  `vertragStandort_lauf_zeuge` (table-writing: `(eD.signatur
  eSetze).schreibt () = true`; memory-changing: slots `0 → 5`; `ReqAmEintritt`
  at its place; `RufErreichbarG`) + real x86 change from `write_read_zeuge`
  (`m.bytes a ≠ m'.bytes a`). Both sides instantiated, neither assumed from
  the other. Channel witness `tor_grund_im_kanal_zeuge` jointly instantiates
  all three conjuncts (admission, EBADF decode, channel membership).
- Axioms (reproduced `lean-probe` output): every theorem within
  `[propext, Classical.choice, Quot.sound]`; the joint witness uses exactly
  the standard triple. No axiom drift.
- CUTS honest and complete: no source-to-entry lowering claim (IR 287 /
  QUELLBRUECKE named open), async interrupt model open, `torRuferPflicht`
  stated-only, single-step scope (`ret` pops to unlisted RIP 0), no
  callee-side/hardware/cost claims, refusals are validator `Bool`s.

## Exact accepted bounded claim

Admitted entry (checked `Bild` mapping AND `eintrittOk` AND `valTore`) gives:
RIP executable through the checked loaded mapping, entry stack window
readable/writable, first fetched `ret` actually steps via the shared
`byteschritt` to RIP 0, and any reason decoded through an admitted gate's
table lies inside its declared channel — with generic + planted refusals
(unlisted RIP, refused gate member) and the joint reached-run + memory-change
witness above. No source-to-emitted-bytes lowering, no interrupt leg, no
multi-step or callee-side claim.

## Minimal repairs

None required. Optional (not a condition): name a future `_zeuge`-suffixed
alias if the merge gate prefers the convention; the current joint witness
already satisfies the substance.

## Producer/consumer interface (stable)

- Produces: `eintrittZulassung`, `zulassung_erster_schritt`,
  `tor_grund_im_kanal`, `torRuferPflicht`, `eintrittAusf_zeuge`.
- Consumes unchanged: `Bild`, `EntryState`, `GateStub`, `Byteschritt`,
  `ValidatorSkeleton.valZeuge`/`valTore`, `VertragOrtB.ReqAmEintritt`,
  `FremdRuf.AufruferPflicht`, `ContractSites.vertragStandort_lauf_zeuge`.
- Measurable next integration: conjoin an actual emitted-bytes claim to
  `eintrittZulassung` once source-to-entry lowering lands; extend
  `eintrittAusf_zeuge` and build multi-step legs on
  `zulassung_erster_schritt`.
