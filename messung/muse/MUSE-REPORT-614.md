# Muse Report 614 — Independent overnight closure review of 602

CANDIDATE: 602 8cb60c644e72091b3524ba92900e0b4f13b2f243
VERDICT: ACCEPT

## Scope and method

Reviewed the exact candidate from `.tmp/review/SNAPSHOT.json` (files:
`MUSE-REPORT-602.md`, `grammatik/Grammatik.lean` one umbrella import line,
`grammatik/Grammatik/X86/ImageStoreFrame.lean` 689 lines) against its owner
task (code/relocation preservation under real data stores) and the actual
changed files in `.tmp/review/author-602/PATCH.diff`. All producer names
resolved against this checkout's `grammatik/Grammatik/X86/`; the candidate
file itself was checked read-only with `./lean-probe
.tmp/review/author-602/grammatik/Grammatik/X86/ImageStoreFrame.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`, with `#print axioms` lines
for every main theorem showing only `propext`, `Classical.choice`,
`Quot.sound` or subsets. No Lean files were added to or modified in this
review clone; no `Grammatik.lean` import was touched here.

Note: the pinned candidate commit object is not present in this clone
(`git branch --contains` reports no such commit; lane clones carry no
remote), so the build check ran the snapshot's exact file content against
current HEAD producers rather than the candidate's own base build. The
candidate's `BUILD-EVIDENCE.json` records its own base build as
`./lean-bau: == exit 0, 440 jobs`, with intermediate red probes during
construction and a final green probe. The snapshot content typechecking
green against newer HEAD (which adds `SourceMemory`, `BridgeWrite` imports
after the candidate's umbrella line) is positive robustness evidence, not
a substitute for the recorded base build.

## What the candidate proves (verified)

- §1 checked-place vocabulary: `istCodeAbschnitt` / `istDatenAbschnitt`
  with W^X agreement (`istCodeAbschnitt_wx`, `istDatenAbschnitt_wx`),
  exclusivity (`daten_nicht_code`), shape probes over the existing
  `zeugenCode`/`zeugenDaten`, and permission facts (`datenStelle_schreibbar`,
  `codeStelle_ausfuehrbar`, `codeStelle_nicht_schreibbar`) via the real
  loader lemmas `geladenSchreibbar_fund` / `geladenAusfuehrbar_fund`.
  All exist in `Bild.lean`; usage matches.
- §2 derived disjointness, no assumed noninterference:
  `codeFremd_von_abbildung` takes fetch-window and store-footprint lookups
  in distinct sections plus the validator's own `paarweise (virtReich bias)
  = true` verdict through accepted `paarweise_virt_trennung` +
  `allePaareDisjunkt_mem`, with stable lookup (`abteilFinden_innen`, proved
  by induction, not assumed), explicit no-wrap bounds, and reused
  `Vektor.addrOff_nat`. Load bias/aliasing handled by loaded sums;
  `bias_alias_beispiel` documents the alias honestly. `codeFremd_von_regionen`
  reuses the accepted `RegionSeparation` interval bridge. Minor note (not
  verdict-changing): the no-wrap bounds `hripNF`/`hANF` in
  `codeFremd_von_abbildung` are in scope for the closing `omega` but do no
  visible work beyond it; they are legitimate side conditions, not a hidden
  desired simulation.
- §3 preservation wrappers (`geholt_nach_erlaubtem_schreiben`,
  `fetchDekodiert_nach_erlaubtem_schreiben`,
  `codeBytes_nach_erlaubtem_schreiben`) over the accepted `CodeImmutability`
  frame. Thin but honest: the substance is §2 + §4 + witness.
- §4 `patchSite_sprung_nach_datenschreiben`: transports fetch equality and
  the `ausfuehrbarN` prefix across an actual `write64` (via
  `ausfuehrbarN_nach_schreiben`) and runs the accepted
  `patchSite_sprung_schritt` on actual memory. Every premise is forwarded;
  metadata only selects bytes. Jump leg only, as the report states.
- §5 refusals: `an_rip_nicht_fremd` (generic overlap never foreign),
  `codeStelle_schreibbar8_falsch` + `codeStelle_schreiben_verweigert` (code
  footprint refused via `write64_verweigert`). Breaking direction correctly
  attributed to producer `ueberlapp_geaendert_zeuge`, not re-proved over an
  impossible image shape.
- §§6–9 joint biased-image witness (`rahmenCode`/`rahmenDaten`/`rahmenDatei`/
  `rahmenBild` at base `0x100000`, `rahmenSite` jump +16 to `0x101015`,
  `rahmenStart`): acceptance by `decide` (`rahmenBild_wohlgeformt`,
  `rahmen_patchSite_ok`), derived foreignness (`rahmen_fremd`), real nonzero
  store with read-back and observable byte change (`rahmen_schreibt`: 42 vs
  0 via `read64_nach_write64` + `writeBytesN_hit`), fetched window
  (`rahmen_geholt`) and execute prefix (`rahmen_hexe`) by `decide`,
  continued branch (`rahmen_sprung_bleibt`), planted refusals
  (`rahmen_code_schreiben_verweigert`, `rahmenBildWx_verweigert`,
  `rahmen_an_rip_nicht_fremd`), joint `rahmen_zeuge` carrying source
  non-degeneracy conjuncts (`zeugenU_schreibt`,
  `zeuge_speicher_aendert_sich.2.1`) explicitly as evidence only.

## Rejection checks (all pass)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (regex over the file:
  no hits); no `Prop`-typed premise; no `intro _` / `have _ :=` discards;
  no contract quantification; no new semantics or interpreter; no second
  decoder/loader/executor/ISA/IR.
- No self-consistency as hardware proof: CUTS states model-`Speicher` only,
  no silicon/TLB/store-buffer claim. No timestamp reset as W-run
  correspondence; no guessed ISA (reuses `relocBytes`/`dispSigned`/
  `patchSiteOk` producers). No hidden desired simulation: foreignness is
  derived per pair, and the source-layout bridge stays an explicit open cut.
- No weakenings: W^X shapes checked, permission refusal via actual
  `write64_verweigert`, overlap-breaking attributed to producer.
- No disconnected filler: wrappers + derivation + instantiated jump +
  witness + refusals form one producer→consumer chain.
- Owned paths only (new file + one umbrella import + report); no
  checker/Spec/goal or optimiser-reserved edits; no named OS assumptions.
- Joint non-degenerate witness present: table-writing function conjunct +
  reached memory-changing run conjunct + own real store with byte
  inequality. Mutation refusals planted (code-store `none`, W^X `false`,
  overlap non-foreign). CUTS precise; axioms standard.
- Tools595 / Rust618 / Docs594-605: the candidate makes no claims about
  them and touches none of their paths; nothing to verify here. Bounded
  accepted scope is Lean-only (see below).

## Bounded accepted scope

One section-pair foreignness derivation, three §3 frame corollaries, one
rel32 jump site surviving one data store at final layout, permission and
W^X refusals, and the single-site biased-image witness pattern. Explicitly
not included (per file CUTS, endorsed): source correspondence, call /
conditional continuations after a store, multi-site / whole-binary /
`valX86` closure, silicon/TLB/coherence, concurrency/TSO-GX.

## Producer/consumer and next tasks (for the coordinator)

- Produces for the layout validator / `valX86` consumer: `datenStelle` /
  `codeStelle` verdicts, `codeFremd_von_abbildung` (discharges one code/data
  pair of `paarweise (virtReich bias)`), §3 corollaries,
  `patchSite_sprung_nach_datenschreiben`, `codeStelle_schreiben_verweigert`,
  `rahmen_zeuge` as the copy pattern.
- Useful next independent tasks (not started): instantiate the call
  continuation after a store (frame image with writable stack section;
  reuse `patchSite_ruf_schritt` as §4 reuses the jump leg); instantiate the
  conditional-taken leg; lift to a whole-section-list verdict
  (`allePaareDisjunkt`-style over all code/data pairs). Ownership to the
  coordinator; no filler.

## Build evidence

- Candidate's own record (`BUILD-EVIDENCE.json`): `./lean-bau == exit 0`,
  440 jobs; final `./lean-probe` 0 errors; axioms standard.
- Independent re-check in this clone (snapshot file, read-only, current
  HEAD producers): `./lean-probe
  .tmp/review/author-602/grammatik/Grammatik/X86/ImageStoreFrame.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0`. This clone's working tree
  is otherwise untouched (report-only commit).

## Task feedback

Nothing in the owner task appears wrong. The report's scoping note (jump
only; call/conditional are separate instantiations) matches the file and is
the correct labelling rather than a gap.
