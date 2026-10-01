# Muse Report 602 — Code and relocation preservation under real data stores

## What was done

New file `grammatik/Grammatik/X86/ImageStoreFrame.lean` (owned path) plus one
umbrella import line in `grammatik/Grammatik.lean`. It connects the checked
`Bild` section mapping/permissions, `CodeImmutability` fetch preservation,
actual `Speicher`/`Byteschritt` stores and `RelocatedExecution`
patch-and-redecode into generic preservation of fetched/decode code bytes
after permitted data stores.

- §1 Section shapes and checked-place vocabulary: `istCodeAbschnitt`,
  `istDatenAbschnitt`, `datenStelle`, `codeStelle`, with W^X agreement
  (`istCodeAbschnitt_wx`, `istDatenAbschnitt_wx`), exclusivity
  (`daten_nicht_code`), shape probes (`probe_code_code`,
  `probe_daten_daten`) and permission facts (`datenStelle_schreibbar`,
  `codeStelle_ausfuehrbar`, `codeStelle_nicht_schreibbar`).
- §2 Physical disjointness DERIVED, never assumed: `codeFremd_von_abbildung`
  (fetch window in one section, store footprint in another, pairwise
  `virtReich` verdict via the accepted `paarweise_virt_trennung` +
  `allePaareDisjunkt_mem` region re-reading, stable lookups via
  `abteilFinden_innen`, explicit no-wrap bounds, `Vektor.addrOff_nat`
  reused) and `codeFremd_von_regionen` (selected-region variant through the
  accepted interval bridge). Load bias/aliasing handled by loaded sums
  throughout (`bias_alias_beispiel` documents the alias).
- §3 Preservation wrappers over the accepted frame:
  `geholt_nach_erlaubtem_schreiben`,
  `fetchDekodiert_nach_erlaubtem_schreiben`,
  `codeBytes_nach_erlaubtem_schreiben`.
- §4 `patchSite_sprung_nach_datenschreiben`: a checked relocated jump site
  still steps to its mapped target after an actual `write64` elsewhere
  (fetch equality + execute-prefix transported, then the accepted
  `patchSite_sprung_schritt` runs on actual memory).
- §5 Refusals: `an_rip_nicht_fremd` (overlap is never foreign, generic;
  the breaking direction is the producer `ueberlapp_geaendert_zeuge`),
  `codeStelle_schreibbar8_falsch` + `codeStelle_schreiben_verweigert`
  (permission refusal through `write64_verweigert`).
- §§6–9 Joint biased-image witness (`rahmenCode`, `rahmenDaten`,
  `rahmenDatei`, `rahmenBild` under base `0x100000`, `rahmenSite`
  jump +16 to `0x101015`, `rahmenStart`): acceptance
  (`rahmenBild_wohlgeformt`), admitted site (`rahmen_patchSite_ok`),
  shape/pairing facts, derived foreignness (`rahmen_fremd`), real nonzero
  store with read-back and observable byte change (`rahmen_schreibbar8`,
  `rahmen_lesbar8`, `rahmen_byte_null`, `rahmen_schreibt`), fetched window
  (`rahmen_geholt`) and execute prefix (`rahmen_hexe`), continued branch
  (`rahmen_sprung_bleibt`), planted refusals
  (`rahmen_code_schreiben_verweigert`, `rahmenBildWx` +
  `rahmenBildWx_verweigert`, `rahmen_an_rip_nicht_fremd`), and the joint
  `rahmen_zeuge` carrying source non-degeneracy conjuncts
  (`zeugenU_schreibt`, `zeuge_speicher_aendert_sich.2.1`) as evidence only.

No source checker/Spec/goal or friend-reserved optimiser files touched. No
second decoder/loader/executor/ISA/IR created; producers reused by name.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (440 jobs).`
`./lean-probe grammatik/Grammatik/X86/ImageStoreFrame.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`#print axioms` for every main theorem: only `propext`,
`Classical.choice`, `Quot.sound` (or subsets); no `sorryAx`.

## What remains open (precise CUTS)

Documented in the file's CUTS block: no source correspondence (source
conjuncts are non-degeneracy evidence only; a source-layout to
target-disjointness bridge stays an explicit open cut); call/conditional
continuation after a store not instantiated (jump only;
`patchSite_ruf_schritt` and the conditional legs are the analogous consumer
instantiations); single site at final layout only (multi-site convergence
and the full `valX86` closing theorem stay with the consumer); model
`Speicher` only, no silicon/TLB/store-buffer claim (TSO bridge owner);
sequential only, no concurrency claim; overlap-breaking proved by the
producer over non-image WX memory, which no accepted image admits.

## Producer/consumer interfaces and next tasks

- Produces for the layout validator / `valX86` consumer: `datenStelle` /
  `codeStelle` verdicts, `codeFremd_von_abbildung` (discharges one
  code/data pair from `paarweise (virtReich bias)`), the three §3 frame
  corollaries, `patchSite_sprung_nach_datenschreiben` (discharges one rel32
  site surviving a data store), `codeStelle_schreiben_verweigert`
  (permission leg), `rahmen_zeuge` (joint acceptance + execution +
  refusals pattern to copy).
- Useful next independent tasks (exact ownership for the coordinator):
  instantiate the call continuation after a store (needs a frame image with
  a writable stack section beside code+data; reuses `patchSite_ruf_schritt`
  the way §4 reuses the jump leg); instantiate the conditional-taken leg;
  lift `codeFremd_von_abbildung` to a whole-section-list verdict
  (`allePaareDisjunkt`-style over all code/data pairs) for multi-site
  consumers. None started here; no filler.

## Task feedback

Nothing in the task appears wrong. One scoping note: the task asks for
"continued execution of a patched branch after actual data write" — this is
delivered for the unconditional jump only; call/conditional are the same
shape but are separate instantiations and are labelled as such rather than
claimed.
