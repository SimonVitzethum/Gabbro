# MUSE-REPORT-893: address-mode selection rule

## What was done

New file `grammatik/Grammatik/X86/OptAddrModeSel.lean` (~510 lines) plus the
owned import line `import Grammatik.X86.OptAddrModeSel` in
`grammatik/Grammatik.lean` (after `OptFoldConst`). It states and proves the
address-mode selection rule lemma: smallest-first addressing
(disp0/disp8/disp32, SIB, RIP-relative for image constants) with
revalidation after patching, over the reused canonical vocabulary
(`Typen`, `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
`X86.AddressEncoding`: `adrEff`, `dispWortArt`, `passtIn8`, `kompaktArt`,
`fussZugelassen`, `leaFormSchritt`, `ripForm`, `adrOk`). Read once each:
the accepted-leaning `OptFoldConst` pattern, `CostSummary`
(`kostenSummeOk`/`expandBound` schema), `TableLayout` (computed layout,
`eintragOk`/`layoutOk`), and the invariant/effect exports
(`InvariantenOpt`, `isWahrAll` checker-rerun precedent). No IR is
referenced: no accepted single IR exists in this clone, so the rule is
stated over arbitrary machine values with validator-decided side
conditions, exactly as the task permits ("until then the real
Syntax/Semantik fragment you cover" for the source side; the target
side reuses `AddressEncoding`).

## Exact names

Certificate: `AddrSelCert` (`kleinOk`, `keinUmbruch`, `ripBildOk`,
`nachgeprueft`), admission `addrSelZulassen` (local rewrite record plus
recomputed-analysis citations: kernel-recomputed displacement equation
`hEq`, kernel-recomputed `passtIn8` `hK`, both conditional on admission).

Refusals (rule must NOT fire): `addrSelVerweigert_gross`
(large displacement narrowed), `addrSelVerweigert_umbruch` (wrapped
footprint), `addrSelVerweigert_ripFremd` (RIP-relative outside image
constants), `addrSelVerweigert_ohneNachpruefung` (unrevalidated patch);
probes `probe_addrSelZulassen_ok`, `probe_addrSelZulassen_gross`,
`probe_addrSelZulassen_ohneNachpruefung`.

Value: `addrSel_wert` (generic, arbitrary state/forms), pins
`probe_addrSel_wert_fuenf`, `probe_addrSel_breite_entscheidet` (wrong
width is a different offset).

Fault: `addrSel_fuss` (admission agrees), `addrSel_lesen` (same read
value/refusal: contracts at their place read the same values),
`addrSel_schreiben` (same write landing: no access added or removed,
concurrency sees the same footprint), pin `probe_addrSel_fuss_zeuge`.

Observation: `addrSel_lea` (same destination, flags, memory; each side
keeps its own encoding length), `addrSel_storeSchritt` (same landing
memory).

IEEE/cost/RIP: `addrSel_gleit_unberuehrt` (non-interference, stated as
such), `addrSel_kompakt` (fitting displacement takes the byte form),
`probe_addrSel_ersparnis` (fewer displacement bytes),
`addrSel_rip_nurBild` (image base only, never the register file),
`probe_addrSel_ripMitBasis_verweigert`.

Connection: `OptAddrModeSel_verbindung` (7 conjuncts: address,
admission, read, write, LEA triple, smallest-first choice, IEEE
verdict) with companion `OptAddrModeSel_verbindung_zeuge` (all
premises jointly instantiated at `r8`/`r9`/scale-8/displacement-0
selecting `8200` on `storeWitZustand`, both LEA sides stepped, wide
write of `42` proved through `write64`, on table-writing `refD` via
`refEin_schreibt` beside reached memory-changing run `MB` via
`refB_erreicht` + `refB_schreibt`).

## Verification

Last `./lean-bau` result: `== exit 0; 0 error line(s) in the COMPLETE
output`, `Build completed successfully (511 jobs)`. `./lean-probe` on
the new file: 0 errors, 0 warnings. `#print axioms` for every theorem:
at most `[propext, Classical.choice, Quot.sound]` (the `_zeuge`
theorem; all others a subset or none) — the standard `gabbro_ziel`
set, no new axiom. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
No diagnostic/gift/example/CLI numbers, no MARKE changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files touched.

## What remains open

Per CUTS in the file: no silicon correspondence; no fresh encoder
round trip for the selected bytes (cites the recomputed equation,
never a new codec proof); no source simulation (source untouched;
preservation argued through address/footprint/observation agreement,
the lowering lanes own the simulation); no TSO/GX bridge; no
whole-image and no full source-to-byte validation claim.

## Task remarks

Nothing in the task is believed wrong. One scoping note: "contracts,
call logs" at the source level are covered by outcome agreement
(reads agree, LEA adds no event, store lands identically) rather than
by an `execEnd` window, because the rewrite fires below the source;
this is stated plainly in section 6 and CUTS instead of manufacturing
a source-level simulation premise.
