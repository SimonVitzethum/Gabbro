# MUSE-REPORT-782: LFENCE load narrowness

Lane 782, clone `/home/simon/Dokumente/gabbro-muse/a782`, branch `muse/782`.
Owned files only: `grammatik/Grammatik/X86/LfenceLoadNarrow.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Proved LFENCE as load-only ordering, strictly narrower than MFENCE, over the
one canonical `TSOZustand`, with byte-facing fetch/step from actual executable
memory under the `fetchDekodiert` admission discipline. No existing file
touched except the `Grammatik.lean` import. No diagnostic/gift/example/CLI
numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits.

Definitions: `LfenceEreignis`, `lfenceSchritt` (total, state-preserving),
`lfenceBytes` (`0F AE E8`), `decodeLfence`, `LfenceByteAusgang`,
`lfenceZugelassen`, `fetchLfence`, `lfenceByteschritt`, witnesses
`lfWitBytes`, `lfWitExec`, `lfWitSpeicher`, `lfWitZustand`, `lfGespült`.

Theorems: `lfence_erhaelt_puffer`, `lfence_erhaelt_speicher`,
`lfence_lasten_bleiben`, `lfence_ereignis_schmal`,
`mfence_verweigert_bei_vollem_puffer`, `roundtrip_lfence`,
`lfenceBytes_len`, `lfenceLaenge_ok`, `pilot_weist_lfence_zurueck`,
`lock_weist_lfence_zurueck`, `fetchLfence_erfolg`,
`lfenceByteschritt_weiter`, `lfenceByteschritt_verweigert`,
`lfence_nachbar_sfence`, `lfence_nachbar_mfence`, `lfence_abgeschnitten`,
`lfence_leer`, `lf_fetch`, `lf_fetch_nachBild`, `lf_nachBild_verweigert`,
`lf_flush`, `lf_speicher_aendert`, `lf_puffer_voll`,
`lf_mfence_verweigert`, `lf_erreichbar`,
`LfenceLoadNarrow_verbindung` (target: preservation + narrow event +
MFENCE refusal on nonempty own buffer, all premises used),
`LfenceLoadNarrow_verbindung_zeuge` (joint, non-degenerate: reached
`sbNach1` with buffered store, memory-changing flush, fetched step
4096 -> 4099 with memory unchanged, MFENCE refusal on the same state).

Key distinction proved: MFENCE (`lockSchritt .mfence`) refuses a nonempty
own buffer; LFENCE admits it and changes nothing (no drain). Bytes `0F AE
E8` are disjoint from the pilot decoder, the locked decoder (reg field 5
vs 6), SFENCE (`F8`) and MFENCE (`F0`); truncations refuse.

Axioms: all new theorems depend on subsets of
`propext, Classical.choice, Quot.sound` (most on `propext` alone or none).

## Last build result

`./lean-probe grammatik/Grammatik/X86/LfenceLoadNarrow.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (485 jobs)`.
First `./lean-bau` attempt failed at the final `Grammatik` link with
`failed to create thread` (resource exhaustion, 484/485 built); retry
passed unchanged. No proof gate was touched.

## What remains open (see CUTS in the file)

Silicon correspondence; store ordering/drain (LFENCE never drains);
dispatch-serializing MSR variant and CPUID gate; fault delivery;
TSO/W/GX bridge; timing/fairness/progress; interrupts/devices; all
source/checker/goal work.

## Task remarks

Nothing in the task appears wrong. One note: the task asks for "the exact
admitted elimination premise or refusal" -- delivered as
`mfence_verweigert_bei_vollem_puffer` (admission gap) plus byte-level
refusals and the load-preservation (elimination) fact
`lfence_lasten_bleiben`. The Intel txt lines could not be grepped (tool
permission denied listing `.tmp/HARDWARE-REFERENCES` via shell); provenance
is grounded in `REFERENCES.json` (Intel SDM 325462-093US, Sept 2026,
sha256-verified) with entry/opcode names stated in the file header.
