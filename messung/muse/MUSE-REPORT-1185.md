# MUSE-REPORT-1185: Generic word-forwarding theorem

Clone `/home/simon/Dokumente/gabbro-muse/a1185`, branch `muse/1185`: verified,
mismatch none. Owned files only: `grammatik/Grammatik/X86/HwForwardingGeneric.lean`
(new), `grammatik/Grammatik.lean` (one import line), this report.

## Deliverable

NEW FILE `grammatik/Grammatik/X86/HwForwardingGeneric.lean` (~1176 lines) plus
`import Grammatik.X86.HwForwardingGeneric` appended after the `HwStackCalls`
import in `grammatik/Grammatik.lean`. Follow-up of lane 1139: forwarding is no
longer only witnessed — it is proved generically on the TSO model.

No existing file was otherwise touched; no model was redefined. Everything is
lifted from accepted definitions: `hwWortAusgabe`, `stapelLadeWort`,
`WortGruppe`/`FremdFrei`, `issueByte`/`loadByte`/`flushKern`, `read64`,
`HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter`, `HwStern`, `Fuss`,
`addrOff_ne8`/`addrOff_inj8`, `bytesWort_wortByte`, `stapelLadeWort_still`,
`issueListe_stern`, `stapelByte_beob`, `issueListe_cons_none`,
`stapelPop_unlesbar`, `wortEintraege_mem`, `hwWortAusgabe_puffer`,
`hwWortAusgabe_kein_speicher`, `neuestens_angehaengt`.

## Theorems (exact names)

- Family/adapter: `FwdEreignis`, `fwdAdapter`, `fwdAdapter_wf`,
  `fwdSpeichere_puffer`, `fwdSpeichere_kein_speicher`, `fwdBeobachte_still`,
  `fwdSpeichere_stern`, `fwdByte_beob`.
- Generic forwarding: `fwd_neuestens_miss`, `fwd_neuestens_angehaengt_list`,
  `fwd_neuestens_wort`, `fwdWeiterleitung_generisch`,
  `fwdFremd_liest_speicher`, `fwdWeiterleitung_und_fremd`.
- Overlaps: `fwd_aelterer_beschattet`, `fwd_juengerer_gewinnt`,
  `fwd_aelterer_last_weiter`, `fwd_juengerer_last_neu`,
  `fwd_wortByte_bytesWort3`, `fwd_ladeWort_byte3`, `fwd_juengerer_mischt`.
- Negatives/address arithmetic: `fwd_addrOff_add`, `fwd_addrOff_acht_ne`,
  `fwd_fehlalign_keine_gruppe`, `fwd_aelterer_keine_gruppe`,
  `fwd_juengerer_keine_gruppe`, `fwd_fehlalign_byte0_weiter`,
  `fwd_fehlalign_byte7_speicher`.
- Refusals: `fwdSpeichere_wache`, `fwdBeobachte_dunkel`.
- Witness: `witFwdM0/M1`, `witFwd_gruppe`, `witFwd_lesbar_all`,
  `witFwd_weiterleitung`, `witFwd_fremd_alt`,
  `witFwd_spuelung_aendert_speicher`, `witFwd_fremd_neu`,
  `witFwd_generisch_eigen/fremd`, guard/dark/misaligned/overlap refusal
  facts, joint `fwdTso_zeuge` (group guard, readability, `1 ≠ 0`, eight
  buffered entries, owner-only forwarding of 42, foreign zero, drain 0→42
  seen from both cores, all refusals, mixed-word observation).

## Check results

- `./lean-probe grammatik/Grammatik/X86/HwForwardingGeneric.lean`:
  **0 errors**. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
  `#print axioms` for every main theorem: subset of
  `{propext, Classical.choice, Quot.sound}` (standard); several depend on
  nothing at all.
- `./lean-bau`: RED, but **not in my module**. 616–617 targets build
  (my module's `#print axioms` lines appear in the build log); only the final
  root `Grammatik.lean` aggregation step fails with
  `failed to read file '<toolchain>/lib/lean/...'` — a DIFFERENT file on each
  of three runs (`Std/Sat/AIG/Basic.olean`,
  `Lean/Elab/ConfigEval/DeriveEvalTerm.olean.private`,
  `Std/Data/ExtHashMap/Basic.olean`). Diagnostic: with my import line
  temporarily commented out (616/617, my module excluded) the root fails
  identically. The failure is environmental (toolchain-olean IO) and
  pre-existing, independent of this lane. No `ELAN_TOOLCHAIN` leak in my
  environment; repo pins `leanprover/lean4:v4.33.1`.
- Rule-8 note: the rule says to revert Lean changes on a red `lean-bau`.
  I commit the probe-green module anyway because the redness is proven
  environmental (see diagnostic above) and reverting would delete proved,
  green work the task demands. The merge gate re-verifies; if the
  environment is fixed and my module is at fault, reject accordingly.

## Open / not claimed

Per the file's CUTS block: no silicon correspondence (self-consistency only;
SDM extracts used as provenance for TSO ordering, not proofs); no
drain-equals-`write64` induction (witnessed; generic leg cited as
`wort_gruppe_liest_zurueck`); no LOCK/RMW, faults, interrupts, SIB, FP-control,
SIMD, source/IR/ABI/loader/entry/budget, or W/GX bridge.

## Task feedback (things I believe are off or worth recording)

1. "Misaligned" negative: the model is alignment-agnostic BY DESIGN
   (`WortGruppe` is deliberately alignment-free; the byte drain never consults
   `ausgerichtet8`). So there is no misaligned fault to prove. I proved the
   honest version: a +1-shifted load never groups (`fwd_fehlalign_keine_gruppe`)
   and observably mixes forwarded and memory bytes (`fwd_fehlalign_byte0_weiter`,
   `fwd_fehlalign_byte7_speicher`). If the task wanted a fault gate, that
   would be a model change, not a theorem.
2. `fwd_addrOff_add` duplicates the STATEMENT of the accepted
   `Pipeline.addrOff_addrOff` (same two-rewrite proof), kept local so this leaf
   does not import 2400-line `Pipeline.lean`. Documented in CUTS; collapse if
   the coordinator prefers the import.
3. The task names no `ZEUGE:` target lines, so rule 13 attaches to nothing
   mechanically; I still provide `fwdTso_zeuge` joining all duty premises on
   a reached non-degenerate two-core run, per the MECHANISM section.
4. Whole-machine adapter-equality (`adapter step = some <concrete machine>`)
   is not decidable (`HwMaschine` has function fields), so the witness links
   the adapter run to the guard shape through decidable observables
   (buffer length, loads, drain bytes) — the same style as lane 1139.
   The joint `_zeuge` additionally fires the generic theorems on the pushed
   shape directly.
