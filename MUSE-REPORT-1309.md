# MUSE-REPORT-1309: Page-fault delivery — CR2, error code and the interrupt frame

Lane 1309, clone `/home/simon/Dokumente/gabbro-muse/a1309`, branch `muse/1309`
(verified via `.git/HEAD`: `ref: refs/heads/muse/1309`).

## What was done

NEW FILE `grammatik/Grammatik/X86/HwPageFaultDelivery.lean` (~1280 lines),
plus one `import Grammatik.X86.HwPageFaultDelivery` line appended to
`grammatik/Grammatik.lean`. No other existing file touched. All accepted
definitions reused unchanged, never copied: `HwMaschine`/`HwSchritt`/`HwWf`/
`HwAdapter`/`verweigertAdapter` (HardwareExecution §11), `seitenGang`/
`PfFehlerCode`/`pfCodeBits`/`witSeitenSteuer`/`witTab`/`wit_schreibe_ro_pf`/
`wit_code_ro` (HwPaging), `asyncMasch`/`asyncMasch_rip`/`asyncMasch_rsp_neu`/
`asyncMasch_wf` (HwInterrupts), `liefere`/`liefere_zugestellt_wechsel`/
`_behalten`/`pruefeTor`/`waehleStapel`/`schiebeRahmen`/`rahmenWorte`/
`liesTorBytes`/`torAdresse`/`torImLimit`/`loWit`/`witTssByte`/`witIdtByte`
(InterruptDescriptorHardware), `przFehler_speicher_still`/`_puffer_still`/
`_beobachtung_still` (HwPreciseFault), `dfVektor`/`dfCode` (HwNestedInterrupts).

Delivery design (synchronous exception, NOT async): `PfEreignis` carries the
walk's faulting linear address and `PfFehlerCode` plus delivery inputs; gate
bytes are read from machine memory. `pfSchritt` runs limit → gate read →
`pruefeTor` (`.extern`, so no software-INT DPL check) → `waehleStapel` →
canonical check → `pfFertig` push of the SIX-word frame (five frame words
plus error code in S2 `pfCodeBits` order). No IF gate (exceptions are not
maskable INTR); new IF follows the gate kind. `HwPfMaschine` pairs the
coherent machine with per-core control and per-core CR2; `HwPfSchritt.pf`
loads CR2 with the faulting address (S5). Refusal at any stage is `none`;
`pfMitDf` escalates any refusal to #DF (S4: vector 8, code zero, the accepted
`dfVektor`/`dfCode`; the full #DF handler entry reuses the same push stage).

Main theorems (all premises used; axioms per `#print axioms` are only
`propext` and `Quot.sound`, never more — several are axiom-free):
- §1: `pfVektor_vierzehn`, `pfAnfrage_vektor`, `pfAnfrage_code`,
  `pfAnfrage_rahmen_sechs`, `pfSchritt_zugestellt_wechsel`,
  `pfSchritt_zugestellt_behalten`.
- §2: `pfFertig_erhaelt`, `pfLieferung_erhaelt`, `pfLieferung_wf`,
  `pfLieferung_puffer_still` (S6: no TSO drain), `pfSchritt_liefere_wechsel`,
  `pfSchritt_liefere_behalten` (exact `liefere` agreement),
  `pfFehler_speicher_still`, `pfFehler_puffer_still`,
  `pfFehler_beobachtung_still` (faulting instruction left no effect),
  `pfEintritt_rip`, `pfEintritt_rsp`, `pfInterrupt_loescht_if` (S3),
  `pfTrap_behaelt_if`.
- §3: `hwPfSchritt_sync_einbetten`, `hwPfSchritt_sync_nur`,
  `hwPfSchritt_wf`, `hwPfSchritt_cr2` (CR2 load, S5), `adapterPf`,
  `adapterPf_treue`, `adapterPf_wf`, eight `pfSchritt_verweigert_*`
  refusals (limit, gate-read, descriptor, stack, canonical ×2, frame ×2)
  plus `adapterPf_verweigert_limit`, `pfMitDf_zugestellt`,
  `pfMitDf_doppelt`, `pfDf_vektor_acht`, `pfDf_code_null`.
- §§4–7 witness: `pfWit_gang` (walk says seitenFehler 8192 with the
  RO-write code), `pfWitCode_wort` (code 7), `pfWit_liest`,
  `pfWit_gate_bereit` (interrupt gate → handler 8192), `pfWit_stapel`
  (IST 16384), handler-entry facts (`pfWit_liefert_rip/rsp/if/gew`,
  six `pfWit_rahmen_*` read-backs incl. error code at 16336,
  `pfWit_aendert_ss`), `pfWit_klar_liefert` (no IF gate: succeeds under
  IF=false too), three refusals (`pfWit_limit_verweigert`,
  `pfWit_tor_verweigert`, `pfWit_dunkel_verweigert`) with #DF
  escalation (`pfWit_dunkel_df_vektor/code`), TSO stage
  (`pfWit_weiterleitung`, `pfWit_fremd_alt`, `pfWit_spuelung_aendert`,
  `pfWit_fremd_neu` at cell 16328, clear of the six-word frame),
  `pfWit_relation` (reached `HwPfSchritt.pf` with `cr' 0 = 8192`) and the
  joint `pfLiefer_zeuge` (walk fault ∧ code ∧ entry state ∧ CR2 ∧ empty
  buffers ∧ frame ∧ IF-bypass ∧ refusals ∧ #DF ∧ forwarding/drain ∧
  `HwWf` ∧ reached extended step — non-degenerate: two cores touch
  memory, frame push and drain both change shared memory).

## Last `./lean-bau` result line

`Build completed successfully (677 jobs).` — green for the whole project.
`./lean-probe grammatik/Grammatik/X86/HwPageFaultDelivery.lean` ends
`== 0 error(s) in the COMPLETE output; exit 0`. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` in the new file.

## What remains open (see CUTS block in the file)

No hardware correspondence (S1–S6 are named SDM-provenance assumptions);
no nested #PF delivery, no handler execution; no per-access W/GX bridge;
no timing/TLB/SMEP-SMAP/large-page/noncanonical-walk delivery; no
supervisor-shadow-stack behaviour. `gabbro_ziel` axioms untouched.

## Notes on the task

- The task phrase "pushes the error code and the interrupt frame through
  the TSO buffer as the interrupt lane models" is implemented as the
  interrupt lane models it: the frame is pushed to canonical memory while
  every per-core TSO buffer is untouched (S6, `pfLieferung_puffer_still`,
  both witness buffer lengths still zero). No buffered push was introduced.
- `asyncSchritt` itself could NOT be reused for vector 14: its admission
  gate (`asyncVektorOk`) admits only NMI vector 2 and maskable 32–255, so
  vector 14 always refuses there. The delivery therefore mirrors its stage
  order with synchronous-exception admission (fixed vector 14, no IF gate)
  while reusing `asyncMasch`, `liefere` and every stage lemma unchanged.
- Apparatus observed: `./lean-bau` failed three times at the final
  `Grammatik` aggregator step only (my module printed its axioms each
  time) — once `failed to create thread`, twice `failed to read file`
  on varying shared-toolchain oleans (`Forall.olean.private`,
  `UV/System.olean`) — then went green on the fourth run with no content
  change. Environmental/shared-load flakiness, not a content defect.
