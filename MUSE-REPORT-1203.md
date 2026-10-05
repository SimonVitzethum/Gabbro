# MUSE-REPORT-1203

Lane 1203: Pipeline atomics — register-address binding, fences, word-install proof.
Follow-up of lane 1163 (`PipelineAtomics.lean`), closing its three named open gaps.
Branch `muse/1203` in clone `/home/simon/Dokumente/gabbro-muse/a1203`.

## Owned files

- NEW `grammatik/Grammatik/X86/PipelineAtomicsBind.lean` (~460 lines)
- `grammatik/Grammatik.lean` (one appended import line only)
- this report

No other file touched. No existing theorem weakened or deleted. No new
`axiom`/`sorry`/`admit`/`native_decide`/`unsafe` anywhere.

## What was done

All three gaps from the task are closed over REUSED accepted definitions only
(no new machine, no new decoder row, no second IR, no source/checker/goal change):

1. **Register-address binding (§1).** The accepted locked steps speak about
   ADDRESSES, the byte forms about REGISTERS. Each theorem states the
   lane-1163 lowering together with the accepted projection at the BOUND
   address, linked by the single equation `effAddr m.zu base d = a`:
   - `bind_xadd` — lowered LOCK XADD runs `lockSchritt (.xadd64 a ...)` at the
     named address (via `lockVoll_xadd_adapter` + `senk_xadd`);
   - `bind_cas_erfolg` — lowered LOCK CMPXCHG success runs
     `casSchritt a rax src` at the named address
     (via `lockVoll_cmpxchg_erfolg_adapter` + `senk_cas`);
   - `bind_mfence` — the fence needs no address at all
     (via `lockVoll_mfence_adapter` + `senk_zaun`).
2. **SFENCE/LFENCE lowering (§§2–3).** `ZaunArt` (`mfence`/`sfence`/`lfence`),
   `zaunBytes` (all three pins reused), decided validator `valZaun` with
   `valZaun_korrekt`, decode facts `zaun_mfence_dekodiert`,
   `zaun_sfence_dekodiert`, `zaun_lfence_dekodiert`; step correspondence
   `zaun_sfence_korrekt` (TSO-observably the identity, fence-only event) and
   `zaun_lfence_korrekt` (state-preserving narrow event while the MFENCE gate
   refuses the same state); refusals `zaun_sfence_ohne_sse` (#UD without SSE),
   `zaun_sfence_puffer_verweigert` (no silent skip); poison probes
   `gift_lfence_pilot`, `gift_lfence_lock`, `gift_sfence_nachbar_mfence`,
   `gift_sfence_nachbar_lfence`.
3. **8-issue word-install proof (§§4–5).** Helpers `issueByte_puffer`,
   `issueByte_mem`; `acht_ausgaben_gruppe` (exactly eight byte issues in
   oldest-first order build `wortEintraege a v` with memory and foreign
   buffers untouched); `acht_ausgaben_erreichbar` (the issues form one
   reached run); `wort_installation` (exclusion-checked `DrainSpur` from the
   exact `WortGruppe` installs the whole word unsplit — accepted
   `wort_gruppe_liest_zurueck` — and is reached —
   `drain_spur_erreichbar`); poison `gift_gruppe_verweigert_lock`
   (group and LOCK never overlap); joint non-degenerate witness
   `bind_zeuge` (fence pins + MFENCE lowering + written table
   `witD.schreibt () ()` + reached memory-changing eight-drain from
   `wort_gruppe_liest_zurueck_zeuge`).

## Exact new names

Definitions: `ZaunArt`, `zaunBytes`, `valZaun`.
Theorems: `zaunBytes_mfence/sfence/lfence`, `bind_xadd`, `bind_cas_erfolg`,
`bind_mfence`, `zaun_mfence_dekodiert`, `zaun_sfence_dekodiert`,
`zaun_lfence_dekodiert`, `valZaun_korrekt`, `zaun_sfence_korrekt`,
`zaun_lfence_korrekt`, `zaun_sfence_ohne_sse`,
`zaun_sfence_puffer_verweigert`, `gift_lfence_pilot`, `gift_lfence_lock`,
`gift_sfence_nachbar_mfence`, `gift_sfence_nachbar_lfence`,
`issueByte_puffer`, `issueByte_mem`, `acht_ausgaben_gruppe`,
`acht_ausgaben_erreichbar`, `wort_installation`,
`gift_gruppe_verweigert_lock`, `bind_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineAtomicsBind.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (whole `grammatik/`): `Build completed successfully (627 jobs).`
- `#print axioms` for every main theorem: only subsets of
  `[propext, Classical.choice, Quot.sound]` (standard; e.g. `bind_zeuge`:
  `[propext, Quot.sound]`). No new axioms. No `sorry`/`admit`/`native_decide`.
- Every premise of every new theorem is used by its proof (one linter
  warning of this kind was found during development and repaired by moving
  the redundant premises into the conclusion of `zaun_sfence_korrekt`).
- Inhabitation: `bind_zeuge` instantiates the fence pins, the MFENCE
  lowering, a written table, and a reached run with a memory-changing step
  (byte 0 changes). No new theorem quantifies over program syntax, and the
  task names no `ZEUGE:` target, so no further mechanical witness duty applies.

## What remains open (also in the file CUTS)

- No `execBlock` correspondence for atomics (pipeline fragment covers integer
  slots only; per-access facts, never a block run).
- No CAS *failure* binding at register level (success only; failure stutter
  stays lane-1163 `cas_korrekt_fehlschlag`).
- No SFENCE/LFENCE bracket for lock sections (sections stay MFENCE-bracketed).
- No seq_cst total order, fairness, CAS retry bound, timing/cost, interrupts,
  devices, MMIO, DMA.

## Task remarks (nothing believed wrong)

- The CONTEXT asks for "a correctness theorem in the style of
  `pipeline_correct_entry` (source `execBlock` ...) and a refusal theorem
  (`pipeline_refuses_*`)". An `execBlock` run over atomics does not exist in
  the accepted fragment (integer slots only, per `Pipeline.lean` CUTS), so a
  block-level closing theorem would have required a second source interpreter
  (explicitly forbidden) or a desired-correctness premise (explicitly
  forbidden). I proved per-access correspondence + refusal theorems instead
  and recorded the boundary honestly in CUTS. If the coordinator wants a
  block-level statement, that needs a fragment extension first.
- One permission-classifier rejection hit a `bash`-based `rg` search
  mid-lane; the same searches via `Read` worked. No blocker resulted.
- The deliverable is Lean-only as specified (Rust out of scope); no
  `./cargo-pruef` or `./emission-pruef` was applicable (no Rust touched).
