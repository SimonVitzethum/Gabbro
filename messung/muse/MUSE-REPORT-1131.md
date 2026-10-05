# MUSE-REPORT-1131: SIMD integer forms and enabled-state gates on the coherent machine

Lane 1131, clone /home/simon/Dokumente/gabbro-muse/a1131, branch muse/1131.
Owned files only: `grammatik/Grammatik/X86/HwVector.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Lifted every accepted packed-integer row (lane 686 `IntVecOp`:
PADDB/W/D/Q, PAND/POR/PXOR, PSLLQ/PSRLQ with register count and imm8,
MOVDQA/MOVDQU 128-bit load/store) onto the coherent machine
(`HwMaschine`/`HwSchritt`, lane 660), reusing the accepted definitions
unchanged (never copied a model):

- **TSO byte layer (§§1-5).** `vecByte`/`vecEintraege` (sixteen canonical
  entries, low chunk then high chunk — entry bytes ARE chunk bytes by
  construction), footprint membership (`vecEintraege_mem_fuss` over the
  accepted `vecFuss`), per-byte permission helpers (`lesbar8_einzeln`,
  `schreibbar8_einzeln`), `vecSpeichern` (sixteen `issueByte` folds via
  the accepted `issueListe`, never the direct `vecWrite` effect),
  `ladeAcht`/`vecLaden` (eight-plus-eight `loadByte` observations with
  forwarding, joined to the packed word), `drainListe` with frame
  (`drainListe_rahmen`), latest-writer installation
  (`drainListe_schreibt_allg`), low/high split (`vecEintraegeLo/Hi`,
  `vecEintraege_zerlegt`), cross-chunk separation
  (`vecLo_fremd_hi` via accepted `vecChunks_disjoint`), entry uniqueness
  (`vecEintraege_nodup_addr`), and the tearing table (`vecDrain_teilt`:
  low bytes new, high bytes old after eight drains; `vecDrain_schreibt`
  for full drains). NO whole-vector atomicity claimed anywhere.
- **Machine lift (§§6-7).** `vecRegSchritt` (eleven register rows through
  the accepted `stepIntVec` over the core projection),
  `vecLadeSchritt`/`vecSpeicherSchritt` (four memory rows through the
  TSO folds with length/legacy/`#GP` gates), event type
  `HwVecEreignis` (CPU/control inputs ride the event), adapter plug
  `adapterVec`, extended step relation `HwVecSchritt` with exact
  embedding (`hwVecSchritt_einbettet`) and projection
  (`hwVecSchritt_projiziert`), well-formedness preservation
  (`hwVecSchritt_wf`), and fn-to-relation bridges
  (`vecReg_ist_schritt`, `vecLade_ist_schritt`,
  `vecSpeichere_ist_schritt`).
- **Agreement (2).** `vecRegSchritt_gleich` (plug IS the accepted
  equation), `vecRegSchritt_speicher`, `vecLaden_ist_vecRead` (load
  observes the accepted `vecRead` value under empty footprint buffers),
  entry bytes = chunk bytes by construction, shared PXOR/PADDQ rows
  agree with the accepted gated steps
  (`vecRegSchritt_pxor_agree`, `vecRegSchritt_paddq_agree`), fetch
  bridge (`hvec_fetch_bruecke`: length from the fetch discipline, gate
  recovered from the successful step, never assumed).
- **Refusals (3).** Length (`vecReg_laenge_verweigert`), legacy gate
  (`vecReg_profil_verweigert`) with each side planted separately
  (`vecReg_ohne_cpu/kontrolle/osxmm/merkmal`), `#GP`
  (`vecLadeSchritt_gp_a`, `vecSpeicherSchritt_gp_a`), per-byte
  permissions (`issueListe_verweigert`, `vecSpeicherSchritt_schreibrecht`,
  `ladeAcht_verweigert`, `vecLadeSchritt_leserecht`), adapter refusals
  (old events, bare refusals, mismatched cores), plus reused planted
  negatives (overlap alias, AVX row, unified-dispatcher disjointness,
  saturate-not-mask).
- **Witness (4).** `hvecWit_zeuge`: two cores, fetched `paddb` bytes
  (lane 0 wraps `0xFF + 0x02` to `0x01`, lane 1 adds independently),
  sixteen-issue `movdqa` store, owner-only forwarding (core 0 reads
  `0x01`, core 1 reads `0`), drain changes shared memory `0 -> 0x01`
  observed from both cores, torn halfway state standing, core-1 fetch
  refusal, both `HwVecSchritt` steps, and the alias/AVX/disjointness
  refusals beside it. Companion `_zeuge` for `vecRegSchritt_gleich`,
  `vecLaden_ist_vecRead`, `vecDrain_schreibt`, all on this
  non-degenerate run. Ends with a `CUTS:` block and `#print axioms`
  per main theorem.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwVector.lean`: 0 errors.
- `./lean-bau` (full project): **Build completed successfully (601 jobs).**
- `#print axioms`: every main theorem depends only on `[propext]`
  and/or `[Quot.sound]` — a subset of the standard
  `propext, Classical.choice, Quot.sound`; no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` in the file.
- Deliberate reuse (no duplication): `issueListe_mem` and
  `issueListe_anderer_kern` from `ConcurrentIntegerExecution`
  (added that import; verified no import cycle); everything else
  reuses the accepted family/coherent-machine lemmas by name.

## What remains open (see CUTS in the file)

No hardware correspondence beyond the accepted rows; no vector
atomicity; no per-access target-to-W/GX simulation, source/IR/loader/
budget link, progress or call-log transfer; LOCK/RMW refused; AVX row
refused; legacy YMM upper bits unmodelled; timing/power absent.

## Task feedback

Nothing in the task was found wrong. Two readings worth recording:
(1) the "event type and HwAdapter (or extended step relation)" clause
was read as inclusive — both are delivered, with the adapter as the
executable face and the relation as the semantic object, connected by
proved bridges; (2) the shared PXOR/PADDQ rows are proved to ride the
new plug identically to the old gated steps, so the pre-existing
two-row coverage is preserved, not shadowed.
