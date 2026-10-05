# MUSE-REPORT-1243: AVX2 32-byte memory accesses on the TSO machine

Clone: `/home/simon/Dokumente/gabbro-muse/a1243`, branch `muse/1243`.
Owned files only: `grammatik/Grammatik/X86/Avx2Mem.lean` (new, ~2390 lines),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

VMOVDQU (no alignment requirement) and VMOVDQA (32-byte alignment, else #GP)
loads/stores as footprint-checked accesses on the coherent machine
(`HwMaschine`/`HwSchritt`, lane 660) over the accepted canonical TSO byte
equations. A 32-byte store is `issueListe` over 32 byte entries in the acting
core's buffer; loads are 32 `loadByte` observations with forwarding; drains
are oldest-first `flushKern` folds. No whole-vector atomicity is claimed
(tearing table proved). Enabled only by the NAMED CPU profile plus
CPUID/XCR0/OS-state gates; absent form = refused encoding.

Key design decisions (all documented in the file header and CUTS):

- YMM value = two accepted 128-bit `Vektor` halves (`Avx2Vektor.mk lo hi`);
  entry bytes ARE accepted chunk bytes by construction
  (`wortByte` over `vLo`/`vHi`). No YMM register file exists here --
  register-file binding stays with the State lane, decode/encode with the
  Vex lane, lane arithmetic with the Ops lane. None of the three sibling
  lanes is imported or depended on.
- Store values are handed to the plug; loads are state-unchanged
  observations (the adapter returns `some m` exactly where `avx2Laden`
  succeeds; the observed value lives in the `HwAvx2Schritt` relation).
- Gate `avx2MemZugelassen` = named profile (`Avx2Profil`, only
  `avx2ProfilName = 7` enables) AND accepted `stufenCpuBereit cpu x .avx256`
  (AVX silicon bit + XCR0 XMM+YMM) AND `kontrollSseFrei` + `cr4Osxsave`
  AND `merkmalZugelassen hw b .paketInt128` (carries OS vector state).
- The accepted 256-bit refusals elsewhere (`stufe_avx256_verweigert`,
  `avx2_reihe_verweigert_immer`) are untouched: this gate is a strictly
  stronger opt-in case and weakens no existing refusal.
- Page-crossing/permission faults refuse with memory unchanged: the issue
  fold returns `none` (carries no state) and every missing byte permission
  refuses by name (`avx2Speichern_verweigert_bei`,
  `avx2SpeicherSchritt_schreibrecht`, `avx2LadeSchritt_leserecht`).

## New definitions/theorems (selection)

Forms/faults: `Avx2MemForm`, `avx2GpFehler`, `avx2Gp_nie_unausgerichtet`,
`avx2Gp_ausgerichtet_fehler`, `avx2Gp_ausgerichtet_ok`.
Values/entries: `Avx2Vektor`, `avx2Wort`, `avx2Chunk`, `avx2EintraegeC0..C3`,
`avx2Eintraege`, `avx2EintraegeLo/Hi`, `avx2Eintraege_laenge/_zerlegt`.
Footprint/no-wrap: `avx2Fuss`, `avx2Fuss_halb` (two accepted `vecFuss`),
`avx2Eintrag_mem_c0..c3`, `OhneUmbruch32`, `avx2Chunk_nat`,
`avx2Chunk_ohneUmbruch`, `avx2Chunk_disjunkt`,
`avx2Eintrag_klass(_c0..c3)`, `avx2Eintraege_mem_fuss`,
`avx2Eintraege_nodup_addr`.
Gate: `avx2ProfilName`, `Avx2Profil`, `avx2ProfilFreigegeben`,
`avx2MemZugelassen`, `avx2Mem_braucht_profil/cpu/kontrolle/merkmal`,
`avx2Mem_ohne_profil/cpu/kontrolle/merkmal`, witness readiness
`avx2WitCpu/Xcr0/Profil`, `avx2Wit_gate`, `avx2Wit_neg_cpu/xcr0/profil`.
Stores: `avx2Speichern`, `avx2Speichern_haengt_an/_kein_speicher/_erfolg`,
`avx2IssueListe_erfolg/_verweigert`, `avx2Speichern_verweigert_bei`,
`avx2Eintraege_mem_c0..c3_entry`, `avx2Schreibbar8_einzeln`,
`avx2Lesbar8_einzeln`, `avx2Schreibbar_einzeln`, `avx2Lesbar_einzeln`.
Loads: `avx2AchtFun`, `avx2Acht`, `avx2Acht_ist_read64`,
`avx2Acht_verweigert`, `avx2Laden`, `avx2Read` (two accepted `vecRead`),
`avx2Laden_ist_avx2Read`, `avx2Laden_verweigert_lo`.
Forwarding/foreign: `avx2Neuestens_append_rechts`, `avx2Neuestens_mem`,
`avx2Weiterleitung_sub`, `avx2Weiterleitung`, `avx2FremdAlt_byte`.
Grouping: `Avx2FremdFrei`, `Avx2Gruppe`, `avx2Teilwort_keine_gruppe`,
`avx2Gruppe_verweigert_bei_fremdeintrag`.
Drains/tearing: `avx2Drain`, `avx2Drain_rahmen`, `avx2Drain_schreibt_allg`,
`avx2Drain_schreibt`, `avx2Eintrag_klass_lo`, `avx2Lo_mem_c0_entry`,
`avx2Drain_teilt16`.
Machine: `Avx2MemEreignis`, `avx2SpeicherSchritt`, `avx2LadeSchritt`,
`adapterAvx2Mem`, `adapterAvx2Mem_verweigert_alt/_fehler`,
`adapterAvx2Mem_fremder_kern_speichere/_lade`,
`adapterAvx2Mem_speichere/_lade`, `HwAvx2Schritt` (arms `alt`,
`speichereA/U`, `ladeA/U`, `fehler`), `hwAvx2Schritt_wf`,
`hwAvx2Schritt_einbettet/_projiziert`, `avx2Speichere_ist_schritt`,
`avx2Lade_ist_schritt`, `avx2SpeicherSchritt_gp_a`,
`avx2LadeSchritt_gp_a`, `avx2SpeicherSchritt_profil`,
`avx2LadeSchritt_profil`, `avx2SpeicherSchritt_schreibrecht`,
`avx2LadeSchritt_leserecht`.
Witness: `avx2WitAdr/FehlAdr/Daten/Mem/V/S0/S1`, `avx2Wit_s1_buflen`,
`avx2Wit_weiterleitung` (owner forwards whole value),
`avx2Wit_fremd_alt` (core 1 reads zero), `avx2WitDrain/DrainLo`,
`avx2Wit_spuelung_aendert_speicher/_letzt`, `avx2Wit_fremd_neu`,
`avx2Wit_teil_neu/_alt`, `avx2WitStart(_wf/_eff/_perm0..3/_gate_m)`,
`avx2Wit_store_schritt` (plug reaches 32-entry successor + step),
`avx2Wit_fehler_schritt`, and the joint `avx2Wit_zeuge` (15 conjuncts:
two cores, buffered 32-byte store, owner-only forwarding, memory-changing
drain observed from both cores, torn halves, alignment/gate/profile
refusals, well-formedness).

## Checks

- `./lean-probe grammatik/Grammatik/X86/Avx2Mem.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
  (plus two benign unused-variable linter warnings in the grouping
  section and the `#print axioms` listing).
- `./lean-bau`: `== exit 0; 0 error line(s)`, `Built Grammatik (642 jobs)`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file
  (verified by search).
- `#print axioms` for all 39 main theorems: every one is within
  `propext`, `Classical.choice`, `Quot.sound` (the goal-allowed set);
  many depend on no axioms at all. No premise is `Prop`-typed; every
  premise is used.
- Silicon provenance: Intel SDM 325462-093US September 2026, clone-local
  `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, sha256-verified
  2026-10-02). The encoded facts (VEX.256 32-byte moves, VMOVDQA #GP on
  32-misalignment, VMOVDQU alignment-free, AVX CPUID + XCR0 AVX state +
  OSXSAVE gate shape) are stated-not-proved; correspondence is claimed
  nowhere (see CUTS). I could not pull VMOVDQA-specific extract lines:
  the content-search index skips `.tmp`, and reading the 26 MB extract
  blind was not productive; the facts encoded match the long-documented
  Tier-3 shape and the accepted 128-bit analogues.

## Open / not claimed (see file CUTS)

No hardware correspondence; no whole-vector atomicity; no W/GX bridge;
no YMM register-file binding (State lane); no VEX decode/encode (Vex
lane); no lane arithmetic (Ops lane); no fetch pinning of AVX2 forms;
no trap classes beyond #GP-alignment/permission refusals; wrap-around
addressing beyond `OhneUmbruch32` stays open.

## Notes on the task and apparatus (all fine, recorded honestly)

- The task text is accurate; nothing in it looked wrong. Scope
  (Mem only, no dependence on sibling lanes) was respected.
- Two Lean facts that cost time: (1) `++` is LEFT-associative, so
  `List.mem_append` splits peel from the right -- the classification
  proof uses binary `List.mem_append.mp` splits, never n-way `rcases`
  on an assumed association. (2) Two textually identical
  `(0 : BitVec 32)` literals elaborated to reducibly-different terms
  (simp could not rewrite one with the other); an `Eq.trans` term,
  which unifies up to default transparency, closed the step. Both are
  now load-bearing patterns in the file, not workarounds.
- `./lean-probe` and once `./lean-bau`-adjacent probing hit the queue
  timeout under machine load with no slot held; both passed on retry
  with no source change. Transient, not a blocker.
- Whole-value forwarding is proved generally at byte level
  (`avx2Weiterleitung`: every entry byte forwards) and for the whole
  value at the reached witness (`avx2Wit_weiterleitung`, `decide`);
  the bytesWort round-trip arithmetic for a general whole-value
  statement is deliberately not re-proved (witnessed, not
  re-arithmetised -- stated in §9).
