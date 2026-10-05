# MUSE-REPORT-1286: exact review of candidate 1285 (FS/GS segment bases and the TLB)

Clone verified: `/home/simon/Dokumente/gabbro-muse/a1286`, branch `muse/1286`
(toplevel and branch both match; mismatch STOP did not trigger).
Own file: this report only. No other file touched (`git status --short` clean
before writing it).

CANDIDATE: 1285, pinned HEAD `33b40c50ecb9c9964edd4b0a7a54f7c2fba4381e`,
base `738366545afbddf7ac664db92804703db24f8868` (from
`.tmp/review/SNAPSHOT.json`). Files in candidate: `MUSE-REPORT-1285.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwSegTlb.lean` (new,
711 lines). Reviewed from the exact snapshot diff only
(`.tmp/review/author-1285/PATCH.diff` plus the snapshotted files); the author
clone itself was not accessed.

## Checks performed

- Grep over the candidate file for
  `sorry|admit|axiom |native_decide|unsafe|split_ifs`: zero matches.
- `PATCH.diff` for `grammatik/Grammatik.lean`: exactly one added line,
  `+import Grammatik.X86.HwSegTlb`, appended after `import Grammatik.X86.Avx2State`
  at end of file. No other existing file touched.
- Axioms per `BUILD-EVIDENCE.json` final probe: every printed theorem is
  `no axioms`, `[propext]`, or `[propext, Quot.sound]` — a subset of the
  `gabbro_ziel` standard (`propext, Classical.choice, Quot.sound`).
- Lifted-not-copied: `adrEff`, `basisKeinForm` (AddressEncoding),
  `HwMaschine`, `HwWf`, `HwSchritt`, `HwEreignis`, `hwSchritt_wf`,
  `projZustand`, `tsoAnsicht` (HardwareExecution), `issueByte`, `loadByte`,
  `flushKern` (TSO) all exist in this clone's base tree and are referenced,
  never redefined, by the candidate.
- Silicon spot-checks against `.tmp/HARDWARE-REFERENCES/`
  (edition `325462-093US, September2026` per `REFERENCES.json`):
  SWAPGS exchanges GS base with `IA32_KERNEL_GS_BASE` at `C0000100+2H`;
  VM-exit field names `C0000100H`/`C0000101H` as the FS/GS base MSRs;
  FSGSBASE gating is `CPUID.07H:EBX[0]` plus `CR4[16]`;
  `64H` is the FS override prefix; CS/DS/ES/SS bases are treated as zero
  in 64-bit mode while FS/GS overrides apply their bases; INVLPG
  invalidates TLB entries for the addressed page and is privileged.
  All match the candidate's definitions (`msrFsBasis/msrGsBasis/
  msrKernGsBasis`, `segPraefix`, `segPraefix_ignoriert`, `fsgsbaseFreigabe`,
  `tauscheGs`, `tlbEntfernen`, stale-use rule). The candidate cites no
  per-fact SDM offsets and says so openly (CUTS provenance gap); every
  silicon fact is a named assumption, no hardware correspondence claimed.
- `./lean-bau` in this reviewer clone (base without candidate):
  `Build completed successfully (666 jobs).`
  Wrapper first line: `== exit 0; 0 error line(s) in the COMPLETE output`.
  The candidate's own full build is taken from its build evidence
  (`Build completed successfully (659 jobs)` after the `witMem` rename
  repair); this clone holds no candidate sources to rebuild, and the merge
  gate rebuilds anyway. Job-count difference (666 vs 659) is base movement,
  not a finding.

## Requirement-by-requirement

1. Segments: MSRs `C0000100/101/102` with `msr_basis_verschieden`;
   prefixes `segPraefix` (`segPraefix_fs/gs`, `segPraefix_ignoriert`
   for 2E/26/36/3E); CPUID+CR4 gate `fsgsbaseFreigabe` with round trips
   `schreibeLiesFsBasis/schreibeLiesGsBasis` and four planted refusals;
   `tauscheGs` with `tauscheGs_involution`/`tauscheGs_tauscht`.
2. NEW `adrEffSeg` over lifted `adrEff` with `adrEffSeg_ohne` and
   `adrEffSeg_basis_null` (zero base = old address), plus closed pins
   `segPin_fs_verschiebt` (`100 -> 8292`) and `segPin_ohne_bleibt`.
3. TLB: 4 KiB pages, `TlbEintrag`, `tlbSuche`, walk kept as parameter
   `SeitenDurchlauf` (never defined), `tlbAufloesung_trifft` (hit answers
   from cache — the stale-entry rule), `tlbAufloesung_verfehlt`,
   `tlbEntfernen_sucht_verfehlt`, re-walk `tlbNachEntfernen_geht_durch`,
   `tlbGlobal_aus` (PCID off), `tlbCr3Spuelung_leert`, `tlbEntfernen_lokal`.
4. Connection: `SegTlbMaschine` beside untouched `HwMaschine`,
   `SegTlbSchritt` with exact embedding `segTlbSchritt_hw_einbettung`,
   preservation `segTlbSchritt_wf` (coherent leg reuses `hwSchritt_wf`),
   agreements `segTlb_wrFs_vereinbarung`/`segTlb_invlpg_vereinbarung`/
   `segTlb_cr3_vereinbarung`, no-step refusals `segTlb_wrFs_verweigert`/
   `segTlb_wrGs_verweigert` (gate-closed writes genuinely impossible:
   `schreibeFsBasis/schreibeGsBasis = none` contradicts `some k'`).
5. Witness `segTlb_zeuge` is non-degenerate: two cores, segmented address
   `8 + 8192 = 8200`, TLB hit to 8200, buffered issue of 42 visible to
   owner only (core 0 sees 42, core 1 sees 0), drain changing shared
   memory `0 -> 42` with start byte pinned at 0, and a reached
   `.invlpg 0` step whose successor re-walks to 8200.
6. CUTS block honest: walk/privilege/global-pages/limits/modes/W-GX all
   disclaimed; `#print axioms` for every main theorem present.

## Notes (not defects)

- `adrEffSeg_basis_null` takes both `hfs` and `hgs`; the `.kein` branch
  closes via `adrEffSeg_ohne` without them, the `.fs`/`.gs` branches use
  one each. Joint premise use across branches; acceptable.
- No privilege gates (SWAPGS/INVLPG are CPL-0 per the extracts) and no
  canonical-address check: disclosed in CUTS, not requested by the task.
- `65H = GS` was not individually grep-confirmed in the extracts (64H = FS
  and the ignored-base rule were); it is standard and consistent with the
  `segPraefix_gs` pin. No reason to doubt.
- Nothing in the lane task looked wrong.

## VERDICT: ACCEPT
