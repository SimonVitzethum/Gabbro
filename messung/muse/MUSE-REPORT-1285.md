# MUSE-REPORT-1285: FS/GS segment bases and the TLB

Clone: `/home/simon/Dokumente/gabbro-muse/a1285`, branch `muse/1285`.
Owned files only: `grammatik/Grammatik/X86/HwSegTlb.lean` (new, ~710 lines),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was built

`Gabbro.Grammatik.X86` extension in two independent parts, connected to the
coherent `HwMaschine`/`HwSchritt` (`HardwareExecution`, lifted unchanged):

**Part 1 — segments (§§1–2).** `SegWahl` (`.kein`/`.fs`/`.gs`); MSR addresses
`msrFsBasis/msrGsBasis/msrKernGsBasis` (C0000100/101/102, pairwise distinct:
`msr_basis_verschieden`); prefix decoder `segPraefix` (0x64 FS, 0x65 GS,
else none) with pins `segPraefix_fs/gs` and the CS/DS/ES/SS refusal
`segPraefix_ignoriert` (2E/26/36/3E name no base — ignored in 64-bit mode);
per-core `SegKern` (both bases, SWAPGS peer, CPUID + CR4 bits);
`fsgsbaseFreigabe` gate with gated writes `schreibeFsBasis/schreibeGsBasis`,
reads `liesFsBasis/liesGsBasis`, round trips `schreibeLiesFsBasis/GsBasis`
and four planted gate-closed refusals; `tauscheGs` (SWAPGS) with
`tauscheGs_involution` and `tauscheGs_tauscht`. NEW address
`adrEffSeg` over the accepted `adrEff` (lifted, never redefined) with
`adrEffSeg_ohne` (no override = old) and `adrEffSeg_basis_null` (zero base
= old, either segment), plus closed shift pins (`segPin_fs_verschiebt`:
`100 → 8292` with FS 8192; `segPin_ohne_bleibt`).

**Part 2 — TLB (§3).** 4 KiB pages (`seitenNr/seitenOffset`, pins for
8197 = page 2 + offset 5); entries `TlbEintrag` (page → frame);
`physAddr` (pin: frame 7 + offset 5 = 28677); `tlbSuche` (first match);
walk PARAMETER `SeitenDurchlauf` (never defined — HwPaging owns it);
`tlbAufloesung` with `tlbAufloesung_trifft` (hit answers from cache
whatever the walk says — the stale-entry rule) and
`tlbAufloesung_verfehlt` (miss walks); `tlbEntfernen` (INVLPG) with
`tlbEntfernen_sucht_verfehlt` and the re-walk theorem
`tlbNachEntfernen_geht_durch`; `tlbGlobal` constantly false (PCID off,
`tlbGlobal_aus`); `tlbCr3Spuelung` (non-global flush) with
`tlbCr3Spuelung_leert`; `tlbEntfernen_lokal` (no cross-core effect).
Closed pins: stale use (`tlbAufloesung_veraltet_pin`: walk moved to frame
7, cached frame 3 still answers), INVLPG shape, re-walk, CR3 emptying.

**Connection (§4).** `SegTlbMaschine` (coherent machine + per-core
`SegKern` + per-core TLB, untouched profiles); `SegTlbWf` (= `HwWf`);
`SegTlbEreignis` (wrFs/wrGs/swapgs/invlpg/cr3 + lifted `hwSchritt`);
`SegTlbSchritt` with exact embedding `segTlbSchritt_hw_einbettung`,
preservation `segTlbSchritt_wf` (coherent leg reuses `hwSchritt_wf`),
forward agreements `segTlb_wrFs_vereinbarung`,
`segTlb_invlpg_vereinbarung`, `segTlb_cr3_vereinbarung`, and no-step
refusals `segTlb_wrFs_verweigert`, `segTlb_wrGs_verweigert`.

**Witness (§§5–6).** `segTlb_zeuge` joins: wf, segmented address
`rbx + FS = 8 + 8192 = 8200`, TLB hit resolving to 8200, buffered issue
of 42 with owner-only forwarding (core 0 sees 42, core 1 sees 0), drain
changing shared memory 0 → 42, start byte 0, and a reached
`.invlpg 0` step whose successor re-walks to 8200. Non-degenerate:
two cores, memory-changing reached run.

## Checks

- `./lean-probe grammatik/Grammatik/X86/HwSegTlb.lean`: 0 errors, no warnings.
- `./lean-bau` (full project): `Build completed successfully (659 jobs).`
- Axioms: none / `[propext]` / `[propext, Quot.sound]` only (subset of the
  `gabbro_ziel` standard). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  no `Prop`-typed premise; every proof premise is used.
- One collision found by the full build and repaired: `witMem`/`witKern`/
  `witBytes` already exist in other X86 modules, so all witness defs carry
  the `segTlb` prefix. Single-file probing cannot see this — full `lean-bau`
  is mandatory before claiming green.

## Open / findings

1. **No SDM provenance.** The clone's `.tmp/HARDWARE-REFERENCES/` extracts
   could not be opened in this lane (permission classifier denied access on
   two attempts; no workaround attempted). Unlike lane 660 no SDM
   edition/offset is cited: every silicon fact (MSR addresses, prefix
   opcodes, gating bits, SWAPGS/INVLPG/CR3 semantics, PCID off, stale-use,
   no-shootdown, ignored CS/DS/ES/SS) is a NAMED ASSUMPTION in CUTS, not
   checked provenance. Re-check against SDM 325462-093US before claiming more.
2. **No privilege model.** SWAPGS has no CPL-0 gate; #GP/#UD are not wired
   into `HwSchritt.fehler`. SWAPGS `tauscheGs` always succeeds in the model.
3. **No walk, no global pages, no limits/modes.** Walk is a parameter;
   `tlbGlobal` is constantly false (PCID off); no segment limits, no
   16/32-bit modes, no canonical-address check on the base addition.
4. **No W/GX bridge**, no source/checker/contract/entry/ABI/loader/budget link.
5. **Nothing in the task looked wrong.** One process note: a `./lean-probe`
   run timed out silently at 10 min (build-slot contention, file innocent);
   retry with a longer budget succeeded. And: single-file green does not
   imply project green (the `witMem` collision) — always finish with
   `./lean-bau`.
