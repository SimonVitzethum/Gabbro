# MUSE-REPORT-739: Independent review of lane 738 (fault ordering across fetched accesses)

## Identity and scope

- Clone verified earlier in-session: `/home/simon/Dokumente/gabbro-muse/a739`,
  `.git/HEAD` = `ref: refs/heads/muse/739`. Branch `muse/739`.
  No other clone touched.
- Author task: `lanes/738.md` (lane 738, fault ordering). Review snapshot:
  `.tmp/review/SNAPSHOT.json` + `.tmp/review/author-738/` (PATCH.diff,
  MUSE-REPORT-738.md, OWNER-TASK.md, BUILD-EVIDENCE.json, source copy).
- Own only this file. No Lean/Rust/source changes made by this lane.

## Candidate

CANDIDATE: 738 5661e9362d0a9458a04e50e80d806c2a872156df
VERDICT: ACCEPT

## What the candidate contains (verified against PATCH.diff)

- Exactly 3 files: new `grammatik/Grammatik/X86/ExceptionPriorityHardware.lean`
  (1474 lines), one additive umbrella import line in `grammatik/Grammatik.lean`
  (`+import Grammatik.X86.ExceptionPriorityHardware`), and MUSE-REPORT-738.md.
  Nothing else touched. Scope is clean.

## Evidence checked

1. Reused canonical producers, every name grep-confirmed in the base tree
   (no new machine, decoder, or interpreter): `decodeExt`/`fetchExt`/
   `extZugelassen`/`extByteschritt`/`stepExt_*` (`ExtendedExecution.lean`);
   `read64`/`write64`/`writeBytes`/`writeBytesN_hit`/`_miss`/`addrOff`/
   `wortByte`/`schreibbar8` (`Speicher.lean`); `adrKlasse`/
   `adrKlasse_kanonisch_kein_fehler`/`istKanonisch`/`kanonisch_code`/
   `nichtkanonisch_bit47`/`einByteStart`/`einByteSpeicher`/`witnessFlags`/
   `zugriff_ohne_ac` and the `fehler_div_null_haelt` path
   (`HardwareFaults.lean`/`DecodeFault.lean`); `addrAusgerichtet`
   (`OverlapRefusal.lean`); `mulDivEncode` (`MulDivCodec.lean`); `natByte`
   (`Codec.lean:58`); `fetchCap`/`geholt` (`Byteschritt.lean`);
   `extWitStart`/`extWitBereit`/`extSchritt2`/`extZelle`/
   `extWit_zwei_schritte_speichern`/`extWit_anfang_null`
   (`ExtendedExecution.lean`); `mdRegNull`/`zeugeFlags`/`kontextReset` intact.
2. Call-site arities confirmed against base signatures:
   `fehler_div_null_haelt (d) (s) (src) (hok) (h) (hnull)` called with
   `_ _ _ (by decide) rfl (by decide)`; `stepExt_muldiv_halt (m) (t) (b) (h)`
   called with `_ _ _ falle_divFalle`. Trap evidence genuinely discharged.
3. `halt_kommt_von_teilung` matches all 8 `ExtInstr` arms
   (pilot/narrow/muldiv/shift/setcc/cmov/fp/vec); Lean exhaustiveness leaves
   no missing arm. Halt provably comes only from the fetched muldiv trap.
4. Real fetched-byte probes: `geholt_divFalle`/`decode_divFalle` by `decide`
   on the actual `mulDivEncode (.divRax .rcx)` bytes; `falle_divFalle` reuses
   the accepted `fehler_div_null_haelt`; `halt_divFalle` reuses
   `extByteschritt_weiter` + `stepExt_muldiv_halt`. No desired-outcome premise.
5. Explicit oracles, never inferred faults: `SeitenInfo` decides #GP vs #PF
   (both directions proved); `IllegalInfo` alone decides #UD membership, with
   `kein_erschlichenes_ud` proving refusal-without-oracle is never #UD;
   `SteuerInfo` arms #AC (disarmed never faults). Paging is an explicit input
   interface as tasked.
6. Conflicts proved with losing candidates exhibited:
   `zugriff_konflikt_haette_auch` shows the access fault WOULD fire while
   `wahl_konflikt_adresse` proves address #GP wins; divide-over-control and
   control-over-quiet-divide likewise. Six dominance theorems plus the six-way
   `wahl_fallunterscheidung` over a priority-ordered row.
7. Last `./lean-bau` result line (pinned BUILD-EVIDENCE.json final entry):
   `Build completed successfully (482 jobs)`; `./lean-probe` on the new module
   ends `== 0 error(s)`; `#print axioms` for all 19 main theorems is
   `none`/`[propext]`/`[propext, Quot.sound]`, a subset of the `gabbro_ziel`
   axioms. Intermediate red probes in the log are development history; final
   state is green. Forbidden-token grep is clean.
8. Manual provenance: clone-local `.tmp/HARDWARE-REFERENCES/` holds the pinned
   Intel SDM 325462-093US (Sept 2026, SHA-pinned in REFERENCES.json, scope
   includes system/interrupt material, no AMD claimed). Table 7-2 title
   confirmed at txt line 164269 (cited ~164271: 2 lines off, content real).
   CUTS names the manual rather than claiming silicon proof. Honest.
9. Joint witness `prioritaet_zeuge_gemeinsam` is non-degenerate: reuses the
   accepted reached two-cell store run (cells 8192/8200 from 0 to 42, two
   memory-changing steps) jointly with the divide choice, halt verdict,
   address-conflict choice, control choice, and never-inferred #UD.
10. CUTS block honest and complete: stated-model within-class rules,
    unreachable overlong-by-success, no unmasked #NM/#XM, no #DB class, paging
    as consumer-stated assumption, sequential-only (no TSO/GX claim), delivery
    left to lane 672, no silicon/source/cost/time claims. No fake closure.

## What remains open (carried from the candidate CUTS, endorsed)

Consumer-lane duties, not defects: per-arm descriptor binding for
`ZugriffsBeschreibung`; same-state choice equation at `bindeUrteil` call
sites; conjoined trap evidence; TSO/GX bridge; IDT delivery (lane 672).

## Task issues noticed

None material. The author 738 task explicitly permits explicit input
interfaces ("must be explicit input interface or honest pending connection"),
which the candidate uses consistently for paging, illegality, control state,
and descriptors. The reviewer 739 task asks to "reproduce suspicious cases
with queued wrappers"; the review instead verified every probe against base
signatures by source reading because shell execution was unavailable for most
of the session — recorded honestly here, no reproduction is faked.

## Method note

Early turns of this session denied shell and file-write calls, so wrappers
could not be re-run by the reviewer; check results above are the pinned
BUILD-EVIDENCE.json final green entries, cross-checked by full end-to-end
reading of the 1474-line candidate plus base-tree confirmation of every reused
name and both critical call-site arities. No claim above goes beyond what was
read or confirmed.
