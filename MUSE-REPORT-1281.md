# MUSE-REPORT-1281: Sign-extend-accumulator ops and register XCHG

Lane 1281, clone `/home/simon/Dokumente/gabbro-muse/a1281`, branch `muse/1281`.
Owned files only: `grammatik/Grammatik/X86/IntSignXchg.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

NEW FILE `grammatik/Grammatik/X86/IntSignXchg.lean` (~1620 lines),
following the structure of the accepted `HwMulDivWidth.lean`
(dispatcher-first, lift-don't-redefine, adapter plug, joint witness).
It connects one family to the coherent `HwMaschine`: CBW/CWDE/CDQE,
CWD/CDQ/CQO, register XCHG (`86`/`87` ModRM-reg, `90+r`), and
register MOVSXD (`REX.W 63 /r`).

- §1 value dispatch: fresh `cbwWert`/`cbwSchritt` (AL→AX merged),
  `cwdWert`/`cwdSchritt` (AX-sign broadcast into DX, merged),
  `sxXchgSeite`/`sxXchgSchritt` (8/16-bit merge, 32-bit
  zero-extends both sides, 64-bit whole; both sides read OLD
  values), `movsxdSchritt` (full `sext .b32` word write).
  `sxSchritt` over `MulDivErgebnis`; the cwde/cdqe/cdq/cqo arms
  ARE the accepted `wdSchritt` vor98/vor99 arms on the same length.
- §2 lift agreement: `sx_cwde_ist_vor98`, `sx_cdqe_ist_vor98`,
  `sx_cdq_ist_vor99`, `sx_cqo_ist_vor99` (all `rfl`-shape).
- §3 read-back (`sxXchgSchritt_eq`, `sxXchgSchritt_bei_a_neq`,
  `sxXchgSchritt_bei_c`), flag/memory silence of every fresh shape,
  6 `decide` value pins.
- §3b accepted-XCHG bridge (see "task feedback" below):
  `pin_xchgAkzeptiert_dekode` (shared bytes decode in
  `decodeXchg` too) and `sxXchg64_ist_reg` (the 64-bit arm IS the
  accepted `XchgForm.reg` swap).
- §4 step-level `sxSchritt_flags`, `sxSchritt_memory`
  (fresh arms by shape, lifted arms via `wdVor98_flags/memory`,
  `wdVor99_flags/memory`).
- §5 no-shadowing: 16 × `decodeExt … = none` (`ext_weist_sx*_zurueck`).
- §6 decoder `decodeSx` reusing accepted `nimmPraefix`/`wdBits`/
  `codeReg`/`modrmReg`. Bare `90` (no prefix at all) is `nop`;
  the 32-bit self-exchange stays reachable via redundant-REX
  `[0x40, 0x90]`. `90+r` has three constructors
  (`xchgRax16/32/64`) because no 8-bit form exists.
- §7 canonical encoder `sxEncode` reusing accepted `wdRex`.
- §8 16 accept pins + 9 refusal pins + 3 encoder pins (all `decide`).
- §9 generic round-trips with suffix (`sxRoundtrip_*`,
  `cases … <;> rfl` idiom).
- §10 dispatcher `decodeSignXchg` (Ext first) with
  `decodeSignXchg_prefers_ext/_sx/_nichts` and 6 dispatcher pins.
- §11 `sxHwSchritt` + 4 selection theorems,
  `sxSchritt_kein_halt` (no fault class on admitted forms).
- §12 named refusals: `SxGrund`
  (lockPrefix/memoryOperand/overdetermined/movsxdWithoutRexW/
  truncated), generic `decodeSx_lock`, `decodeSx87_mem`,
  `decodeSx86_mem`, `decodeSx63_mem`, and the checked
  `sxGrundTabelle`/`sxTabelle_verweigert` (one `decide` over the
  table: every tabled input refuses).
- §§13–14 `adapterSignXchg : HwAdapter SxDecodiert` (`_wf`, `_ok`,
  `_proj`, `_verweigert_bei_laenge` via `sx_laenge_misslungen`)
  and `sxHwRegSchritt : … → HwRegAusgang` (weiter/halt/verweigert
  selection, `halt_ist_kein_weiter`, `weiter_wf`).
- §15 joint witness `sxHw_zeuge`: CBW on core 0 (AX=`0xFFFF`),
  32-bit exchange on core 1 (EAX=`0xAABBCCDD`, ECX=`0x55667788`),
  MOVSXD on core 1 (RDX=`0x55667788`), owner-only forwarding of
  byte 42, drain changing shared memory 0→42, `HwWf`, bad-length
  refusal, LOCK refusal through the dispatcher.
- CUTS block + `#print axioms` for every main theorem (all
  `propext`-only or `propext + Quot.sound`: subset of the standard
  goal axioms, no `Classical.choice` needed).

## Verification

- `./lean-probe grammatik/Grammatik/X86/IntSignXchg.lean`:
  `== 0 error(s) …, exit 0` (only benign `unusedSimpArgs`
  linter warnings in `sxSchritt_kein_halt`: `cases`-substitution
  already discharges those goals).
- `./lean-bau`: `Build completed successfully (659 jobs).`
  (after the rename fix below; first attempt failed on the name
  collision, caught by the build as designed).
- No Rust changes; `cargo-pruef`/`emission-pruef` untouched by
  this lane (Lean-only deliverable, no checker rules).

## Task feedback (things in the task that were wrong)

1. "This instruction family has NO model yet" is inaccurate for
   64-bit XCHG: `grammatik/Grammatik/X86/XchgOrderNeed.lean`
   (lane 779) already models `XchgForm.reg` (pure 64-bit swap)
   with a `REX.W + 87` codec, plus the memory form with its
   barrier. The first full `lean-bau` caught my duplicate
   `xchgSchritt` name. Resolution: renamed mine to
   `sxXchgSchritt`/`sxXchgSeite`, proved `sxXchg64_ist_reg`
   (my 64-bit arm IS the accepted swap), pinned the shared
   bytes in both decoders, and left its memory/barrier/alias
   business untouched. Genuinely new here: 8/16/32-bit XCHG,
   `90+r` incl. the exact bare-`90`-is-NOP rule, the whole
   CBW/CWD/CWDE/CDQE/CDQ/CQO + MOVSXD coverage, and the
   `HwAdapter`/dispatcher connection (none of which 779 has).
2. MOVSXD is not in `NarrowOps.lean` (only the generic
   `loadNarrowExtend` helper, which has no decode); the `63`
   form is defined here as instructed, reusing `sext`.
3. SDM provenance: I could not re-check the supplied extracts —
   a tool-permission classifier rejected the search call over
   `.tmp/HARDWARE-REFERENCES/`, and I did not work around it.
   Provenance therefore rests on (a) the accepted files' cited
   rows (`MulDivWidthHardwareForms` 98/99 with SDM line refs;
   `XchgOrderNeed` header with XCHG/LOCK volume refs, whose
   NOP-alias and implicit-LOCK rules this file models exactly),
   and (b) standard opcode knowledge, all labeled as
   self-consistency only in CUTS. No silicon correspondence is
   claimed.
4. Two implementation findings worth keeping: (a) `Nat.decLt`
   (`<`/`≤` on literals) blows the kernel recursion limit inside
   `rfl` round-trips over match-compiled decoders, while
   kernel-accelerated `/`/`%`/`==` do not — the `90+r` range
   test is `byteNat op / 8 == 18` for this reason; (b) a
   multi-line `{ s with … }` update whose continuation line
   starts with `(` misparses — all such updates here are
   single-line with `let`-bound values.
5. Lean slot contention: several probes needed 15–60 min
   queue waits (single `lean-slot` shared across lanes);
   background launching is not permitted in this environment,
   so each check blocked the turn. No filler work was started.

## Open (not claimed)

See CUTS: no silicon proof; documented over-refusals (non-`0x48`
REX on 98/99, `66`+REX combos, REX-without-W on 87, REX.X,
MOVSXD without REX.W/with `66`); no XCHG-mem (locked
families) and no MOVSXD-mem (TSO read path open); no
source/IR/loader/entry/budget link; no W/GX bridge; no timing.
