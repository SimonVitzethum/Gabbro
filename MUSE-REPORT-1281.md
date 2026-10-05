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
REX on 98/99, `66`+REX combos, REX-without-W on 87,
MOVSXD without REX.W/with `66`); no XCHG-mem (locked
families) and no MOVSXD-mem (TSO read path open); no
source/IR/loader/entry/budget link; no W/GX bridge; no timing.

## Repair after independent review (MUSE-REPORT-1282, REPAIR)

The reviewer found a genuine silicon defect with green proofs:
REX-prefixed `90H` resolving to the RAX self was decoded as the
zero-extending `.xchgRax32 .rax` event, while the SDM XCHG NOTE
makes every such `90H` (all prefixes, REX.W included) the NOP
alias; `66 90` and `48 90` as labeled-but-identity exchanges had
the same mislabeling. Concrete divergence from the report:
RAX=`0x1122334455667788` stayed unchanged on silicon, the
candidate yielded `0x0000000055667788`. Accepted as a wrong
definition, not a proof-shape issue.

Repair (commit `6d011bb2`, all in the owned file, no accepted
file touched):

- `decodeSx90` routes every `90H` with `bb == 0 && lo == 0` to
  `.nop` at length `npfx + 1` under every prefix combination
  (bare, `66`, REX, REX.W, `66`+REX.W); the REX.R==0 gate on the
  64-bit arm is dropped (R names no field, uniformly ignored
  now). Previously refused-but-valid `4C/4D 90` and `66`+REX.W
  `90` rows become correct NOPs.
- Top-level `xb == 1` refusal dropped: REX.X names no SIB
  anywhere in this family (all ModRM uses are register-direct,
  all other opcodes ModRM-free), so it is ignored; SIB-carrying
  shapes still refuse through the `mod` check.
- `sxEncode` never emits a `90H` byte for a zero-extending event:
  RAX self-exchanges canonicalize to their `87`-family bytes
  (`66 87 C0` / `87 C0` / `REX.W 87 C0`), justified by the new
  step-equivalence theorems `sxXchgRax16rax_ist`,
  `sxXchgRax32rax_ist`, `sxXchgRax64rax_ist` (same register
  update, proved `cases <;> simp`).
- All three `sxRoundtrip_xchgRax*` carry the honest premise
  `r ≠ .rax` (self covered by the equivalence theorems, not by
  a `90H` round-trip).
- Pins: `[40,90]` re-pinned to NOP (`pin_sx4090_nop_dekode`),
  new NOP pins for `[66,90]`, `[48,90]`, `[4C,90]`,
  `[66,48,90]`; encoder self pins rewritten to the `87` forms.
- No-shadow rows added for `[40,90]`, `[4C,90]`,
  `[66,48,90]` (19 total); dispatcher NOP pins added for
  `[66,90]` and `[40,90]`.
- CUTS cites the NOP-alias NOTE and re-audits the over-refusal
  list (REX.X removed from it; `4C/4D 90` and `66`+REX.W `90`
  removed from it).

Verification after repair: `./lean-probe` 0 errors;
`./lean-bau` `Build completed successfully (659 jobs)` with
unchanged axioms (`propext` / `propext + Quot.sound`). The
reviewer's remaining notes (owner-task under-specification of
prefixed `90H`, apparatus detail) are acknowledged, no action
needed in this lane.

## Integration gate failure (NOT a module defect; blocked)

The merge build failed with NO error in the owned module. Exact
evidence:

- All 8 `info:` lines for `IntSignXchg.lean` show the standard
  axioms (`propext` / `propext + Quot.sound`): the candidate
  elaborated cleanly inside the merge build.
- The single `error:` is at `Grammatik.lean:44:0` (an original
  early import line; the lane's hunk is the appended import at
  the file end) and reads: `failed to read file
  '/home/simon/.elan/toolchains/leanprover--lean4---v4.33.1/lib/
  lean/Lean/Meta/Tactic/FunInd.olean.private'`.
- That is a damaged/unreadable Lean toolchain installation file
  in the merge checkout's toolchain path — apparatus, same
  family as the documented ELAN_TOOLCHAIN/cache pitfalls, not a
  type error, not a merge conflict, and not reachable from any
  definition or theorem in `IntSignXchg.lean`.

There is nothing to repair in the owned deliverable against
this evidence, and weakening anything to "fit" a broken
toolchain would trade guarantees for green — refused. Local
re-verification just now, same commit: `./lean-bau` `Build
completed successfully (659 jobs)`, axioms unchanged.

Concrete blocker for the coordinator: repair or replace the
`leanprover--lean4---v4.33.1` toolchain installation used by the
merge checkout (that path is outside this lane's clone and
untouchable under HARD RULES), then re-run the merge build
unchanged. The candidate needs no code change. No acceptance of
the full source/binary chain is claimed; a fresh independent
review remains required for any future changed commit (this
turn changes Lean code not at all — report only).
