# MUSE-REPORT-1367: Every LOCK-prefixed read-modify-write instruction

## What was done

NEW FILE `grammatik/Grammatik/X86/LockedAllRmw.lean` (~1130 lines, namespace
`Gabbro.Grammatik.X86`) plus one `import Grammatik.X86.LockedAllRmw` line at the
end of `grammatik/Grammatik.lean`. The whole LOCK read-modify-write family as one
vocabulary with canonical encode/decode, an extended decoder chain over the
accepted `kapDecode`, and a `HwAdapter` that admits exactly the accepted 662 rows
and refuses everything else. No existing file was edited except the import line.

- §1 value layer: `lockAllWert` (Group-1 ARE `addB`/`orB`/`adcWert`/`sbbWert`/
  `andB`/`subB`/`xorB`; INC/DEC ARE `incWert`/`decWert`; NEG IS `negW`; NOT IS
  `notB`; BTS/BTR/BTC ARE `btRoh`; XADD installs the sum), `lockAllWertCmp`
  (compare-exchange value), `lockAllCf` (bit-test CF IS `btBit`, else none),
  each with a one-line `rfl` agreement theorem (17 theorems).
- §§2-3 canonical encoder `encodeLockAll` (LOCK, 66H, REX.W prefixes; mod-2
  base-plus-disp32 over rbp; direct 00-3F forms; FE/FF digits 0/1; F6/F7 digits
  2/3; 0F AB/B3/BB; 0F BA plus imm8; 0F C0/C1; 0F B0/B1; 0F C7 digit 1) with ten
  closed canonical forms (`canonAdd32/64/16`, `canonXadd64`, `canonCmpxchg64`,
  `canonBts32`, `canonInc64`, `canonNeg32`, `canonXaddPlain64`, `canonC7B`) and
  ten `rfl` encode pins.
- §4 family decoder `decodeLockAll` (prefixes LOCK/66H/REX in any order, each at
  most once, REX.W overrides 66H; mod 0/2 tails with disp32 plus the accepted
  SIB-36 subset; LOCK-on-register parses to `regZiel`, LOCK-without-write to
  `keinSchreiben`; unlocked XADD/CMPXCHG/CMPXCHG8B/bit-test decode with
  `lock=false`) with ten closed `decide` decode pins = checked byte round trips
  with the encode pins, and eight closed `decide` pins that the accepted
  `kapDecode` refuses every new row.
- §6 extended chain `kapDecodeAll` (accepted chain first, family arm where it
  refuses) with exact-agreement theorems (`kapDecodeAll_stimmt_alt/neu/nichts`),
  one old-arm pin reusing `kapKette_lock`, eight new-arm pins.
- §7 map `lockAllAufLock` onto the accepted 662 rows (64-bit locked XADD/CMPXCHG,
  mod 2, canonical 662 REX via `rexLockBits`, registers via `codeReg`) with
  general non-map, narrow-width and missing-LOCK refusals; family step
  `hwLockAllSchritt` and plug `adapterLockAll` with `HwWf` preservation
  (`adapterLockAll_wf`), exact step agreement (`hwLockAllSchritt_aufgenommen`)
  and UD/refusal selection.
- §8 joint witness `lockAll_zeuge`: the canonical XADD form maps onto the
  accepted 662 row, so the family step replays the accepted two-core locked-add
  run (word 10 to 15 on core 0, 15 to 22 on core 1 after the drain, old words
  through rax, owner-only forwarding of the foreign byte) beside Group-1, UD
  and unlocked-XADD refusals and new-arm chain evidence.
- CUTS block and `#print axioms` for 20 main theorems. Axioms are `[propext]`
  (data/round-trip theorems) or `[propext, Quot.sound]` (chain/step/witness
  theorems) — a subset of the goal-theorem triple, no `sorryAx`.

Last `./lean-bau` result line: `Build completed successfully (709 jobs).`
`./lean-probe` on the new file: `== 0 error(s)`. `lean-layout --check` passes
(X86/ at 16 of 20 entries). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Exact new names

Types: `LockAllOp`, `LockAllUd`, `LockAllForm`, `LockAllAnweisung`,
`KapAllDekodiert`. Values: `lockAllWert`, `lockAllWertCmp`, `lockAllCf` (+17
agreement theorems). Codec: `lockAllPrefix`, `lockAllDirektOp`, `lockAllModrm`,
`encodeLockAll`, 10 `canon*` forms, 10 `enc_*` pins, `lockAllPraefixAux`,
`lockAllGruppe`, `lockAllSchwanz`, `lockAllMem`, `decodeLockAllNach`,
`decodeLockAll`, 10 `dec_*` pins, 8 `kap_weist_*_zurueck` pins. Chain:
`kapDecodeAll`, `kapDecodeAll_stimmt_alt/neu/nichts`, `kapAllKette_lock`, 8
`kapAll_neu_*` pins. Adapter: `lockAllAufLockWort`, `lockAllAufLock`,
`lockAllAufLock_ablehnung/schmal/ohne_lock`, `hwLockAllSchritt`,
`adapterLockAll`, `hwLockAllSchritt_ud/aufgenommen/abgelehnt`,
`adapterLockAll_wf`. Witness: `aufLock_canonXadd64`, 4 mapping pins,
`hwLockAll_nach1/nach2` (+wort/rax/sicht pins), 3 step refusals, `lockAll_zeuge`.

## Findings

- The old chain genuinely refuses all eight new rows (`decide`-proved), including
  LOCK ADD qword and LOCK INC qword: no carry/core arm takes LOCK-prefixed
  memory shapes. The two 662 rows (LOCK+REX.W XADD/CMPXCHG) keep their exact arm.
- Two decoder bugs were caught by the closed pins before merging: the `0x0F`
  escape sorts below 62 and was swallowed by the direct-form branch (moved the
  escape check first), and the direction bit was inverted (`01` is wide
  memory-destination, not register-destination; `04/05`-style accumulator
  immediates take no ModRM at all). Both are fixed and pinned.
- Maintainer extension point (in CUTS): widen `decodeLock` in
  `TSO/Verriegelt/LockedInstructionExecution.lean` with the new rows of
  `decodeLockAll`, lift the §1 value functions into the accepted step, and extend
  `kapDecode` with a family arm behind `kapDecodeAll_neu`.

## Open / not claimed

No hardware correspondence beyond self-consistency for any new row; no execution
of Group-1/INC/DEC/NEG/NOT/bit-test/CMPXCHG8B (adapter refusals); mod-1 disp8,
RIP-relative, non-36 SIB and redundant prefixes refused at the decoder; encoder
canonical (mod 2) only; no universal round trip (ten closed rows pinned); no
W/GX bridge, timing or progress claims. Rule 13: no theorem quantifies over
program syntax, so no `_zeuge` companion is owed; `lockAll_zeuge` is the reached
two-core witness the mechanism asks for.

## Task issues believed wrong

1. The task line is truncated mid-sentence ("REX.W..."), so the CMPXCHG8B/16B
   scope past 0F C7 /1 is reconstructed from the ledger reports, not quoted.
2. Apparent contradiction: the lane owns exactly one new file and may not edit
   existing files, yet the mechanism asks for chain embedding "in the style of
   HwMulDivWidth" — resolved as a NEW extended chain over (not inside) the old
   one, with the exact file to extend named in CUTS.
3. Environment: two compound shell introspection calls were refused by the
   permission layer mid-lane (simple wrapper calls passed), and one
   `./lean-probe` exceeded 600 s with no output (lean-slot contention with other
   lanes) before a retry completed. No files outside the clone were touched.
