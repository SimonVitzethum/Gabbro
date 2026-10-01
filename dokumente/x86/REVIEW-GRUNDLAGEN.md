# Independent review of x86 foundations and the byte contract (lane 281)

Scope: `grammatik/Grammatik/X86/{Typen,Wort,Speicher}.lean`,
`crates/gabbro-check/src/x86/{mod,typen}.rs`,
`dokumente/x86/BYTE-PILOT.md`, against `dokumente/x86/WELLE-A.md`.
Method: read every definition and proof statement, rechecked each
equation against the Intel 64-bit architecture by hand, and replayed
the boundary values with independent `python3` computations
(documented in MUSE-REPORT-281.md). No code was modified.

## Verdict

No architectural mistake found in the reviewed scope. Every concrete
arithmetic/flag equation, address edge case, permission/refusal/
read-back/frame premise, Rust representation boundary, and byte
encoding row checked is correct. All wider claims (concurrent
atomicity, hardware correspondence, source-to-bytes chain) are
correctly NOT made; each file books them as open in its CUTS section.

## 1. Arithmetic and flags (`X86/Wort.lean`)

- `cfAdd` (`2^64 <= x+y`), `cfSub` (`x < y`), `ofAdd`/`ofSub` (pure
  sign-bit functions) keep carry and overflow structurally distinct.
  Boundary replay: `0xFF..FF + 1` gives carry without overflow and
  result zero; `0x7FF..FF + 1` gives overflow without carry and result
  `0x8000000000000000`. Both match the file's `probe_add_*` theorems.
- `afAdd`/`afSub` (nibble carry `16 <= x%16 + y%16`, borrow
  `x%16 < y%16`) are the textbook auxiliary-carry definitions.
- `parityEven` (even popcount of `toNat % 256`), `zfTest` (`== 0`),
  `sfTest` (bit 63) are the correct PF/ZF/SF readings. Replay:
  parity of `0/0x03/0x01/0xFF` is `true/true/false/true`, as stated.
- `sext` (`lo + (2^64 - 2^bits)` under sign bit) replays to
  `0xFF->0xFF..FF`, `0x7F->0x7F`, `0x8000->0xFF..8000`, as stated.
- `xor64` clears CF/OF and leaves AF `none` (undefined, never false):
  architecturally correct for XOR.
- The 16 `bedingung` rows map `o/no/b/ae/e/ne/be/a/s/ns/p/np/l/ge/le/g`
  to codes 0-15 with the standard Intel condition tests (`b` reads CF,
  `be` is `cf || zf`, `l` is `sf != of`, and so on). Replay: after
  `1 - 2`, `l` and `b` hold while `g` and `a` fail, as stated.
- Narrow widths have modular arithmetic, masks, and sign/zero
  extension, but no narrow flag snapshots. This is booked in CUTS, not
  hidden: only the three 64-bit operations produce flags here.

## 2. Memory (`X86/Speicher.lean`)

- `addrOff a i = a + ofNat 64 i` is modular; footprint injectivity
  (`addrOff_inj8`, no wrap hypothesis) is genuinely unconditional
  (addition is a group), confirming the lane-271 report's claim.
  `OhneUmbruch` (`toNat + 8 <= 2^64`) is provided for Nat-reasoning
  consumers, not as a frame premise. That design is sound.
- Permissions are per byte and independent: `read64` needs `lesbar8`,
  `write64` needs `schreibbar8`, and read-after-write correctly
  demands readability BESIDES writability (`hrd` premise). No
  read/write/execute conflation.
- Refusal returns `none` with no memory change by construction;
  partial-permission stores are refused whole, which is strict.
- Little-endian coefficients (`1, 256, ..., 72057594037927936`) equal
  `256^0..256^7`; reassembly inverts splitting. The joint witness
  (`0x0102030405060708` at address zero, byte `0x00` to `0x08`)
  replays byte-exact.
- Frames state the exact footprint premise and disjointness for
  cross-reads; per-byte event lists claim eight events with explicitly
  NO atomicity. The TSO bridge stays open.

## 3. Rust mirror (`x86/{mod,typen}.rs`)

- Register codes (`rax=0 .. rdi=7, r8=8 .. r15=15`), names, and the
  `from_code` refusal above 15 match the hardware encoding; tests pin
  hardcoded tables, never round-trip alone. Condition codes likewise
  match Intel numbers 0-15 with refusal above 15.
- `Breite` bits/bytes/masks/truncate match Lean (`maske`,
  `breite_bytes`); `Disp32` keeps raw `u32` bits with explicit signed
  readings only (`signed`/`extended`), sign-extends to `i64`, and
  computes branch targets from the FOLLOW address with wrapping
  arithmetic. Edge replay: `0x80000000 -> i32::MIN -> -2147483648`,
  `0xFFFFFFFF -> -1`; `effektive_adresse(0)` of `-1` is `u64::MAX`.
- Sparse `Speicher` (absent means unmapped and unpermitted) versus
  Lean total functions is an explicitly booked coverage gap pointing
  the safe way: Rust refuses where Lean might grant, never the reverse.
  The `lege_ab(false)` revocation regression is repaired with a test.
- All 14 `Befehl` constructors mirror `Typen.lean`; `disp_bits`
  covers exactly the displacement carriers; `Decodiert::laenge` is
  carried, unvalidated data by documentation. Nothing is wired into
  checker/emitter/CLI. Rust-to-Lean fidelity is stated as UNPROVED.

## 4. Byte encoding contract (`BYTE-PILOT.md`)

Checked row by row against the Intel 64-bit encoding; all 14 pilot
constructors are covered exactly once, with issue bytes replayed:

- `movImm64`: REX.W+B (`0x49` for r15), `B8+rd` (`0xBF`), imm64
  little endian: 10 bytes. Correct (`MOV r64, imm64`).
- `mov/add/sub/xor` register forms: REX.W with R=src/8, B=dst/8
  (for example `add r15, r8` gives `4D 01 C7`), opcodes
  `89/01/29/31`, ModRM `C0+8*(src%8)+dst%8` (mod=11). `cmpReg64`
  uses `39` with rhs in reg and lhs in r/m (for example
  `cmp rax, rcx` gives ModRM `C8`): the `r/m - reg` direction is
  correct for `lhs - rhs`.
- `load64` (`8B`, reg=dst) / `store64` (`89`, reg=src), mod=10
  always, SIB `0x24` exactly when `base%8=4` (for example
  `load r9, [r12-8]` gives `4D 8B 8C 24 F8 FF FF FF`): 8 bytes.
  Forcing mod=10 keeps `rbp`/`r13` real bases and never RIP-relative;
  the SIB value is scale=1, no index, `rsp`/`r12` base. Correct.
- `jump32` (`E9`, 5 bytes), `jumpIf32` (`0F 80+cc`, 6 bytes; `l/ge/le/g`
  give `8C/8D/8E/8F`), `call32` (`E8`, 5 bytes),
  `push64`/`pop64` (`50+r`/`58+r`, `41` prefix for high registers:
  `push r9` is `41 51`, `pop r12` is `41 5C`; note `41`, not `49`,
  is correct since push/pop need no REX.W), `ret` (`C3`). Correct.
- Scope discipline is right: REX.W always present for 64-bit operands,
  displacements little endian raw int32 with sign extension at use,
  lengths within 1-15 (maximum canonical here is 10), decoder returns
  first instruction plus remainder, non-canonical valid forms refused.
- One doc nit (not a mistake): the REX byte value (`0x48 | R<<2 | B`,
  `0x49` with B) is implied by the field assignment rather than
  spelled out. Lanes 279/280 implement from the same contract, so any
  divergence will show as a round-trip failure, not a silent split.

## 5. Generic-requirement and non-weakening check

- No example or function-name special cases anywhere in the reviewed
  files; the hardcoded tables in Rust tests pin architecture numbers,
  not program names.
- No weakening: partial-permission stores refused whole, Unix-style
  permission conflation avoided, `af=None` kept undefined rather than
  defaulted, sparse-Rust refuses more rather than granting more, and
  the canonical subset refuses non-canonical forms explicitly.
- Stronger unproved claims correctly left open: instruction execution
  (lane 272), encoder/decoder round-trip (lanes 279/280), per-access
  TSO and tearing (lane 274), source correspondence (lane 277),
  ABI/image coverage (lane 276), float/time profile (lane 278), and
  the full source-to-bytes chain. None is asserted by the reviewed
  foundations.
