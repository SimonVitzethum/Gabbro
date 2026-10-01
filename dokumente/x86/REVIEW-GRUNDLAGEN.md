# Independent review of x86 foundations and the byte contract (lane 281)

Scope: `grammatik/Grammatik/X86/{Typen,Wort,Speicher}.lean`,
`crates/gabbro-check/src/x86/{mod,typen}.rs`,
`dokumente/x86/BYTE-PILOT.md`, against `dokumente/x86/WELLE-A.md`.
Method: read every definition and proof statement, rechecked each
equation and encoding row against my own knowledge of the x86-64
encoding, and replayed the boundary values with independent `python3`
computations (exact commands in section 6). Disclosure: no primary
architecture manual was available locally and none was fetched (per
task constraints), so the architecture recheck is trained-knowledge
comparison, not manual-verified hardware correctness. No code was
modified.

## Verdict

No error found in the inspected equations and encodings: every
concrete arithmetic/flag equation, address edge case,
permission/refusal/read-back/frame premise, Rust construction rule,
and byte encoding row checked matches. This is a manual review
finding, not machine-checked hardware correctness, and it establishes
no hardware correspondence. All wider claims (concurrent atomicity,
codec/hardware correspondence, source-to-bytes chain) are correctly
NOT made; each file books them as open in its CUTS section.

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
  consumers, not as a frame premise. No error found in that design.
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
- Sparse `Speicher` versus Lean total functions: by construction, an
  absent address answers `None` for bytes and `false` for every
  permission. That is all that is stated. The representation relation
  between Rust and Lean states is UNPROVED (Rust-to-Lean fidelity is
  explicitly unproved in `typen.rs`), so no generic safe-direction
  refinement ("Rust refuses more, never the reverse") is claimed here.
  The `lege_ab(false)` revocation regression is repaired with a test.
- All 14 `Befehl` constructors mirror `Typen.lean`; `disp_bits`
  covers exactly the displacement carriers; `Decodiert::laenge` is
  carried, unvalidated data by documentation. Nothing is wired into
  checker/emitter/CLI. Rust-to-Lean fidelity is stated as UNPROVED.

## 4. Byte encoding contract (`BYTE-PILOT.md`)

Checked row by row against my own knowledge of the x86-64 encoding
(no primary manual consulted, see Method); all 14 pilot
constructors are covered exactly once, with issue bytes replayed.
"No error found" per row means the row matches the known encoding,
not hardware-verified correctness:

- `movImm64`: REX.W+B (`0x49` for r15), `B8+rd` (`0xBF`), imm64
  little endian: 10 bytes. Matches (`MOV r64, imm64`); no error found.
- `mov/add/sub/xor` register forms: REX.W with R=src/8, B=dst/8
  (for example `add r15, r8` gives `4D 01 C7`), opcodes
  `89/01/29/31`, ModRM `C0+8*(src%8)+dst%8` (mod=11). `cmpReg64`
  uses `39` with rhs in reg and lhs in r/m (for example
  `cmp rax, rcx` gives ModRM `C8`): the `r/m - reg` direction matches
  `lhs - rhs`; no error found.
- `load64` (`8B`, reg=dst) / `store64` (`89`, reg=src), mod=10
  always, SIB `0x24` exactly when `base%8=4` (for example
  `load r9, [r12-8]` gives `4D 8B 8C 24 F8 FF FF FF`): 8 bytes.
  Forcing mod=10 keeps `rbp`/`r13` real bases and never RIP-relative;
  the SIB value is scale=1, no index, `rsp`/`r12` base. No error found.
- `jump32` (`E9`, 5 bytes), `jumpIf32` (`0F 80+cc`, 6 bytes; `l/ge/le/g`
  give `8C/8D/8E/8F`), `call32` (`E8`, 5 bytes),
  `push64`/`pop64` (`50+r`/`58+r`, `41` prefix for high registers:
  `push r9` is `41 51`, `pop r12` is `41 5C`; note `41`, not `49`,
  matches since push/pop need no REX.W), `ret` (`C3`). No error found.
- Scope discipline matches the stated contract: REX.W always present
  for 64-bit operands,
  displacements little endian raw int32 with sign extension at use,
  lengths within 1-15 (maximum canonical here is 10), decoder returns
  first instruction plus remainder, non-canonical valid forms refused.
- One doc nit (not a mistake): the REX byte value (`0x48 | R<<2 | B`,
  `0x49` with B) is implied by the field assignment rather than
  spelled out. Explicit warning: a shared contract plus round-trip does
  NOT suffice to catch divergence — two matching encoder/decoder bugs
  preserve round-trip, and two parallel implementations can agree on
  the same bug. What is needed is independently pinned architecture
  bytes plus independent review; generic codec/hardware correspondence
  remains OPEN (lanes 279/280 own the codec, not its correspondence).

## 5. Generic-requirement and non-weakening check

- No example or function-name special cases anywhere in the reviewed
  files; the hardcoded tables in Rust tests pin architecture numbers,
  not program names.
- No weakening within the inspected scope: partial-permission stores
  refused whole, no read/write/execute conflation, `af=None` kept
  undefined rather than defaulted, and the canonical subset refuses
  non-canonical forms explicitly. (No claim about the Rust/Lean
  direction: the representation relation is UNPROVED, see section 3.)
- Stronger unproved claims correctly left open: instruction execution
  (lane 272), encoder/decoder round-trip AND generic codec/hardware
  correspondence (lanes 279/280), per-access
  TSO and tearing (lane 274), source correspondence (lane 277),
  ABI/image coverage (lane 276), float/time profile (lane 278), and
  the full source-to-bytes chain. None is asserted by the reviewed
  foundations.

## 6. Independent replay: exact commands and results

Both commands below were run in this clone during this review; outputs
are quoted verbatim. They recompute flag equations, sign extension,
parity, little-endian coefficients, the witness bytes, the REX/ModRM/
SIB/jcc issue bytes, and the `Disp32` signed edges independently of
the Lean and Rust sources (plain integer arithmetic, no project code).

Command 1 (flag/extension/memory boundaries):

`python3 -c "M=2**64; <cfAdd/ofAdd/cfSub/ofSub/par/sext
definitions>; print(carry/overflow/sub/parity/sext/af/coefficients/
witness-bytes/reassemble-ok)"`

Results:

- `carry-no-overflow: 0x0 True False`
- `overflow-no-carry: 0x8000000000000000 False True`
- `sub-zero: CF False OF False`
- `sub-borrow: 0xffffffffffffffff True False`
- `sub 1-2: CF True OF False SF True ZF False`
- `parity: True True False True` (for `0/0x03/0x01/0xFF`)
- `sext: 0xffffffffffffffff 0x7f 0xffffffffffff8000`
- `af add F+F: True; sub 0-1 nibble borrow: True`
- `coeffs: [1, 256, 65536, 16777216, 4294967296, 1099511627776,
  281474976710656, 72057594037927936]`
- `witness bytes: ['0x8','0x7','0x6','0x5','0x4','0x3','0x2','0x1'],
  reassemble ok: True`

Command 2 (encoding issue bytes and displacement edges):

`python3 -c "<rex/modrm helpers, struct.pack('<i',-8),
ctypes.c_int32/c_int64>; print(movImm/add/modrm/load/sib/push/pop/
jcc/displacement-edges)"`

Results:

- `movImm r15: 0x49 0xbf`
- `add r15,r8: 0x4d 01 0xc7`
- `cmp rax,rcx modrm: 0xc8`
- `load modrm: 0x8c sib 0x24 disp f8ffffff`
- `push r9: 41 0x51; pop r12: 41 0x5c`
- `jcc l/ge/le/g: ['0x8c','0x8d','0x8e','0x8f']`
- `disp edges: 0x0->0; 0x7fffffff->2147483647;
  0x80000000->-2147483648; 0xffffffff->-1` (with sign extension to
  `i64` identical)

Each result matches the corresponding reviewed statement
(`probe_add_*`, `probe_parity`, `probe_sext`, `probe_bedingung_lt`,
`bytesWort` coefficients, `zeugenWort` bytes, BYTE-PILOT rows,
`typen.rs` displacement tests). Manual-knowledge disclosure: the
expected x86-64 issue bytes above (REX/ModRM/SIB/opcode values) come
from my own knowledge of the encoding; no primary architecture manual
was consulted (none available locally, none fetched). The replay
therefore checks the reviewed files against an independent
computation, not against hardware or a manual.
