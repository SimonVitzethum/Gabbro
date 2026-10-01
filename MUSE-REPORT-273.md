# MUSE-REPORT-273: Rust target vocabulary

## What was done

Implemented the safe, dependency-free Rust mirror of the canonical
`grammatik/Grammatik/X86/Typen.lean` (`Gabbro.Grammatik.X86`) for the direct
x86-64 target, owned files only:

- `crates/gabbro-check/src/x86/typen.rs` (new): full vocabulary as Rust data.
- `crates/gabbro-check/src/x86/mod.rs` (new): umbrella module, re-exports,
  boundary record.
- `crates/gabbro-check/src/lib.rs` (one export): `pub mod x86;` with an
  unwired-foundation doc note. No other line touched.
- No Lean file added or changed; no umbrella import needed (Rust-only lane).

Read before acting: `AGENTS.md`, `dokumente/x86/WELLE-A.md`,
`grammatik/Grammatik/X86/Typen.lean`, `crates/gabbro-check/src/lib.rs`,
`src/abi.rs` and `src/syscall.rs` (register-list and doc conventions).

## Exact new definitions (all in `x86::typen`, re-exported by `x86`)

- Types `Byte` (= u8), `Wort` (= u64), `Adresse` (= u64).
- `Register` (repr u8, 16 variants `Rax..R15` in architectural encoding order):
  `ALLE`, `code()`, `from_code()` (checked, refuses > 15), `name()`.
- `Breite` (`B8/B16/B32/B64`): `bits()`, `bytes()`, `mask()`, `truncate()`.
- `Bedingung` (repr u8, 16 variants `O..G` in Intel condition-code order):
  `ALLE`, `code()`, `from_code()` (checked, refuses > 15).
- `Flags` (`cf/pf/af: Option<bool>/zf/sf/of`): `undefiniert_af()`
  (`af = None` = undefined, never false).
- `Disp32` (`bits: u32`, raw bits only): `von_bits()`, `von_signed()`,
  `signed()`, `extended()` (sign-extended i64), `effektive_adresse()`
  (wrapping base + extended), `sprungziel()` (address AFTER the decoded
  instruction + extended, the canonical relative-flow rule).
- `Speicher` (sparse `BTreeMap` bytes + `BTreeSet` r/w/x sets):
  `leer()`, `byte_an()` (None off-map), `lege_ab()`,
  `ist_lesbar()/ist_schreibbar()/ist_ausfuehrbar()` (false off-set).
- `Zustand` (`register: [u64; 16]`, `flags`, `rip`, `speicher`):
  `anfang()`, `lese()`, `schreibe()` (indexed by `Register::code`).
- `Befehl` (14 pilot constructors mirroring `Befehl`: `MovImm64`,
  `MovReg64`, `AddReg64`, `SubReg64`, `XorReg64`, `CmpReg64`, `Load64`,
  `Store64`, `Jump32`, `JumpIf32`, `Call32`, `Push64`, `Pop64`, `Ret`;
  displacements as raw `u32` via `Disp32`): `disp_bits()`.
- `Decodiert` (`befehl`, `laenge: u64`): `unvalidiert()` (carries data,
  validates nothing; length belongs to validated decoding).
- Tests (`typen::proben`, 9 tests; `x86::proben`, 1 test): hardcoded
  architectural register numbers 0..15, hardcoded Intel condition numbers
  0..15, rejection of 16/17/200/255/`u8::MAX`, hardcoded width bits/bytes
  and masks, signed displacement edges (`0x00000000` -> 0,
  `0x7fffffff` -> `i32::MAX`, `0x80000000` -> `i32::MIN`,
  `0xffffffff` -> -1), sign extension, branch targets from the follow
  address, wrapping address arithmetic, disp-bits carriage, sparse-memory
  absence semantics. Round-trip is asserted only alongside the hardcoded
  tables, never instead of them.

No new Lean theorems or definitions. No source diagnostic codes, no
gift/example numbers, no CLI switch, no `MARKE_EMIT` touch.

## Check outcomes (truthful last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` /
  `== total: 1467 passed, 0 failed, 1 ignored`.
- New tests in isolation (`./target/debug/deps/gabbro_check-<hash> x86`):
  `10 passed; 0 failed` (9 in `typen::proben`, 1 in `x86::proben`).
- `./lean-bau`: `Build completed successfully (366 jobs).` (no Lean file
  touched; build confirms the untouched tree stays green).
- Emission: unchanged by construction (only new unwired module + one
  `pub mod` line; `emit.rs` untouched). `./emission-pruef` not run; zero
  source-scope change: no checker rule, no diagnostic, no template, no
  corpus file added or edited.

## What remains open (cuts)

- Rust-to-Lean representation fidelity is UNPROVED (by inspection only).
- No encoder/decoder, no round-trip, no instruction semantics, no flag
  computation, no permission-checked load/store, no TSO/per-access bridge,
  no source correspondence, no ABI/image/entry coverage.
- `Speicher` is sparse/partial where Lean is total; `Decodiert::laenge`
  is unvalidated carried data.
- The module is unwired: nothing in checker/emitter/CLI reads it.

## Task assessment

Nothing in the task as given appears wrong. The ownership boundary
(new Rust files + one export line, no Lean edits, no numbers, no CLI,
no encoder/decoder) was respected. The `Disp32` wrapper was chosen so the
explicit signed interpretation cannot be bypassed by a silent `as i32`
at a use site.
