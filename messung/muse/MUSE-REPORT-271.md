# MUSE-REPORT-271: Byte memory semantics

## Task

Lane 271 of wave A (`dokumente/x86/WELLE-A.md`): permission-checked little-endian
byte reads/writes on the canonical `Speicher` (`grammatik/Grammatik/X86/Typen.lean`,
read as reference only, not modified). Owned files: `grammatik/Grammatik/X86/Speicher.lean`
(new file, 761 lines), one umbrella import line, this report.

## What was done

Implemented in `Gabbro.Grammatik.X86`, importing only `Grammatik.X86.Typen`:

- Addresses: `addrOff a i = a + BitVec.ofNat 64 i` (64-bit modular), with
  `addrOff_inj8`/`addrOff_ne8` (offsets below 8 are injective, no wrap hypothesis
  needed), `addrOff_null`, and the explicit no-wrap condition `OhneUmbruch`
  (`a.toNat + 8 ≤ 2^64`) with `ohneUmbruch_addrs` (machine addition is Nat addition)
  and `disjunkt_von_intervallen` (Nat-interval disjointness gives `Disjunkt`).
- Permissions: per-byte `lesbar8`/`schreibbar8` (every touched byte checked) plus
  generic `lesbarN`/`schreibbarN`, with `lesbarN_acht`/`schreibbarN_acht` by `rfl`.
- Stores via `findIdx` position search and `writeBytesN` (proved once, used for every
  width); `writeBytes = writeBytesN · · · 8`, `write64` refuses with `none`
  (no memory change by construction: `write64_verweigert[_kein_effekt]`).
- Exported `read64`/`write64` with the required signatures; reusable `Breite`
  helpers `readBreite`/`writeBreite` (explicit 1/2/4-byte LE access, `.b64` arms are
  `read64`/`write64` by `rfl`: `readBreite_b64`, `writeBreite_b64`).
- Proved actual read-after-write (`read64_nach_write64`,
  `read8/16/32_nach_write8/16/32` with `% 256 / % 65536 / % 4294967296` low-bits
  statements, Breite corollaries) and outside-footprint preservation
  (`write64_rahmen`, `read64_rahmen` over explicit `Disjunkt`, per-width frames and
  Breite corollaries). Successful writes preserve all permissions
  (`write64_erhaelt_berechtigungen`, per-width analogues).
- Per-byte event lists `leseEreignisse`/`schreibEreignisse` (+ `Fuss`, length/mem
  facts, `fuss_entzerrt`) as hooks for the TSO bridge; no atomicity is claimed.
- Joint witness: `write_read_zeuge` (concrete fully-permissive zeroed memory,
  address `0`, nonzero word `0x0102030405060708`): write succeeds, reads back,
  and observably changes memory (`0x00` becomes `0x08` at the base); plus the
  `writeBreite_read_zeuge` twin through the width-indexed interface.
- Exported signatures recorded early and finally in `.tmp/INTERFACE.md`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/Speicher.lean`: 0 errors.
- `./lean-bau` (full project, required for a new Lean task): exit 0, 0 error lines,
  367 jobs, build completed successfully.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no premise of type `Prop`
  itself; every premise is used. `#print axioms` for every main theorem: only subsets
  of `{propext, Quot.sound}`, no `sorryAx`.
- Umbrella change is one added import line (`Grammatik.X86.Speicher`); `Typen.lean`,
  goal statements, checker, emitter, TODO/AGENTS/SATZKARTE untouched. No diagnostic,
  gift/example numbers, no MARKE_EMIT change.

## Open / cuts (also as `CUTS:` in the file)

- No concurrent atomicity: all lemmas are sequential over one `Speicher`. Per-access
  TSO granularity, alignment/tearing, and the GX refinement are lane 274's business.
- No decoder/encoder/instruction semantics/ABI/cost/source correspondence: byte memory
  only. No separate refusal analogues for 1/2/4-byte stores (same `none` construction).
- One belief worth flagging: the task's "no-wrap conditions needed by frame/read-back
  lemmas" turn out to be unnecessary for footprint injectivity (addition is a group,
  proved unconditionally); `OhneUmbruch` is provided for consumers that reason in Nat
  addresses rather than as a premise of the frame lemmas. If the coordinator wants the
  frame lemmas to literally carry an `OhneUmbruch` premise, that is a one-line
  strengthening via `disjunkt_von_intervallen`, not a gap in what is proved.
