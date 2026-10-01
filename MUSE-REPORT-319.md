# MUSE-REPORT-319: Fetch decoded instructions from actual canonical byte memory

## What was done

New file `grammatik/Grammatik/X86/Byteschritt.lean` plus one additive import
line (`import Grammatik.X86.Byteschritt`) at the end of `grammatik/Grammatik.lean`.
It couples permission-checked fetch from actual instruction memory to the existing
byte decoder (279, `Codec.decode`) and instruction step (272, `Ausfuehrung.schritt`).
No second decoder, ISA, word/memory or instruction semantics; no source/Spec/goal/Rust
edits; no new hardware/software assumptions.

## New definitions (all in `Gabbro.Grammatik.X86`)

- `fetchCap : Nat := 15` — the x86 maximum instruction length cap.
- `ausfuehrbarN : Speicher -> Adresse -> Nat -> Bool` — execute permission of the
  first `n` bytes. Fetch checks execute permission ONLY; data-read (`lesbar`) is
  never consulted.
- `holeFetchAux (m) (a) (off) : Nat -> List Byte` — the executable prefix of actual
  `m.bytes` from `a`, stopping before the first non-executable byte, capped.
- `geholt (s) : List Byte` — the fetched window: actual bytes at `s.rip`, executable
  prefix only, capped at 15.
- `fetchDekodiert (s) : Option (Decodiert x List Byte)` — decodes the ACTUAL fetched
  bytes with the independent decoder, then checks consumed-length/remaining-suffix
  consistency (`laenge + rest.length = fetched`), `laengeOk`, and execute permission
  of the consumed prefix. Any mismatch, truncation, non-canonical form or bad length
  refuses with `none`. The decoded value is never trusted without this check.
- `ByteAusgang` (`weiter : Zustand -> ByteAusgang` | `verweigert`) — deliberately NO
  halt/termination constructor: `verweigert` means no successful transition, never
  normal program termination (empty-caller `ret`, thread end stay OPEN).
- `byteschritt (s) : ByteAusgang` — takes ONLY the state (no caller `Decodiert` is
  trusted, so a forged decoded value cannot inject an instruction): fetch, then the
  existing `schritt`; any failure is `verweigert`.
- Witness helpers: `ausgangRip`/`ausgangByte`/`ausgangReg` projections,
  `laufBytes` (bounded byte run; fuel exhaustion answers `weiter`, no halt claim),
  `ketteProg` (mov/store/load chain bytes), `bytesAusProg`, permission predicates.

## New theorems

- `holeFetchAux_laenge_le`, `geholt_laenge_le` — fetch never exceeds its cap.
- `ausfuehrbarN_vorsilbe` — execute permission is prefix-closed.
- `holeFetchAux_ausfuehrbar`, `geholt_nur_ausfuehrbar` — every fetched byte address
  is executable.
- `fetchDekodiert_entspricht` — FETCH-TO-DECODER: success implies decode of the
  actual window plus the checked length/suffix/permission facts.
- `byteschritt_weiter`, `byteschritt_verweigert_ohne_fetch`,
  `byteschritt_verweigert_ohne_schritt` — BYTE-STEP-TO-SCHRITT in both directions.
- `fetch_nutzt_nur_praefix` — success uses only the executable consumed prefix
  within the 15-byte cap; no execute access beyond a short instruction is demanded.
- `kanonisch_schritt_ueberein` — CANONICAL AGREEMENT for an ARBITRARY `Befehl`:
  if the fetched window is `encode b ++ suffix` with an executable prefix, fetch
  returns `⟨b, len⟩` and the byte step agrees with `schritt ⟨b, len⟩`. Proved from
  the round-trip instances, so the open arbitrary-input length soundness is avoided.
- Witnesses (all `by decide` over actual byte memories, each executing the bytes at
  `rip`, never a separate unexecuted buffer):
  - `kette_mov_store_load` — MEMORY-CHANGING MOV/STORE/LOAD chain: `rcx = 42`,
    data cell observably 0 -> 42, with code NOT data-readable (fetch needs execute
    only).
  - `opcode_geaendert_verweigert` — one forged opcode byte (REX.X) turns the
    executed step from `weiter` (rip 4106) into refusal.
  - `sprungziel_folgt_byte` — one forged displacement byte moves the executed jump
    4117 -> 4118 (byte affects instruction without refusal).
  - `praefix_abgeschnitten_verweigert` — jump cut off by the permission boundary.
  - `ohne_exec_verweigert` — readable-but-not-executable `ret` refused.
  - `ret_an_grenze_ohne_ueberlesen` — valid RET with non-executable suffix steps to
    the popped address (no over-read).

## Last `./lean-bau` result

`== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully
(382 jobs)`. `./lean-probe` on the file: 0 errors. `#print axioms` for every main
theorem is a subset of `propext, Classical.choice, Quot.sound` (most use only
`propext, Quot.sound`). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no
`Prop`-typed or unused premises.

## What remains open (also in the file's CUTS block)

- Arbitrary-input decoder length soundness
  (`forall bs d rest, decode bs = some (d, rest) -> d.laenge + rest.length =
  bs.length /\ 1 <= d.laenge /\ d.laenge <= 15`) is NOT proved — precise statement
  recorded in CUTS. Blocker: case analysis over every decoder path on arbitrary byte
  lists (279 left exactly this open). Fetch does not depend on it: the equation is
  checked at runtime (`fetchDekodiert_entspricht`), canonical instances go through
  round-trips (`kanonisch_schritt_ueberein`).
- No physical hardware claim (model memory only; caches/TLBs/store buffers/coherence
  OPEN), no whole-source/whole-binary theorem, no termination claim, no concurrency /
  atomic / interrupt / entry / ABI / relocation / cost claims.

## Notes on the task (for reviewer 320)

- Inhabitation rule: no theorem here has a universal premise over the listed source
  syntax types (`Vertrag`, `Stmt`, `Endblock`, `ErgExpr`, `Expr`, `Args`), and the task
  names no `ZEUGE:` target, so no `_zeuge` companion is formally required. The one
  `forall b : Befehl` theorem (`kanonisch_schritt_ueberein`, X86 target syntax) is
  jointly instantiated by the concrete chain/opcode/jump witnesses over non-degenerate
  runs (multi-step, memory-changing: cell 0 -> 42).
- Base checked: branch `muse/319` in `/home/simon/Dokumente/gabbro-muse/a319`;
  dependencies 272 (`Ausfuehrung.lean`) and 279 (`Codec.lean`) present and reused
  unmodified, as were `Speicher.lean`/`Bild.lean` vocabulary.
