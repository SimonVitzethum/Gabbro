# MUSE-REPORT-346: Reviewed organisation plan C2 — GateStub

## What was done

New module `grammatik/Grammatik/X86/GateStub.lean` (389 lines) plus one
additive import at the end of `grammatik/Grammatik.lean`. Caller-side gate
declaration checks mirroring the source gate shape (N063–N067,
`crates/gabbro-check/src/syscall.rs`, sentences `syscall.erklaerung` /
`syscall.stub` in `saetze.rs`) plus caller-stub byte-shape obligations, with
C186 / C187 / M140 as refusal predicates. Callee-side contract (obligation
(c)) stays OPEN. No existing file touched except the one import line; no
second IR, no duplicated evaluator of the 14 pilot forms, no source admission
tightened.

## Exact new definitions

- `TorArt` (`.normal` / `.region` / `.stapel`), `TorDekl` (nummer, ein, aus,
  clobber, errors, gruende, hatOr, art, paramAnzahl) over canonical
  `X86.Register`.
- Decided checks: `regsDistinctB` (N063), `alleGebundenB` + `paramsAbgedecktB`
  (N065 + arity: length = paramAnzahl, indices Nodup, all 0..n-1 present),
  `ausNichtClobberB` (N064), `linuxClobberB` (rcx + r11), `fehlerOkB` (N067:
  distinct errnos, every target < gruende, nonempty map needs `hatOr`),
  `torOkB` (conjunction).
- Refusals: `c186VerweigertB` (region without `or R`), `rufbewahrt` /
  `freieRufbewahrt` / `c187VerweigertB` (stack gate, < 2 free callee-saved of
  rbx rbp r12–r15), `m140VerweigertB` (number used as pointer).
- Stub shape: `trapBytes` (`0F 05`, literal only), `trapBytes_pin`,
  `stubEndsTrapB`, `bindungErstelltB`, `zeugenMoves`, `zeugenStub`.
- Decode: `RohKlasse` (`.ok` / `.grund errno` / `.hardware`), `klassifiziere`
  (negative `-4095..-1` against the errors map, else range-checked ok, else
  hardware outcome).

## Exact new theorems

- Admission: `schreibTor_ok` (write-shaped witness admitted).
- Refusals: `torDoppelt_verweigert`, `torAusClobber_verweigert`,
  `torUngebunden_verweigert`, `torOhneR11_verweigert`,
  `torDoppelErrno_verweigert`, `torFremdGrund_verweigert`,
  `torRegionOhneOr_verweigert`, `schreibTor_kein_c186`,
  `torStapelOhneTrampolin_verweigert`, `schreibTor_stapel_kein_c187`,
  `m140_geschmiedet`, `m140_echt_kein_fund`.
- Stub: `zeugenMoves_ok`, `zeugenStub_trap`,
  `zeugenStub_prefix_dekodiert` (via canonical `roundtrip_movReg64`).
- Decode: `klassifiziere_ebadf` (-9 → reason 0), `klassifiziere_ok`,
  `klassifiziere_unbekannt` (-22 → hardware), `klassifiziere_ausserhalb`
  (99999 → hardware), `klassifiziere_zaun` (-5000 → hardware).
- Joint: `torStub_zeuge` (admission + moves + trap suffix + EBADF decode +
  memory-change existential via canonical `write_read_zeuge`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/GateStub.lean`: 0 errors. Axioms per
  `#print axioms`: subset of `[propext, Quot.sound]` only (`torStub_zeuge`:
  `[propext, Quot.sound]`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (strict word-boundary grep clean); every premise used; no `Prop`-typed
  premise; no per-program rule.
- `./lean-bau` last line: `Build completed successfully (386 jobs).`
- Goal probe: `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged.

## What remains open (see CUTS)

Caller side only (IMAGE-ABI section 7 caller half). OPEN: trap semantics (no
`Befehl` form, literal `0F 05` shape only); callee-side obligation (c);
bare-metal `int $0x80` clobber rule (`linuxClobberB` is Linux-only); kernel
meaning of numbers/tables/costs; source-to-byte correspondence; refused-form
scalar fallback (consumer obligation); N066 implicit (unrepresentable type,
not a refusal). Full final-byte/source/hardware correspondence OPEN.

## Task remarks (believed wrong or noteworthy)

1. N066 has no Bool in this file by construction: `TorDekl` ranges over the
   canonical 16 `Register`, so an unknown register cannot be stated. This
   mirrors the source check without duplicating it; the report states this
   openly rather than inventing a refusal.
2. Lean `{ s with a := .x, b := ... }` multi-field update with dot-notation
   first value failed to parse in this tree; single-field `with` updates and
   explicit `TorArt.stapel` in struct literals were used instead.
3. The joint `_zeuge` reuses the canonical `write_read_zeuge` memory witness
   from `Speicher.lean` (name `zeugenSpeicher` was already taken there)
   rather than minting a second memory.
