# MUSE-REPORT-1363: REX.W LEA wired into the decoder chain (KapsteinDrei)

## What was done

NEW FILE `grammatik/Grammatik/X86/Hw/Kapstein/HwKapsteinDrei.lean`
(namespace `Gabbro.Grammatik.X86`, 602 lines), one import line in
`grammatik/Grammatik.lean`, one map row in
`instrumente/lean-layout-map.json` (mechanical product of the
prescribed `lean-layout.py --apply`; see placement note below).

Family: REX.W LEA (`8D`) from the accepted `AddressEncoding.decodeLea`
/ `leaFormSchritt` / `encodeAdr`. Every accepted definition is reused
unchanged (lifted, never redefined); no new machine, no new evaluator.

- `Kap3Dekodiert` (`alt` / `lea dst form len`) and `kapDecode3`: the
  accepted `kapDecode` first (no shadowing by construction), the
  accepted `decodeLea` where the chain refuses, gated by `laengeOk`.
- Agreement: `kap3_alt` (general: old chain embeds exactly),
  `kap3_lea` (general: LEA arm takes exactly what the old chain
  refuses). Every premise is used.
- Four new rows with gap evidence (`kapDecode ... = none`, all
  `by decide`): scaled-disp8 (len 5), REX.R scaled-disp8 (len 5),
  REX.R base-disp8 (len 4), RIP-relative (len 7).
- Overlap exhibit (measured): the eight-byte scaled-disp32 form
  already decodes through the accepted integer-core `lea64` arm
  (`kap3_kern_lea64_hoch`); the third chain keeps it
  (`kap3_hoch_bleibt_alt`, proved via `kap3_alt`). No semantic
  `leaFormSchritt`-vs-`coreSchritt` agreement is proved (CUTS).
- Encoder `leaEncode` (accepted `encodeAdr` tail plus opcode byte)
  with three `bind`-round-trips and the pilot-owned-shape refusal.
- `HwAdapter LeaDecodiert` plug (`adapterLea`, in the style of
  `adapterRot`): `wf` (via `setKernDaten_wf`), `ok`, `proj`
  (via `leaFormSchritt_speicher`), `dst` (via `leaFormSchritt_dst`),
  length refusal. Every premise is used.
- `HwVollSchritt3` over `Kap3Ereignis` with exact embeddings of
  `HwVollSchritt2` (`kap3_alt_embedded`) and the LEA arm
  (`kap3_lea_embedded`), plus the `kap3Ereignis` decoder-to-event
  bridge (with refusal for old-chain rows).
- Reached witness `leaHw_zeuge`: core 0 LEA computes
  `8192 + 8 + 5 = 8205` into `rax` through the adapter; a buffered
  store forwards to the owner only; the drain changes shared memory
  0 -> 42; `HwWf` holds; a reached `HwVollSchritt3` LEA step stands
  (`leaHw_schritt_erreichbar`); bad-length and LOCK-NOP refusals
  beside it. Non-degenerate: the drain changes actual shared memory.
- CUTS block plus `#print axioms` for every definition and theorem.

## Last build results

- `./lean-probe grammatik/Grammatik/X86/Hw/Kapstein/HwKapsteinDrei.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (709 jobs).`
- `./lean-layout.py --check`: all 852 Lean files placed.
- Axioms: data/bridge theorems none; chain/adapter/witness theorems
  `[propext, Quot.sound]` (same footprint class as the accepted
  `kapW_*` theorems); no `Classical.choice`, no new axioms.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file;
  no premise has type `Prop`; no `intro _` / `have _ :=` discards.
- Rule 13: no theorem quantifies over program syntax and the task
  names no `ZEUGE:` target (the tail of line 26 was unreadable, see
  below), so no `_zeuge` companion is owed; the reached
  `leaHw_zeuge` conjunction is provided regardless.

## Findings

1. The ledger debt is real but smaller than listed: 8-byte REX.W LEA
   forms already decode via `decodeCore.lea64` (fixed length 8).
   The remaining chain gap is exactly the non-8-byte forms, four of
   which are wired here. The ledger row "REX.W LEA zurueckgestellt"
   should credit the `lea64` overlap.
2. Task-text defects (not candidate defects): the lane paths
   (`X86/HwKapsteinDrei.lean`, `X86/HardwareExecution.lean`) are
   stale; the modules live under `X86/Hw/...`. The family-list tail
   of line 26 (>2000 chars) is unreadable with the file tools, so
   the choice of LEA rests on the readable prefix (which names
   `AddressEncoding.decodeLea` explicitly) plus the ledger gap.
3. Placement: the lane's OWN path put the file at
   `X86/HwKapsteinDrei.lean`; rule 18 (`^HwKapstein` ->
   `Hw/Kapstein`) required the move, done by the prescribed
   `--apply` (import rewritten, map row added). The file header
   still names the old path (same staleness as `HwKapsteinZwei`'s
   header); the permission allowlist covers only the old path, so
   the one-line header fix is left to the maintainer.
4. `#eval` is rejected by the file parser in `grammatik/` (measured:
   "unexpected token '#eval'"), so decoder values were established
   through failing-`decide` probes, never guessed.

## What remains open

- Semantic `leaFormSchritt`/`coreSchritt` agreement on the eight-byte
  overlap; MOVSXD-mem / XCHG-mem (locked families); VEX/system
  families; the W/GX bridge. All named in CUTS, none claimed.
- Maintainer integration: extend the `kapDecode` chain definition in
  `HwKapsteinDecoder.lean` with the `.lea` arm (this file states the
  extension as a new definition over the old one, per the lane rule).

## Task feedback

The CONTEXT/MECHANISM paragraphs describe `HwMaschine`/`decodeExt`
paths that do not match this lane's operative deliverable (a third
capstone chain over `kapDecode`/`HwVollSchritt2`, following lane
1311's `HwKapsteinZwei` pattern); the TASK paragraph's chain-shape
spec is what this lane implements. The two-core forwarding witness
uses TSO issue/drain beside the register-only LEA step (LEA itself
is no memory event, per the named SDM entry), stated honestly.
No premise was added, no conclusion weakened.
