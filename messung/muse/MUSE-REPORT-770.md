# MUSE-REPORT-770: indirect CALL provenance (function pointers, entry-fn values)

## Task

Lane 770: cover indirect `CALL r/m64` for function pointers and entry-fn
values under the N575-N577 discipline with per-call target-set proof and
pinned bytes, reusing the accepted indirect forms and dispatcher, no new
decoders or interpreters, no source/checker/emitter edits.

## What was done

New file `grammatik/Grammatik/X86/IndirectCallProv.lean` (458 lines),
registered as `import Grammatik.X86.IndirectCallProv` at the end of
`grammatik/Grammatik.lean`. It adds a provenance layer over the accepted
lane-680 constructors (`decodeIndirekt`, `callRegSchritt`,
`callMemSchritt`, `indByteschritt`, witness states `indS0`/`indS1`,
`memS0`/`memS1`); nothing is re-decoded or re-executed.

A provenance row binds one call site to one allowed target with its
origin: `.fnZeiger` (function-pointer value, target must be a decoded
instruction start) or `.eintrittFn` (entry-fn value, target must be a
listed entry handed once by the driver — the hardware side of the
checker `N575`-`N577` discipline).

## Exact new names

Definitions: `rufProvHandbuch`, `RufHerkunft` (`.fnZeiger`,
`.eintrittFn`), `RufZeile`, `rufProvOk`, `provTabelle`, `provStarts`,
`provEintraege`, `provTabelleEintritt`, `provEintraegeEintritt`.

Theorems: `rufProvOk_zeile`, `rufProvOk_fnZeiger`,
`rufProvOk_eintrittFn`, `IndirectCallProv_verbindung` (TARGET),
`rufProv_rahmen`, `IndirectCallProv_verbindung_eintritt`,
`pin_prov_callReg_rax`, `pin_prov_callReg_rax_dekode`,
`pin_prov_callMem_rbx`, `pin_prov_callMem_rbx_dekode`,
`prov_nachbar_verweigert`, `prov_fremd_verweigert`,
`prov_unbekannt_verweigert`, `prov_herkunft_verweigert`,
`prov_eintritt_akzeptiert`, `prov_fnZeiger_akzeptiert`,
`IndirectCallProv_verbindung_zeuge` (TARGET companion),
`IndirectCallProv_verbindung_eintritt_zeuge`.

Pins (all closed `decide`): `CALL rax` is `FF D0` (length 2);
`CALL [rbx+16]` is `REX.W FF 93` + disp32 (length 7); the `/0`
neighbour `FF C0` is refused. Provenance refusals: off-table target,
unknown call site, origin mismatch; one acceptance per origin.

## Verification

- `./lean-probe grammatik/Grammatik/X86/IndirectCallProv.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (485 jobs)`.
- Axioms of the new theorems: `[propext]` or `[propext, Quot.sound]`;
  pins axiom-free or `[propext]`; no `sorryAx` anywhere.
- `gabbro_ziel` axioms re-checked (scratch probe, uncommitted):
  `[propext, Classical.choice, Quot.sound]` — standard, unchanged.
- Two `./lean-bau` runs before the green one failed at the root
  `Grammatik` module with `failed to read file ... CTicket.olean` /
  `NarrowCodec.olean` (a different missing olean each run, my module's
  own lines built fine to job 484/485). This was a transient
  incremental-cache flakiness in this clone, not the lane change; the
  retry passed with 0 errors and no file changed in between.

## Open (see CUTS)

No new decoding/execution (all rows/steps reused); no silicon claim
beyond the stated SDM headings; no source/checker bridge (N575-N577 is
the named origin only); no TSO/GX, concurrency, cost, time or
termination claim — the frame theorem covers registers/flags plus
return-word read-back only; no whole-image/loader/ABI/entry/budget
connection (`starts`/`eintraege` are checked inputs).

## Note on the task

The task asks for "asynchronous/TSO effects for every form claimed",
but the per-access target-to-W/GX simulation is recorded OPEN, so a
TSO leg cannot be closed by this lane; I proved register/flag framing
and return-word read-back instead and booked the rest as CUTS. The
N575-N577 half is checker-side by construction — the hardware side can
only model the two provenances distinctly, which this file does. No
diagnostic/gift/example/CLI numbers taken, no MARKE_EMIT changes, no
friend-reserved files touched.
