# MUSE-REPORT-758: Hardware completion — disp0 memory form

## Task
Lane 758: cover mod=00 (no displacement, rbp/r13 base forces disp8=0)
with the canonical-address check per actual length and SIB exactly
where base%8=4, pinned bytes. New module
`grammatik/Grammatik/X86/Disp0Frame.lean`, import added to
`grammatik/Grammatik.lean`. Target: `Disp0Frame_verbindung` with joint
companion `Disp0Frame_verbindung_zeuge`.

## What was done
Built `Disp0Frame.lean` (~320 lines) entirely over the accepted
vocabulary (`AdrForm`, `adrEff`, `encodeAdr`, `parseAdrTail`,
`kanonisch48`, `fussZugelassen`, `adrStoreSchritt`); no new register,
memory, decoder, arithmetic or source model:

- §0 frame predicate `disp0Form` (art `.kein` + accepted `adrOk`) with
  admission pin `disp0Form_basisKein`.
- §1 disp0 address is the bare base (`disp0_adr_base`); SIB exactly
  where base low code is 4 (`disp0_sib_rsp` with pinned bytes
  `[REX, ModRM 04, SIB 24]`, `disp0_sib_r12` length 3) and SIB-free
  two-byte encoding elsewhere (`disp0_ohne_sib_rbx`).
- §2 mod=00 refuses `rbp`/`r13` (`disp0_rbp_verweigert`,
  `disp0_r13_verweigert`); the mod=01 disp8=0 escape is admitted and
  computes the bare base (`disp0_rbp_entkommt`, `disp0_r13_entkommt`).
- §3 fetched witness `mov [rbx], rax` = `[72, 137, 3]` through actual
  executable memory: decode pin, 42 lands at 8192 from zero, whole-word
  readback, RIP past the 3 actual bytes, dark-memory refusal.
- §4 `Disp0Frame_verbindung`: bare-base address, actual two-byte
  encoding length, accepted-footprint admission (`fussZugelassen`),
  admitted write — every premise used. `Disp0Frame_verbindung_zeuge`
  instantiates all premises jointly on the witness state beside the
  fetched memory-changing run.

## Verification
- `./lean-probe grammatik/Grammatik/X86/Disp0Frame.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (483 jobs)`.
- `#print axioms`: `[propext]` or `[propext, Quot.sound]` per theorem —
  within the standard `gabbro_ziel` set; no `sorry`/`admit`/`axiom`/
  `native_decide`; English throughout.
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved files.

## Provenance
Intel SDM combined Vols. 1-4, edition 325462-093US Sep 2026 (local
`.tmp/HARDWARE-REFERENCES/REFERENCES.json`); ModRM/SIB framing per
Vol. 2 Table 2-2, canonical addresses per Vol. 1 Sec. 3.3.7.1 via the
accepted checks. No AMD provenance (AMD URLs 404); no silicon proof.

## Open / not claimed
Silicon correspondence; disp8/disp32 frames (accepted API + own lanes);
TSO/GX bridge (sequential footprints only); source/ABI/loader/entry/
budget claims. See file CUTS.
