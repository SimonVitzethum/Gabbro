# MUSE-REPORT-317: Single instruction-access footprint owner

## What was done

New file `grammatik/Grammatik/X86/Zugriffe.lean` (~690 lines) plus one
additive umbrella import (`import Grammatik.X86.Zugriffe` at the end of
`grammatik/Grammatik.lean`). No other file touched. No source, Spec, goal,
Typen, or Rust edits.

### The single extraction

- `Zugriff` (structure: `lesen`, `schreiben`, `speicherWert`).
- `stapelOben` (stack address a push/call writes: old RSP minus 8).
- `zugriff (d : Decodiert) (s : Zustand) : Zugriff`: ONE generic match over
  all 14 pilot `Befehl` constructors, reusing `effAddr`, `Fuss`,
  `ripNach`, and the old-RSP stack addresses. Read/write distinctions:
  pure/control forms expose nothing; `load`/`pop`/`ret` read only;
  `store`/`push`/`call` write only. Stored words: `store` = source
  register, `push` = source register read before the move, `call` = the
  ACTUAL next RIP `ripNach s.rip d.laenge`.
- The extraction is a CHECKED POTENTIAL footprint (computed from the
  pre-state, no permission/length check inside); it is a REALISED
  SUCCESSFUL footprint exactly when `schritt d s` succeeds. Stated in the
  file header and the CUTS block.

### Theorems (all with every premise used in the proof)

- Per-constructor equations (14): `zugriff_movImm64`, `zugriff_movReg64`,
  `zugriff_addReg64`, `zugriff_subReg64`, `zugriff_xorReg64`,
  `zugriff_cmpReg64`, `zugriff_load64`, `zugriff_store64`,
  `zugriff_jump32`, `zugriff_jumpIf32`, `zugriff_push64`,
  `zugriff_pop64`, `zugriff_call32`, `zugriff_ret`.
- Membership: `fuss_mem`.
- Pure/read agreement (11): `erfolg_movImm64_ohne_speicher`,
  `erfolg_movReg64_ohne_speicher`, `erfolg_addReg64_ohne_speicher`,
  `erfolg_subReg64_ohne_speicher`, `erfolg_xorReg64_ohne_speicher`,
  `erfolg_cmpReg64_ohne_speicher`, `erfolg_jump32_ohne_speicher`,
  `erfolg_jumpIfGenommen_ohne_speicher`,
  `erfolg_jumpIfNicht_ohne_speicher`, `erfolg_load64_ohne_speicher`,
  `erfolg_pop64_ohne_speicher`, `erfolg_ret_ohne_speicher` (12 counting
  both jumpIf arms; each concludes `s'.speicher = s.speicher` AND the
  extracted footprint).
- Read linkage (3): `zugriff_load64_liest`, `zugriff_pop64_liest`,
  `zugriff_ret_liest` (extracted base address feeds the actual `read64`
  equation; destination/RIP holds the returned value).
- Write agreement (3): `erfolg_store64_im_fuss`, `erfolg_push64_im_fuss`,
  `erfolg_call32_im_fuss` (every changed byte in extracted footprint,
  permissions preserved, stored word named).
- Refusal (7): `zugriff_laenge_versagt_kein_erfolg`,
  `zugriff_load64_versagt_kein_erfolg`,
  `zugriff_store64_versagt_kein_erfolg`,
  `zugriff_push64_versagt_kein_erfolg`,
  `zugriff_pop64_versagt_kein_erfolg`,
  `zugriff_call32_versagt_kein_erfolg`,
  `zugriff_ret_versagt_kein_erfolg` (each concludes `False` from a
  successful-step hypothesis: refusal is never a trace).
- Non-atomicity (6 + 2 empties): `AtomarZugriff` (empty inductive),
  `kein_atomarer_zugriff`, `AblaufSpur` (empty inductive),
  `keine_ablauf_spur`, `zugriff_store64_acht`, `zugriff_push64_acht`,
  `zugriff_call32_acht`, `zugriff_load64_acht`.
- Witness/probes (7): `zugriffZeugeProg`, `zugriff_lauf_zeuge` (reached
  two-step run, byte 8192 zero-to-42), `zugriff_zeuge_im_fuss`,
  `probe_zugriff_schub`, `probe_zugriff_schub_wert`,
  `probe_zugriff_ruf_wert`, `probe_zugriff_ruf`, `probe_zugriff_nimm`.

## Last build result

`./lean-bau`: `exit 0; 0 error line(s)`, `Build completed successfully
(376 jobs)`. `./lean-probe` on the new file: `0 error(s)`.
`#print axioms` for every main theorem: `[propext, Quot.sound]`, except
`kein_atomarer_zugriff` / `keine_ablauf_spur` (no axioms). No `sorry`,
`admit`, `axiom`, `native_decide`, or `unsafe` anywhere.

## What remains open (see CUTS)

Byte order beyond little-endian `wortByte`, TSO visibility, grouping of
the eight bytes, any W/GX simulation or per-access linearisation, and
tearing/alignment observability. No RMW/LOCK/fence/narrow forms admitted
(`Befehl` has none). Fetch footprint left to lane 319. No source, cost,
contract, progress, timing, ABI/loader, or whole-image claim.

## Task remarks

Nothing in the task appeared wrong. Two implementation notes: (a) the
extraction takes `Decodiert` (not bare `Befehl`) because CALL's stored
word is the length-dependent next RIP; (b) this toolchain's struct
syntax requires one-line `{ befehl := ..., laenge := ... }` literals
(multi-line splits misparse), matching the note in `Ausfuehrung.lean`.
