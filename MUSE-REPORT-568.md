# MUSE-REPORT-568: Executed pilot instruction to realised access footprint

## Task
Connect `Zugriffe.zugriff` (checked POTENTIAL footprint from the pre-state) to ACTUAL
successful `Ausfuehrung.schritt` and `Byteschritt.byteschritt` for all 14 pilot forms,
in the new file `grammatik/Grammatik/X86/AccessExecution.lean` (+ additive umbrella import).

## What was done
Every footprint fact is derived from a successful-step premise
(`istRealisiert d s s'`, i.e. `schritt d s = some s'`, or `byteRealisiert s s'`);
a computed list alone is never claimed as a realised trace. All `Speicher`
read/write frame facts are reused through the existing `Ausfuehrung`/`Zugriffe`
linkage theorems; no evaluator, decoder, ISA form or memory model was duplicated
or invented.

### New definitions (`AccessExecution.lean`, namespace `Gabbro.Grammatik.X86`)
- `istRealisiert (d s s')` — the actual `schritt` succeeded.
- `byteRealisiert (s s')` — actual fetch, decode and `schritt` succeeded.
- `zeugeStore`, `zeugeStoreVor` — joint-witness decoded store and its pre-state.

### New theorems (all `#print axioms` clean, standard goal set only)
- §0: `realisiert_laenge_ok` — a realised step had a valid decode length.
- §1: `byte_aus_weiter` — a realised byte step runs `schritt` on a fetched instruction.
- §2 realised existence, permission success derived from `hstep` alone:
  `realisiert_store64_gefunden`, `realisiert_load64_gefunden`,
  `realisiert_push64_gefunden`, `realisiert_pop64_gefunden` (non-`rsp` destination),
  `realisiert_call32_gefunden`, `realisiert_ret_gefunden`.
- §3 realised footprints from `hstep` alone (frame + exact shape + stored word/read value):
  `realisiert_store64_fuss`, `realisiert_push64_fuss`, `realisiert_call32_fuss`
  (stored word is the ACTUAL next RIP evaluated pre-state),
  `realisiert_load64_fuss`, `realisiert_pop64_fuss`, `realisiert_ret_fuss`.
- §4: `frame_aus_speichergleich` (axiom-free) and the generic coverage theorem
  `realisiert_fuss_abdeckung` casing over all 14 pilot forms (pure/read forms change
  no byte; write forms change only their eight pre-state addresses; footprints are
  empty or one eight-byte `Fuss`; `pop` covers `dst = rsp` via an inline branch).
- §5 alias shapes: `realisiert_store_alias` (base-is-source: footprint and stored
  word at the same pre-state register), `realisiert_push_rsp` (`push rsp` stores
  the OLD top). CALL next-RIP and POP/RET reads are pinned in §3 (`call32_fuss`,
  `pop64_fuss`, `ret_fuss`).
- §6 byte bridge: `byte_realisiert_fuss` (a realised byte step carries a realised
  footprint), `byte_realisiert_aus_bytes` (fetch + `schritt` is a realised byte step
  decoding the ACTUAL fetched bytes at `rip`).
- §7 refusal: `realisiert_versagt_laenge`, `byte_ohne_fetch_kein_realisiert`.
- §8: `realisiert_store64_wort_kein_atom` — eight-byte word footprint vs. one
  atomic TSO event distinguished by construction (`AtomarZugriff` empty).
- §9 witnesses: `schritt_zeuge_speicher` (`decide`: store step changes byte 8192
  to 42), `realisiert_fuss_abdeckung_zeuge` (joint instantiation of ALL generic
  coverage premises on that real reached memory-changing execution),
  `byte_zeuge_verweigert` (planted refusal: truncated jump has no transition).

## Verification
- `./lean-probe grammatik/Grammatik/X86/AccessExecution.lean`: `== 0 error(s)`.
- `./lean-bau`: `Build completed successfully (428 jobs).` (includes the new module
  via the umbrella import; no existing file touched except the additive import line).
- Axioms: every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
  (or a subset); `Classical.choice` is used solely to name realised read/write
  witnesses. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- The goal statement, checker, emitter and Spec files are untouched.

## Open / next integration
- No source/IR/checker link: a Gabbro-source-to-footprint correspondence is not
  claimed (needs the pending shared IR and source-byte representation).
- No W/GX mapping: per-access linearisation, TSO visibility and tearing stay OPEN.
- `pop rsp` has realised memory/footprint facts (generic coverage) but no dedicated
  destination-value theorem (only the non-`rsp` shape pins the destination).
- Consumer interface for downstream lanes: `realisiert_fuss_abdeckung`,
  `byte_realisiert_fuss`, `realisiert_fuss_abdeckung_zeuge`,
  `realisiert_versagt_laenge`, `byte_ohne_fetch_kein_realisiert`.
- Measurable next step: a consumer (byte-level projection or W-bridge lane) citing
  `byte_realisiert_fuss` for fetched stack/call execution.

## Notes on the task
- Nothing in the task statement was found to be wrong. Two elaboration findings:
  `obtain`-destructuring of proof terms that contain an inner `cases` on the step
  fails dependent elimination, and `have`-bound `Classical.choose` witnesses do
  not unify; both are worked around with direct `choose_spec` use (documented in
  neither conclusion, purely proof engineering).
- The `pop64 dst = rsp` sub-case is covered inline in the generic theorem rather
  than by a dedicated realised-destination theorem; reported honestly, not closed.
