# MUSE-REPORT-569: Fetched call/return to stack-frame proofs

## What was done

New file `grammatik/Grammatik/X86/StackExecution.lean` (plus additive
umbrella import in `grammatik/Grammatik.lean`), connecting actual
`Byteschritt` fetch/decode of canonical CALL/PUSH/POP/RET bytes to the
accepted `Stapel` frame obligations, `CodeImmutability` fetch
preservation and `StackUnwind` restoration/refusal results. No new
transition, decoder, memory model, source claim, checker/Spec/goal or
emitter change; no friend optimiser file touched.

- `StapelGeholt s b suffix`: the fetched window at `rip` is the canonical
  encoding of stack operation `b` followed by actual suffix bytes.
- `stapelGeholt_fetch`: fetched window decodes to `b` with consumed
  length, via `kanonisch_schritt_ueberein` (round-trip instances only).
- `byteschritt_geholt_call/push/pop/ret`: from actual bytes, the byte
  step stores the correct next-RIP return word (`ripNach` of pre-state
  `rip`) below the pre-state top. No hand-built decoded value enters.
- `geholt_verschachtelt_wiederhergestellt`: fetched call+push+pop+ret
  windows with executable prefixes, passing stack guards and disjoint
  slots, give the four-link byte-step chain, pre-state `rsp`
  restoration, landing on the correct next-RIP return word, inner-value
  delivery and full permission preservation. The `Decodiert` values are
  forced to match the fetched bytes (`stapelGeholt_fetch` yields exactly
  those outcomes); restoration reuses accepted `StackUnwind`.
- `nest_aussen_fremd`, `nest_innen_fremd`,
  `nest_schreiben_haelt_fetch`: both stack stores are `CodeFremd` to
  their code windows (interval bridge), so neither changes fetch/decode.
- `nestRahmen`, `nest_rahmen_ok`, `nest_slot_innen/aussen`,
  `nest_rahmen_sonde`: witness slots 8176/8184 are checked `Stapel`
  frame slots 2/3 of `{basis:=8160, tiefe:=32}`; every stage top stays
  inside; top is the 16-aligned call boundary.
- Guard/non-executable-return refusal stays explicit:
  `byteschritt_geholt_call_wache`, `byteschritt_geholt_push_wache`
  (fetched bytes decode, store hits the guard), and
  `byteschritt_geholt_ret_nicht_ausfuehrbar` (fetched `ret` steps, next
  byte step refuses; guards included since they carry
  `ausfuehrbar = false`).
- `codefremd_nie_selbst`: no store is foreign to its own code window,
  so overlap never claims preservation; the accepted
  `ueberlapp_geaendert_zeuge` is the negative side.
- Joint witnesses with real reached memory-changing execution:
  `geholt_verschachtelt_wiederhergestellt_zeuge` (call `+99` at 4096
  targeting 4200; push/pop/ret there; `laufBytes 4` chain; observable
  zero-to-4101 change; `rsp` restored; `rip` = 4101),
  `byteschritt_geholt_call_wache_zeuge`,
  `byteschritt_geholt_ret_nicht_ausfuehrbar_zeuge`.
- Supporting concrete facts: `nest_call/push/pop/ret_geholt` (+`_exe`),
  `nest_rsp0/rsp1`, `nest_oben0/obenp_schreibbar/lesbar`,
  `nest_call/push_schreibt`, `nest_push/ret_liest`, `nest_ziel_4200`,
  `nest_slots_disjunkt`, `wacheNest_geholt/exe/guard`,
  `retNest_geholt/exe/liest/kein_exec`. The pop/ret fetches measurably
  stop at the executable boundary (no over-read into non-executable
  suffix bytes).

## Verification

- `./lean-probe grammatik/Grammatik/X86/StackExecution.lean`:
  `== 0 error(s) in the COMPLETE output` (checked after every increment).
- `./lean-bau`: `Build completed successfully (428 jobs).`
- `#print axioms`: every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard goal axioms) or on
  no axioms at all. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (grep clean). No premise has type `Prop` itself; every premise is used.
- `Spec.lean`/goal untouched, so `gabbro_ziel` axioms are unaffected.

## Open / cuts (see file CUTS)

- ABI callee-save/entry contracts and source-call linkage (cuts by task).
- TSO bridge (all sequential over one `Speicher`); loader, entry,
  relocation, cost, final-image claims.
- Whole-source self-modifying-code refusal (only the per-store
  foreignness boundary is proved).

## Producer/consumer interface and next integration

- Producers reused (unchanged): `kanonisch_schritt_ueberein`,
  `byteschritt_weiter`, `schritt_*_erfolg/verweigert`, `Stapel`
  slot/permission lemmas, `CodeFremd` + preservation lemmas,
  `StackUnwind` restoration/refusal + `zeugFlags`.
- Consumers offered: `byteschritt_geholt_call/push/pop/ret` (any fetched
  stack-byte step), `geholt_verschachtelt_wiederhergestellt` (any
  four-site fetched nested call), `nest_schreiben_haelt_fetch` pattern.
- Measurable next step: a loader/relocation lane can place these two
  code windows from an actual image layout and reuse the fetch facts
  unchanged; a TSO-bridge lane can lift the per-access granularity while
  this sequential chain stays the reference.

## Task remarks

Nothing in the task appears wrong. `StackUnwind` was accepted in this
clone (commits `41ddd18f`, `d5bf467d`), so it was reused as instructed.
`pop rsp` keeps its accepted `schrittPopTop` shape and is explicitly not
covered by the fetched-pop lemma.
