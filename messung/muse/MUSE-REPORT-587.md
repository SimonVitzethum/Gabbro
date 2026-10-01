# MUSE-REPORT-587: Independent exact-candidate connection review of 569

## Scope

- Reviewed exact candidate pinned in `.tmp/review/SNAPSHOT.json`.
- Candidate diff (base `8596f83e` .. head `1ce78360`): `MUSE-REPORT-569.md`,
  `grammatik/Grammatik.lean` (one additive import), new
  `grammatik/Grammatik/X86/StackExecution.lean` (901 lines). No checker,
  Spec/goal, emitter, or friend optimiser file touched.
- Owner task (`OWNER-TASK.md`): connect actual `Byteschritt` fetch/decode of
  canonical CALL/PUSH/POP/RET bytes to accepted `Stapel` frame obligations,
  `CodeImmutability` fetch preservation and `StackUnwind` restoration/refusal,
  with correct next-RIP return word, pre-state `rsp` semantics, and explicit
  guard/non-executable-return and code-store overlap refusal.

## Reproduction

- Copied `review569:grammatik/Grammatik/X86/StackExecution.lean` into this
  clone (producers `Byteschritt`, `Stapel`, `CodeImmutability`, `StackUnwind`
  all present) and ran `./lean-probe`: `== 0 error(s) in the COMPLETE
  output; exit 0`. Removed the scratch copy afterwards; this branch owns no
  Lean file.
- `grep` for `sorry|admit|^axiom|native_decide|unsafe`: 0 hits.
- `#print axioms` (from probe output): every theorem depends on a subset of
  `[propext, Classical.choice, Quot.sound]` or on no axioms. Standard goal
  axioms only.
- File ends with an explicit `CUTS` block plus `#print axioms` for every main
  theorem. No premise has type `Prop` itself; spot-checked
  `geholt_verschachtelt_wiederhergestellt` uses every premise (all fetch,
  guard, disjointness, and `schritt` premises feed `byteschritt_weiter` and
  the reused `verschachtelt_wiederhergestellt`).

## Connection check (producer/consumer, no forgery)

- `StapelGeholt s b suffix` (`geholt s = encode b ++ suffix`) pins the
  fetched window to actual executable-memory bytes. `stapelGeholt_fetch`
  derives the decode outcome via accepted `kanonisch_schritt_ueberein`
  (round-trip instances only); no new decoder, transition, or memory model.
- `byteschritt_geholt_call/push/pop/ret` combine that fetch fact with the
  matching `schritt_*_erfolg` lemma through `byteschritt_weiter`. The stored
  return word is `ripNach` of the pre-state `rip` below the pre-state top;
  the `Decodiert` in each `schritt` premise is fixed to the canonical
  `⟨b, (encode b).length⟩`, i.e. exactly what the fetch yields, so no
  hand-built/forged decoded value can enter. `pop rsp` correctly stays out
  (keeps accepted `schrittPopTop` shape, stated in the doc comment).
- `geholt_verschachtelt_wiederhergestellt` lifts the four fetched legs to
  the byte-step chain plus `rsp` restoration, correct next-RIP landing,
  inner-value delivery, and permission preservation by reusing accepted
  `verschachtelt_wiederhergestellt` (StackUnwind). Disjointness, guards, and
  read-backs are all threaded through, not assumed away.
- `nest_schreiben_haelt_fetch` with `nest_aussen_fremd`/`nest_innen_fremd`
  (via `codeFremd_von_intervallen` and `geholt_nach_fremd_schreiben`) proves
  both stack stores keep the fetch. `codefremd_nie_selbst` plus the pointer
  to accepted `ueberlapp_geaendert_zeuge` keeps code-store overlap outside
  the preservation claim. Guard refusal (`call`/`push` via
  `write64_verweigert` + `byteschritt_verweigert_ohne_schritt`) and
  non-executable-return refusal (via `ret_ins_nicht_ausfuehrbar_verweigert`,
  guards included since they carry `ausfuehrbar = false`) stay explicit.
- Witnesses are joint and non-degenerate on real bytes: call `+99` at 4096
  targeting 4200, push/pop/ret there, `laufBytes 4` chain, observable
  zero-to-4101 memory change, `rsp` restored, `rip` = 4101
  (`geholt_verschachtelt_wiederhergestellt_zeuge`); planted refusals
  (`byteschritt_geholt_call_wache_zeuge`,
  `byteschritt_geholt_ret_nicht_ausfuehrbar_zeuge`) instantiate every premise
  jointly. Frame sonde (`nest_rahmen_sonde`) checks slots 8176/8184 as
  `Stapel` slots 2/3 of `{basis:=8160, tiefe:=32}` with 16-aligned top.
- No TSO, loader, relocation, source, ABI, cost, or final-image claim; CUTS
  names exactly these as open. No guessed ISA/FP faults, no atomic grouping,
  no contract-duty weakening, no wrong widths (`nest_ziel_4200` by `decide`).
  No vacuity: fetch stops at the executable boundary per the report, and the
  memory-change conjunct blocks the empty-run reading.

## Finding (non-blocking)

- `byteschritt_geholt_call_wache` contains a duplicated `have hs` (lines
  157-160); the second shadows the first. Harmless (build is green,
  semantics unaffected). Optional cleanup: delete one of the two lines. Not
  a repair gate.

## Accepted bounded claim

- For canonical CALL/PUSH/POP/RET bytes fetched from actual executable
  memory, the byte step executes the accepted `schritt` with the correct
  next-RIP return word; a four-site fetched nested call restores pre-state
  `rsp`, lands on the correct return word, delivers the inner value, and
  preserves permission maps; the two stack stores preserve fetch via
  `CodeFremd`; guard and non-executable-target refusals are loud; no store
  is foreign to its own code window. Sequential over one `Speicher` only;
  TSO/loader/source/ABI linkage remain open per CUTS.

## Next integration

- A loader/relocation lane can place the two code windows (4096/4200 shapes)
  from an actual image layout and reuse the fetch facts unchanged; a
  TSO-bridge lane can lift per-access granularity with this sequential chain
  as reference. Stable consumer entry points: `byteschritt_geholt_call`,
  `byteschritt_geholt_push`, `byteschritt_geholt_pop`,
  `byteschritt_geholt_ret`, `geholt_verschachtelt_wiederhergestellt`,
  `nest_schreiben_haelt_fetch`.

CANDIDATE: 569 1ce78360cfb314a54186290c45e5a0180bdf2974
VERDICT: ACCEPT
