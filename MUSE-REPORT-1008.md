# MUSE-REPORT-1008: Exact review of author 858 (Composition closing: entry-duties closing)

CANDIDATE: 858 a305fcb8629bb72ab02d407da548f282a0f55fef
VERDICT: ACCEPT

## Scope and method

- Clone verified `/home/simon/Dokumente/gabbro-muse/a1008`, branch `muse/1008`
  (HEAD `b040b155`), which equals the candidate base in
  `.tmp/review/SNAPSHOT.json` (`base b040b155...`, `clean: true`).
  The pinned snapshot was reviewed exactly: `OWNER-TASK.md`, `PATCH.diff`
  (388 diff lines: new `grammatik/Grammatik/X86/ComposeEntryDuties.lean`,
  one import line in `grammatik/Grammatik.lean`, `MUSE-REPORT-858.md`),
  `MUSE-REPORT-858.md`, `BUILD-EVIDENCE.json`.
- Every reused accepted name was checked against this clone's identical
  base tree (`EntryExecution.lean`, `ValidatorSkeleton.lean`,
  `GateStub.lean`, `TableLayout.lean` usages); statement shapes were read,
  not assumed. No source file was touched: this lane owns only this report.
- `.tmp/HARDWARE-REFERENCES/` (Intel instruction reference PDF/TXT,
  `REFERENCES.json`) inspected for scope: the candidate adds no new
  instruction semantics, so the manual check reduces to the one inherited
  executed form (see architecture section).

## What the candidate does (confirmed from the patch)

- `pflichtSchluss` (def): `eintrittZulassung && bildDeckung && valLayout
  && externOk` per image. Pure Bool conjunction over accepted predicates.
- `pflicht_eintritt`, `pflicht_valX86`: projections. The tuple
  projections (`h.1.1.1`, `h.1.1.2`, `h.1.2`, `h.2`) were hand-checked
  against the left-nested `&&` shape: correct.
- `ComposeEntryDuties_verbindung` (TARGET): composes `pflicht_eintritt`,
  `pflicht_valX86`, `zulassung_wohlgeformt`,
  `zulassung_rip_ausfuehrbar` by name. RIP executability is through the
  CHECKED loaded mapping (`(geladen bild bias).ausfuehrbar`), not the
  state's permission function. Verified against the accepted shapes in
  `EntryExecution.lean` lines 27-61.
- `pflicht_erster_schritt`: reuses `zulassung_erster_schritt` (which
  concludes `ausfuehrbar /\ byteschritt = weiter`); the `hstep.2,
  hstep.1` swap matches the stated goal order. Correct.
- Four generic refusals (`pflicht_verweigert_eintritt` /
  `_ohne_deckung` / `_ohne_layout` / `_ohne_extern`): `unfold; rw [h];
  simp` per missing conjunct. Each uses its premise. Correct.
- Four `decide` probes: `pflicht_zeuge_ok` (accept on minimal image),
  `pflicht_mutiert_verweigert` (opcode 195->0; mapping intact per
  accepted `valZeuge_mutiert_mapping_bleibt`), `pflicht_layout_verweigert`
  (extents [4096,4112)/[4104,4120) overlap), `pflicht_extern_verweigert`
  (`bewiesen := false`; matches accepted `valFremd_verweigert` shape).
- `ComposeEntryDuties_verbindung_zeuge` (TARGET companion): the
  `obtain` pattern against `eintrittAusf_zeuge` (9 components, one `_`)
  was verified component-by-component against `EntryExecution.lean`
  lines 295-311. The discarded component is the raw admission truth,
  replaced by the stronger `pflicht_zeuge_ok` — not a premise discard
  under rule 4(d) (existential component, and the theorem itself has no
  premises). Witness is non-degenerate: reached run with table-writing
  call (`0 -> 5`, inherited via `vertragStandort_lauf_zeuge`), real
  eight-byte x86 memory change (`write_read_zeuge`), `ReqAmEintritt` at
  actual values, fetched `ret` stepping to RIP zero, plus three planted
  refusals (unlisted RIP 0x5000, clobbered gate `torAusClobber`, mutated
  opcode). Fixture shapes (`{... with datei}`, `{... with zustand}`,
  `{tab, basis, len, ausr}`, `{ort, bewiesen}`, `⟨.ret, 1⟩`) all match
  accepted usages verbatim.

## Rule compliance

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the final patch
  (token grep over `PATCH.diff`: only English words "admitted/admits/
  admission" and `#print axioms` lines). One mid-development `sorryAx`
  appears in `BUILD-EVIDENCE.json` (unsolved-goals probe) and is repaired
  in the immediately following probe run — evidence of repair, not a
  defect in the candidate.
- No Prop-typed premises, no restated-premise conclusions, no
  contract-parameter quantification, no new semantics (execution leg
  goes through `byteschritt`/`schritt`), every premise used.
- ZEUGE names exact per task; CUTS block present and precise (source
  lowering -> lane 287 + QUELLBRUECKE; per-access target-to-W/GX -> TSO
  bridge lane; budget/work + `valX86_sound` -> their owners;
  multi-step control flow / entry legality beyond containment /
  callee templates -> their owners). Missing legs are named, never
  assumed.
- Owned files only (`ComposeEntryDuties.lean`, `Grammatik.lean` import
  line, report). No diagnostic/gift/example/CLI numbers, no MARKE_EMIT,
  no Spec/checker/emitter/friend-optimizer touches.

## Architecture assessment (byte forms through gates)

- The module introduces zero new hardware semantics: no decoder,
  executor, register/REX/width/flag model, no TSO/memory-ordering claim,
  no MXCSR/feature/interrupt-enable content, no fault invention. All
  such behavior is inherited from accepted producers by name.
- The one executed form is the accepted minimal `ret` (1 byte, opcode
  195, `⟨.ret, 1⟩` fetch with empty remainder, step to RIP zero) —
  nothing new to check against the Intel reference.
- No invented determinism over undefined hardware state; refusal `Bool`s
  are validator admission, and the CUTS say so explicitly. No desired
  simulation premise: the composition concludes truths of accepted
  predicates, and the execution leg goes through the accepted byte
  machine, not through the conjunction itself.
- `torRuferPflicht` handling (report remark): consumed only through the
  accepted channel-link theorem and reached-run contract at actual
  values; the gate-call lowering obligation is correctly left open and
  named. Agreed.

## Evidence and bounds of this ACCEPT

- Author evidence: final `lean-probe` 0 errors with all theorems on
  `[propext]`, `pflicht_erster_schritt` on `[propext, Quot.sound]`
  (inherited), TARGET witness on exactly `[propext, Classical.choice,
  Quot.sound]` (standard `gabbro_ziel` set); final `lean-bau` exit 0,
  0 error lines, 511 jobs, committed as `a305fcb8` on the author's
  branch. The `#print` line numbers in the build log (272-284) are
  consistent with the 286-line new file; the TARGET's own print is
  evidenced in the probe runs.
- This ACCEPT is bounded to the candidate content as inspected. I did
  not re-execute the queued wrappers from this reviewer sandbox
  (execution tool unavailable here; applying the patch as buildable
  source would also violate the owned-files rule). The standard
  merge-time `lean-bau` rebuild remains the final gate, as always.

## What remains open

- Nothing from this candidate. Composition is closed for its stated
  interface; the named open consumer legs (source lowering, per-access
  target-to-W/GX, budget/work, `valX86_sound`, multi-step control flow)
  rest with their owners per the CUTS.

## Task remarks

- Nothing in the lane-858 task statement was found wrong. The review
  task's demand to check byte forms/REX/flags/TSO/MXCSR is correctly
  scoped here to "inherited, nothing new" — recorded above rather than
  treated as a gap.
