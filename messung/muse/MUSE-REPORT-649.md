# MUSE-REPORT-649: Independent exact-candidate review of 648

## Scope

Review-only. Inspected the exact pinned snapshot `.tmp/review/SNAPSHOT.json`,
owner task `.tmp/review/author-648/OWNER-TASK.md`, `PATCH.diff` and the actual
candidate module `.tmp/review/author-648/grammatik/Grammatik/X86/GenericSourceByteCert.lean`
(606 lines). No source edits; this report is the only owned file. Verified clone
`/home/simon/Dokumente/gabbro-muse/a649`, branch `muse/649`.

CANDIDATE: 648 bbd1ffe8c5b61fdae966fd65cd239fcd9524fdb0

## What the candidate claims

New file `grammatik/Grammatik/X86/GenericSourceByteCert.lean` (+ one import in
`grammatik/Grammatik.lean`): finite-data `GenByteCert` with recomputed Bool
`genCertOk`, generic soundness `genCert_sound` over any declaration/table/field/
expression/environment, two acceptances through the same checker (values 42/17,
ranges `0..100`/`10..60`, distinct declarations `witD`/`witDB`), six planted
refusals (opcode, entry, layout, value, profile, map), joint non-degenerate
witness `genCert_sound_zeuge`. Lane-632 fixed witness untouched.

## Checks performed

- Banned patterns: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`
  (word-boundary grep, exit 1 = absent); no `intro _` / `have _ :=` discards.
- Staged the exact candidate file plus its one import line temporarily, then:
  `./lean-probe grammatik/Grammatik/X86/GenericSourceByteCert.lean` ->
  `== 0 error(s) in the COMPLETE output; exit 0`.
  `./lean-bau` -> `Build completed successfully (459 jobs).`
  (458 in author evidence; +1 job is newer-master drift, not a candidate change.)
  Reverted the staging afterwards (`git checkout -- grammatik/Grammatik.lean`,
  removed the staged file); `git status` clean before writing this report.
- `#print axioms`: `genCert_sound` and `genCert_sound_zeuge` on exactly
  `propext, Classical.choice, Quot.sound`; `genCertOk`, acceptances and all six
  refusals on a subset. Standard goal axioms, no new axiom.
- All referenced interfaces resolve to accepted modules in this clone:
  `repOk`/`repOk_klingt`/`rep_schritt_bleibt`/`zahlWort_wortZahl`/`witD` family
  (`SourceMemory`), `valEintrittStark`/`valStark_wohlgeformt`/`valStark_eintrag`
  (`ValidatorExecution`), `bildStore`/`bildStoreMutiert`/`bildStoreWx`
  (`LoadedExecution`), `fetchDekodiert`/`byteschritt`/`ausgangByte`
  (`Byteschritt`), `byte_aus_weiter`/`realisiert_store64_gefunden`/`_fuss`
  (`AccessExecution`), `schritt_store64_erfolg` (`Ausfuehrung`),
  `effAddr_null` (`EffectiveAddress`), `read64_nach_write64` (`Speicher`).

## Semantic review

- Real source semantics: `genCert_sound` consumes the actual `execStmt` step
  (`hExec`) over the goal's own `eval`, with `hLese`/`hk`/`hv` naming the
  evaluated index/value. Real fetched bytes: `genCertStart` recomputed in Lean
  via `bildZustand`, `fetchDekodiert` shape pinned, `byteschritt` decomposed via
  `byte_aus_weiter`, never a forged input.
- No desired simulation in premises: `hvCert : v.n = c.vval` is finite number
  identity linking the evaluated source value to the certificate datum (which
  determines `rax` via `genCertReg`). `RepSlot`, word read-back, parse and exact
  footprint are DERIVED via `rep_schritt_bleibt` + fetched-step decomposition.
  No proof-valued certificate field; `GenByteCert` is pure data.
- No target-state equality smuggled: conclusion's `read64 = some (zahlWort v)`
  comes from the decoded store's `write64` + `read64_nach_write64`, not from the
  single-byte `ausgangByte` leg (which only excludes the `verweigert` branch).
  Full-word claim therefore rests on accepted store semantics; the CUTS honestly
  notes the checker's observation is the low byte only (values >255 need a wider
  window). No unjustified byte-to-carrier atomicity.
- All theorem premises used: `hT`/`hLoEq`/`hHiEq` move range onto field type;
  `hLese`/`hk`/`hv`/`hExec` feed `rep_schritt_bleibt`; `hvCert` feeds register
  identity; every `genCertOk` conjunct feeds admission/entry/decode/consistency/
  readability/byte legs across the two `byteschritt` branches. No vacuous joint.
- No contract weakened or quantified away; no conclusion-as-premise; memory
  changes on both sides (source `0->42`/`10->17`, target byte `0->42`/`->17`,
  `RepSlot` at joint post-states). Non-degenerate on both declarations.
- Refusals genuine, each by `decide`: opcode (forged image defeats fetch),
  entry (data-section start), layout (verified `repOk` still holds at base 4096
  from its definition, so refusal is the redundant `rbase = basis + off` leg as
  claimed), value (43 vs byte 42 breaks value/byte leg), profile (`.p57` refused
  by explicit scope pin, honestly noted as scope leg not mapping difference),
  map (writable code). Six distinct mutation axes, not one test renamed.
- Lane-632 witness untouched (PATCH touches only the new file, the import line,
  and the report); `witD` reuse is witness-A instantiation only, never a premise
  of the generic theorem. No `DecidableEq` on `World`; finite syntax/layout
  projections only. No checker/Spec/goal/Rust/emitter/friend-file edits.

## Accepted bounded claim

Generic finite-data certificate for the admitted fragment only: one `.int lo hi`
slot with `repOk`, one `assignSlot` form, one decoded `store64 rbx rax` image
under pinned profile `.p48`. From `genCertOk c = true` + the actual source step
+ finite value identity, the decoded loaded step agrees (representation at joint
  post-states, word read-back and parse, mapping/entry legs, exact realised
  footprint). Two distinct source assignments through the same checker, one joint
  memory-changing witness, six planted refusals. CUTS truthful about all of this.

## Not claimed (preserved)

No `valX86_sound`; no multi-step control flow, relocation re-decode, TSO/GX
bridge, hardware, OS/loader, optimiser/loader closure, cost/time/budget-stop;
single-low-byte observation only. None of this is presented as closed.

## Verdict

VERDICT: ACCEPT
