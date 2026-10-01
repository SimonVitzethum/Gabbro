# MUSE-REPORT-632: Direct-source closure (SourceValidatorConnection)

Lane 632, branch `muse/632`, clone `/home/simon/Dokumente/gabbro-muse/a632`.
Delivered and committed green; full project build green.

## What was done

New owned module `grammatik/Grammatik/X86/SourceValidatorConnection.lean`
(~340 lines) plus one additive import line in `grammatik/Grammatik.lean`.
It connects ONE genuinely checked finite source/byte certificate to its
covered source-step representation relation, consuming only already
accepted producers — no new IR, no new interpreter, no source/Spec/
checker/emitter or friend-reserved optimiser edits.

- Source side (recomputed in Lean from the typed AST, never from a Rust
  print): `srcStmt` (`Stmt.assignSlot` writing 42 into row 0 of the
  accepted `SourceMemory` witness declaration `witD`, one table with one
  `.int 0 100` field), evaluated by the goal's own `execStmt`
  (`srcStmt_ausgefuehrt`: slot 0 → 42, zero before).
- Target side: the accepted `LoadedExecution` store image `bildStore`
  (fetched bytes decode to `store64 rbx rax 0`, length 7; one loaded byte
  step moves 42 into data cell `0x102000`), admitted by the accepted
  `ValidatorExecution` strengthened entry check `valEintrittStark`.
- The link is the layout choice base `0x102000`/len 16/off 0, for which
  `effAddr` of the decoded store provably equals `slotAddr` and
  `storeReg .rax` provably equals `zahlWort witVal`.
- Checked Bool `srcCertOk` (pure data certificate `SrcByteCert`, no
  proof-valued field, no assumed simulation) recomputes 8 legs in Lean:
  `repOk`, `.p48` scope pin, `valEintrittStark`, fetched-decode shape,
  register value, address agreement, `lesbar8`, observed lowest byte 42.

## New definitions/theorems (exact names)

Defs: `SrcByteCert`, `certStart`, `srcStmt`, `srcCert`,
`srcCertOk`, `srcCertMutiertBytes`, `srcCertProfil57`, `srcCertWx`,
`srcCertFalschBasis`.
Theorems: `srcCert_ok`, `srcCert_mutiert_bytes_verweigert`,
`srcCert_profil57_verweigert`, `srcCert_wx_verweigert`,
`srcCert_falschBasis_verweigert`, `srcStmt_ausgefuehrt`,
`srcCert_sound`, `srcCert_sound_zeuge`.

`srcCert_sound` (from `srcCertOk c = true`) derives: the source step and
the decoded loaded step at joint post-states, `RepSlot` at the admitted
slot, source slot 42, target word read-back `read64 = some (zahlWort
witVal)` with `wortZahl` parse, `wohlgeformt .p48` + entry containment,
and the realised footprint `(zugriff store-decoded start).schreiben =
Fuss (slotAddr …)` — via `rep_schritt_bleibt`, `valStark_wohlgeformt`,
`valStark_eintrag`, `byte_aus_weiter`, `realisiert_store64_gefunden`,
`schritt_store64_erfolg`, `read64_nach_write64`,
`zahlWort_wortZahl`, `realisiert_store64_fuss`. Every one of the 8 Bool
legs is consumed. `srcCert_sound_zeuge` instantiates all premises
jointly (nondegenerate table-write source, memory-changing steps on both
sides: slot 0 → 42, target lowest byte 0 → 42) plus all four refusals.

## Verification

- `./lean-probe` on the module after every increment: final `0 error(s)`.
- `./lean-bau`: exit 0, 0 error lines, `Build completed successfully
  (448 jobs)`; module built as job 446/448.
- `#print axioms`: decide-theorems `[propext, Quot.sound]`; execution
  theorems `[propext, Classical.choice, Quot.sound]` — standard goal set,
  no `sorry`/`admit`/`axiom`/`native_decide`, no `Prop`-sorted premise.
- Acceptance and all four refusals (bytes/profile/map/certificate) hold
  by `decide` on concrete witnesses.

## What remains open (explicit CUTS in the file)

Single-fragment connection only (one `.int` slot, one `assignSlot` form,
one store image). No `valX86_sound`; general CFG/calls/loops,
concurrency (TSO/GX bridge with its owner), other widths/forms,
multi-step control flow, relocation re-decode, cost/time/termination and
hardware correspondence stay OPEN. Full source-to-final-loaded-bytes
validation remains OPEN until a generic closing proof is derived.

## Notes on the task (nothing blocking, two observations)

1. `.p57` accepts the same store-image map (`wohlgeformt .p57 bildStore
   = true`, measured), so the profile refusal is carried by an explicit
   `.p48` scope leg in `srcCertOk`, not by a mapping difference. This is
   documented in the file and the CUTS. If a future image is profile
   sensitive through the map itself, the pin can be dropped for it.
2. `match hs : byteschritt …` substitutes the discriminee in the branch
   goals, so the weiter-branch step conjunct is closed by `rfl`, with
   `hs` consumed by `byte_aus_weiter`. No workaround, just Lean behaviour
   recorded for follow-up lanes.
