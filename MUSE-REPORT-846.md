# MUSE-REPORT-846: Composition closing — patch-bytes closing

## What was done

Closed displacement/relocation patching to byte-level re-verification in the
new file `grammatik/Grammatik/X86/ComposePatchBytes.lean` (wired into
`grammatik/Grammatik.lean`), composing already-accepted modules without
re-proving their internals and without duplicating any interpreter/executor.

Closed producer/consumer interface: producer `Relokation.patchAt` /
`patchRel32` (finite byte patching) plus `BranchLayout` displacement facts
and `RelocatedExecution` site vocabulary (`RelocArt`, `relocBytes`,
`relocLen`, `relocBefehl`) produce the patched image; consumer
`DecodingCoverage.decode_abdeckung` / `decode_fenster_kongruenz`
(arbitrary-input re-decode carries its own length) and
`Byteschritt.kanonisch_schritt_ueberein` (execute permission plus
actual-memory step) consume it.

New definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `patchRel32_passt` — a successful rel32 field patch passed its
  signed-32 fit check (no axioms).
- `ComposePatchBytes_verbindung` — generic whole-region closing over
  arbitrary admitted inputs, all three `RelocArt` classes: patched taken
  region equals the site bytes; length equation on the patched window;
  exact region re-decodes; site in range; site bytes and outside frame as
  patched; form covered (`decktAb`). Axioms: propext, Quot.sound.
- `ComposePatchBytes_schritt` — permission-carrying execution leg: fetched
  patched window plus execute permission over the patched length reaches
  the admitted `schritt` successor, with the patch-range conjunct keeping
  the producer premise load-bearing. Axioms: propext, Classical.choice,
  Quot.sound.
- `ComposePatchBytes_feld_verbindung` — field-level displacement agreement
  for the jump site: the re-decoded displacement IS the patched value,
  via `rel32Bytes_dispSigned` and decoder determinism (same bytes decode
  to one instruction), never through decoder internals; plus length/fit/
  opcode-survival/site/coverage/exact-region conclusions. Axioms: propext,
  Quot.sound.
- `ComposePatchBytes_ueberlauf_verweigert` — planted overrun refusal
  (no axioms). `ComposePatchBytes_opcode_falsch_verweigert` — planted
  forged-opcode re-decode refusal (propext only, from `decide`).
- `patchZeugenBild` / `patchZeugenDisp` / `patchZeugenGepatcht` — concrete
  jump `E9 00 00 00 00` patched to displacement +16.
- `ComposePatchBytes_verbindung_zeuge` — joint witness: both `verbindung`
  premises decided on the concrete patched jump; derived region,
  displacement-agreement (`dispSigned 16 = 16`) and length facts; a
  reached memory-changing call run reused from `ruf_schritt_zeuge`
  (return address stored, read back, observed byte change); patch-level
  (overrun), decode-level (forged opcode), permission-level
  (`ohne_exec_verweigert`: readable but not executable) and
  execution-level refusals (`opcode_geaendert_verweigert`), plus the
  patched-byte-moves-target pair (`sprungziel_folgt_byte`: displacement
  byte 16 vs 17 moves the executed target 4117 vs 4118). Axioms:
  propext, Classical.choice, Quot.sound.

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is used
by its proof; conclusions are derived, never premise restatements. The
byte-level non-degeneracy analog of the inhabitation rule: accepted
multi-byte image plus a reached `byteschritt` run with an observed memory
change (source-level tables do not exist at this layer).

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposePatchBytes.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (509 jobs).`
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`: 0 errors;
  `gabbro_ziel` still on exactly propext, Classical.choice, Quot.sound.

## What remains open (explicit CUTS in the file)

Whole-image layout convergence and the `valX86` closing theorem (consumer
`ValidatorSkeleton` business); call/conditional field-level agreement (same
determinism pattern as the jump leg, not carried out here); TSO/GX bridge,
concurrency, source correspondence, contracts, cost/time. None assumed.

## Task feedback

Nothing in the task was wrong. Two friction points worth recording: (1) the
pre-existing name `zeugenBild : Bild` forced a rename of my witness
(`patchZeugenBild`); a lane-local witness-name registry would avoid the
collision-repair round. (2) `(x, y)` pair notation does not elaborate to a
structure under an expected type — `⟨x, y⟩` must be used for `Decodiert`
values; `dsimp only` reliably reduces the resulting projections.
