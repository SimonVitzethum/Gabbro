# MUSE-REPORT-1271: Byte-level entry/call linkage for the start-anchored bridged run

## What was done

NEW FILE `grammatik/Grammatik/X86/TsoGxEntryBytes.lean` (plus one import line
appended to `grammatik/Grammatik.lean`). Follow-up of lane 1253
(`TsoGxStart.lean`): the source-level entry/call prefix (`RufStartG` to the
fragment head) is linked to the byte machine, where `PipelineEntry.prolog_lauf`
and `StackExecution.geholt_verschachtelt_wiederhergestellt` live. All existing
definitions were reused unchanged; no existing file was edited except the
import append; `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched;
no new IR, no second interpreter, no Rust.

New definitions/theorems (namespace `Gabbro.Grammatik.X86.TsoGxEntryBytes`):

- `StapelLayoutFremd` — admission predicate: both stack slots foreign to every
  placed slot.
- `worldRep_schreiben_fremd` — one foreign `write64` keeps `WorldRep` (frame
  via `read64_rahmen`, permissions via `lesbar8/schreibbar8_nach_schreiben`).
- `eintrittCallPrefix_lauf` — entry run (`proLen` fetched steps) plus one
  fetched call/push/pop/ret nest reaches the fragment-head byte state: stack
  pointer restored, next-`rip` return word, inner value delivered, permissions
  kept. Named extra admission: `src ≠ rsp` (call preserves the pushed value
  into `dst`).
- `byteKopf_antwortErhalten` — from an admitted entry (`prologImageOk`,
  caller's `AbiArgs` duty) the head state keeps the entry world represented
  and every variable in its pipeline register. `EnvRepr` is ESTABLISHED by the
  fetched entry sequence (`prolog_lauf`, joined by run determinism), not
  assumed; `WorldRep` crosses both frame writes by the foreign-store frame;
  pop/ret memory passthrough derived from the accepted success lemmas.
- Refusals: `eintrittCall_verweigert_wache`,
  `eintrittCall_verweigert_ret_nicht_ausfuehrbar`,
  `eintrittProlog_verweigert_ohne_frisch` (¬Pairwise → `prologOk = false`).
- Poison probes: `gift_wache_verweigert`, `gift_ret_verweigert`,
  `gift_prolog_clobber` (+ `giftPrologCfg`, `gift_prolog_clobber_grund`, both
  by `decide` / through the refusal theorem).
- `eintrittCallPrefix_zeuge` — joint witness: source prefix reaches its head
  on the accepted program (table written, start world `konto[0] = 0`, logged
  entry world `konto[0] = 5`) AND the byte prefix runs 4 fetched steps whose
  frame is written and restored through memory (return word reads back, same
  byte differs, `rsp` restored). Non-degenerate: memory-changing reached run
  on both sides.

## Verification

- `./lean-probe` per addition: final `== 0 error(s)`.
- `./lean-bau`: `Build completed successfully (658 jobs)`, whole project green.
- `#print axioms` for every main theorem: at most
  `propext, Classical.choice, Quot.sound` (standard; `giftPrologCfg`: none).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise of every
  theorem is used by its proof (checked by construction: each premise feeds
  the accepted lemma application, a rewrite, or the transport).

## What remains open (also in CUTS)

- No lowering certificate from source program `eP` to bytes: the IDENTITY of
  the source fragment head with the byte head is OPEN with the pipeline
  owners. Proved here is co-reachability plus transport.
- No TSO/GX bridge: all facts sequential over one canonical `Speicher`.
- One call nest only (`dst ≠ rsp`, `src ≠ rsp`, disjoint slots); deeper
  nesting, callee-saved registers, stack/float/pointer parameters, and
  interrupt/guard-page behaviour beyond the two planted refusals are refused
  or open. Pilot ISA, one core, model memory, no time (inherited cuts).

## What I believe is wrong in the task

Nothing blocking. One note: the task text says the linkage target is "the same
fragment head state that the source-level prefix reaches" — without a lowering
certificate `eP → bytes` that identity is unstatable (different machines), so
the deliverable proves joint reachability plus representation transport and
books the identity as OPEN. If the reviewers want the identity, it needs the
pipeline owners' certificate, not more premises here (rule 12/4a would forbid
assuming it).
