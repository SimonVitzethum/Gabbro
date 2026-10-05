# MUSE-REPORT-1163: Pipeline: atomics and locks onto TSO

Lane 1163, clone `/home/simon/Dokumente/gabbro-muse/a1163`, branch `muse/1163`.
Owned files only: `grammatik/Grammatik/X86/PipelineAtomics.lean` (new, ~800 lines),
one import line in `grammatik/Grammatik.lean`, this report. No other file touched.

## What was done

New module `Gabbro.Grammatik.X86.PipelineAtomics` lowers a small source atomic
vocabulary to TSO target forms, reusing accepted definitions unchanged:

- Source ops `AtomQuelle`: `lese`/`schreibe` (address + `Ordnung` + machine
  operands), `zaun`, `xadd`/`cas` (src/base/disp, expected value in rax for CAS,
  as hardware compares against rax), `sperre` (fence-bracketed body list).
- Target ops `ZielOp`: `movLoad`/`movStore` (pilot `load64`/`store64`) and
  `lock` (`LockForm`, reused). Bytes `zielBytes` via reused `encode`/`encodeLock`.
- Lowering `senkEinzeln`/`senkListe`/`senkAtom` + decided validator `valAtom`
  with `valAtom_korrekt`. Relaxed/acquire loads and release stores go to plain
  aligned MOV; fences to MFENCE; RMW to LOCK XADD / LOCK CMPXCHG; lock sections
  to MFENCE-bracketed bodies. Nested lock sections are REFUSED.
- NAMED hardware assumption `TSOPlainRegel` (the plain-MOV reordering rule:
  `unsichtbar`, `zaunLiest`, `drainSichtbar`, `eigenSichtbar`), discharged once
  by `TSOPlainRegel_gilt` against the accepted TSO model and cited by every
  plain-access theorem.
- Per-access correspondence, each with ledger closing (`ledgerDeckt`):
  `lese_korrekt` (pilot step + TSO group under the named rule),
  `schreibe_korrekt` (footprint + off-core invisibility + on-core visibility),
  `zaun_korrekt` (+ `zaun_byteseite`), `xadd_korrekt`, `cas_korrekt_erfolg`,
  `cas_korrekt_fehlschlag`, `sperre_korrekt` (with run-chaining helper
  `erreichbar_kette`).
- GX legs: `gx_lese_korrekt` (committed read simulates the W read, reusing
  `wLesbar_aus_gruppe`) and `rely_stabil` (reusing `havoc_erhaelt_gruppenwert`).
  `schwach_ist_gX` is cited, not applied — the recorded boundary.
- Refusals: `sperre_verschachtelt_verweigert`, `lese_unlesbar_verweigert`,
  `xadd_unaligned_verweigert`, `xadd_puffer_verweigert`. Poison probes
  (`gift_zaun_stumpf15`, `gift_zaun_nachbar_lfence`, `gift_zaun_mit_lock_ud`,
  `gift_zaun_byteseite_nachbar`, `gift_holt_puffer`, `gift_holt_unaligned`,
  `gift_holt_schreibfehler`) reuse accepted pins; one fetched positive
  (`positiv_holt_xadd`: word 10 to 15, rax takes 10).
- Joint witness `senkAtom_zeuge`: all five lowerings + a reached two-core drain
  run with observable memory change (`MfenceDrainOwn_verbindung_zeuge`), a
  written table (`witD.schreibt () ()`), and the fetched memory-changing XADD.
  Non-degenerate on both sides.
- File ends with CUTS and `#print axioms` for every main theorem. Axioms are
  standard subsets of `propext, Classical.choice, Quot.sound` (verified in probe
  output). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no discarded
  premises (rg-verified), English only.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/PipelineAtomics.lean`:
  `== 0 error(s) in the COMPLETE output`, no warnings.
- `./lean-bau`: `Build completed successfully (608 jobs).`
  (`✔ [607/608] Built Grammatik`). Three earlier `lean-bau` attempts failed with
  resource-shaped process errors (`bad_alloc`, `failed to create thread`,
  `failed to read` existing oleans); the fourth attempt with drained load passed
  fully. This was apparatus pressure, not a file defect (probe was green throughout).

## What remains open (also in CUTS)

No `execBlock` correspondence (see task critique below); no register-address
binding for RMW/fence byte forms; no SFENCE/LFENCE lowering (refusal side only);
no 8-issue word-install proof; no full `SchrittW`; no `seq_cst` total order;
no fairness/progress/retry-bound/timing/cost claims.

## Task critique (rule 4/9 disclosure)

The task asks for "a correctness theorem in the style of `pipeline_correct_entry`
(source `execBlock` result related to the byte-level run on the loaded image)".
That theorem is unstatable as specified: `execBlock`'s fragment has no atomic,
fence or lock forms (Pipeline CUTS: integer slots only), and I am forbidden from
changing `Syntax`/`Semantik`, adding a second interpreter, or editing existing
files. The per-access correspondence theorems above are the honest weaker
replacement, recorded in CUTS. Related: `LockXaddFetch`/`LockCmpxchgSuccess` and
the narrow-fence modules are consumed as vocabulary and refusal-side facts, not
restated as fetched connections — the register-address binding is the stated gap.
