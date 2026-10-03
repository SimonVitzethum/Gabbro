# Muse Report 778 — Hardware completion: LOCK XADD fetch-add

Lane 778, clone `/home/simon/Dokumente/gabbro-muse/a778`, branch `muse/778`.
Owned files only: `grammatik/Grammatik/X86/LockXaddFetch.lean` (new),
`grammatik/Grammatik.lean` (one added import line), this report.

## What was done

New thin connection module `Grammatik/X86/LockXaddFetch.lean` covering the
64-bit LOCK XADD word form as constant-cost fetch-add. No new register,
memory, decoder, arithmetic or source model; everything reuses the accepted
vocabulary: `Zustand`, `read64`/`write64`, `Fuss`, `TSOZustand`,
`lockSchritt`/`lockKosten`/`casKosten` (`LockedOps`); `LockForm`,
`encodeLock`, `decodeLock`/`decodeLockExt`, `LockMaschine`, `toTSO`,
`lockSchrittVoll`, `lockFetch`/`lockByteschritt`, observers and pins
(`LockedInstructionExecution`); `decodeExt` (`ExtendedExecution`).

New definitions/theorems (exact names):

- `xaddKosten` (def): fetch-add shape cost as reuse of accepted `lockKosten`.
- `xadd_kosten_eins`: one fetch-add counts one shape unit.
- `xadd_guenstiger_als_cas`: one fetch-add costs at most any CAS retry
  count (`casKosten n = n + 1`; unboundedness itself stays with the accepted
  `cas_schleife_unbeschraenkt`).
- `LockXaddFetch_verbindung` (TARGET): a LOCK XADD word step is a
  constant-cost fetch-add with full local barrier (empty own buffer required,
  all buffers untouched), one atomicity unit (single RMW event over the
  pinned 8-byte `Fuss` footprint), precise observables (word grows by the
  source register, source takes the old word, addition flags via `add64`,
  RIP advance by parsed length), TSO projection agreement on the same words
  (accepted `lockVoll_xadd_adapter`), and cost one below every CAS retry.
  Every premise is used by the proof (each pins one guard of the accepted
  `lockSchrittVoll_xadd_erfolg` / adapter).
- `LockXaddFetch_verbindung_zeuge` (TARGET companion): all premises jointly
  on the accepted fetched `zeugXadd` machine (word 10 at 8192, delta 5 in
  rax, base rbp, empty buffer, 9 checked bytes); the connection fires and
  the reached fetched run changes memory (10 to 15, old 10 back through
  rax, start word observably changed). Non-degenerate, memory-changing.
- `xadd_gemeinsam_verweigert`: `decodeExt` refuses the LOCK XADD bytes
  (no older row shadows it; reused pin).
- `xadd_kombiniert_nimmt`: `decodeLockExt` takes the LOCK XADD row whole
  where `decodeExt` refuses (admitted bytes enter through the common
  architecture; reused pins).
- `xadd_nachbarn_verweigern`: unsupported neighbours refuse explicitly —
  pending own store, misaligned word, LOCK on register destination (#UD),
  execute-denied bytes (reused pins).

Manual provenance (clone-local `.tmp/HARDWARE-REFERENCES/REFERENCES.json`,
Intel SDM combined vols 1-4, edition 325462-093US, Sep 2026): LOCK prefix
Vol. 2A 3-565/3-566, XADD Vol. 2D 6-27/6-28. Only these named entries are
used; no silicon timing, vendor-difference or cycle claim.

## Verification

- `./lean-probe grammatik/Grammatik/X86/LockXaddFetch.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (last): `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (485 jobs).` Whole project green.
- Axioms of new theorems: subsets of `[propext, Quot.sound]` (see `#print
  axioms` block at file end; full output in build log).
- `gabbro_ziel` axioms (scratch probe `.tmp/zielcheck778.lean`, not
  committed): `[propext, Classical.choice, Quot.sound]` — standard.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched.

## Apparatus findings (not code defects)

`./lean-bau` failed three times before the final green run while the owned
module itself always compiled (its `#print axioms` lines emitted every
time): twice the root `Grammatik.lean` step reported a *different* missing
dependency olean (`SourceAccessCompleteness`, then `Zielsatz/Divergenz`,
then `FortschrittZeuge`) although all those files existed at rest
immediately afterwards, and twice (including once for the single-file
`gabbro_ziel` probe) `lean` died with `failed to create thread`
(exit 134). All transient under concurrent load; a plain retry turned the
full 485-job build green with no source change. If the merge gate sees a
red root step with missing-olean or thread-creation errors, retry before
blaming the candidate.

## What remains open (see CUTS in the file)

- No silicon correspondence: encodings are the stated canonical subset
  with self-consistency (generic round trips live with the owner
  `LockedInstructionExecution`), not proved hardware truth.
- Only the 64-bit word row (REX.W + 0F C1, mod=2 base+disp32); narrower
  widths, LOCK CMPXCHG (stays with its owner), other addressing modes and
  unlocked XADD stay open.
- No W/GX refinement and no cycle/latency/progress/fairness claim; the
  bridge owns refinement, `xaddKosten` is a shape count, CAS retry stays
  unbounded here.
- No source, checker, contract, budget, duty or goal change.

## Task remarks

Nothing in the task statement appears wrong. One note: the task asks for
"full barrier" for LOCK XADD; what is proved is the *local* barrier the
accepted model reaches (empty own buffer as precondition, buffers
untouched, canonical-memory operation) — a global fence claim over
foreign buffers or device/MMIO effects is correctly left open and is
stated as such in CUTS.
