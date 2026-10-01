# MUSE-REPORT-417: Reserve register-only conditional select (ConditionalMove)

## Task

Lane 417 (continuous Lean proof reserve): create ONLY
`grammatik/Grammatik/X86/ConditionalMove.lean` plus one additive X86 import
at the end of the umbrella. Model and prove register-only conditional select
from the canonical condition/flags/registers; preserve unaffected registers
and flags; prove the chosen operand. Show safe optional-lowering premises and
a real target-execution consumer. Never invent a second machine/IR; reuse the
accepted pilot vocabulary (`Ausfuehrung`, `FlagBeweis`, `Typen`,
`ControlFlow`). Keep codec/source/full-hardware correspondence OPEN
(CMOVcc has no native pilot encoding: `EMITTER-INVENTAR` lists NO
setcc/cmovcc, `Befehl` has no cmov constructor).

## What was done

New module `grammatik/Grammatik/X86/ConditionalMove.lean` (318 lines),
imported as the last line of `grammatik/Grammatik.lean`. No existing file
touched otherwise; no new machine, instruction, decoder row, memory model,
or source claim. Everything is proved over the REUSED definitions
`ControlFlow.cmovAnwenden`, `cmovSchritt`, `cmovMemSchritt` and the reused
witness states `witTrue`/`witFalse`.

Definitions (1):

- `cmovLowerOk (d : Decodiert) (flagsNachCmp flagsVorCmov : Flags) : Bool`
  — safe optional-lowering admission: checked decoded length
  (`laengeOk d.laenge`) AND flag identity between compare and select
  (`decide (flagsNachCmp = flagsVorCmov)`). Register-only by construction
  (the reused `cmovAnwenden` takes no memory operand). Validator admission,
  never a hardware fault.

Theorems (17), every premise used in its proof:

- `cmovAnwenden_nicht_wert` — untaken select keeps the destination word.
- `cmovAnwenden_genommen_wert` — taken select takes the source word.
- `cmovAnwenden_fremd` — every register except `dst` is preserved.
  (Flags/memory framing of the pure application is reused from
  `cmovAnwenden_flags` / `cmovAnwenden_speicher`, not restated.)
- `cmovSchritt_nicht_genommen` — untaken decoded step (complements the
  reused taken-only `cmovSchritt_genommen`).
- `cmovSchritt_verweigert` — bad decoded length refuses (`none`).
- `cmovSchritt_flags` / `cmovSchritt_speicher` / `cmovSchritt_rip` —
  per-step framing of a successful select step.
- `cmovLowerOk_garantiert` — admission implies good length AND flag
  identity (both conjuncts from the single `Bool` premise).
- `cmovLowerOk_laenge_verweigert` (length 0, concrete `decide`),
  `cmovLowerOk_flags_verweigert` (flag clobber, concrete `decide`),
  `cmovLowerOk_akzeptiert` (good length + identical flags, concrete).
- `cmov_store_verbraucher` — REAL pilot consumer: the taken select value
  is stored by the CANONICAL pilot `schritt` store64 (reused
  `schritt_store64_erfolg`); conclusion pins the full successor state and
  the selected word. Uses all five premises (`hbed` rewrites the word,
  `hne` keeps the store address, `h`/`hok` drive the store equation).
- Joint witnesses with concrete ALL-premise instantiation on the reused
  non-degenerate states plus the reused memory-changing run
  `cmov_speicher_zeuge` (word 20 stored at 8192, byte observably changed
  from zero; taken/untaken split reused from
  `cmov_witness_unterscheidet`):
  `cmovSchritt_nicht_genommen_zeuge`, `cmovSchritt_verweigert_zeuge`,
  `cmovLowerOk_garantiert_zeuge`, `cmov_store_verbraucher_zeuge`
  (stored word reads back as `some 20` through the real `schritt` store).
- No-speculation for the memory form is reused from
  `cmovMem_feheler_bleibt` (fault kept on the untaken path), not restated.

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` (grep: only the
English word "admitted" in two prose comments). No `Prop`-typed premise,
no discarded premise, no premise-free existential of a premise.

## Check results (measured, this clone)

- `./lean-probe grammatik/Grammatik/X86/ConditionalMove.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. All 17 `#print axioms`
  standard: value/framing/guarantee theorems depend on `[propext]` or
  nothing; the consumer and all four witnesses on `[propext, Quot.sound]`
  (via the reused store equation and witness run). Subset of the allowed
  triple everywhere.
- `gabbro_ziel` axiom check (scratch probe of `BeweisAtomar`):
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged, exit 0.
- `./lean-bau`: 392/393 targets build, INCLUDING this module (its 17
  axiom lines print in the build log); the final umbrella step
  (`Grammatik.lean`, the import-all file) aborts with
  `libc++abi: terminating ... failed to create thread`, exit 134.
  PROVEN ENVIRONMENTAL, not caused by this lane: with my umbrella
  one-liner stashed (`git stash push grammatik/Grammatik.lean`), the
  identical umbrella step fails identically; the change was restored
  afterwards (`git stash pop`, diff verified: exactly the 1-line import).
  Cause is machine resource exhaustion (many concurrent lanes; swap full).
  The merger/integration only needs to re-run `./lean-bau` on a quiet
  machine; no Lean content change is indicated.

## Open / CUTS (also at the end of the file)

- No `Befehl` constructor, `Codec` row, or bytes for CMOVcc: no codec,
  source, or emitted-native-ISA claim by design (pilot subset).
- No hardware correspondence: flag readings reuse `bedingung`, faults are
  the permission-checked `read64`/`write64` outcomes, not silicon.
- No TSO/GX, concurrency, cost, time, termination, or timing claim.
- 32-bit narrow clearing (upper32 zeroing) is not modelled — only the
  64-bit register select is stated.

## Addendum: integration gate failure (no merge) — evidence review

The integration gate failed with the output quoted in the repair request.
Reading that log exactly:

- Steps `[397/398]` in the integration checkout print all 17 of this
  lane's `#print axioms` lines (up to `cmov_store_verbraucher_zeuge`):
  **this module elaborated cleanly in the integration build too.**
- The failing step is the final umbrella `Grammatik.lean` import-all
  compile, aborting with `failed to create thread`, exit 134 — the same
  signature as measured locally (twice with, once without my change).

Repair status: **no defect found in owned files; nothing repaired because
nothing owned is broken.** Any edit (e.g. deleting the required `#print
axioms` lines or shrinking already-green proofs) would be a fake fix: the
crashing step loads ~398 modules and fails identically on unmodified
master. Fresh local re-checks after the verdict:

- `./lean-probe grammatik/Grammatik/X86/ConditionalMove.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, same 17 standard axiom
  lines as before.
- `./lean-bau`: again 392/393 green including this module, umbrella step
  aborts identically (`failed to create thread`, exit 134).

Concrete blocker for integration: machine resource exhaustion at the
umbrella import-all step (`-j2` thread spawn aborts under concurrent-lane
load; swap full). Resolution is operational, not a Lean change: re-run
the merge build on a quiet machine (or raise the thread/memory headroom
of the umbrella step in the unowned `lean-bau`/slot wrappers). A fresh
independent review of the changed commit is still required as ordered;
the Lean content is unchanged since `ee5d6ffd` except this report.

## Addendum 2: repeated identical gate failure

The gate failed again with a byte-identical signature: all 17 module
axiom lines print, then the umbrella `Grammatik.lean` step aborts with
`failed to create thread`, exit 134. Fresh local checks confirm the
unchanged picture: module `./lean-probe` exit 0 / 0 errors, `./lean-bau`
umbrella step aborts identically. Still no owned defect, still no Lean
change (this commit touches only the report). The blocker remains
operational: the umbrella import-all step cannot spawn threads under
current machine load, on unmodified master exactly as with this lane.

## Task feedback

Nothing in the task as written is wrong. One note for future reserve
lanes: under current machine load the umbrella `Grammatik.lean` step is
the fragile one (`-j2` thread spawn aborts); module-level `./lean-probe`
stays reliable and should remain the primary gate, with `./lean-bau`
re-run at integration.
