# Connection plan: direct-compiler connection wave (lanes 559-575)

*Owner: lane 558. Base: `8596f83e` (merge Muse 552). Scope: this document
plus `MUSE-REPORT-558.md` only. No Lean, checker, goal, emitter or optimiser
file is changed by this lane. This is an integration-owner handoff, not proof
acceptance and not permission to merge. Reviewer: lane 576.
Binding closure plan since 2026-10-04: `COMPILER-SCHLUSSPLAN.md`.*

## 0. What counts as connected (closure rule for every lane below)

A lane closes only when it derives a NEW fact about real execution or
projection from actual byte evidence through existing accepted definitions,
with all of: (a) reuse of the canonical producer (no second decoder,
loader, executor or IR); (b) a jointly inhabited non-degenerate `_zeuge`
(a table some function writes; a reached run with a memory-changing step);
(c) a planted refusal (truncated/corrupt/unaligned/out-of-range/foreign
probe that fails closed); (d) standard goal axioms unchanged; (e) an exact
`CUTS` block. Anything weaker is labelled blocked, never closure.

## 1. Derived results (reusable producers) vs trusted inputs and cuts

Derived in this snapshot (checked by reading the defining files):

- `Codec.decode : List Byte -> Option (Decodiert x List Byte)`,
  `Codec.encode`, `roundtrip`, `roundtrip_len_ok`, per-form round-trips,
  `decode_nichts_*` refusals.
- `Byteschritt.fetchDekodiert`, `geholt`, `byteschritt`, `ByteAusgang`,
  `fetchCap` (= 15), `ausfuehrbarN`; `fetchDekodiert_entspricht`,
  `byteschritt_weiter`, `byteschritt_verweigert_ohne_fetch/schritt`,
  `fetch_nutzt_nur_praefix`, `kanonisch_schritt_ueberein`; witnesses
  `kette_mov_store_load`, `opcode_geaendert_verweigert`,
  `praefix_abgeschnitten_verweigert`, `ohne_exec_verweigert`.
- `Ausfuehrung.schritt : Decodiert -> Zustand -> Option Zustand`,
  `ripNach`, `effAddr`, `regSet`; per-form `schritt_*` success/refusal
  lemmas for all 14 pilot forms.
- `Bild`: `Profil`, `Abschnitt`, `Relok`, `Bild`, `Modus`, `effBias`.
- `Relokation`: `rel32Fuer`, `rel32Bytes`, `patchRel32`, `patchAbs64`,
  `patchAt`, `patchZwei`, `rel32_rundgang`, `rel32_adress_gleichung`,
  `rel32_next_rip`, `rel32Fuer_trifft/verweigert`, `patchRel32_stelle`.
- `TSO`: `TSOZustand`, `issueByte`, `loadByte` (with own-buffer
  forwarding via `neuestens`), `flushKern`, `zaunBereit`, `TSOSchritt`,
  `tso_store_buffering` (`sb_*` witness family), `paket_reisst`
  (tearing has no single-message image), `kein_lock_schritt` (no LOCK
  step yet: LOCK execution is absent).
- `Zugriffe.zugriff` (potential footprint per decoded form),
  `erfolg_*_im_fuss` / `*_ohne_speicher` frame facts, `kein_atomarer_zugriff`.
- `NarrowOps`: `loadNarrow`/`storeNarrow`/`moveNarrow`/`loadNarrowExtend`,
  `narrowAdmitted`, `extendFormOk`, `load/storeNarrow_success/refused`.
- `TableLayout`: `layoutOk`, `hinweisOk`, `layoutFuer`, `slotAufz`,
  witness `zeugenLayout_ok`.
- `ValidatorSkeleton`: `valX86`, `valX86Voll`, `valLayout`, `valTore`,
  `valX86_wohlgeformt`, `valX86_deckung`.
- Source bridge (`bruecke/Bruecke/Quelle.lean`): `uebersetzeAllg`,
  `declOf`, `einheitAllg` (fragment defaults), `Pflichten`,
  `nutzer_aus_quelle`, `nutzerA_aus_quelle`; `schwach_ist_gX`
  (`AtomarW.lean`) reused as the W-to-GX leg.

Trusted inputs (checked, not derived here): `gabbro_ziel` over GX with
exactly `propext, Classical.choice, Quot.sound`; the QUELLBRUECKE schema
(`valX86_sound`, `schluss_x86`) as PROPOSAL; TSO-GX-BRUECKE obligations
(O-access, O-align, O-spill, O-lock, O-ord, O-enable, O-cas-cost, OBS-5).

Explicit cuts (nobody may claim them): no `IR.lean` in this snapshot
(absent: `ls grammatik/Grammatik/X86/IR.lean` fails); no extension byte
decoder (narrow/muldiv/shift/SSE2/control all lack byte rows); no LOCK/
fence execution; no full-carrier W/GX mapping; no `valX86_sound` proof;
OBS-5 (unrecorded oracle reads) and O-cas-cost (unbounded CAS retries
void constant time bounds) stay open toward a possible reviewed
`Spec.lean` diff.

## 2. Producer -> consumer assignments (one owner per file, no overlap)

Prerequisite hash for every lane below: `8596f83e` unless its row says
otherwise. Reviewer of lane N is N+18 (576->558, 577->559, ... 593->575).

- 559 `X86/DecoderSoundness.lean`: consumes `Codec.decode`,
  `Byteschritt.fetchDekodiert`. Produces: arbitrary-input consumed-length/
  suffix agreement + 1..15 bounds + fetched-length facts. Closure: every
  pilot branch covered, one non-roundtrip input with trailing bytes,
  truncated/corrupt refusal probes. No second decoder.
- 560 `X86/LoadedExecution.lean`: consumes `Bild` mapping + actual memory
  construction, `Byteschritt.geholt/fetchDekodiert/byteschritt`. Produces:
  executable-section interior file-bytes = fetched-memory-prefix theorem
  (nonzero offset/base/bias, BSS, exec/data split) + a loaded store that
  changes memory. Prereq: 559 for length facts (soft: may proceed, must
  not duplicate them).
- 561 `X86/RelocatedExecution.lean`: consumes `Relokation.rel32Fuer/
  patchRel32`, `BranchLayout` length facts, `Bild` sites, `Codec.decode`,
  `Byteschritt` actual-memory execution. Produces: bounded rel32
  patch-and-redecode correspondence (virtual address + bias + length +
  signed range), forward/backward/nonzero-bias joint cases, out-of-range
  and interior-target refusal. Checks patched bytes independently.
- 562 `X86/NarrowCodec.lean`: consumes `NarrowOps.loadNarrow/
  storeNarrow/moveNarrow/loadNarrowExtend`. Produces: bounded independent
  extension decoder + canonical encoder over pinned bytes, generic
  roundtrip, arbitrary-decode consumption, width-exact execution reuse,
  corrupt/truncated/illegal-register refusal, pilot-dispatch
  collision/disjointness statement. Only admitted rows count.
- 563 `X86/MulDivCodec.lean`: consumes accepted `MulDiv` evaluator
  (resolve real type names first). Produces: prefix/opcode/ModRM decode +
  length, pinned encoding, execute correspondence with RDX:RAX and
  divide-refusal/trap distinction, divisor/overflow + truncation probes.
- 564 `X86/ShiftCodec.lean`: consumes `ShiftLogic` ops. Produces: decode/
  length + execution reuse, count masking, count-0/1/large probes,
  undefined flags preserved as represented, pilot-dispatch statement.
- 565 `X86/ScalarFloatCodec.lean`: consumes `ScalarFloat.FpBefehl/
  FpDecodiert/fpSchritt`. Produces: independent SSE2-DOUBLE decoder
  (prefix/opcode/ModRM/length from bytes, never a caller-supplied
  `FpDecodiert`), execution + upper-half/profile preservation, byte-
  evidenced memory store, wrong-prefix/truncation/MXCSR refusal,
  NaN/preservation cuts kept.
- 566 `X86/ControlCodec.lean`: consumes `ControlFlow`/`ConditionalMove`
  register-only forms. Produces: condition/register/REX/ModRM decode +
  length, evaluator reuse, taken/untaken + high-register pins,
  mutation/truncation refusal, no memory-CMOV speculation.
- 567 `X86/TSOHistory.lean`: consumes `TSOZustand`, `issueByte`,
  `loadByte`, `flushKern`, real `Sicht` Nachricht/Lesbar/Frisch + actual
  W defs. Produces: THE reusable history/view projection + related-state
  invariant + finite issue/flush freshness/FIFO lemmas, two-core joint
  memory-changing witness, foreign-drain/tearing refusal. STAYS
  byte-level: full typed-carrier mapping is an explicit cut. Stable
  interface published in its report for 573/574.
- 568 `X86/AccessExecution.lean`: consumes `Zugriffe.zugriff`, ACTUAL
  `Ausfuehrung.schritt` + `Byteschritt.byteschritt` success, `Speicher`
  read/write frame lemmas. Produces: realised read/write facts for all
  14 pilot forms (base-alias, rsp-stack, CALL next-RIP store, POP/RET
  reads), generic coverage theorem + joint store witness. A computed
  potential list alone is not closure. One-word footprint != atomic TSO
  event (stated, not bridged).
- 569 `X86/StackExecution.lean`: consumes fetched CALL/PUSH/POP/RET bytes
  + `Stapel`/`CodeImmutability` lemmas (+ `StackUnwind` only if present
  in its snapshot). Produces: nested-call run from executable-memory
  bytes with correct return word + restoration, non-executable/guard/
  code-overlap refusal, pre-state RSP preserved.
- 570 `X86/SourceMemory.lean`: consumes real `Deklaration`/`Welt` table
  carriers, `TableLayout`/`Speicher` bytes, `execStmt` table writes.
  Produces: THE small generic representation interface (bounded
  integer/table fragment) + source-write/target-write64 preservation +
  disjoint-carrier facts, joint source-table-to-bytes witness,
  overlap/out-of-range/width refusal. Stable interface published for
  567/573/574. No new IR, no `int->ptr`.
- 571 `X86/EntryExecution.lean`: consumes `EntryState`, `GateStub`,
  `Bild`, actual source start/binding duties. Produces: fetched first
  instruction + stack/permission facts from checked mapping + entry
  obligations, reached memory-changing entry, wrong/unchecked-entry
  refusal. OS/binding contracts stay user logic.
- 572 `X86/BudgetExecution.lean`: consumes `exec/execStmt` budget stops,
  `CostSummary`/`TimeTransfer` finite runs. Produces: source/target halves
  with explicit representation interface + real store + exhaustion +
  optimisation/retry/stutter obstruction. No IR.lean exists: the missing
  IR leg is reported exactly, not invented. Hardware bounds are named
  assumptions; no free CAS-retry bound.
- 573 `X86/BridgeWrite.lean`: PREREQ accepted 567 + accepted 570
  (waits; do not fork them). Consumes their published interfaces +
  actual W/`RufSchrittW`. Produces: per-access store issue/flush to W-
  write relation for the admitted carrier profile, FIFO order, stutter
  bookkeeping, two-core witness, tearing/foreign-drain refusal.
  Per-byte Sicht alone is not a full-carrier claim.
- 574 `X86/BridgeRead.lean`: PREREQ accepted 567 + accepted 570 (waits).
  Consumes the same + W read/view rules. Produces: load/forwarded-read
  to W-read simulation (value + view + atomic-rely duties), youngest-
  own-buffer cases, joint two-core witness + stale/tearing refusal.
  `schwach_ist_gX` reused only once real W execution is derived.
- 575 `X86/ExtendedExecution.lean`: PREREQ accepted 559-566 interfaces
  (waits; reports mismatches as concrete repairs, never an alternate
  architecture). Consumes `Codec.decode`/`Ausfuehrung.schritt` for the
  14 pilot forms + each accepted helper for its new forms only.
  Produces: ONE selected-profile byte-facing execution path (length,
  fetch/permission, disjoint prefix dispatch, exact evaluation
  selection), mixed pilot/FP-or-narrow/store run from fetched bytes,
  invalid/unsupported refusal.

## 3. Cross-module mismatches found (exact follow-up edits, assigned)

- M1 `valX86` binds `(Profil, Bild)`, the QUELLBRUECKE schema needs
  `valX86 E bild` over the FULL source-computed unit. Owner 560/571 must
  NOT paper this over by validating `P` alone: follow-up is a new
  validator-adapter file (unassigned; propose as next wave) extending
  `valX86Voll` with the `E`-identity premise. Until then every consumer
  states `hE : E = einheitAllg u P hn` explicitly.
- M2 `Zugriffe.zugriff` is a potential-footprint function, not a
  realised trace. Owner 568 must derive realised facts from `schritt`
  success (the `erfolg_*` lemmas exist); quoting `zugriff` alone is
  rejected by its reviewer (586).
- M3 `TSO` has `kein_lock_schritt`: no LOCK execution exists. Owners
  563/567/573 must keep LOCK claims refused until a LOCK step is
  modelled (propose as next wave; not inside 567).
- M4 `IR.lean` is absent. Owner 572 and consumers 573/574 must carry an
  explicit representation/checkable-coverage interface and name the
  missing IR leg; reviewer 303 still waits for a committed IR287
  candidate. No competing IR may be created by any connection lane.
- M5 `StackUnwind` is accepted in this snapshot, so 569 may reuse it;
  if its interface mismatches fetched-byte needs, 569 reports the exact
  repair, it does not invent a parallel unwind.
- M6 Optimiser files `OptimizationRules.lean`/`OptimizationWitnesses.lean`
  are friend-reserved: no connection lane touches them; 572 states the
  optimisation/retry obstruction without certifying any pass.
- M7 `TorDekl`/`torOkB`/`c186/c187VerweigertB` (GateStub) and
  `TabLayout`/`hinweisOk` are Bool checks, not execution facts. Owners
  570/571 reuse them as premises only; the memory consequence must be
  derived, never conjoined.

## 4. Dependency order and backfill (no overlapping writers)

Wave order: 559 -> {560, 561} -> {562, 563, 564, 565, 566} (independent
of each other; shared rule: never rewrite `Codec.decode` or
`Ausfuehrung.schritt`, state dispatch only) -> {568, 569} -> 570 ->
567 (needs only TSO + Sicht/W, can run parallel to 568-570 but its
consumers wait) -> 571, 572 (need 570 interface; 572 proceeds without IR)
-> 573, 574 (wait ACCEPTED 567 + ACCEPTED 570) -> 575 (waits ACCEPTED
559-566 helpers). IR287 resumes alongside; 572/573/574 track its accepted
interface, never a draft.

Smallest useful backfill tasks if models idle (each one file, one owner,
no overlap): (a) pinned-byte table for 562-566 from the selected
profile/manual evidence (docs table under `dokumente/x86/`, no Lean);
(b) `decode_nichts_*`-style refusal probes for each new extension
decoder inside its own lane file; (c) two-core TSO litmus witnesses for
567 (`sb_*` pattern); (d) source-table write witnesses for 570 against
`zeugenU_schreibt` pattern; (e) validator-adapter proposal file for M1
(next wave, not 559-575).

## 5. CUTS

This document proves no theorem, adds no decoder, executor, loader,
projection, representation or refinement. All interface claims are by
reading the cited definitions at base `8596f83e`. `valX86_sound`,
`schluss_x86`, the per-access TSO->W/GX simulation, extension byte rows,
LOCK/fence execution, the single IR and the full source-to-final-byte
chain remain OPEN. Model process counts are not progress; only ACCEPTED
exact-candidate reviews move lanes to integration.
