# MUSE-REPORT-992: Exact review of author 842 (fault-ledger closing)

## Review outcome

CANDIDATE: 842 174cec9d2961fc14e85ec235147778bfcbb6e7b8

VERDICT: ACCEPT

Pinned base: e7c75908456285d1e37c18dc32d4f9c0e10d1fa4. Acceptance is bounded;
see the bounded-acceptance section below for the exact claim boundary.

Scope of this review: report only. I own only MUSE-REPORT-992.md. No source
file was created, edited, or applied in this clone; the candidate was inspected
via the pinned snapshot (`.tmp/review/author-842/`: OWNER-TASK.md,
MUSE-REPORT-842.md, PATCH.diff, BUILD-EVIDENCE.json), the official local
hardware reference (`.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US,
sha256-verified), and the producer modules as merged at this clone's HEAD
(b040b155).

## What was reviewed

Candidate adds `grammatik/Grammatik/X86/ComposeFaultLedger.lean` (294 lines)
plus one import line in `grammatik/Grammatik.lean`. New vocabulary:
`LedgerOut` (`weiter`/`halt`/`verweigert`), `ledgerSchritt`, `ledgerSchritt2`.
Theorems: `ledger_verweigert_bei_mapping`, `ledger_halt_klasse`,
`ledger_weiter_ohne_fehler`, `ledger_verweigert_bei_schritt`,
`ledger_ordnung_kopf`, `ledger_ordnung_halt`, `ledger_falle_nie_optimiert`,
`ledger_stopp_nach_art`, TARGET `ComposeFaultLedger_verbindung` with companion
`ComposeFaultLedger_verbindung_zeuge`.

## Evidence (independently checked, not just Lean-green)

1. Halt-is-#DE mapping is reused, not invented. `ExtAusgang.halt` is produced
   by `stepExt` in exactly one arm (`.muldiv` on `mulDivSchritt = .hardwareHalt`;
   ExtendedExecution.lean:315-319); every other arm yields only
   `weiter`/`verweigert`. `extByteschritt` routes fetch through `stepExt`
   (ExtendedExecution.lean:616-619), fetch failure gives `.verweigert`.
   `klassifiziereExt .halt = some .de`, `weiter`/`verweigert = none`
   definitionally (HardwareFaults.lean:60-62). The candidate's `rfl` steps
   after rewriting with the step equation are therefore sound. The producer
   even carries the accepted `stepExt_halt_ist_de` leg.
2. Hardware correspondence confirmed against the official local SDM text:
   vector 0 #DE is Divide Error from DIV/IDIV (txt lines 9643, 163867);
   DIV/IDIV pseudocode raises #DE on zero divisor and unrepresentable quotient
   (txt lines 50207-50241, 58088-58133). Trapping DIV/IDIV leave destinations
   undefined per the DIV/IDIV entries; the ledger's `.halt k` carries no
   successor state, so post-fault state is soundly abstracted, never
   determined. No zeroed/ignored defined effect.
3. Every reused name resolves at this clone's HEAD with a matching statement:
   `bewegung_verweigert_fuer_falle`, `bewegen_aendert_beobachtung`,
   `fehler_div_null_haelt_zeuge`, `stoppReihenfolge`, `beobachtung_stopp_sichtbar`,
   `valZeuge_akzeptiert`, `valZeuge_mutiert_verweigert`,
   `fetch_abgeschnitten_verweigert`, `extWit_erster_speichert`,
   `extWit_anfang_null`, `extZelle`, `einByteStart`, `natByte`,
   `klassifiziereMulDiv`, `mdZustandNull/Div`. Signatures match the candidate's
   uses argument-for-argument.
4. Witness is non-degenerate and joint: reached one-step store run through
   `extByteschritt extWitStart extWitBereit` moving cell 8192 observably 0 -> 42
   (with the `≠` proof), threaded through the composed `ledgerSchritt` via the
   TARGET theorem itself (not beside it); two planted refusals (mutated
   validator byte refuses `valX86`; truncated `jump32` byte refuses the byte
   step); zero-divisor trap with its #DE class; impurity pair for the witness
   register. The `cases` on the byte-step outcome closes the halt/verweigert
   arms by `simp [extZelle]`, so a non-storing outcome cannot silently pass.
5. Reproduction with queued wrappers: `./lean-probe
   grammatik/Grammatik/X86/HardwareFaults.lean` at this HEAD gives
   `== 0 error(s) in the COMPLETE output; exit 0`, standard axioms only.
   `./lean-bau` at this HEAD: `Build completed successfully (510 jobs).`
   (Master state only — the candidate file itself is not in this clone, so
   this measures the producer foundation, which is what the candidate stands
   on.) The candidate's own BUILD-EVIDENCE.json shows the full trajectory
   including final green `lean-bau` (509 jobs) with every `#print axioms` at
   `[propext, Quot.sound]`.
6. Rule hygiene from the full PATCH text: no `sorry`/`admit`/`axiom`/
   `native_decide`/`unsafe`; no premise of type `Prop` itself; every premise
   of every new theorem is used (checked per theorem, including `src` in
   `ledger_falle_nie_optimiert`/`ComposeFaultLedger_verbindung` and all nine
   binders plus three hypotheses in `ledger_stopp_nach_art`); no conclusion
   restates a premise (ledger conclusions are about `ledgerSchritt`, premises
   about `valX86`/`extByteschritt`). Scope clean: one new file plus one
   import line; no diagnostic/gift/example/CLI numbers, no MARKE or
   instrumente changes, no source/checker/Spec/goal/emitter edits, no
   friend-reserved optimiser files.

## Findings (none blocking)

- The report prose says the admitted image "feeds" the byte step. Formally
  `bild` gates `ledgerSchritt` but does not flow into `extByteschritt t b`;
  the TARGET theorem takes admission and execution as independent premises.
  This is stated honestly in the theorem (no link assumed, none concluded)
  and the admission-of-the-executed-bytes correspondence stays outside the
  claim under the existing `valX86_sound` CUT. Read "feeds" as "gates".
- The witness pairs `valZeuge` (1-byte `ret` image) with `extWitStart` (15-byte
  store/FP-store image): correct joint inhabitation of independent premises,
  not a same-image link. Same boundary as above; no correction required for
  the claims as proved.
- `valX86_sound` CUT names no owning lane. Natural owner is the ValidatorSkeleton
  line (lane 349 family); suggested, not required.

## Bounded acceptance

Accepted exactly: one gated ledger step over the reused canonical vocabulary
(admission AND decode coverage first, byte step from actual memory, divide trap
reports #DE, every refusal reports no fault), its four legs, fail-closed
two-step order for refusal and trap heads, stops reported by kind through the
reused joint stopping order plus observable refusal projection, trapping
divisions impure with a concrete halt/answer pair, and the closing composition
with its joint non-degenerate witness. Everything else — fault priority,
#UD/#XM/#AC/#NM membership beyond the reused classifier, paging
disambiguation, delivery, `valX86_sound`, source/TSO/GX/concurrency/contract/
budget-transfer/cost/time/FP claims — is explicitly CUT and not claimed.

## Last wrapper results

- `./lean-probe grammatik/Grammatik/X86/HardwareFaults.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
- `./lean-bau`: `Build completed successfully (510 jobs).`
