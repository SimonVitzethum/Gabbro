# Muse Report 905: Exact review of author 755 (pure LEA address arithmetic)

CANDIDATE: 755 093642d11dec51442a497a436df70f1c0135e986
VERDICT: ACCEPT (bounded, see scope below)

## Clone / branch

- Review clone: `/home/simon/Dokumente/gabbro-muse/a905`, branch `muse/905` (verified, HEAD `23b9a42fb44f2365b636cf8a9c440a2dfd8cae50` matches snapshot `base`).
- Snapshot: `.tmp/review/SNAPSHOT.json` pins author 755 head `093642d1…5e986` over that base, files `MUSE-REPORT-755.md`, `grammatik/Grammatik.lean` (one import line), `grammatik/Grammatik/X86/LeaPureForm.lean` (new, 197 lines). `clean: true`.
- Own file only: `MUSE-REPORT-905.md`. No source or live-control changes; `git status` clean except this report.

## What was reviewed

The full pinned PATCH (`.tmp/review/author-755/PATCH.diff`), the new module copy (`.tmp/review/author-755/grammatik/Grammatik/X86/LeaPureForm.lean`), the owner task (`.tmp/review/author-755/OWNER-TASK.md`), the author report (`MUSE-REPORT-755.md`), `BUILD-EVIDENCE.json`, the accepted base modules in this clone (`AddressEncoding.lean`, `EffectiveAddress.lean`, `ExtendedExecution.lean`), and the clone-local official manual (`.tmp/HARDWARE-REFERENCES/`, Intel SDM combined vols 1-4, ed. 325462-093US Sept 2026).

## Architecture check (independent, against the manual)

Manual entry verified in-clone: `LEA—Load Effective Address`, opcode `8D /r`, `REX.W + 8D /r` for `r64` (txt lines 62795-62800); "Computes the effective address of the second operand and stores it in the first" with source a memory address and destination a general-purpose register (lines 62808-62814); 64-bit `OperandSize=64, AddressSize=64` stores all 64 bits using REX.W (line 62841-62842); "Flags Affected: None." (lines 62882-62883); `#UD` if source is not a memory location or LOCK prefix is used (lines 62885-62887).

- Byte forms: the connection reuses accepted `decodeLea` (REX.W 72-79 + `0x8D` + selected tail, no legacy prefix) and pins the exact 5-byte witness `[48, 8D, 44, C8, 05]` (`leaGeholt_dekodiert`, reusing accepted `lea_dekodiert_skaliert`). No new codec rows; correct for the claimed 64-bit scope. 16-bit forms (66H) stay refused with the base, which is a disclosed bound, not a silent gap.
- REX/register/width: destination `rax`, base `rbx`, index `rcx`, scale 8, disp8 5 through the accepted `skaliertForm`; address arithmetic is the canonical 64-bit modular `adrEff`. No width confusion.
- Flags: connection concludes `s'.flags = s.flags`, matching "Flags Affected: None". No invented determinism; undefined state is not touched at all.
- Source/destination/implicit operands: destination register written, source address computed and never dereferenced (`leaFormSchritt_speicher` reused: memory untouched, no memory event). No implicit operands for LEA; none modelled, none needed.
- Pre-fault effects: data-address faults are correctly ABSENT (no `fussZugelassen`/`read64`/`write64` on the computed address — LEA never touches data memory); code-fetch faults stay handled by the accepted `geholt` window (base `leaWit_nachBild_verweigert` refuses past-image fetch). `#UD` shapes (LOCK `F0` first byte, non-memory source via mod=3) are refused by the reused `decodeLea`/`parseAdrTail`, consistent with the manual.
- Memory access order / TSO / atomicity: no footprint, so no order, visibility, tearing or grouping to transfer. CUTS correctly claims no TSO/GX bridge instead of inventing one.
- Feature/MXCSR/interrupt gates: LEA needs none (base ISA, no SSE, no MXCSR); interrupts only via code fetch, already covered. Nothing ignored that is defined.
- Canonical interaction: thin reuse only — `decodeLea`, `leaFormSchritt`, `leaGeholtSchritt`, `adrEff`, `leaWitZustand`, `storeWitZustand`, `storeWit_zeuge`, `leaWit_rechnet`, `dispWort` pins, `geholt`, `decodeExt`. No duplicated arithmetic, decoder, register/memory model, or source interpreter. `leaGemeinsam_verweigert` (`decodeExt` is `none` on the LEA bytes) proves no shadowing of the common dispatcher; LEA runs only through the accepted fetched-LEA step.

## Proof-hygiene check

- Full file read: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no premise typed `Prop` itself; both premises of `LeaPureForm_verbindung` (`hdec`, `hok`) are used; the proof unfolds the accepted fetched/form steps and closes with the accepted shape — no desired-simulation premise, no guarantee weakening (purity is proved, not assumed).
- Displacement side condition (`leaDispOk`/`leaDispWert`): signed-32 range with `decide` pins (`leaDisp_negEins`, `leaDisp_maxPos`, `leaDisp_minNeg`) and explicit refusals (`leaDisp_zuGross`, `leaDisp_negZuGross`, `leaDisp_negNull`); bridges (`leaDispWort_negEins/maxPos/minNeg`) reuse the accepted `EffectiveAddress` sign-extension pins. The condition lives at the source-nat level (any 4-byte pattern trivially IS some i32 at the byte level); this matches the task wording and is not misrepresented as a new codec refusal.
- Witness `LeaPureForm_verbindung_zeuge`: both connection premises jointly on `leaWitZustand` (verified: `rbx=8192, rcx=1`, disp 5, scale 8 gives `8205` via accepted `leaWit_rechnet`), plus the accepted scaled-store run changing data memory `0 -> 42` at `8200` (accepted `storeWit_zeuge` parts `.1` and `.2.2.1`, verified against base lines 1076-1087). Non-degenerate and reached. The task's "memory-changing reached run" cannot come from the LEA step itself (pure by definition); pairing the reached pure LEA with the reached memory-changing store beside it is the honest resolution, and the author states the tension plainly in the report. Accepted as satisfying the ZEUGE line at the conjunction level.
- CUTS: precise — lists the i32 side condition, bridges, fetched decode + length, dispatcher refusal, purity connection + joint witness as proved; and no silicon correspondence, no new codec rows, no TSO/GX bridge, no source/ABI/loader/budget claim as not proved. Claim matches proof.
- Axioms reported (`propext`, `Quot.sound` subsets) are within the goal standard; `Zielsatz`/`Spec`/checker/emitter untouched, so `gabbro_ziel` is unaffected. No diagnostic/gift/example/CLI numbers, no `MARKE_EMIT` changes, no friend-reserved optimiser files — per the 2026-10-03 user priority.

## Verification performed

- No fresh `./lean-bau` run in this review clone: the review owns no source, and the candidate build evidence is complete and specific (`./lean-bau` tail: `Built Grammatik.X86.LeaPureForm`, `Built Grammatik`, `Build completed successfully (483 jobs)`; `./lean-probe` `0 error(s)`; `#print axioms` output listing each main theorem's axioms). Verification here was by independent full-text inspection of the pinned module, base-theorem cross-checks (names and statements verified present in this clone's accepted files), manual-entry verification (lines cited above), and snapshot/HEAD/base identity checks. No suspicious case requiring a queued-wrapper reproduction was found; no wrapper run was needed to settle the verdict.
- Negative mutations present in-candidate by `decide`: past-maxPos, past-minNeg, negative zero, common-dispatcher refusal; base adds legacy-prefix, missing-REX.W, pilot-row and past-image refusals. Real and checked.

## Bounded acceptance scope

ACCEPT covers exactly: the source-level i32 admission/refusal pins, the bridges to canonical sign extension, the fetched 5-byte LEA decode + length + dispatcher-non-shadowing, and the fetched-LEA purity connection with its joint witness — all over the accepted canonical vocabulary, 64-bit REX.W scope, Intel-profile manual evidence only (no silicon, vendor-difference, timing, TSO/GX, source, ABI, loader, or budget claim).

## Open / not claimed

Per the candidate CUTS, which I endorse: silicon correspondence beyond the named manual entry; disp8/disp32 selection stays with the accepted compact encoder; no TSO/GX bridge (correctly: no footprint); no source correspondence or ABI/loader/entry/budget claim.

## Task remark

Nothing in the owner task is believed wrong. The ZEUGE parenthetical, read literally per-step, is contradictory for a provably pure instruction; the author's paired-witness resolution is the correct honest reading, and the task should keep allowing it.
