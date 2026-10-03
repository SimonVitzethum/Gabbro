# MUSE-REPORT-729: Exact review of author 728 (IDT/TSS descriptor and entry stack selection)

Lane 729, clone `/home/simon/Dokumente/gabbro-muse/a729`, branch `muse/729`
(verified via `.git/HEAD`; tree `git status --short` clean; HEAD `4ebf7893`).
Own file only: this report. No source file was created, edited, or moved.

CANDIDATE: 728 ef34e53cabe55c6f1c2db0237fd315318852caab
VERDICT: ACCEPT

## Pinned material reviewed

- `.tmp/review/SNAPSHOT.json` re-read this turn: author 728, head
  `ef34e53cabe55c6f1c2db0237fd315318852caab`, base
  `9fc15bf411e3dd7061a5bec2b79f54f0ee9722c3`, files
  `MUSE-REPORT-728.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/InterruptDescriptorHardware.lean`, clean true.
  Unchanged from the original pin; no drift. The a728 clone was not touched
  (out of scope); the snapshot is the exact pin under review.
- `lanes/728.md` vs `.tmp/review/author-728/OWNER-TASK.md`: identical.
- `.tmp/review/author-728/PATCH.diff` (1313 lines): exactly the three files above;
  the `Grammatik.lean` change is one additive import line
  (`import Grammatik.X86.InterruptDescriptorHardware`). Nothing else touched.
- The 1187-line candidate module read in full (lines 1-1187).
- `.tmp/review/author-728/MUSE-REPORT-728.md` and `BUILD-EVIDENCE.json`: read in full.
- Official manual: clone-local `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`:
  Intel SDM combined volumes 1-4, edition 325462-093US, September 2026, SHA-256
  pinned; AMD retrieval failed, no AMD claim). Table 6-1 rows and canonical
  section headings reproduced from the local txt (see evidence below).

## Scope and prohibition checks (source inspection)

- No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` as tactics: grep over
  the candidate file finds only the English word "admitted" in prose comments.
  No new axiom declaration.
- No premise of type `Prop` (grep for `: Prop` finds nothing).
- No `intro _` / `have _ :=` discards; no `forall rho` / `forall v` contract
  quantification; no `successor`/`refinement` assumption; no second interpreter
  (no `execStmt`/`exec` parallel world, no source-semantics import). `TSO`
  appears only in two CUTS/downstream comments as explicitly out of scope.
- Imports are exactly four accepted canonical modules: `Grammatik.X86.Typen`,
  `Grammatik.X86.Speicher`, `Grammatik.X86.Codec`, `Grammatik.X86.HardwareFaults`.
  No import of unmerged 672/708 files, no checker/Spec/goal/emitter/Rust/friend
  optimiser dependency. Canonical reuse confirmed: `read64` (gate halves, TSS
  slot load, frame read-back), `write64` (frame push chain), `istKanonisch`
  (handler and RSP checks), `addrOff`/`wortByte`/`natByte`, `ArchFehler`
  (only `.gp`/`.ss`, both present in `HardwareFaults.lean`; `#NP`/`#TS` have no
  admitted member, proved as `none` with the vector as the fact).
- No trusted parsed descriptor: `liefere` starts from raw `(Wort x Wort)` gate
  words; every refusal is a precise `TorFehler` (9 members). `codeOk` (GDT row)
  arrives as an explicit checked input, documented as downstream-owned. No OS
  content in `Steuerstand` (IDTR/TSS windows, CPL, IF bit only).
- No sequential/concurrent memory swap: the layer is over canonical `Speicher`
  only; TSO/store-buffer interaction is named as downstream (672/708), not claimed.
- No duplicate complete interrupt executor: check/select/push
  (`pruefeTor`, `waehleStapel`, `schiebeRahmen`, `liefere`) stop at the
  `zugestellt` fields (new memory, handler RIP, new IF, switch flag); handler
  execution, nesting, #DF escalation, and timing stay downstream per CUTS.

## Architectural correctness (hand-verified against the local manual)

- Vectors (`torVektor`): GP=13, NP=11, TS=10, SS=12. Confirmed against local txt
  lines 9662-9665 (`#TS` 10, `#NP` 11, `#SS` 12, `#GP` 13). Correct.
- Gate selection: `torAdresse = basis + v*16`; limit `v*16+15 <= limit`. Correct
  for 16-byte gates; witness vector 2 at 4096+32 = 4128 proved by `decide`.
- Parse: offset bytes 0-1/6-7/8-11, selector bytes 2-3, IST byte 4 bits 2:0 with
  bits 7:3 reserved, type/DPL/P byte 5, bytes 12-15 reserved; types 0xE/0xF.
  Vol. 3 figures are outside the local txt snapshot; header and CUTS state this
  honestly as stated architecture with checks proved from canonical-memory
  equations. Acceptable and disclosed.
- Check order (`pruefeTor`/`pruefeTorKern`): limit, type/reserved, DPL, present,
  NULL selector, code row, canonical handler. DPL rule (software non-INT1 needs
  `cpl <= dpl`; INT1 and external pass) matches the INT-entry pseudocode note.
  DPL-fault EXT hardcoded 0 is unobservable (software EXT is 0; external never
  takes the DPL branch). Fine.
- TSS slots (`stapelSlotOffset`): IST `ist*8+28`, else `neuDpl*8+4`. Pins
  IST1=36, IST7=84, RSP0=4, RSP3=28 all recomputed by hand: correct. No TSS read
  where nothing switches; limit precedes load; refused TSS read is a #TS fault.
- Error codes recomputed by hand: `codeFuerIdt 3 software` = 3*8+2 = 26;
  `nichtVorhanden 2 extern` = 2*8+2+1 = 19; `selektorFehler 24 extern` = 24+1
  = 25. All match `neg_codes`. Correct.
- Frame push: `rahmenWorte` = [SS, RSP, RFLAGS, CS, RIP] ++ code; head-first
  descending push puts SS highest and the error code lowest, matching the
  IA-32e frame; read-back pins (SS at top-8 = 16376, RIP at top-40 = 16344)
  consistent. Interrupt gate clears IF, trap keeps it. Noncanonical RSP and
  refused `write64` fault #SS without partial effects
  (`liefere_prueft_zuerst`, `liefere_stapel_vor_wirkung`,
  `liefere_rsp_nichtkanonisch`, both `liefere_zugestellt_*` equations).
- Witness: byte-populated IDT (vector-2 interrupt gate, IST 1, selector 8,
  handler 0x2000) and TSS (IST1 = 0x4000) in canonical memory; joint theorem
  `liefer_zeuge_gemeinsam` ties RIP, cleared IF, two `read64` frame read-backs,
  and two observably changed cells from zero. Non-degenerate (memory-changing).
  Twelve negative probes counted in source (limit, type, absent, IST-reserved,
  high-reserved, NULL selector, noncanonical target, DPL contrast incl. INT1
  exemption and external bypass, TSS limit naming slot 36, no-switch keep,
  dark-stack #SS with vector/code projections, error-code values). Count matches.
- Priority: structural first-failure-wins plus per-stage forward equations and
  `erste_pruefung_gewinnt_dpl` (DPL fault implies limit+type passed). `fehlerRang`
  is defined but consumed by no theorem (single grep hit at its definition).
  The author discloses this (rank exists, no ordering theorem beyond the DPL
  leg). Non-blocking observation, not a defect: ordering IS the pipeline, and no
  false cross-class ranking claim is proved or consumed.

## Evidence and build status

- `BUILD-EVIDENCE.json` shows honest development: intermediate red `lean-probe`
  runs (dependent-elimination and rewrite failures during proof construction),
  converging to final `== 0 error(s) in the COMPLETE output; exit 0`, followed
  by `git status`/`commit.sh` evidence for the pinned head with the lane
  co-author line. The author report claims `./lean-bau` `== exit 0` over 482
  targets and standard-only axioms with a full `#print axioms` block at file end
  (present) plus a CUTS block matching the report's open list.
- Independent re-execution by this reviewer: not run (report-only lane; the
  candidate file lives in the author snapshot, not in this tree, so a reviewer
  `lean-bau` here would only rebuild the unchanged base). The green is therefore
  evidenced by the preserved author log. No evidence contradicts it: final probe
  output, committed state, and source (no `sorry`, first-order `simp`/`decide`
  proofs) are mutually consistent. The merge gate rebuild must confirm.
- Quantitative claims (1187 lines, 482 targets, twelve probes, slot/code/vector
  values) were independently recomputed or counted from source and match.
  Measured counts are bookkeeping, not closure; closure rests on the per-stage
  equations plus the joint memory-changing witness, which are present.

## Task feedback

- The owner task is well-posed and the candidate meets it without weakening: no
  desired-correctness premise, no guarantee weakened, no fake closure. The two
  honest scope notes (Vol. 3 figure provenance; `fehlerRang` without a
  delivery-side ordering theorem) sit in CUTS/the report rather than papered over.
- Reviewer-lane note: "verify whole green checks" needs the queued wrappers;
  for shell-less review lanes, scope the lane to source/evidence review
  explicitly.

## Remaining work for others (not this lane)

- 672/708 consumers: `idtWit_liest`, `wit_zerlegt`, `wit_bereit`, `wit_stapel`,
  `liefere_zugestellt_*`, `torFehlerCode`/`torVektor`,
  `erste_pruefung_gewinnt_dpl` are the consumed interface (per section 9 header).
- Still open (author CUTS, endorsed): GDT/code-row ownership, async/nested/#DF,
  TSO interaction, full 20-vector error-code presence table, RSP alignment mask,
  shadow-stack/CET/FRED/task gates, silicon proof (never claimed).

Co-Authored-By: muse-agent-729 <muse-agent-729@noreply.invalid>
