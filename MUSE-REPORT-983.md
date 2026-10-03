# MUSE-REPORT-983: Exact review of author 833 (call-log ghost closing)

## Candidate

- CANDIDATE: 833 `004925e033ae8b51f74048c6e10dfe3604dac566` (base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, my clone HEAD — match).
- VERDICT: ACCEPT (bounded; see §5).
- Scope (from `.tmp/review/SNAPSHOT.json` + `PATCH.diff`, 393 lines): only
  `MUSE-REPORT-833.md` (new), `grammatik/Grammatik.lean` (+1 import line),
  `grammatik/Grammatik/X86/ComposeCallLogGhost.lean` (new, 307 lines).
  No diagnostic/gift/example/CLI numbers, no MARKE changes, no source/checker/
  Spec/goal/emitter edits, no friend-reserved optimiser files. Patch hunk
  context for `Grammatik.lean` matches my base exactly (lines 509-511).

## What I did (report-only; no source touched in this clone)

1. Verified clone `/home/simon/Dokumente/gabbro-muse/a983`, branch `muse/983`,
   clean, HEAD = snapshot base.
2. Read owner task, author report, build evidence, full candidate module and
   full patch from `.tmp/review/author-833/`.
3. Cross-checked every reused producer name against the pinned base in my
   clone: `GeistAntwort`/`geistPaar`/`geistRekon_folge`/`geistRekon_folge_grund`
   (`AufrufOpt.lean` lines 27/32/57/72), `wahlOk` (flagsLive-first arg order)
   and `wahlOk_verweigert_xor_le` (`InstructionSelection.lean` lines 43/147),
   all witness fixtures/builders (`Φ50`, `eP_folge50`, `eD/eP/eO/eSp/eInit`,
   `eSetze/ePruefe/eHaupt`, `eHpSetze/eHpPruefe`, `w_rufEnde/w_blatt/w_rueckP`).
4. Ran queued wrappers in my clone: `./lean-probe …/AufrufOpt.lean` → 0 errors;
   `./lean-probe …/InstructionSelection.lean` → 0 errors (axioms standard).
   No full `./lean-bau` in this reviewer clone: I own no source, changed
   nothing, and had nothing to build; the candidate's own evidence records
   `./lean-bau` green at 509 jobs (= base 508 + 1 new module, consistent).
5. Grepped the candidate module for `sorry/admit/axiom/native_decide/unsafe`:
   no hits. Audited the Bool encodings and proofs by reading (details §3).

## Findings

- `senkeOk` faithfully encodes the two armed side conditions of
  `geistRekon_folge`/`_grund` for both channels, with actual `rho/v/r/s0/s1`
  throughout (no quantified-away contract values). The trivially-true
  `(eintritt :: rest) ≠ []` antecedent of the producer's second side condition
  is discharged by `fun _ => o2` in `ComposeCallLogGhost_verbindung` — exact,
  not a weakening.
- `schlussOk = senkeOk && wahlOk`: both refusal directions proved generically
  (`verweigert_wahl` via the accepted rfl-lemma, `verweigert_senke` by the
  `senkeOk = false` hypothesis). Neither leg is decorative.
- ZEUGE target `ComposeCallLogGhost_verbindung` + companion
  `ComposeCallLogGhost_verbindung_zeuge` delivered with exact names. Witness is
  jointly inhabited on the non-degenerate fixture: `setze` writes table
  (`schreibt = true` by rfl), 5-step reached run, slots `0 → 5`
  (memory-changing `w_blatt` assignSlot/schreibSlot step), log holds exactly the
  ghost pair over the `setze` return, `senkeOk = true` and `FolgeLog` derived
  through the composition theorem — not projected back. The `rfl` fixture
  facts used in the witness (entry required, armed tail, return not required)
  are mutually consistent with the four `decide` instances (order loss
  refuses, good splice/choice pass, xor refuses): genuine positive + negative
  coverage, no fake closure.
- Axioms per build evidence: `[propext]` everywhere, plus
  `Classical.choice, Quot.sound` only for the `_zeuge` (inherited from accepted
  run builders) — within the standard `gabbro_ziel` set. Rule 3/4/12/13 clean:
  no `Prop`-typed premises, every premise used, no restated conclusions, CUTS
  block + `#print axioms` per main theorem present.
- Hardware-architecture checklist: the candidate introduces no new byte-facing
  execution, no register/flag/memory-ordering claims of its own — byte forms
  (REX/width/`mov` vs `xor` lengths) and the flag gate enter only through the
  accepted `wahlOk` verdict, reused by name and never re-proved. No invented
  determinism, no ignored defined effects. Correct division for a composition
  lane; full byte-connected execution remains with the producer/hardware waves.

## Open / bounds of this ACCEPT

- No executable body-splice simulation; ghost lowering to the shared
  representation stays with the bridge wave; no closed `grund`-channel fixture
  inhabitant (`eD.gruende = 0`); `ensures`-extraction where `AufrufOpt` left
  it — all stated in the file CUTS and accurate. Nothing in the owner task
  believed wrong.

## Commits (branch muse/983)

- This report only. No source or live-control changes.
