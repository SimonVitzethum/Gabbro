# MUSE-REPORT-1346: Exact review of candidate 1345 (opcode ledger 0F 80-BF)

CANDIDATE: 1345 5f54e9f2ee705cbbdb3e051573fe2a0c42be2cdd

VERDICT: REPAIR

## What was checked

- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1346`, branch
  `muse/1346` (clean `git status`). The author clone and pinned hash were not
  touched; the candidate was reviewed strictly as delivered files
  (`.tmp/review/SNAPSHOT.json`: author 1345, 3 files, `clean: true`;
  `.tmp/review/author-1345/PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
  and the changed files under `.tmp/review/author-1345/` at repository paths).
- The permission profile of this lane allows edits only to
  `MUSE-REPORT-1346.md`, `arbeitsprotokoll/.commitmsg` and `.tmp` scratch, so
  the candidate file could not be copied under `grammatik/`. Instead
  `./lean-probe` was run on the delivered copy in place at
  `.tmp/review/author-1345/grammatik/Grammatik/X86/OpcodeLedger0F80.lean`.
  Imports resolve through the `grammatik/` package, so the check is valid.
- `./lean-probe` result: `== 0 error(s) in the COMPLETE output; exit 0`.
  Every `#print axioms` output is within `[propext, Classical.choice,
  Quot.sound]` (goal-theorem standard): ledger/count/coverage theorems are
  axiom-free; decode pins depend on `[propext]`, `[propext, Quot.sound]`, or
  `[propext, Classical.choice, Quot.sound]` (CPUID only).
- `./lean-bau` on the clean baseline (candidate not merged here):
  `Build completed successfully (696 jobs).` The author's evidence shows the
  full build green with the candidate merged (`694 jobs` there).
- Grep over the candidate file: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe` (only `#print axioms` lines match `axiom`).
- Every reused name was verified to exist in this clone with a matching
  statement: `roundtrip_jumpIf32` (`Codec.lean:504`), `roundtrip_setCC`
  (`ControlCodec.lean:88`), `pin_bt_dekode` (`IntBitTest.lean:809`,
  3-part conjunction), `pin_bsf_reg` (`IntBitScan.lean:386`),
  `encodeBsr_decodeBs` (`IntBitScan.lean:333`), `decodeCpu_cpuid`
  (`CpuFeatureHardwareForms.lean:152`), `kapUeber_wd_ext_imul2`
  (`HwKapsteinDecoder.lean:555`, bytes and conclusion match the candidate
  exactly), `pinCmpxchg` + `pin_lock_cmpxchg_decodiert`
  (`LockedInstructionExecution.lean:735,757`, bytes `F0 48 0F B1 ...`
  match). `Bedingung` has exactly the 16 conditions and `condCode` maps
  them bijectively onto 0-15 (`Codec.lean:35-47`), so the Jcc/SETcc
  generics cover all 32 rows. All four generic theorems use every premise.
- Silicon spot-checks against the supplied Intel snapshot
  (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  edition 325462-093US): POPCNT = `F3 0F B8 /r`; LZCNT = `F3 0F BD /r`;
  TZCNT = `F3 0F BC`; `0F B9` = UD1; RSM = `0F AA`; `0F BE/BF` = MOVSX
  (MOVSXD is opcode `63`); Appendix-A table row confirms JMPE at `0F B8`.
- Clean items: one import line appended to `grammatik/Grammatik.lean` only;
  own namespace, self-contained schema, no decoder redefined (lifted, never
  copied); no `Prop`-typed premises; English throughout; CUTS block plus
  `#print axioms` per theorem present; no hardware-correspondence, W/GX,
  source, contract, timing or budget claims; opcode map stated as a named
  assumption with no AMD provenance claimed; decode-only pins pin no
  vendor-variable values. Rule 13 (`_zeuge`) is not applicable: no premise
  quantifies over program syntax and the owner task has no `ZEUGE:` lines.
  The "two cores / memory-changing witness" boilerplate in my line 24 comes
  from the contradicted HwAdapter mechanism (see task issues) and is N/A
  for a ledger lane.

## Reasons for REPAIR (concrete)

1. Required prefix/extension coverage is missing. The owner TASK demands
   "every opcode byte (and every legal prefix/ModRM.reg extension)", the
   FILE spec requires `LEintrag` to carry "the opcode bytes (and
   prefix/reg extension)", and REGION explicitly names "POPCNT `F3 0F B8`",
   "the `F3` TZCNT/LZCNT variants as `zurueckgestellt`", the Group 15
   `0F AE` ModRM split, and Group 8 `0F BA`. The candidate's `LEintrag`
   has only `op2 : Nat`; there is no row for `F3 0F B8` POPCNT even though
   the accepted `IntBitScan` family models it (`encodePopcnt_decodeBs`,
   `pin_popcnt_reg`, verified in tree); no rows for `F3 0F BC/BD`
   TZCNT/LZCNT even though the family documents them as deferred with
   planted refusals (`bs_nichts_tzcnt`, `bs_nichts_lzcnt`) and REGION
   orders them `zurueckgestellt`; Groups 15/8/10 are collapsed to one row
   each with no extension mapping. Byte 184 is marked `verweigert`
   ("Itanium emulator op, #UD") while its `F3`-prefixed form is a real,
   modelled instruction, so the row verdict misleads exactly where this
   gap-finding ledger must not. (Supporting point: the SDM notes
   unsupported LZCNT executes as BSR, unsupported TZCNT as BSF — the
   model-dependent behaviour that per-row FREE marking exists for.)
2. Two `modelliert` rows have no witness, against the CHECKED PART ("for
   every `modelliert` entry give a canonical witness byte string and
   prove ... it decodes"): rows 171 (BTS, `0F AB`) and 179 (BTR, `0F B3`)
   appear in no theorem. The one-line generic `roundtripBtReg (op :
   BtOp) ...` (`IntBitTest.lean:727-731`, `cases op <;> ... <;> rfl`,
   covers all four ops) was available and matches the candidate's own
   generic-reuse pattern for Jcc/SETcc/BSR, but was not used. The CUTS
   claim "BT/BTS/BTR/BTC register ... rows" as proved is therefore an
   overclaim.
3. Minor corrections (not verdict-driving alone): row 191 mnemonic
   "MOVSXD/MOVSX r, r/m16" — per the snapshot, `0F BF` is MOVSX and
   MOVSXD is opcode `63`; the `bt_reg_modelliert` doc comment says
   "`0F A3`" but the witnessed bytes are `0F BB` (BTC); row 174 names
   only `LockedInstructionExecution.lean` while fence rows live across
   modules (LFENCE in `LfenceLoadNarrow.lean`, MFENCE pin in
   `LockedInstructionExecution.lean`); BSF has a single pin where the
   accepted generic `encodeBsf_decodeBs` exists (sufficient at
   byte granularity, asymmetric with BSR); SETcc rows say "r/m8" but the
   reused decoder accepts register-direct only.

## Repair scope (small, concrete)

Add the prefix/extension dimension: at minimum rows for `F3 0F B8`
POPCNT (via `decodeBs`) and `F3 0F BC/BD` TZCNT/LZCNT (`zurueckgestellt`,
citing the family's planted refusals), with the byte-184 `grund`
noting the `F3` exception; either split Groups 15/8/10 per extension or
justify the collapsed rows with a per-extension witness mapping. Cover
rows 171/179 with `roundtripBtReg`. Narrow the CUTS sentence to what is
proved. Fix the row-191 mnemonic and the `bt_reg` comment.

## Open / not claimed by this review

No statement about `kapDecode` refusals beyond what `./lean-probe`
kernel-checked (`verw_*` by `decide`); the rel16 Jcc forms named in the
mnemonics were not separately verified; Isabelle, emission and Rust
corpus checks are untouched (Rust-free lane, no Rust changes in
candidate).

## Task issues

- The owner task's line 25 is truncated mid-sentence ("Do no..."), as the
  author reported; all visible requirements were reviewed.
- The owner CONTEXT/MECHANISM paragraphs describe a different lane family
  (one-family `HwAdapter` connection with two-core witnesses) and
  contradict the ledger TASK; the author was right to follow the TASK.
  My own line 24 repeats part of that boilerplate — recorded here as N/A
  for this ledger review.
