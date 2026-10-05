# MUSE-REPORT-1346: Exact review of candidate 1345 (opcode ledger 0F 80-BF)

RE-REVIEW after repairs (previous verdict REPAIR on `5f54e9f2` is stale).

CANDIDATE: 1345 783115dfcd77a73dbfa700d294991c61417f27dc

VERDICT: ACCEPT

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
- `./lean-probe` result on the NEW file: `== 0 error(s) in the COMPLETE
  output; exit 0`. Every `#print axioms` output is within `[propext,
  Classical.choice, Quot.sound]` (goal-theorem standard): ledger/count/
  coverage theorems are axiom-free; decode pins depend on `[propext]` or
  `[propext, Quot.sound]`; `cpuid_modelliert` and `gruppe8_alle` use the
  full standard set; `popcnt_modelliert` and both deferral theorems are
  axiom-free.
- `./lean-bau` on the clean baseline (candidate not merged here):
  `Build completed successfully (696 jobs).` The author's evidence shows
  the full build green with the NEW candidate merged (`694 jobs`), and
  the evidence `git status`/`diff --stat` shows only the one import line
  (`grammatik/Grammatik.lean | 1 +`).
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
- New reuses verified with exact matching statements: `roundtripBtReg`
  (`IntBitTest.lean:727`, generic over `op : BtOp`), reused as
  `bts_reg_alle`/`btr_reg_alle` with all premises used; `encodeBsf_decodeBs`
  (`IntBitScan.lean:326`), reused as `bsf_alle_modelliert`;
  `roundtripBtImm (op) (w) (dst) (n) (h : n < 256) (suffix)`
  (`IntBitTest.lean:910`), reused as `gruppe8_alle` with `5 < 256` closed
  by `decide`; `BtOp` has exactly the four ctors `bt/bts/btr/btc` with
  opcodes 163/171/179/187 (`IntBitTest.lean:31-37`), so the two reg
  generics plus `gruppe8_alle` cover rows 171/179/186 fully;
  `pin_popcnt_reg` (`IntBitScan.lean:404`, bytes `F3 0F B8 C1` and
  conclusion match exactly); `bs_nichts_tzcnt`/`bs_nichts_lzcnt`
  (`IntBitScan.lean:496/501`, `F3 0F BC/BD ... = none` match exactly);
  `pin_lock_mfence_decodiert` over `pinMfence = [0F, AE, F0]`
  (`LockedInstructionExecution.lean:735-766`), inlined exactly.
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

## Re-review of the three REPAIR items (all closed)

1. Prefix/extension dimension: CLOSED. `LEintrag` now carries `praefix :
   Option Nat` with key `schluessel` (prefix, byte) via `praefixNr`;
   ledger has 67 rows (64 base + `F3 0F B8` POPCNT modelliert, `F3 0F BC`
   TZCNT and `F3 0F BD` LZCNT zurueckgestellt); counts 43/3/5/0/16 sum
   to 67; `ledger_opcodes` proves key coverage `[(0,128)..(0,191),
   (243,184), (243,188), (243,189)]` and `ledger_nodup` key uniqueness,
   both `decide`-closed and probe-green. POPCNT is witnessed by the
   accepted pin, TZCNT/LZCNT by the family's planted refusals (statements
   match exactly, verified above). Byte-184 `grund` now notes the F3
   exception. Group rows are mapped per extension: Group 8 every /4../7
   op in imm8 form (`gruppe8_alle`, `BtOp` exhausts the four), Group 15
   the MFENCE /6 extension (`gruppe15_mfence`), Group 10 refusal
   (`verw_b9`). Deferral grunds note the unsupported-CPU fallback,
   keeping vendor-variable behaviour FREE.
2. Rows 171/179 witnesses + CUTS: CLOSED. `bts_reg_alle` and
   `btr_reg_alle` reuse `roundtripBtReg` generically (all premises used);
   CUTS now says "generic round trips for BTS/BTR, pins for BTC" and
   separately lists the group/extension mapping, the deferrals, and an
   explicit rel16 non-witness note — no overclaim remains.
3. Minors: CLOSED. Row 191 is plain "MOVSX r, r/m16"; `bt_reg`
   comment says `0F BB`; row 174 names both fence modules; BSF has pin
   plus generic; SETcc mnemonics say "reg-direct only".

## Remaining observations (not verdict-relevant)

- `gruppe8_alle` appends `++ []` (stylistic, harmless) and covers imm8
  form only; other Group 8 operand shapes are family properties, not
  ledger claims.
- No statement about `kapDecode` refusals beyond what `./lean-probe`
  kernel-checked (`verw_*` by `decide`); Isabelle, emission and Rust
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
