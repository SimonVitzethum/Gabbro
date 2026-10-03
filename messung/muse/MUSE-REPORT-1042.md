# MUSE-REPORT-1042: Exact review of author 892 (MOV-immediate selection rule)

CANDIDATE: 892 f6d094221adb62f69fc722acabef3cedcf25fdcc
VERDICT: ACCEPT

Acceptance is bounded by B1–B4 below; no repairs are demanded.

## Scope and method

Report-only exact review. Owned file: only this report; no source file was
touched and no build state was modified. The author clone was not available,
so the pinned content was reviewed through `.tmp/review/author-892/PATCH.diff`
(753 lines: new `grammatik/Grammatik/X86/OptMovImmSel.lean`, one import line in
`grammatik/Grammatik.lean`, `MUSE-REPORT-892.md`), `.tmp/review/SNAPSHOT.json`,
`OWNER-TASK.md` and `BUILD-EVIDENCE.json`, cross-checked read-only against this
clone at the snapshot base and against the local Intel reference text.

Base check: this clone is at `b040b155159f47629542b0083e2f0a8a607f2b4c`, which
equals the snapshot `base`. The candidate is 4 commits on top
(`de7f312e`, `58a24842`, `12fd464f`, `f6d09422` per build evidence).

## What the candidate does

New file `OptMovImmSel.lean` states the DESIGN 2B MOV-immediate rows as a
layer-A local rewrite: three tiles (`MovTile`: `weit` = pilot `movImm64`,
`kompakt` = accepted `CompactImmMov32Zero` row, `sign` = C7/0-style value
level), validator-decided certificate `MovImmCert` (`oberTot`), exact gates
`passtU32`/`passtI32`, admission `nullZulassen`, selector `waehleMovImm` in
zero/sign/wide order, lengths `tileLaenge` (10 vs 5/6 vs 7), value preservation
`waehle_wert`, three firewall theorems, wide+compact step agreement
(value/flags/memory/other-registers), downstream `Bedingung` agreement, byte
grounding for the wide and compact rows through the accepted round-trips,
four `decide` pins, and the connection `OptMovImmSel_verbindung` with joint
companion `OptMovImmSel_verbindung_zeuge` at `rax := 0x80000001` over hostile
all-ones registers plus the reached `lauf` run taking cell 8192 from 0 to 42.

## Evidence (independently checked)

1. Reused names all exist in the base tree with matching roles:
   `schritt_movImm64` (+`_flags`/`_speicher`/`_reg`, `Ausfuehrung.lean`),
   `stepCompact_mov32imm` (+`_flags`/`_speicher`/`_fremd`, `compactLen_ok`,
   `CompactImmMov32Zero.lean`), `compactWert`/`compactWert_nat`/`compactWert_fits`,
   `compactLen`, `roundtripCompact`, `brauchtImm64`/`brauchtImm64_genau`,
   `kompaktWitState`, `zeuge_speicher_aendert_sich`, `narrowTruncMod`
   (`NarrowOps.lean`), `roundtrip` (`Codec.lean`), `sext`/`trunc`/`signBit`,
   `bedingung` (`Wort.lean`), `lauf`/`zeugeProg`/`zeugeZustand`.
2. No Lean-name collisions: none of `MovTile`, `tileWert`, `MovImmCert`,
   `passtU32`, `passtI32`, `nullZulassen`, `waehleMovImm`, `tileLaenge`,
   `OptMovImmSel_verbindung` occurs anywhere in the base `grammatik/` tree.
3. No forbidden tokens in the added Lean code: the only matches for
   sorry/admit/axiom/native_decide/unsafe in the review bundle are prose
   mentions in the task/report and quoted build logs, never proof terms.
4. Architecture cross-check against the local Intel text (edition 093):
   `REX.W + B8+ rd io` = MOV r64, imm64 (10 = REX + opcode + imm64);
   `REX.W + C7 /0 id` = MOV r/m64, imm32 sign-extended (7 = REX + C7 +
   ModRM + imm32, register-direct); B8+rd id row already accepted in-tree.
   Length claims 10/5-6/7 are consistent. MOV has no memory operand, affects
   no flags, raises no memory fault, is a full-register write on every tile,
   and carries no TSO event by itself — the file's "no fault above guard,
   no new shared access" treatment matches the manual.
5. Selector and pins hand-verified: 5/admitted fires kompakt; all-ones fires
   sign (u32 gate false, i32 gate true since 2^64-2^31 <= 2^64-1); 2^32 stays
   wide (both gates false); live upper half refuses admission for 5. The
   `sext` identity at the i32 boundaries holds by the case split proved
   (low half below 2^31 vs near-top with the mod-2^32 bridge lemma).
6. Witness is jointly inhabited and non-degenerate: one existential tuple
   (dst, v, s, c); register-changing reached step (all-ones to 0x80000001,
   upper half observably cleared) plus the store-changing reached `lauf` run
   from actual `Ausfuehrung` vocabulary. ZEUGE names match the task exactly.
7. Build evidence shows an iterative red-to-green path ending in
   `./lean-bau` green (511 jobs), `lean-probe` 0 errors, standard-only axioms
   on every main theorem, and `gabbro_ziel` unchanged on
   propext/Classical.choice/Quot.sound. No fresh build was run by this
   reviewer (report-only lane; source untouched by design).
8. Hygiene: exactly the 3 snapshot files; no new diagnostic/gift/example/CLI
   numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits,
   no friend-reserved optimiser files.

## Bounds of acceptance

- B1 (sign tile): no C7/0 bytes, decoder, or fetched step exist anywhere yet;
  the file defines none and duplicates none of lane 747's future names. Until
  747 lands, a validator must refuse to EMIT the sign tile and keep the proved
  wide fallback. Value-level `waehle_wert` covers sign; execution agreement
  covers only the byte-connected wide/compact pair — the connection theorem
  claims nothing beyond that, and the CUTS say so plainly.
- B2 (concurrency/FP/duties/budget): memory/flags/other-register preservation
  is sequential over one `Speicher`; per-access TSO/W/GX simulation,
  `FpZustand`/`stepExt` lift, call-log transfer, and source range re-derivation
  stay with their owner lanes as stated. The `oberTot` gate only ever
  restricts firing (refusal falls back to wide), so it cannot weaken any
  guarantee.
- B3 (prose correction, not a repair): the report text says downstream
  agreement holds "for every Bedingung (integer and float unordered rows
  alike)"; the `Bedingung` type has only the 16 integer Jcc conditions, and
  the proved theorem quantifies over exactly that type. The statement is
  exact; only the "float" wording in prose overreaches. No theorem change needed.
- B4 (style suggestion, not a repair): `movSelBit_div_pow`/`movSelBit31`
  openly restate the accepted `RelocatedExecution` bit pattern under local
  names to avoid a relocation import. Sound but duplicated; future work may
  reuse the accepted lemmas directly.

## Open items (none block acceptance)

Sign-row codec/fetch/byte-step (lane 747), TSO bridge, FP-context lift,
layer-C ghost-event transfer, and hardware correspondence — all explicitly
listed as NOT proved in the file's CUTS, consistent with a layer-A rule lemma.

## Lane-task note

The owner task's "premises from the DESIGN section 7 row" points at a row that
does not exist for MOV-immediate; the author used DESIGN 2B rows with the
section-7 certificate discipline instead and documented the deviation. I agree
with that reading; nothing else in the task text looks wrong.
