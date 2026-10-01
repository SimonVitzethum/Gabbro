# MUSE-REPORT-302: Independent review of candidate 286 (X86/Gleitprofil.lean)

Lane 302, branch `muse/302`, model opencode-go/muse-spark-1.3-contributor.
Review ONLY of the exact snapshot pinned by `.tmp/review/SNAPSHOT.json`
(author 286, HEAD `d159e08fd9e134649d636709e6e7e2bca30cd7c9`,
base `dd02d912`, files `MUSE-REPORT-286.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/Gleitprofil.lean`).
Owned file: only this report. No code or central file edits.

## What was checked

1. **Snapshot integrity.** Base `dd02d912` exists in this clone; candidate
   HEAD is (as expected) only present as the `.tmp/review/author-286/`
   copy. `diff` of snapshot `Grammatik.lean` against `git show
   dd02d912:grammatik/Grammatik.lean` is exactly one additive line:
   `import Grammatik.X86.Gleitprofil`. No `Ty.fl`/Spec/source change.
2. **Independent Lean check.** `./lean-probe` on the snapshot file:
   `== 0 error(s) in the COMPLETE output`. Full-file elaboration
   (all proofs checked, not just statements). Dependencies
   (`Gleitkomma`, `GleitkommaBits`, `Typen`, `X86.Speicher`) are
   byte-identical between the candidate base and this clone
   (`git log dd02d912..HEAD` on those files is empty), so the probe
   result transfers exactly. Author's `BUILD-EVIDENCE.json` final
   `./lean-bau` (`exit 0`, `369 jobs`, `Build completed successfully`)
   is consistent with my probe, including the per-theorem axiom dump
   (spot-matched tail lines: identical axiom sets).
3. **Banned forms.** `rg` for `sorry|admit|native_decide|unsafe|^axiom`:
   no match. `#print axioms` output (both author's and mine): every
   theorem depends on a subset of `[propext, Quot.sound]` — standard,
   within the goal's allowance.
4. **HARD-RULES gate 3/4.** No premise typed `Prop` itself
   (`hF : F.dicht` is a normal propositional premise over the existing
   model's `Prop`-valued predicate, used via `unfold ... at hF; omega`
   — the same pattern as `GleitkommaBits.lean` itself). Every premise
   of every theorem is used. No `intro _` / `have _ :=`; no
   conclusion-restates-premise; no `forall rho/v` contract
   quantification; nothing called a semantics that cannot change
   memory (the only memory claims go through real `X86.Speicher`
   `write32/read32/write64/read64` and conclude `m.bytes a ≠ m'.bytes a`).
5. **Inhabitation.** No theorem quantifies over program syntax
   (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args` — zero matches
   outside comments), so no `_zeuge` companions are owed. Generic
   target helpers carry real boundary probes (`0x1F80`, `0x9F80`,
   `0x1FC0`, `0x3F80`, `0x0F80`, `0x1FBF`, `0x9FBF`, min-subnormal
   triples, `16777217`) and both memory witnesses observably change
   memory with nonzero patterns.
6. **Claim-by-claim cross-check against code:**
   - MXCSR bit values verified numerically: `0x1F80` = bits 7–12
     (masks, RNE, no FTZ/DAZ) → valid; `0x9F80` adds bit 15 (FTZ);
     `0x1FC0` adds bit 6 (DAZ); `0x3F80` adds bit 13 (RC=01);
     `0x0F80` clears bit 12 (PM mask); `0x1FBF`/`0x9FBF` set sticky
     bits 0–5. All six verdicts match the definitions.
   - Counterexample values verified: `⟨8388608, 1⟩` = 2^24 exactly;
     `⟨4503599895805952, -28⟩` with
     4503599895805952 = 2^52 + 2^28, i.e. (2^24+1) exactly — so the
     f32/f64 pair differs in VALUE, not just width, as claimed.
     `gleitAusInt` confirmed to be `ofInt f64` (`Typen.lean:92`), so
     `quelle_gegen_f32` is genuinely source-type-aware.
   - `muster32_null`: −0 → `0x80000000` follows from sign-bit layout.
   - `zehntel32_modell`/`zehntel64_modell` reuse the existing
     `zeuge_zehntel32/64` — no new trust.
   - `SSEAdd32Entspricht` is a `def`, never concluded by any theorem —
     the "named, unproved" gap claim is accurate; a green build is not
     presented as a hardware theorem. Same for NaN payloads (only
     classification concluded) and sticky flags (only check-ignorance
     proved). CUTS block complete and honest.
   - No name/example-specific rules, no diagnostic/gift/example/CLI
     numbers, no MARKE_EMIT, no Rust — confirmed by grep (only
     comment mentions of `Ty.fl`).
7. **Report accuracy.** One immaterial nit: the author report says
   "573 lines" while the snapshot file has 653 total lines
   (difference plausibly non-code `CUTS`/`#print` tail, ≈45 + ≈40
   lines). Not a defect; all named theorems/claims verified present.

No counterexamples found; no failing values or probes to reproduce.

## Verdict

CANDIDATE: 286 d159e08fd9e134649d636709e6e7e2bca30cd7c9
VERDICT: ACCEPT
