# MUSE-REPORT-296: Independent review of candidate 272 (pilot instruction execution)

Scope: ONLY the pinned snapshot of author 272 (HEAD
ccefc1e208f4dc855f16a8b0fdee5ab5fc187041, base
229cb13e9323abc565feab56a85d1c4828613ff7, clean) in
.tmp/review/author-272/ (MUSE-REPORT-272.md, OWNER-TASK.md,
BUILD-EVIDENCE.json, PATCH.diff, snapshot copy of
grammatik/Grammatik/X86/Ausfuehrung.lean). No other clone read,
no source edits.

## Dependency check

- Base 229cb13e is an ancestor of this clone's HEAD; `git diff
  base HEAD -- grammatik/Grammatik/X86/` is empty, so the Typen /
  Wort / Speicher sources I probed against are byte-identical to
  the author's base. The snapshot file was copied into
  grammatik/Grammatik/X86/ only for probing, then removed; the
  tree is clean and no candidate file is committed here.

## What was verified independently

1. `./lean-probe grammatik/Grammatik/X86/Ausfuehrung.lean` on the
   snapshot copy: `== 0 error(s) in the COMPLETE output`. All 18
   `#print axioms` lines report exactly `[propext, Quot.sound]`
   (no sorryAx, no Classical.choice needed, nothing beyond the
   standard pair).
2. Report figure check: 869 lines, 69 `theorem`, 26 `def` --
   all match the snapshot file.
3. Forbidden patterns: `grep` for sorry/admit/axiom/native_decide/
   unsafe finds only the 18 `#print axioms` lines; no `: Prop`
   premise, no `intro _` / `have _ :=` discard.
4. Patch scope: PATCH.diff touches exactly MUSE-REPORT-272.md
   (new), grammatik/Grammatik.lean (one added umbrella import),
   grammatik/Grammatik/X86/Ausfuehrung.lean (new). No codes,
   gifts, examples, CLI or MARKE changes.
5. Semantic spot checks against Wort.lean / Speicher.lean:
   - `dispWort` is a genuine sign extension: `trunc .b32` masks
     to the low 32 bits and `sext` tests bit 31, so negative
     int32 displacements extend correctly (not zero extension).
   - `add64/sub64/xor64` return `(value, flags)`; `schritt`
     passes `r.2` as flags and `r.1` as value -- correct order,
     matching the stated equations.
   - All 14 `Befehl` constructors have a `schritt` arm (Lean
     exhaustiveness plus 0 errors confirms); `push rsp` reads the
     source before decrementing; `pop rsp` takes the loaded word;
     `call32` stores the post-decode address (`ripNach`) and adds
     the extended displacement to it; `ret` pops the target;
     `cmp` writes only flags/RIP (with register and memory frame
     lemmas); failed `read64`/`write64` and bad length yield
     explicit `none`, never a halt.
   - Witness `zeuge_speicher_aendert_sich` and all six probes are
     `decide` proofs over concrete states, so they executed the
     semantics: rbx = 42 with memory byte 0 -> 42; je taken to
     4114 / untaken to 4098; call+ret round trip (4101, 8192);
     push rsp stores old top 8192; pop rsp loads 7. The witness
     is state- and memory-changing, satisfying the spirit of the
     memory-changing requirement; hard-rule 13 needs no `_zeuge`
     here (no source-syntax universal, no ZEUGE line in the owner
     task).
6. Build evidence plausibility: BUILD-EVIDENCE.json shows the
   full `./lean-bau` (369 jobs, exit 0) run after the final
   state, preceded by honest intermediate failures (unknown
   identifier, struct-literal parse errors, rewrite failures)
   that were repaired in the log. No name clash with existing
   `schritt_*` theorems (different namespaces; author's full
   build with the umbrella import is the integration proof).
7. Claim boundaries: the report and the file's CUTS block agree
   -- no decoder/encoder, no TSO bridge, no source
   correspondence, no ABI/loader/timing/whole-binary claim,
   sequential `lauf` only. Nothing in the report overstates the
   code; the toolchain struct-literal note is corroborated by
   the single-line literals throughout the file.

## Finding

None material. German identifiers (`schritt`, `zeuge`) follow
the established X86 wave vocabulary from lanes 270/271; all
comments, docs and the report are English.

CANDIDATE: 272 ccefc1e208f4dc855f16a8b0fdee5ab5fc187041
VERDICT: ACCEPT
