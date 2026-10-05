# MUSE-REPORT-1328: exact review of candidate 1327 (isa/addr/muldiv TSO projection)

## VERDICT: ACCEPT

CANDIDATE: lane 1327, pinned HEAD `c72c015cbe0408779d2fdac057596e3b08fd1d57`
(base `10fb97f11ec29c426cf09f34b72433566a758c0b`, SNAPSHOT `clean: true`).

## What was checked

- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1328`, branch
  `muse/1328`, working tree clean. The pinned author hash was never read
  (`git show/log/diff` on it untouched); the candidate was reviewed purely
  from the delivered FILES (PATCH.diff, per-path copies, OWNER-TASK.md,
  BUILD-EVIDENCE.json), read with the file tools.
- Scope: exactly the 3 owned files. `Grammatik.lean` hunk adds one line,
  `import Grammatik.X86.HwKapsteinTsoIsaAddr`, nothing else. New file holds
  17 theorems, zero `def`/`abbrev`/`inductive`/`axiom` (lifted, never copied).
- Forbidden tokens: grep over the candidate file finds no `sorry`, `admit`
  tactic, `axiom`, `native_decide`, `unsafe`, `sorryAx` — only the English
  words "admitted"/"admit no successor" in doc comments and the required
  17 `#print axioms` lines.
- Every cited accepted lemma exists in this clone with a matching signature:
  `adapterIsa_reg/_lade/_gibAus/_verweigert` + all five refusal variants
  (`HwIsaFamilies.lean`), `adapterAddr_verweigert`, `kapTso_schritt_erreichbar`,
  `kapTso_issueListe_erreichbar`, `kap_union_wort_tso`, `kap_union_stapel_tso`
  (lane 1295 — the wort/stapel no-op claim checks out), `wdSchritt_speicher`,
  `entriesOf_laenge`, `hwAddrWitTeil/Overlap_keine_gruppe`,
  `kap_step_isa/_addr/_muldiv`, `isaFam_weiterleitung/_fremd_alt/_spuelung_aendert_speicher`,
  `hwAddrWit_weiterleitung/_fremd_alt/_spuelung`, `kapTso_setTso`,
  `kapTso_setKernVonFp`. Union constructors `isa/addr/muldiv` and their
  `HwVollSchritt` embeddings match the three union lifts.
- `kapTso` is definitionally `tsoAnsicht` (`HwKapsteinTso.lean:19-20`), so the
  `rfl` silence legs and the `tsoAnsicht`-vs-`kapTso` hypothesis reuse in
  `kap_isa_tso_klass` / `kap_addr_store_issue` / `kap_addr_load_still`
  elaborate as written.
- Every premise of every theorem is used (checked per theorem; `len` via the
  `laengeOk` split, `kap_drei_tso` legs each consume their own universal).
  No conclusion restates a premise; no discarded hypotheses.
- Planted refusals really refuse: every `adapter*_verweigert*` leg rewrites the
  step to `none` and closes by `cases`, so no non-step is classified as a
  projection step. `kap_addr_tearing` reuses the accepted tearing refusals.
- Witness `kap_isa_addr_muldiv_zeuge` is non-degenerate: the exhibited events
  match the accepted `kap_step_*` statements character for character
  (buffered isa byte 7 at the stack slot, width-4 SIB store, register-only
  divide 17/5 in the `.ok` leg), and the two-core facts are genuine —
  owner-only forwarding (42 / `hwAddrWitV`), foreign core reads stale 0,
  drain observably changes shared memory (0 becomes 42 / `0x04`),
  observed from both cores (core 0 vs core 1 in `HwIsaFamilies.lean`
  1016-1059 and `HwAddressed.lean` 470-519).
- Silicon/vendor: no encoding, flag, fault-class or ordering fact is pinned
  beyond the reused family definitions; nothing Intel-only or AMD-only;
  the muldiv divide trap stays a cited refusal path. CUTS is honest:
  13 union tags stay FINDINGs, no W/GX bridge, no whole-word atomicity
  beyond byte drains + tearing refusals, no source/checker/contract/entry/
  ABI/loader/budget/liveness claim, no hardware correspondence beyond
  self-consistency.
- Author process evidence is credible: BUILD-EVIDENCE.json shows the file
  built in small increments with honest intermediate reds (including one
  `sorryAx` episode) repaired the same session, ending at
  `== 0 error(s)` with every theorem at `[propext, Quot.sound]`,
  `[propext]`, or no axioms, plus a full `./lean-bau` green (691 jobs).

## Last build result

`./lean-bau` on this clean clone: `Build completed successfully (693 jobs)`
(job count differs from the author's 691 because this clone sits at a later
master; the tree built with zero errors).

## Limitation (sandbox, not a candidate defect)

This reviewer could not re-run `./lean-probe` on the candidate file itself:
file writes outside `MUSE-REPORT-1328.md` / `arbeitsprotokoll/.commitmsg` /
`.tmp` (non-review) are denied and shell copy out of `.tmp/review` is
rejected, so the candidate could not be placed under `grammatik/` for a
mechanical probe. Mitigation: complete full-file review against the live
tree (above) plus the author's contemporaneous per-step probe evidence.
The merge gate rebuilds `grammatik/` locally anyway (AGENTS.md section 5),
which re-verifies elaboration then.

## What remains open (candidate's own CUTS, endorsed)

The 13 remaining union tags keep lane 1295 FINDING status; no W/GX bridge;
no whole-word atomicity; no source/checker/contract/entry/ABI/loader/budget/
liveness claim. The owner's three "task is wrong" notes are accurate
(MECHANISM/TASK mismatch, multi-step addr stores vs "exactly one event",
stale pilot-form census) and the file correctly follows the TASK paragraph.

## New definitions/theorems by this reviewer

None (report-only review; OWN ONLY MUSE-REPORT-1328.md).
