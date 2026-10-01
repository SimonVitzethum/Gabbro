# MUSE-REPORT-492: Independent exact-candidate review of 412

Clone: `/home/simon/Dokumente/gabbro-muse/a492`, branch `muse/492` — verified
(`pwd` + toplevel + branch) before any inspection. No other clone read.
Candidate commit `4fea6855...` is not in this clone's lineage, so review is
against the exact supplied material: `.tmp/review/SNAPSHOT.json`,
`.tmp/review/author-412/OWNER-TASK.md`, `PATCH.diff` (372 lines),
`dokumente/x86/AUDIT-FLOAT-SIMD.md` copy, `MUSE-REPORT-412.md`,
`BUILD-EVIDENCE.json` — plus independent spot-checks and reproduced probes
in my own clone (current master lineage, `Gleitprofil.lean` / `Vektor.lean`
both 653/651 lines as cited).

## What the candidate delivers

Docs-only adversarial audit `dokumente/x86/AUDIT-FLOAT-SIMD.md` (296 added
lines) + `MUSE-REPORT-412.md`. PATCH touches exactly those two files: no
Lean, Rust, checker, Spec, goal, emitter, Typen/execution/codec or friend
path touched. Bounded claim: accepted `Gleitprofil`/`Vektor` modules are
"correct within their stated claims", with file/theorem/line evidence,
reproduced probes, and prioritized consumer bridge tasks P0–P3. No full
compiler closure claimed; CUTS of the audit names what stays OPEN.

## Independent verification (my clone)

- `Gleitprofil.lean` / `Vektor.lean` line counts 653/651: confirmed.
- `mxcsrGueltig` admission theorems, `kontextReset_gueltig`,
  `kontext_nicht_global`, `mxcsr_sticky_egal_*`: names confirmed by grep.
- `f32_rundet_16777217` / `f64_trennt_16777217` / `quelle_gegen_f32` /
  `nan_nutzlast_offen32`: present as cited.
- `SSEAdd32Entspricht` is a `def` with zero theorems concluding it:
  confirmed (`grep -c "theorem.*SSEAdd32Entspricht"` = 0). The audit's
  warning against citing model `add` as executed-SSE behaviour is accurate.
- Pilot `Befehl` (`X86/Typen.lean:53-67`): 14 integer/control constructors,
  no float/XMM/SSE/FMA form: confirmed by direct read.
- No fused/FMA op in the model: confirmed in substance (only comment words
  like "refused" match a naive `fused` substring grep — immaterial).
- `GFloat = GBits f64`, `klasse` with no quiet-bit distinction, NaN input-bit
  propagation arms (`.nan, _ => a`), canonical computed `nanQ`: confirmed.
- `vecWrite` two-chunk lowering with no `OhneUmbruch16` premise in the `def`,
  while `vecRead_nach_write` demands `hno`: confirmed — the audit's
  do-not-fork-a-second-refusal-register note is correct.
- `vecWrite_teilt`, `simdFreigabe = false` + `simd_gesperrt`: confirmed.
- Reproduced in `$TMPDIR` (private scratch, removed after) via `./lean-probe`:
  **0 error(s)**, and `#check @vecWrite_teilt` / `@SSEAdd32Entspricht` print
  exactly the statements quoted in BUILD-EVIDENCE. No forged evidence.
- BUILD-EVIDENCE commit sequence is coherent (files untracked → staged →
  committed as `4fea6855` with owned-files-only status).

## Defect check

- Hidden correctness assumptions / unused premises / vacuity: N/A, no new
  theorems. None in the prose either — every "correct" verdict is explicitly
  scoped to the stated claim with the OPEN bridge named beside it.
- Invented bugs out of OPEN bridges: none found; the audit explicitly refuses
  this pattern (§3 reviewer-trap paragraph verified against the actual `def`).
- Safety weakening / duplicated IR / second registers: none; P0–P3 assign work
  to consumer lanes (340, 348, 424/425/426, 347) without changing the modules.
- Overclaim toward full closure: none; the report states `lean-bau` full was
  not run with the docs-only justification, which is acceptable (no
  `grammatik/` change exists to rebuild).
- Two immaterial nits, not repair-blocking: (1) "zero `fma`/fused matches"
  is true only modulo the substring inside "refused"; (2) a few cited
  `Gleitkomma.lean` line numbers drift by ~2 lines (audit's own §7 CUTS notes
  line numbers may drift; theorem names are stable and correct).

## Verdict rationale

The precisely delivered bounded claim — a scoped, evidence-anchored audit
with honestly listed OPEN bridges and no code/model change — is what the
PATCH contains, and its material technical claims reproduce. Nothing in it
weakens a guarantee or misstates a theorem. ACCEPT.

CANDIDATE: 412 4fea68555b297f1c4af15f7e390a0d62397bfe6e
VERDICT: ACCEPT

Co-Authored-By: muse-agent-492 <muse-agent-492@noreply.invalid>
