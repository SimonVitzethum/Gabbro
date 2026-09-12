# MUSE-REPORT-45: read-only audit of the wave-1 BUILD merges
(VertragOrtB.lean, QLeer.lean, BlattGegenbeispiel.lean)

Lane 45. No existing file was modified. Scope: the three BUILD-merged files
only (`grammatik/Grammatik/VertragOrtB.lean` 488 lines, `QLeer.lean`
205 lines, `BlattGegenbeispiel.lean` 354 lines), read in full plus the
definitions behind the audited claims (`rufAt` in Semantik.lean,
`QRequires`/`QEnsures` in Extraktion.lean). The SATZKARTE
(`dokumente/SATZKARTE.md`) and the wave-1 lane reports 02/14/15
(`messung/muse/`) were read first; audit method follows lanes 19/23.
Rule-3 hygiene grep over the three files: no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`, no premise typed `Prop` itself, no `intro _`
or `have _ :=` discards. All probe `#print axioms` report only the
project baseline `[propext, Classical.choice, Quot.sound]`.

## What I did

Read-only audit with the wave-1 method: hunt for (a) conclusions equal to
premises or their existentials, (b) unused or `Prop`-typed premises,
(c) definitions trivially true/false for ordinary programs, (d) docstrings
or names claiming more than the Lean states, (e) premises false for
ordinary programs. Every finding carries a minimal checked Lean
demonstration under `messung/muse-audit/45/` (each ends with `CUTS:` and
`#print axioms`; each passed `./lean-probe` with 0 errors on the first
output line). `./lean-bau` was not re-run after the probes: the task is
read-only, nothing under `grammatik/` changed, and the pre-audit build was
green (`Build completed successfully (33 jobs).`); probes are not part of
the build (not imported by `Grammatik.lean`).

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration | status | severity |
|---|-----------|---------|----------------------|---------------|--------|----------|
| 1 | VertragOrtB.lean:75 (`contrAtomVonPC`) | (d) name/docstring claims an embedding; Lean states `ContrAtom D -> ContrAtom D := id` | The type never mentions `PCAtom`; the proof is `rfl`-level identity, so no plain-PC position is ever mapped | `messung/muse-audit/45/Audit45Embed.lean` (`rfl` fixed points incl. an entry atom) | VERIFIED | low |
| 2 | vertragOrtB.lean:101-109 (`contrProjRegel`) | (d) docstring "ties steps to atom lists"; Lean gates only the `ev = none` case | A run whose every step carries an event satisfies the rule vacuously; atom lists never constrain event steps; nothing in the build consumes the rule (grep) | `messung/muse-audit/45/Audit45ProjRegel.lean` | VERIFIED | low |
| 3 | vertragOrtB.lean:444-462 (`rueck_ohne_nachbedingung`) | (a) first conclusion conjunct is the premise `hens_pos` verbatim | Proof is `refine <hens_pos, ?_>`; the `.ok != .logik` half needs only `hruf`, no ensures check; the "bridge" echoes its own premise | `messung/muse-audit/45/Audit45Bruecke.lean` (both halves isolated) | VERIFIED | medium |
| 4 | vertragOrtB.lean:155-166 (`ensAmRueck_gibt_qensures_pkt`) | (a)-adjacent: conclusion is the premise `w` at `(v, rho)` | Proof applies `w v rho` (`have hv := w v rho`); the place-check `h` only supplies the `hs`-transport spelling, provable from `w` alone | `messung/muse-audit/45/Audit45Link.lean` | VERIFIED | low |
| 5 | QLeer.lean / BlattGegenbeispiel.lean | negative control, NOT a finding | Q-falsity witnesses compute by `rfl`; the slot contract distinguishes true/false-slot worlds, so it is memory-sensitive, not constant | `messung/muse-audit/45/Audit45Negativ.lean` | VERIFIED (pass) | info |

Zero findings of type (b) (every premise of every audited theorem is used;
checked by reading each proof), type (c) in the strict sense (no world
fold makes a predicate trivially true/false for ordinary programs; the
closest is finding 2, where event-carrying runs vacate the rule), or type
(e) as a new premise defect (the false-for-ordinary-programs premises
`hSeedAll`/`hBlattAll` are the wave-1 BUILD claims themselves, confirmed by
the negative control, not re-flagged here).

## New definitions/theorems

None in `grammatik/` (read-only audit; no `import Grammatik.<Name>` line
added). New demo probes only, all under `messung/muse-audit/45/`:
`Audit45Embed.lean`, `Audit45ProjRegel.lean`, `Audit45Bruecke.lean`,
`Audit45Link.lean`, `Audit45Negativ.lean`.

## Last build result

Pre-audit `./lean-bau`: `Build completed successfully (33 jobs).`
Post-audit `./lean-bau` was not re-run (read-only: no file under
`grammatik/` changed, so the build is untouched by construction). Every
probe passed `./lean-probe` with `0 error(s)` on the first output line.

## What remains open

- Findings 1-2 are about the wrapper's disconnected halves (`ContrAtom`
  vs `PCAtom`, `contrProjRegel` vs `PCSchritt`): the file's own CUTS
  already books this as missing `PCReach` wiring. Whether the follow-up
  file envisioned in MUSE-REPORT-02 (placed after `Maschine.lean`) can
  identify the atoms without collapsing the entry/return positions is the
  open design question; findings 1-2 say the current file does not.
- Finding 3 sharpens the file's own CUTS (only one direction of the
  "exactly the case" iff is proved): even the proved direction carries no
  ensures content beyond echoing `hens_pos`. A genuine bridge would need
  to derive the ensures check from the `rufAt` equation instead of taking
  it as a premise.
- Finding 4 is flagged low deliberately: transporting a pointwise fact
  along a world equation is legitimate bookkeeping. The residual issue is
  only that the lemma name ("place-check gives quantified check")
  suggests lifting place truth to quantified truth, while the proof goes
  the other way (quantified truth `w` discharged at one point).

## Anything in the task I believe is wrong

Nothing material. One scoping note: the task lists `VertragOrtB.lean`
alongside two counterexample files, but `VertragOrtB.lean` is a BUILD
attempt (new contracts-at-place machinery), not a degeneration exhibit,
so patterns (c)/(e) fit it poorly by construction -- its defects, where
found, are of type (a)/(d) (echoes and overclaiming names), as tabulated.
The genuine (e)-class content of this wave (`hSeedAll`/`hBlattAll` false
for ordinary programs) lives in QLeer/BlattGegenbeispiel and verified
clean (probe E).
