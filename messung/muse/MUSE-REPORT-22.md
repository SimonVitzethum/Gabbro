# MUSE-REPORT-22: read-only audit of Maschine.lean lines 2000-end

Scope: `grammatik/Grammatik/Maschine.lean` lines 2000-4111 (sections 14-tail
through 22). No existing file was modified; all demonstrations are new files
under `messung/muse-audit/22/`, each checked with `./lean-probe` (zero errors;
two intentional unused-variable linter warnings that corroborate findings 2
and 4). `./lean-bau` was not run because the task forbids touching existing
files and adds no imports to `Grammatik.lean` -- there is nothing new to build.

## What I checked

Every theorem/def/inductive with a declaration at line >= 2000 (21 items):

- `kette_aus_maschinenlauf_nimmt` (2167), `kette_aus_maschinenlauf_gibt`
  (2206): thin wrappers instantiating `kette_aus_maschinenlauf_schritt` with
  `rfl` memory facts. Same single-application shape as finding 3; not given a
  separate demo file (diminishing returns), counted in the table as
  pattern (a), UNVERIFIED (no dedicated demo).
- `zaehler_zeigt_atom` (2298), `hpc_hΛa_hcs_aus_zaehler` (2312),
  `SchrittImLauf` (2322), `zaehler_zeigt_atom_lauf` (2346): findings 1-2.
- `HeadAtom` (2451), `ThreadFiredIn` (2458),
  `pc_zero_without_prior_step` (2477), `pc_ne_zero_with_prior_step` (2504),
  `zaehler_aus_konstruktion_erstschritt` (2532),
  `zaehler_aus_konstruktion_einzelblatt_lauf` (2561): explicitly NOT flagged
  (genuine derivations; see "Cleared" below).
- `zaehler_aus_konstruktion_voll` (2688), `zaehler_routing_fremd` (2729),
  `zaehler_routing_gen` (2750): findings 2, 5, 6.
- `blatt_rahmen_vertrag` (2851), `blatt_rahmen_schritt` (2868),
  `kette_aus_maschinenlauf_blatt` (2892): finding 3 (first two with demos;
  the third reuses the mirrored §14 construction with one substituted frame
  proof -- same wrapper shape, UNVERIFIED, no dedicated demo).
- `hsingle_aus_einfaedig` (3123): finding 3.
- `SpeicherVertrag` (3209), `speicher_welt_speicher` (3216),
  `spec_aus_fuehrung_schritt` (3230): finding 7 (lock branches only).
- `PCSpur` (3594), `pcSpur_von_reach` (3607), `spec_aus_fuehrung_fremd`
  (3627), `spec_aus_lauf_voll` (3741), `stabil_aus_lauf` (3879): finding 4
  (seed/base vacuity) plus checked-but-honest induction steps (see "Cleared").
- `Stmt.speicherfest` (3988), `speicherfest_speicher` (4003),
  `hBlattAll_speicherfest_aus_feuerung` (4093): checked, NOT flagged --
  `speicherfest_speicher` does real case analysis over 27 statement shapes
  and `hBlattAll_speicherfest_aus_feuerung` genuinely combines it with
  `hMem`. Narrow but honest fragment discharge.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` found in the slice; no
  premise with type `Prop` itself; `#print axioms` lines throughout show only
  `[propext, Classical.choice, Quot.sound]`.

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration file | status | severity |
|---|-----------|---------|----------------------|--------------------|--------|----------|
| 1 | Maschine.lean:2298,2312 | (a) | `zaehler_zeigt_atom` concludes `hpc` rewritten by `hΛa`/`hcs`; `hpc_hΛa_hcs_aus_zaehler` packs it back into an existential -- a rewrite round-trip, no machine content. | messung/muse-audit/22/ZaehlerIdentitaet.lean (round-trip example + both directions) | VERIFIED | medium |
| 2 | Maschine.lean:2346,2729,2750 | (a)/(b) | `zaehler_zeigt_atom_lauf`, `zaehler_routing_fremd`, `zaehler_routing_gen` case on `hmem : SchrittImLauf ...` but both branches replay the per-step fact; run context (`M`, `pc`, `h`, `hmem`) is unused. | messung/muse-audit/22/SchrittMitgliedschaft.lean (demos A/B/C prove conclusions without `hmem`) | VERIFIED | medium |
| 3 | Maschine.lean:2851,2868,3123 | (a) | `blatt_rahmen_vertrag` is `(stmt_gut ...).1`; `blatt_rahmen_schritt` is `.weiter` on it; `hsingle_aus_einfaedig` is one positional `gen_gesittet` application -- single-application foldings, also true of `_nimmt`/`_gibt` (2167/2206) and the §18 chain theorem by the same shape. | messung/muse-audit/22/HuellenFaltung.lean (demos A/B/C) | VERIFIED (2167/2206/2892 partly UNVERIFIED, no dedicated demo) | low-medium |
| 4 | Maschine.lean:2015-2018,2151-2154,3050-3053,3697-3713,3769-3783 | (c)/(e) | Guarded conclusions close vacuously at the new/frontier index: `SerialLink` new-step branch derives `False` from guard+writer (`rw [hnw] at hwrF; simp at hwrF`); `SpecTriple` seed eigen goals over `schrittFaden = []` are rfl-trivial (Lean unused-variable linter fires on the emptiness hypothesis); `hBeyond`/`hNew` same shape. | messung/muse-audit/22/LeereHuelfen.lean (demos 1/2/3; linter warning on `hempty` is the evidence) | VERIFIED | medium |
| 5 | Maschine.lean:2688-2721 | (a) | `zaehler_aus_konstruktion_voll` conclusion is the step's own `hpc`/`hpcT`/`hpcR` slots plus `pcSchritt_eigen` advance; `hmem` only selects the (identical) branch. | messung/muse-audit/22/SchrittMitgliedschaft.lean (demo D replays conclusion from `hs` alone; linter flags `M0` unused) | VERIFIED | medium |
| 6 | Maschine.lean:2633-2675 (§17 header), 2276-2286 (§15 header) | (d) | Headers claim "positional routing (the atom the counter points at fires)" and "per-run form"; the proofs unpack the atom FROM the step's own `hpc` slot (direction reversed) and add no per-run content. Genuine remainder is booked honestly (S12 extraction match). | messung/muse-audit/22/KopftextAnspruch.lean (unpacking witness by casing `hs`) | VERIFIED (Lean part) / judgment prose | low |
| 7 | Maschine.lean:3397-3459,3460-3522 (lock branches) | (a) | Both lock branches of `spec_aus_fuehrung_schritt` close the eigen iff via `hMem.memPre/memPost` over same-`speicher` worlds (`speicher_welt_speicher`); no lock/trace/firing fact is inspected. Leaf branch genuinely needs `hBlatt` -- NOT flagged. | messung/muse-audit/22/GleicheSpeicher.lean (both demos) | VERIFIED (lock branches only) | low |

## Cleared (looked carefully, not flagged)

- `pc_zero_without_prior_step` / `pc_ne_zero_with_prior_step`: real induction
  over run/firing derivations; conclusions (`pc f = 0` / `≠ 0`) appear in no
  premise.
- `zaehler_aus_konstruktion_erstschritt`: computes the atom from `HeadAtom`
  (text shape), not from the step's `hpc` slot; counter zero derived from
  threading.
- `zaehler_aus_konstruktion_einzelblatt_lauf` singleton impossibility: genuine
  use of `hprog` against `hpc`/`hpcT`/`hpcR` (second step contradicts text
  shape).
- `spec_aus_fuehrung_schritt` leaf branch and `spec_aus_lauf_voll` induction
  step: real chaining of `hMem` + `hBlatt` + prefix triple; `hBlattAll`
  universally quantified over all intermediate machines is a strong,
  non-degenerate obligation (near-pattern-(e) but the strength is in the
  quantifier, and §22 honestly books the seven uncovered leaves).
- `speicherfest_speicher` / `hBlattAll_speicherfest_aus_feuerung`: real
  27-shape case analysis; honest fragment.
- `stabil_aus_lauf`: one-line `stabil_from_spec` application, documented as
  such -- folding, but honestly labeled a "consumer corollary".

## What remains open (audit does not close these)

- Whether `gen_gesittet`'s W4/W5 premises (`hEin`, `hungeteilt`) discharge for
  ordinary multi-thread programs -- finding 3 makes `hsingle_aus_einfaedig`
  only as strong as those premises.
- Whether `SpeicherVertrag` discharges for `QRequires`/`QEnsures` (booked
  downstream) -- finding 7's lock branches rest on it.
- S12 extraction match (`Λa = Λ`, `cs = cs₀` per occurrence) and S13
  `axiomCall` contract: untouched by this slice, correctly booked as witness
  duty.

## What I believe is wrong (in the task or the slice)

- Task rule 4(b) warns against quantifying contract parameters away; the slice
  does something adjacent that the rule does not name: it keeps parameters
  but weakens the CONNECTIVE -- `SpecTriple` eigen fields conclude `↔`
  (agreement) rather than preservation/implication along execution. An iff
  between two same-memory worlds says the contract cannot distinguish them;
  it does not say the contract HOLDS. The whole §§20-21 chain therefore
  transports indistinguishability, and only `stabil_from_spec`'s head validity
  plus `InterferenceFree` ever assert truth. This is not a rule violation, but
  it is the load-bearing weakening the lane taxonomy should name.
- §19 header claims "no bare `Prop` slot" as a load-bearing-premise guarantee;
  several flagged theorems satisfy that letter (every premise is elaboration-
  load-bearing) while violating its spirit (premises contribute no CONTENT:
  `hmem` in finding 2, `hempty`-style hypotheses in finding 4). "Used by its
  proof" (task rule 3) has the same gap: casing on `hmem` counts as use.
  Recommend: "every premise must restrict the conclusion" (deleting it must
  make the statement false or unprovable), not merely "be used".

## Build status

- `./lean-probe` on all five demo files: zero errors. Two intentional
  unused-variable linter warnings (`hempty` in LeereHuelfen.lean:50,
  `M0` in SchrittMitgliedschaft.lean:68) corroborate findings 4 and 5.
- `./lean-bau`: not run (nothing added to the build: no existing file touched,
  no import added to `grammatik/Grammatik.lean`, per the read-only task).
  Last build result line: N/A -- no build needed, none performed.

## New definitions/theorems (demonstration files only, none in grammatik/)

- messung/muse-audit/22/ZaehlerIdentitaet.lean: 3 examples (substitution use,
  corollary use, round-trip).
- messung/muse-audit/22/SchrittMitgliedschaft.lean: 4 examples (demos A-D).
- messung/muse-audit/22/HuellenFaltung.lean: 3 examples (demos A-C).
- messung/muse-audit/22/LeereHuelfen.lean: 3 examples (demos 1-3).
- messung/muse-audit/22/GleicheSpeicher.lean: 2 examples.
- messung/muse-audit/22/KopftextAnspruch.lean: 1 example + header analysis.

CUTS: no S12 extraction-match result is claimed; no statement about ordinary
programs' W4/W5 discharge; findings on 2167/2206/2892 lack dedicated demos
(UNVERIFIED parts); pattern-(d) "overclaim" judgments are prose comparisons,
not Lean theorems; `./lean-bau` was not executed (see Build status).

#print axioms: recorded per file via `./lean-probe` output -- every named
slice theorem depends only on `[propext, Classical.choice, Quot.sound]`;
demo files introduce no axioms beyond those.
