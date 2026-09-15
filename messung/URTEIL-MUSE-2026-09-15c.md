# Confirmation verdict (independent Muse reviewer, round 5, 2026-09-15c)

*Base: branch `muse/192` (master at `cf154952`). No existing file changed; no Lean file
added outside scratch. Probe: `grammatik/.tmp/sonde192.lean` (git-ignored):
`./lean-probe` **0 errors** (exit 0). `./lean-bau`: **Build completed successfully
(226 jobs)**. I did NOT read `messung/URTEIL-OPUS-2026-09-15c*`. I read both round-4
verdicts (`URTEIL-OPUS-2026-09-15b.md`, `URTEIL-MUSE-2026-09-15b.md`), `SATZKARTE.md`
§23, and `Zielsatz/Spec.lean` at this tree.*

> **Goal (owner):** a Gabbro user proves only their OWN logic plus named hardware
> assumptions; everything else is carried by the language.

## VERDICT: **the goal with named gaps -- no unnamed gap found.**

F1-F3 are closed as §23 claims, each re-checked below. The sweep over every remaining
user-reachable stop finds nothing the user's code decides alone that is not already
named. The four §5 questions give the same answers as round 4, plus the three repairs.

## 1. F1-F3 re-verified (probe `sonde192.lean`, 0 errors)

- **F1.** `f1_lauf`: every body of `f1P` ends in `EndAusgang.logik Logik.bereich` for
  EVERY oracle, handler and budget; `probeF1_widerlegt_gilt`: (b) refuted;
  `f1_akzeptiert` (`by decide`): the checker accepts, so the refusal is (b)'s.
  By grep, all three float forms produce `.logik .bereich` in BOTH semantics
  (`Semantik.lean:743,747,752`; `SperreSem.lean:347,351,356`), and NO line of either
  file produces `.hardware .ieee` any more (only the inductive declaration itself,
  `Semantik.lean:302`, plus comments). The repair is in the obligation with no new
  shape, as §23 claims: (b)'s no-`logik` clause is `∀ e`, so `bereich` is inside it.
- **F2.** `kein_warteZyklusG` (`Beweis.lean:83`): `KeinWarteZyklus M` from `GutO` +
  `StufenM` on every reachable machine; wired as `keinZyklus` into `gabbro_ziel`
  (`Beweis.lean:144`). Statement read: a rank cycle is impossible for ANY thread
  chain, not only global deadlock. Holds.
- **F3.** `HaltArt` has exactly the three constructors; probe proves
  `haltArt_geschlossen : ∀ k, k = .hardware ∨ k = .flagge ∨ k = .budget` by cases,
  so the kind list is exhaustive. `KopfHalt`/`RestHalt` (`Spec.lean:508-528`) map
  each leaf/residue stop to exactly one kind; float stops are absent from the list.
  The ONE-list justification per kind is in the Spec header (`:120-153`). Holds.
- `gabbro_ziel` prints `[propext, Classical.choice, Quot.sound]` (probe tail). No
  `sorryAx`, no new axiom.

Producer sweep -- every `.hardware _` site in the flagship path
(`execBlock`/`execBlockH`, i.e. what (b) quantifies over), each tried as a
probe-A variant (contracts `ensures false` everywhere, checker accepting):

| Site | Who decides it | Probe-A variant disposition |
|---|---|---|
| `.fortschritt a` (spent `forever` budget; `Semantik.lean:480`) | budget counter, quantified in (b) (probe D refutes `forever`-with-`leave` + `ensures false` at some budget: `probeD_widerlegt_gilt`) | `forever` WITHOUT `leave` + `ensures false` meets (b) vacuously and never returns -- NAMED partial correctness (both round-4 verdicts; termination NOT CLAIMED, Spec header `:278`) |
| `.annahme a` (axiom answer ill-typed; `Semantik.lean:652,708`, `SperreSem.lean:255,312`) | the oracle's answer | An axiom with an (almost-)empty result type stops deterministically under every oracle -- NAMED honest vacuity, both kinds (Spec header `:101-108`: "`Q := false`" correction) |
| `.register r` / `.geraet r` (device answer; `:713-714,721`, `SperreSem:317-318,325`) | `O.regLies` | NAMED hardware; `rzusage = false` is the same honest vacuity, visible in the declaration (Spec header `:129-132`) |
| `.sichtbarkeit` (`awaits` not visible; `:726`, `SperreSem:330`) | `O.sichtbar` | NAMED `flagge` wait, with the never-published case explicitly justified as liveness, not claimed (Spec header `:133-142`) |
| `.ieee` | NOBODY in the flagship path -- no producer (above) | Legacy `ZielOrtGanz.lean:86` still produces it, but that chain is superseded (§13) and NOT imported by `Beweis.lean` (imports: `RuheNutzer`, `Ruhe`, `ZielOrtStart`, `ZielOrtInvGrund`, `Fortschritt`); the `MitRuhe` mappings (`\| .ieee => .ieee`) transport a never-produced constructor. Hygiene note, not a gap. |

No outcome the user's code decides independently of the oracle (or budget) empties
the obligation through an unnamed stop. Integer `narrow` keeps its `else`
(`Semantik.lean:731`); reason exits (`grund`) carry owed invariants but no
`ensures` -- a named boundary (round 4, unchanged).

## 2. The four questions (PLAN-ZIELSATZ.md §5) -- anything NEW?

1. **Legs vs words.** Unchanged from round 4 except the three repairs, each now
   matching its words: no user-decidable float stop (`BereichG`, no float in
   `FortschrittG`), no wait cycle (`keinZyklus`), stops by kind. `zeit` stays the
   weakest leg (own-step bounds, named NOT CLAIMED). Nothing weaker found.
2. **Premise groups.** `GabbroZiel` (`Spec.lean:588-599`): (a) one Bool on `E`,
   (b) `NutzerPflicht E`, (c) `HardwareAnnahmen O E.Q`, (d) `Laufzeit E sp init`,
   run data otherwise. Every premise in exactly one group; `S`/`Q`/`starts`/`sp0`
   are fields of `E`, and each user-controlled field that could empty an
   obligation is met by a shipped refutation (`unerfuellbar_widerlegt`,
   `start_req_widerlegt`, `probeA_falsch_inv_nicht`, probe D pair) or a named
   vacuity (the table above). The `∀ C` quantifier's force still rests on the
   concrete `akzeptiert_pruefer` + `decide` witnesses -- an aging risk, already
   named, not new.
3. **Emptying by user choice.** Probes A, D, F1, table-breaker, unguarded-write
   (all in `Proben.lean`, green build) plus the sweep above. No new attempt
   succeeds: recursion past depth is `logik abstieg` (refusal, named adequacy
   limit); `E.starts = []` is a different program about the root
   (`akP3_ohne_starts`); `RegLokal` constancy is named (`register_ohne_traeger_konstant`).
4. **G vs the language.** Unchanged, still named: translation validation T1-T5
   open, DRF-SC assumed, exporter gaps (`starts`, `sp0`, source `requires`),
   no single Rust `Akzeptiert` Bool. Not re-measured here beyond confirming no
   `Spec.lean`/`Beweis.lean` change since round 4 alters the bridge.

## 3. Gaps (no change from round 4 except F1-F3 moving to the named side)

Named (may stay named): §6 list of `URTEIL-MUSE-2026-09-15b.md`, now with F1 as
"`Logik.bereich`, excluded by (b)", F2 as "`keinZyklus`, proved", F3 as "three
stop kinds in the ONE list". Two hygiene notes, neither a gap: the legacy
`ziel_ort_ganz` chain retains `.hardware .ieee` (superseded, unassembled); the
`MitRuhe` `.ieee` mappings transport a dead constructor.

---
CUTS (this verdict file): proves nothing; it classifies, counts and cites. Probe
theorems re-checked, not re-proved: `f1_lauf`, `probeF1_widerlegt_gilt`,
`f1_akzeptiert`, `kein_warteZyklusG`, `gabbro_ziel` (axioms as above); original:
`haltArt_geschlossen`, `bereich_ist_logik` (standard three or fewer). Producer
sweep by grep over `Semantik.lean`/`SperreSem.lean`/`ZielOrtGanz.lean`/
`Zielsatz/Beweis.lean` at branch `muse/192`. No cargo run (Lean-only lane),
nothing pushed.

(End of file.)
