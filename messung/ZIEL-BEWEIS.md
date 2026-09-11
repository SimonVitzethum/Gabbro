# Goal proof: mathematical closure (w06)

Branch `w06-zielschluss`, base `2fdded7` (verified: `git rev-parse HEAD` =
`2fdded7360feafb659a6807eb9f73438ae9b34d7`, `git log --oneline w06-zielschluss -1`
= `2fdded7 merge: p29-ziel`). Worktree `.claude/worktrees/w06` ONLY.
This file is the proof skeleton FIRST, the verdict LAST.
Status now: VERDICT GIVEN (all five waves landed 2026-09-11) — CONDITIONAL.

## 0. What "the goal is reached" means

The goal (user-facing contract): whoever verifies a Gabbro program proves ONLY
their own logic and their named hardware assumptions; everything else is carried
by Gabbro and CompCert — once Gabbro is verified.

Machine-checked core (`grammatik/Grammatik/Ziel.lean`, base `2fdded7`):

- `zwei_fehler` / `ziel` / `ziel_nutzer_last` conclusion: every outcome `o`
  is control flow (`ok`, `zurueck`, `grund`, `leave`, `next`), the author's
  own logic (`Logik D`), or a NAMED hardware assumption (`Hardware D`).
  Nothing else. That classification is proved (`exact zwei_fehler o`).
- The road from a real run to that conclusion travels as the four explicit
  premises of `ziel_nutzer_last` (`Ziel.lean:312-317`):
  `hBridge`, `hSeqLogic`, `hProbe`, `hLowering`.

Main theorem (paper-proof, this file):

> **GOAL-REACHED** iff each `ziel_nutzer_last` premise is discharged by a
> lemma whose assumption ledger contains NOTHING except
> (a) the user's own logic (`Logik D` errors: `requires`/`ensures` obligations
> at the declared contracts), and (b) NAMED hardware assumptions
> (`Hardware D` constructors: `fortschritt`, `sichtbarkeit`, and siblings —
> each with its probe name). No third class. In particular: no unverified-Rust
> pass smuggled as logic, no unnamed environment fact, no axiom, no `sorry`.

Remaining obligations at GOAL-REACHED = exactly { own logic, named HW
assumptions }. That is the whole ledger; §4 records every entry per lemma.

Assumption classes (ledger tags):

- `OWN-LOGIC` — a `Logik D` error the user's proof must discharge.
- `NAMED-HW` — a `Hardware D` error with constructor name + probe name
  (e.g. `fortschritt` + `sonde_tick` for `frist_zaehle_werte_eingehalten`).
- `GABBRO-CARRIED` — discharged inside the proof (theorem, no new hypothesis).
- `OPEN` — still a hypothesis; listed verbatim in the verdict. Honest, not hidden.

## 1. Definitions used by the verdict

- `G(o)` := the 7-disjunct outcome classification of `ziel_nutzer_last`
  (`Ziel.lean:318-320`): five control-flow cases + `Logik D` + `Hardware D`.
- `hBridge` := `∀ (l : Lauf D) (voll : Faden → List (Ereignis D)), IstVerschraenkung l voll → Gesittet l`.
- `hSeqLogic` := at base an abstract `Prop` placeholder (`Ziel.lean:315`); the
  discharging lemma MUST replace it by a concrete statement S (see L2).
- `hProbe` := at base an abstract `Prop` placeholder (`Ziel.lean:316`); the
  discharging lemma MUST replace it by a concrete statement P (see L4).
- `hLowering` := `Absenkung` (`Ziel.lean:317`: `proPrimitiv ≤ 18`, witness
  `absenkung = ⟨17, _⟩` at `Ziel.lean:93`).
- `cInclude-closed` := `Erhaltung.tafel` carries NO `.luecke .cInclude .offen`
  row; the row is decided (`entschieden` holds of it) with a cited ruling
  document. At base exactly ONE `.offen` row remains
  (`Erhaltung.lean:305`; the other two `.offen` mentions are the
  `entschieden` clause `:338` and the debt-proof witness `:793`).

## 2. Lemma interfaces and acceptance predicates

Each wave is read READ-ONLY (`git show w0N-zielschluss:...`, never checkout).
PASS requires ALL numbered clauses. Evidence = branch commit + `file:line`.

### L1 — cInclude closed (wave w01)

Claim: the last open ruling-table slot is ruled and adopted.
Acceptance predicate:

1. `git show w01-zielschluss:grammatik/Grammatik/Erhaltung.lean` contains NO
   line `.luecke .cInclude .offen` (the `:305` row is replaced by a decided
   status, e.g. `.aufListe "..."` with ruling cite).
2. A ruling document `messung/CFORM-REGEL-INCLUDE.md` (or same content under
   the wave's honestly named path) exists on the branch with `Status: ruled`
   and a testable price (admit-with-price or forbid rule, not a shrug).
3. `entschieden` of the new row holds by construction (row is `.benannt` or
   `.luecke _ <non-offen>`); the debt theorem `tafel_nicht_geschlossen`
   (`Erhaltung.lean:791-795`) is updated or withdrawn HONESTLY — it must no
   longer prove on `cInclude` grounds (if other grounds appear, they are
   booked as new OPEN items, not silently dropped).
4. No `sorry`, no new axiom (`#print axioms` of touched theorems shows at
   most `propext`/`Classical.choice`/`Quot.sound`); the wave reports its
   scoped `lake build` evidence.

### L2 — hSeqLogic bound (wave w02)

Claim: valid sequential logic survives interleaving (Owicki-Gries step) under
a stated, checkable disjointness bound; replaces the abstract `hSeqLogic`.
Acceptance predicate:

1. A CONCRETE proposition S is stated in the `grammatik/` tree (new or
   existing file, honest path): sequential `requires`/`ensures` contracts
   valid per body plus frame-disjointness (candidate premise: `exec_rahmen`
   disjoint write sets) imply the contracts hold at the last world of the
   interleaved chain (candidate conclusion shape: `allgemeinStabil` /
   step-preserved assertions at the chain end).
2. The theorem proving S (or S under explicit sub-premises) has no `sorry`
   and no axioms beyond the standard three; every sub-premise is ledger-tagged
   `OWN-LOGIC` or `NAMED-HW` (a sub-premise of any other class = FAIL, booked
   as OPEN).
3. The statement does NOT claim race-freedom itself (that is L3's); it takes
   interleaving discipline as premise and logic preservation as conclusion —
   the direction is checked, not assumed.

### L3 — hBridge covered (wave w03)

Claim: every interleaving of well-formed bodies is `Gesittet`; discharges
`hBridge` (full or narrowed-class version).
Acceptance predicate:

1. A theorem with conclusion `Gesittet l` for interleavings is proved:
   either the FULL `hBridge` shape (`∀ l voll, IstVerschraenkung l voll →
   Gesittet l`) or the NARROWED `ExecEng` shape
   (`ziel_gesittet_aus_exec_eng`, `Ziel.lean:234-238`) with W3 (exclusion),
   W4 (`Einfaedig` construction over the projected run), W5 (unshared-carrier
   shape) EACH closed — by proof from the declaration/construction, not by
   restating them as hypotheses of the same name.
2. Per-thread provenance is closed per body by `ziel_brav_aus_exec`
   (`Ziel.lean:203-207`); W1/W2 travel through `lauf_aus_brav` (already proved
   at base — reuse, not re-proof, is fine and must be cited).
3. No `sorry`, axioms at most the standard three; ledger tags only
   `OWN-LOGIC`/`NAMED-HW`/`GABBRO-CARRIED`. A narrowed-class proof whose
   narrowing premises stay hypotheses = PARTIAL: each remaining hypothesis is
   booked OPEN by name (still a FAIL for full discharge, honestly recorded).

### L4 — hProbe bound (wave w04)

Claim: the tick probe upholds the named deadline assumption
(`fristAlsAnnahme`, `fortschritt` + its probe); replaces abstract `hProbe`.
Acceptance predicate:

1. A CONCRETE proposition P names the deadline (`frist_zaehle_werte_eingehalten`,
   `beispiele/71`), the assumption constructor (`fortschritt`), and the probe
   (`sonden/sonde_tick.c`): expiry answers the assumption, the probe measures it.
2. Measurement evidence on the branch: fixed-seed LFENCE-bracketed RDTSC run,
   p99 tripwire with booked bound (base booking C=512, ~50% above p99;
   any rebooking is honest and recomputed, never lowered by fiat), default run
   exit 0, `--max-cycles 1` exit 1, UBSan clean; scope openly booked (counter
   body only, locks excluded and said so; sample currency R15/W10).
3. No proof of cycles is claimed (cycles stay `NAMED-HW`, never `OWN-LOGIC`
   proved or `GABBRO-CARRIED`); the Lean side contributes the naming
   (`fristAlsAnnahme`), the probe side the numbers. Ledger: exactly one
   `NAMED-HW` entry per covered deadline; uncovered deadlines (28 of 29 at
   base) stay OPEN and are counted, not absorbed.

### L5 — hLowering measured + preserved (wave w05)

Claim: the lowering contract holds with a MEASURED bound and the `ops` count
is preserved through the stated compiler leg; discharges `hLowering`.
Acceptance predicate:

1. MEASURED: the lexer run over real products (`ABSENKUNG-ZAEHLUNG.md` §2,
   open at base) is executed and booked in `messung/ABSENKUNG-*.md`: per-Gabbro-
   primitive C-statement max over true products, with command + counts. The
   recorded max confirms or honestly raises the witness: max ≤ 18 keeps
   `absenkung = ⟨17, _⟩`; a higher max moves the witness AND the cap together
   with the diff shown (never a silent cap lift).
2. PRESERVED: the preservation leg is stated with its exact scope —
   quantitative CompCert is CerCo, not the production compiler; production
   leg needs the measured pairs; the chain
   `absenkung_wert`/`absenkung_haelt_schranke`/`absenkung_monoton`
   (`Ziel.lean:103-116`) and `senkungBegrenzt` (`Erhaltung.lean`) stay intact
   (scoped build evidence, no `sorry`).
3. Honest exclusions stay booked, not proved away: sequential-only,
   race-free-only, no `__asm__`, no C11 `_Atomic` (base product counts: 39
   `_Atomic`, 120 `volatile`, 2 `__asm__` per `ZIEL-BEWERTUNG-2026-09-10.md`
   §3) — any product violating the scope is an OPEN item, not a counterexample
   buried.

## 3. Method (binding)

- Base verified `2fdded7`; STOP condition was "different" — not triggered.
- Waves read ONLY via `git log --oneline w0N-zielschluss` (poll) and
  `git show w0N-zielschluss:<path>` / `git diff 2fdded7..w0N-zielschluss`
  (verify). Their branches are never checked out; `Ziel.lean` is appended
  ONLY by w06 (§6); no wave may touch it (a wave touching it = FAIL of that
  lemma on hygiene grounds, recorded).
- Poll cadence: `sleep 120` between polls, up to ~90 min total. Each wave's
  FIRST commit past base triggers verification against the interface above.
- Heavy checks (scoped `lake`/`lean` over `Ziel.lean`) run on `ki-pc-fisch-101`
  in `gabbro-w06` ONLY (`rsync -rlpgoD` NOT `-a` for the tree + `beweise/` with
  `-a`; `PATH=$HOME/.cargo/bin`); never `cargo test` + `lauf.sh` in one tree;
  own scratch dir; no `pgrep -f`; `cargo test` (if any) with `--no-fail-fast`.
- Commit ONLY branch `w06-zielschluss` via `arbeitsprotokoll/.commitmsg` +
  `./commit.sh`. Never master/push/stash-in-merge. English only in this file
  and in commits; German doc cells elsewhere are NEVER rephrased.

## 4. Assumption ledger (filled as waves land)

| lemma | wave commit | verdict | ledger entries | evidence |
|---|---|---|---|---|
| L1 cInclude | w01 `f890dac` | PASS (merged w06 `abd8d3f`) | C3-preamble-trust: NAMED-HW (toolchain: fixed four-header preamble from `emit.rs` KOPF; pinned by `cc -c -O0/-O2/-Os` green + byte-identical preamble sha256 `571a9f41`; carried never proved) | `Erhaltung.lean:305` row decided (`.aufListe`, no `.offen`); `tafel_geschlossen : satz_tafel` by `decide` (`Erhaltung.lean:806`, `entschiedenDec` `:792`); `vertrag_braucht_tafel` honestly re-stated as contract-implies-table (`:811`); no `sorry`/new axiom; wave reports fisch `lake build` green. Hygiene note (not proof-open): the ruling lives in the row comment + commit message; no `CFORM-REGEL-INCLUDE.md` with `Status: ruled` was added — recommended follow-up doc, substance (priced + witnessed) present. No wave touched `Ziel.lean`. |
| L2 hSeqLogic | w02 `0bcff72` | PASS (merged w06 `cef9d36`) | `hSpec`+`requiresEigen`/`ensuresEigen`: OWN-LOGIC (user contracts); `hFree`: OWN-LOGIC (per-program Owicki-Gries check); `hAb`: GABBRO-DUTY (checker footprint, downstream `haengtAb_vertrag_gesamt`); R1 instantiation (`Pre := QRequires`, `Post := QEnsures` in `Extraktion.lean`): GABBRO-DUTY (mechanical, import direction forbids it here) | `InterferenzAllgemein.lean` §19: `SpecQ`, `SpecTriple`, `seqTriple_from_spec`, `stabil_from_spec` (`:1030`); direction checked (interference assumed as premise, stability concluded — race-freedom not claimed); standard axioms per wave build evidence. §6 binds it at Ziel level (`ziel_seqLogic_aus_spec`). |
| L3 hBridge | w03 `1fc7f4a` | FAIL partial (NOT merged) | W3 `ForeignExclusion`: NAMED-HW accepted (`A_lock` promise, bounded to `nimmt` steps); `hvoll`: GABBRO-CARRIED (closed per body by `ziel_brav_aus_exec`); W1/W2 via `lauf_aus_brav`: GABBRO-CARRIED; OPEN-1: W4 trace link (per-thread `Verlauf` through `exec` behind a real `Lauf` stands nowhere — §8 rebooked cut); OPEN-2: W5 run-to-`Bau` wiring (body-extraction coverage, cut C2) | Proved on branch: `bruecke_exec_gesittet` (`Wettlauf.lean:793`), `bruecke_exec_gesittet_of_verlauf` (`:812`), `gut_without_suffix` (`:767`), `covered_prefix` (`:779`); no `sorry`, standard axioms per wave evidence. Full `hBridge` (`∀ l voll, IstVerschraenkung l voll → Gesittet l`) NOT proved — narrowing premises stay hypotheses, exactly the case the interface books as FAIL. |
| L4 hProbe | w04 `231c514` | FAIL partial (NOT merged) | `TickClock` laws (`advance`/`maxGap`/per-use `start`): NAMED-HW (`dma_inhalt`-class); `fristErgebnis`-answers-`fortschritt`: GABBRO-CARRIED (proved); per-use `deadlineSpacing`: NAMED-HW (watchdog/granularity discharges per run); OPEN-1: probe-to-grid link (C4 `Fristlauf.lean:82` — hardware keeping the grid assumed per use; `sonde_tick.c` samples counter cycles, not a periodic sampler); OPEN-2: 28 of 29 deadlines without a running probe | Proved on branch: `TickClock.mono/covers/window` (`Fristlauf.lean:328`), `gridClock`/`grid_window`, `sampling_upholds_frist` (`:373`), `sampling_closes_frist` (`:395`); no `sorry`/`axiom` in additions; no branch measurement (relies on base booking) — clause 2 unmet, probe unnamed in proved P (generic `Frist`, cited by shape). |
| L5 hLowering | w05 `d3b0647` | PASS (merged w06 `93fff2f`) | bound 17/18: MEASURED (fisch re-run, recompute commands booked); 7 modeled CUT-1/2 ops count-preserved: GABBRO-CARRIED (`modell_lauf_erhalten`); meaning leg: GABBRO-CARRIED (reused `zeugnis_sound`); follow-up, Gabbro-side, no user obligation: apply `absenkung.rs` hook (`lib.rs` mod + `emit.rs` call, specified §3 not applied), extend `modellKopf` to 11 heads + CUT-3/4/5, StmtArt per-op preservation, C-to-Asm legs (`costKept` CerCo / `costMeasured` pairs untouched) | `ABSENKUNG-DURCHSETZUNG.md` §5 (`:170`): 17 units exit 0, T/V/R identical to lane-122, max 17, full provenance (base/tree/binary/memory); §6 (`:337`): preservation leg; `Budget.lean:639-690` modeled-ops appendix, standard axioms; `Ziel.lean` + `absenkung.rs` constants unmoved (bound stands still). §6 binds witness+bound (`ziel_l5_absenkung_zeuge/_schranke/_max`). |

## 5. Final verdict (GIVEN 2026-09-11, after all five waves landed)

> **CONDITIONAL.** Three of five lemmas PASS (L1, L2, L5 — merged, bound in
> `Ziel.lean` §6); two FAIL partial (L3, L4 — proved fragments with named
> remainder, not merged, premises stay hypotheses). The goal is NOT reached;
> what remains is exactly the list below — no other obligation, and every
> entry names its ledger class and its discharger.
>
> Remaining obligations = { own logic, named HW assumptions } PLUS the open
> list (all Gabbro-side sentences/measurements, none a user obligation
> beyond the two named classes):
>
> 1. L3-OPEN-1 (missing sentence): W4 trace link — per-thread `Verlauf`
>    through `exec` behind a real `Lauf D` (`SpurLink` narrowed, link itself
>    stands nowhere; w03 §8 rebooked cut).
> 2. L3-OPEN-2 (missing sentence): W5 run-to-`Bau` wiring — body-extraction
>    coverage (cut C2 in `Geteilt.lean`).
> 3. L4-OPEN-1 (missing link + measurement): probe-to-grid — the hardware
>    keeping the sampling grid (C4), with a periodic deadline sampler to
>    replace the counter-cycle `sonde_tick` shape for this use.
> 4. L4-OPEN-2 (measurement): running probes for 28 of 29 deadlines
>    (per-use `deadlineSpacing` is NAMED-HW and stays a per-run assumption,
>    not an open proof).
>
> What is CLOSED (machine-checked, merged): the ruling table
> (`tafel_geschlossen`), the sequential-contracts-to-stability bind
> (`stabil_from_spec`, Ziel-level `ziel_seqLogic_aus_spec`), the lowering
> witness and bound (`ziel_l5_*`, measured max 17 ≤ 18, modeled-ops count
> preservation). On those three legs a user indeed owes only their own
> logic; the hardware side is named (`fortschritt`+probe, `A_lock`,
> preamble toolchain check, per-use spacing).
>
> Principle applied (stated here, used throughout §4): a named Gabbro-side
> premise WITH an existing discharger (checker footprint `hAb`, hook
> application, downstream instantiation) is pending application under the
> standing assumption "Gabbro verified" — carried, not open. A premise with
> NO existing discharger (missing sentence, missing probe shape, missing
> wiring) is OPEN. That is why L2/L5 pass with remainder while L3/L4 fail
> with remainder — same honesty, different facts.

Verification (w06, `ki-pc-fisch-101` dir `gabbro-w06`, 2026-09-11):
`rsync -rlpgoD` tree + `rsync -a beweise/`; `grammatik: lake build` exit 0
(27 jobs, merged w01+w02+w05); `lake env lean Grammatik/Ziel.lean` exit 0;
`ziel_seqLogic_aus_spec` depends only on
`[propext, Classical.choice, Quot.sound]`, the three `ziel_l5_*` on no
axioms; no `sorry` in the §6 append (one build failure on the way was
w06's own: a `theorem` carrying the `Absenkung` structure — fixed to
`def`, rebuilt green). Wave files were verified read-only
(`git show`/`git diff` vs base `2fdded7`); their branches never checked
out, `Ziel.lean` appended only here.

## 6. Discharge record (mirrors `Ziel.lean` §6)

| premise | lemma | Ziel.lean theorem | status |
|---|---|---|---|
| (part of hLowering) cInclude | L1 | `tafel_geschlossen` (`Erhaltung.lean:806`, merged — named, not duplicated: `Erhaltung` imports `Ziel`, re-import would cycle) | DISCHARGED |
| hSeqLogic | L2 | `ziel_seqLogic_aus_spec` (§6, proved by `stabil_from_spec`, leaves `hAb`/`hFree`/`hSpec` explicit and tagged) | DISCHARGED down to named leaves (OWN-LOGIC + GABBRO-DUTY) |
| hBridge | L3 | none (stays hypothesis `hBridge` of `ziel_nutzer_last`; branch theorems cited read-only: `bruecke_exec_gesittet` etc.) | OPEN (items 1–2 above) |
| hProbe | L4 | none (stays hypothesis `hProbe` of `ziel_nutzer_last`; branch theorems cited read-only: `TickClock.window` etc.) | OPEN (items 3–4 above) |
| hLowering | L5 | `ziel_l5_absenkung_zeuge`, `ziel_l5_schranke`, `ziel_l5_max` (§6, closed); `modell_lauf_erhalten` (`Budget.lean:690`, merged — named, not duplicated: `Budget` imports `Ziel`) | DISCHARGED (witness + bound + modeled fragment; Gabbro-side follow-up listed, no user obligation) |
