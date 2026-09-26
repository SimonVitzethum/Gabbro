# Verdict — the Spec diff of Opus agent G (OFFEN O1: the order leg `folge`, `N531`/`N532`)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-ade28fb3665aaaee9`, head
`4f82e886` (master `43c6ae32` merged in); report `messung/OPUS-G-O1.md`. Measured in the worktree
through the queued wrappers only (`./lean-bau`, `./lean-probe`, `./cargo-pruef`) and the branch's
own `target/debug/gabbro` for single `pruefe` runs. Two fixes committed separately: `2bf4bbf7`
(Rust, `N531`) and `9c54b97f` (Spec header and OFFEN O1, comments only). Nothing merged into
master, nothing pushed.*

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| Premises of `GabbroZiel` / `GabbroZielVerbund` | **unchanged** — the `Spec.lean` diff is header comments, one `import Grammatik.Folge`, the `Ziel` docstring and ONE new field `folge : FolgeG P M`; `Einheit`, `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`, `GabbroZiel` are byte-identical |
| Old `Ziel` a projection of the new | **yes** — one field added; `ziel_aus` proves every old field by the same term (`Beweis.lean` diff: one line `folge := folgeG_erreichbar sp init hr`) |
| Leg `folge` (`FolgeG`) | **SOUND, contentful as a soundness theorem of a static check; unconditional** (§2) |
| Quantification over `Φ` inside the leg | **well-formed, not vacuous** (§3) |
| L24/L34 closed "by argument" | **L34 correct; L24 OVERCLAIMED in wording** — one of the three legs cited (`invSicht`) is nominal in the model; fixed in `9c54b97f` (F2) |
| Header "what it adds" | **honest, two omissions** — fixed in `9c54b97f` (F3, F4) |
| Witnesses (`FolgeZeuge.lean`) | **SOUND, non-degenerate** — real 4/5-step runs, memory changed, the leg applied through `folgeG_erreichbar`; `folge50_gegen` a real counter-run |
| `N531` | **SOUND in direction, one false refusal** (static/state group carriers) — **fixed in `2bf4bbf7`** (F1) |
| `N532` | **SOUND** — sentence, gift 1292, positive twin |
| Corpus | **unchanged except one unreported extra line**: gift 249 now also shows `N531` (F5) |
| Emission check | **RED after the merge**: the `breaking` lowering probe no longer emits (F7, open) |

**Verdict: SOUND (with `2bf4bbf7` and `9c54b97f`).** No Lean soundness gap found. **Safe to merge
once F7 is decided** -- the emission ratchet is red because of this branch's `N531`.

## 1. Build and axiom evidence (measured, before the merge)

| Measurement | Result |
|---|---|
| `./lean-bau` (head `4f82e886`) | **exit 0, 0 error lines in the complete output, 328 jobs** |
| `./lean-bau` after `9c54b97f` | exit 0, 0 error lines, 328 jobs |
| `#print axioms` via `./lean-probe` (`import Grammatik`): `gabbro_ziel`, `gabbro_ziel_folge`, `folgeG_erreichbar` | **`[propext, Classical.choice, Quot.sound]`** each |
| the same in the build log for `folge50_zeuge`, `folge52_zeuge`, `folge50_gegen`, `folgeOk_mitRuhe` | the same three |
| `sorry` / `admit` / `native_decide` / `axiom` in `Folge.lean`, `FolgeBeweis.lean`, `FolgeZeuge.lean`, `Zielsatz/FolgeZiel.lean`, and the diff of `Spec.lean`/`Beweis.lean` | **none** (the only hits are the English word "axiom" in comments) |
| `./cargo-pruef` after `2bf4bbf7` | **exit 0; 1397 passed, 0 failed, 1 ignored** |

## 2. The leg `folge` — is it content?

**It is unconditional.** `folgeG_erreichbar (sp) (init) (hr : RufErreichbarG P O pa (RufStartG P
sp init) M) : FolgeG P M` holds for EVERY program of machine G; `ziel_aus` uses none of (a)–(d)
for it. As with `keinKernHalt`, adding an unconditional theorem as a conjunct of `Ziel` adds
nothing that depends on the checker's verdict — **the Lean acceptance Bool plays no role in it.**

**But it is not empty,** because the static premise sits INSIDE the leg: `FolgeG P M := ∀ Φ,
FolgeOk P Φ → …`. So the leg is the soundness theorem of a decidable per-block scan against
machine G — "if the program passes the scan for `Φ`, every run orders its call log by `Φ`" — and
both sides are real:

* **`FolgeOk` is a real check.** `eP2_folge50_falsch` (by `decide`) refuses the swapped program;
  every sub-block starts unarmed, an indirect call of a signature in `ind` demands the bit, and
  `FolgeOk` demands `ind (sig g)` for every `ruf g`, so no entry escapes through a pointer.
* **Failing programs can violate the order.** `folge50_gegen` is a reached 5-step run of `eP2`
  whose log contains the `ruf` entry AND the `vor` return, and `¬ FolgeLog` — so the conclusion is
  not a tautology of G, and `folgeLog_nicht_schwach` shows "directly behind" is strictly stronger
  than "both happened".
* **The ordered event occurs.** `folge50_zeuge` is a reached 4-step run where the newest event is
  the `pruefe` entry directly behind the `setze` return, with `konto[0]` changed 0 → 5 in the entry
  world (via the contract leg on the certified fixture), and the leg holds by the theorem;
  `folge52_zeuge` the finished-thread clause.

I read `Folge.lean` against the claim: `fS`/`fB`/`fE` arm only on a direct `call`/`bindCall`/
`bindCallElse` of a `vor` function; every compound statement, loop, lock block, `else` branch and
continuation layer is checked with `false`; returns demand the bit iff the frame's function is in
`ende`. `FolgeLog` exempts only the oldest event (`rest ≠ []`). The invariant `FolgeInvG`
(residue at the log's armed bit, every suspended caller at `vor` of its callee, `FolgeLog`) is
proved over every rule of G by `folgeInvG_schritt` — kernel-checked, standard axioms.

**What it gives a user, concretely:** pick `Φ`, decide `FolgeOk` on the exported Lean program,
read the order off `gabbro_ziel_folge`. **Nobody does this today** — no certificate states a `Φ`,
no Rust pass mirrors `FolgeOk`, and the tree applies the leg to no certified program (grep:
`FolgeOk` is used only in the fixture `eP`). The header said "naming `Φ` is the reader's step";
it did not say deciding `FolgeOk` is too (F3).

## 3. The quantification over `Φ`

`Folge D` is four Boolean functions over `D.Fn`/signature numbers; `∀ Φ : Folge D, FolgeOk P Φ →
…` is an ordinary Prop over a type in the same universe — well-formed. Not vacuous in either
direction: the all-false `Φ` passes every program and yields nothing (harmless); `Φ50`/`Φ52` pass
`eP` and yield real ordering; `Φ50` fails `eP2`. An over-broad `Φ` (e.g. `ruf := true`) fails
every program that calls anything first thing, so the leg is silent for it — that is the check
refusing, not a vacuity of the claim. `gabbro_ziel_folge` lifts `Φ` over `D` to `D.mitRuhe`
(idle root in no set, `ind` shifted by one) and `folgeOk_mitRuhe` is a structural induction —
checked it covers every `Stmt`/`Block`/`Endblock` constructor (`ruS_fS`, `ruB_fB`, `ruEnd_fE`,
the arm lemmas); the build accepts it.

## 4. Findings, ranked

### F1 — MEDIUM: `N531` refused a correct program (fixed, `2bf4bbf7`)

`breaking_rests_here` collected the written carriers as TABLE names only (`tabellen.contains`),
but `invariantentraeger` lists a `group` invariant's members, and a group may span a `static` or
`state` (`U001`: "carriers are `table`, `static` and `state`"). Measured with the branch binary:
a group `Paar over { Zellen, zaehler }` (a table and a `static mut`), a function `breaking
paar_stimmt { zaehler = 7; }` — **`N531`: "writes none of them and calls nothing"**, while the
same program without `breaking` checks with zero errors. The rule's own sentence promises it
"refuses only where the answer is certain". Fix: every written carrier root counts (a pointer
parameter still maps to its table); sentence `kbedingung.breaking-rests-here` updated; test
`n531_statischer_gruppentraeger_ist_sauber` pins both forms clean. After the fix the corpus hits
are unchanged (below).

### F2 — MEDIUM: L24 "claimed by `invSicht`, `sperrSicht`, `sperrWechsel`" overreaches (fixed, `9c54b97f`)

The review of Opus agent D (F2) found `invSicht` NOMINAL in the model: an accepted model program
never writes a guarded table invariant. With `Inv := Empty` for every certified program, the
table-invariant route to L24 is empty twice over. The **lock** route is real: `S` is exported
(`lean_g.rs`: `S := gS`), and `sperrSicht` (every access to a protected carrier is by the holder)
plus `sperrWechsel` (every acquire starts from the invariant) do say "no other thread sees the
pair half set" — when the pair sits under ONE lock whose invariant relates it. The header L24
bullet and the OFFEN O1 row now say so. L24's literal reading being false small-step, and the
observational reading being the content, I accept; L34 as an existence statement with the
`tabelle_gebrochen` shape is correct and needs no leg.

### F3 — LOW: deciding `FolgeOk` is the reader's step too (fixed, `9c54b97f`)

See §2. Added to the order block.

### F4 — LOW: the start-entry exemption was not in NOT CLAIMED (fixed, `9c54b97f`)

`FolgeLog` exempts the oldest event, and every thread — declared start or a dormant slot entered
at a run-time spawn (FadenMaschine) — begins with its start function's `eintritt`. So a `ruf`
function that runs as a thread's start function is never ordered. The definition's docstring said
"except the thread's start entry"; the NOT CLAIMED list did not. Added there and to the order
block.

### F5 — LOW: one corpus line the report does not mention

Over all of `beispiele/*.gab` and `beispiele/gift/*.gab` (branch binary, after F1's fix) `N531`/
`N532` fire exactly on gifts 1291 (`N531`), 1292 (`N532`) **and 249** (`N531`, besides its
expected `D009`: its `breaking belegt_zaehlt` block only reads). The extra line is correct — the
block writes nothing — and no clean example changes. The report's "corpus unchanged" should be
read as "no clean file changes; gift 249 gains a second refusal".

### F7 — MEDIUM, OPEN: `N531` takes the `breaking` lowering probe out of the emission check

`./emission-pruef` after the merge: **exit 1, cut at stage 9** — "RATSCHE GEBROCHEN: 151 emitting
files in messung/*/, booked are 152" (`MARKE_EMIT_M=152`, not edited). The file that left is
`messung/proben/absenkung/probe-absenkung-bricht.gab` (unchanged from master), the lowering probe
for the `Bricht` primitive, whose body is `breaking kette_ruht { } return n;` — an EMPTY block,
which `N531` now refuses, correctly. Scanning every `.gab` under `messung/` with the branch
binary, it is the only file `N531`/`N532` touch. The agent did not run the emission check.
Everything behind stage 9 (stage 10, the library chain) was NOT measured.

Not repaired here, because every repair is a decision about a measurement file:
(a) a body that calls a declared function (`breaking kette_ruht { gegenstelle_schreibt(1); }`)
emits (measured: exit 0) and keeps the shared scaffold, but only by using `N531`'s call exemption
for a callee that writes no `Baum` carrier -- a bypass of the rule's intent, rejected here;
(b) a body that writes a `Baum` carrier is the honest probe, but needs `writes b.slots` in the
signature the seventeen probes share; (c) lower the ratchet to 151 with a dated reason. (b) is
recommended.

### F6 — NOTE: "directly behind" is per thread and at call-log granularity

Leaves between the `vor` return and the `ruf` entry — assignments, axiom calls, register
accesses — are allowed and not logged; other threads interleave freely. The header says both
(leaves in between; axiom/register effects not in the log). For L50 this means "no Gabbro call in
between", not "no effect in between" — honestly named.

## 5. `N531` / `N532`

* **`N531`** (`kbedingung.breaking-rests-here`): a call-free `breaking I` block that writes no
  carrier of `I`. Sentence present, `Satzstand::Gemessen`, gift 1291 (example 53 with the name
  swapped), positive twins 53, 55 and `n531_richtiger_name_ist_sauber`. Conservative: any
  function call or indirect call exempts the block. A tightening only; after F1 no correct program
  I could construct is refused.
* **`N532`** (`kbedingung.breaking-blocks-maintainers`): a direct call inside `breaking I` of a
  function whose `maintains` names `I`. Sentence present with its limits (`requires I` as a
  predicate word and indirect calls not resolved; matches by the last path segment, so a name
  shared across modules could over-refuse — not observed in the corpus). Gift 1292, positive twin
  `n532_pflegende_nach_dem_block_ist_sauber`. Correctly stated as source discipline the Lean model
  does not need.
* `D013`'s `vorbehalt` updated to point at both. Numbers N531/N532 and gifts 1291/1292 from the
  reserved block N531–N535 / 1291–1300, booked in AGENTS.md §7.

## 6. Plain judgement

The order leg is a genuine, well-built addition: a decidable check, a premise-free invariant over
all rules of G, a non-degenerate witness and a real counter-run. It is **not** a guarantee the
checker enforces on the user's program — it is a theorem the user can instantiate, and nobody
instantiates it for a real program yet. The Spec diff now says exactly that. L24 is closed only
through the lock legs; L50/L52 are closed at call-log granularity for any `Φ` a program passes.

## 7. After the verdict: F7 repaired, second merge (2026-09-26)

* **F7 fixed in `624abc87`** by repair (b): the `breaking kette_ruht` block of
  `probe-absenkung-bricht.gab` writes `b.slots[s].benutzt`, and this unit alone adds
  `writes b.slots` to the shared signature. No other probe changed.
* Master `fc2de65a` (Opus lane O25b) merged in `36285f38`: G's SATZKARTE section renumbered 55 → 56.
* Measured after that merge: `./lean-bau` exit 0, 0 error lines, 347 jobs; `./cargo-pruef` 1401
  passed, 0 failed, 1 ignored; `./emission-pruef` exit 0, ALL PASS (42 differential units,
  310 of 310 files compile, 2 inverse probes). The messung ratchet holds again, and no MARKE
  counter was edited. ASan (stage 6b) did not run on this machine; it runs on fisch.
