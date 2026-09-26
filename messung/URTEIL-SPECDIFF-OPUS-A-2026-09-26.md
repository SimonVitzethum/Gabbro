# Verdict — the Spec diff of Opus agent A (threads created at run time)

*Independent adversarial review, 2026-09-26, of `git diff ba6c16a7..0bb682cc` (commits
`f554eaa2` Lean, `0bb682cc` exporter/docs/report) on branch `worktree-agent-a128f79321c4a4287`.
AGENTS §2: every extension of the goal is reviewed as a diff of `Spec.lean`. Nothing was accepted
on the strength of a comment or of the lane's own report
(`messung/OPUS-A-LAUFZEITFAEDEN.md`).*

**Machine:** the laptop, locally, through the queued wrappers only (`./lean-bau`, `./lean-probe`,
`./cargo-pruef`). `free -g` beside the runs: 31 GB total, 19 GB available.

---

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| `Einheit.gestartet` (default `[]`) and `Einheit.ws` listing each run-time root twice | **SOUND** |
| (b) `StartPflicht.req` and (d) `Laufzeit.start` over `starts ++ gestartet` | **SOUND** (for old units word for word the old ones, proved) |
| Conclusion moved to the thread machine: `∀ lebt0 K, FadenErreichbar … → ZielF …` | **SOUND**; `ZielF.g : Ziel` on the G state, so `ZielF ⊇ Ziel` |
| `gabbro_ziel_g`, `gabbro_ziel_vor` (the old statement preserved) | **SOUND** (§2.3 for the one nuance of "verbatim") |
| The new named assumptions in (d) | **SOUND, one assumption was missing** (F2, fixed: every spawn succeeds) |
| Exporter (`check_gestartet`, `Start` leaves no G term, LG001 relaxation) | **SOUND** (F3: the LG001 relaxation is broad, but Rust `H011` stands behind it, measured) |
| The report and OFFEN text | **OVERCLAIMED in two places** (F1, fixed) |

No unsound step was found. **Safe to merge** once the two review commits on this branch go with it.

---

## 1. Build and axiom evidence (measured, not quoted)

| Measurement | Result |
|---|---|
| `./lean-bau` on `0bb682cc` | **exit 0, 0 error lines, 289 jobs** |
| `./lean-bau` after the text fixes (`c7406624`) | **exit 0, 0 error lines, 289 jobs** |
| `#print axioms` (probe file through `./lean-probe`) for `gabbro_ziel`, `gabbro_ziel_g`, `gabbro_ziel_vor`, `spawn_start_ziel`, `spawn_kind_ziel`, `sj_lauf`, `kw2_lauf`, `start_nicht_poolsicher_abgelehnt`, `kind_unter_sperre_abgelehnt`, `klon_ziel_faden` | **every one exactly `[propext, Classical.choice, Quot.sound]`** |
| added lines of the diff under `grammatik/`: `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `opaque`, `unsafe` | **none** |
| `axiom` declarations in `grammatik/` | only the pre-existing `dma_inhalt` (`Geraet.lean:204`), outside `gabbro_ziel`'s set |
| `./cargo-pruef` | **exit 0: 1327 passed, 0 failed, 1 ignored** |
| new files imported by `Grammatik.lean` | `FadenMaschine`, `Zielsatz.Faeden`, `Zielsatz.FaedenVor`, `Zielsatz.FaedenZeuge` — all four, so the build checks them |

## 2. The premises and the conclusion, line by line

### 2.1 Premise changes: relaxation or restriction?

* **`Einheit.gestartet := []`** — a new field. On every unit of before it is `[]`.
* **`Einheit.ws := (starts ++ gestartet ++ gestartet).map (·.1)`** — for `gestartet = []` the old
  list (`ws_ohne_gestartet`, by `rw`). For a unit with roots it is longer, which feeds every
  `ws`-reading component of `AkzeptiertSpec`. I checked each for a direction that a longer list
  could RELAX: `wurzeln` (∀ over more elements: stricter), `einzeln` (`EinzelnPool`, more
  `Mehrfach` routines: stricter), `renn`/`SchreibGetrennt` (∀ pairs: stricter), `fuss` through
  `lokW = Getrennt` (∀ pairs, and self-pairs for `Mehrfach`: `lokW` is true less often, so a
  carrier is local less often: stricter). **No component is relaxed by the duplicates**; none
  becomes vacuous, and no `Nodup`-style premise exists any more that duplicates could falsify
  into vacuity (F10 removed it).
* **(a) `Pruefer.korrekt`** — textually unchanged, reads the new `ws`. For the concrete
  checker, `akzeptiert_pruefer := Akzeptiert … E.ws`, so the Bool really sees the doubled roots.
* **(b) `StartPflicht.req` over `starts ++ gestartet`** — a new DUTY for units with roots (the
  root's `requires` at `E.sp0`); for old units the same (`startPflicht_vor_iff`). It is
  satisfiable and satisfied on the witnesses (`zStart_nutzerPflicht`, `zKind_nutzerPflicht`).
* **(d) `Laufzeit.start` over `starts ++ gestartet`** — admits more `init`s (a relaxation of what
  the runtime may do, so a larger class of runs is covered); `einmal` unchanged in text, and a
  root is always `Mehrfach` (`mehrfach_gestartet`), so it may occupy any number of slots. For
  old units the same (`laufzeit_vor_iff`).
* **Runs** — `∀ M, RufErreichbarG …` became `∀ lebt0 K, FadenErreichbar … (FadenStart … lebt0) K`.
  `fadenErreichbar_von_G` embeds every G run (all live, nothing spawned), and `lebt0` is
  universally quantified, so the class of runs only grew.

**Is any previously accepted unit now rejected?** At the Lean level: no — with `gestartet = []`
`ws`, (b), (d) and the Bool are identical (proved). At the Rust/exporter level: no — every unit
the exporter produced before has no `start` (it was `LG004`), and a unit without `start` prints
no `gestartet` line, byte for byte as before (test `exports_start_roots_as_gestartet`;
`pruefe-genlean.py` 2/2 in the lane's report). The LG001 relaxation (`!scan.startet`) touches
only bodies with a `start`, i.e. units that were refused before.

### 2.2 The conclusion: `ZielF ⊇ Ziel`

`ZielF.g : Ziel P S O passes M0 K.m` with the same `M0 = RufStartG …` as before. The other six
fields are additions. `gabbro_ziel_g` projects `.g` at `FadenMaschine.alleLebend M` — exactly the
old conclusion on every G run. Every former caller (Korpus 59/109/124/125, GenOblig104/108,
Schlusssatz, PoolZeuge, Proben, CloneHandoff) was switched to `gabbro_ziel_g` mechanically; I read
the diff of each: only the extra `[]` field, `List.append_nil` in `simp`, and the renamed call.
No probe was deleted or weakened.

### 2.3 Is the old statement REALLY preserved? (`gabbro_ziel_vor`)

I set `GabbroZielVor` beside the text of `GabbroZiel` at `ba6c16a7:Spec.lean:904–915`. Binder for
binder it is the old statement, with three differences, each examined:

1. `E.gestartet = [] →` is added: the old `Einheit` type had no such field; a new `Einheit`
   with `gestartet = []` is exactly an old one. Correct restriction to "units of before".
2. `NutzerPflichtVor`/`StartPflichtVor`/`LaufzeitVor` are verbatim copies of the old
   structures (checked against `ba6c16a7`).
3. `C : PrueferVor`, whose `korrekt` promises `AkzeptiertSpec … (E.starts.map (·.1))` for EVERY
   new `Einheit`, not only those with `gestartet = []`. This is a hair stronger than the old
   interface, whose domain was old units only. **Not a loss:** every old checker, read on a new
   unit by ignoring the field it cannot see, satisfies it, since the old `AkzeptiertSpec` reads
   only old fields. So "verbatim" is accurate in substance; I record the nuance, and do not ask
   for a change.

`gabbro_ziel_vor` then goes through `pruefer_aus_vor` (the old checker `&& gestartet.isEmpty`,
`pruefer_aus_vor_gleich`) and `gabbro_ziel_g`. Read line by line: nothing hidden.

## 3. The "roots twice in `ws`" trick, and the named assumptions

**Does it smuggle anything?** No (§2.1: only restrictions). What it buys is `Mehrfach`, hence
`PoolSicherW` and self-pairing in `Getrennt` — exactly what a routine that may run on arbitrarily
many threads needs. `akzeptiertSpec_gestartet` derives the root facts from the spec, not from a
new axiom or field.

**Against Rust `N458`–`N462`.** I built a probe the lane did not: a starter that writes an
UNGUARDED table before `start { leser }`, the root only reading it (`.tmp/probe/start-lesen.gab`).
Rust refuses it with **`N462`** ("touches a carrier that is written and that no lock guards"),
so the export never happens. That means Rust over-approximates exactly as the model does (a root
runs beside the starter as well), and the direction Rust-accepts ⇒ Lean-refuses I was hunting for
does not open here. But the two rules are **not the same rule** (F1): `N462` bounds every carrier
a root touches, `einzelnPoolB` only the written ones (reads are `Getrennt`'s), and `N458`'s
parameter/result half is the exporter's `LG001`. `N461` has **no** Lean-Bool counterpart at all:
it lives only as the side condition of the `start` step, so the model contains the real run of a
starter only because Rust refuses a `start` under a held lock and the exporter refuses to export
a unit with checker errors. That is the named assumption (2), and it is named — correctly.

**Satisfiable by lane 260's lowering?** (raw `clone` + futex join; child entered by jump with an
empty held set.)
* A `clone`d thread starts at its root on a fresh stack holding no lock: the `start`/`kind`
  steps' dormant slot at `startSpur`. Yes.
* A futex join that releases the starter only once every root has signalled completion after
  its body returned: the `join` step's `∀ u ∈ wartet p, FertigG`. Yes.
* The starter holding nothing at the site: `N461` in the source, side condition of `start`. Yes.
* Child by jump with an empty held set: `faden_schlafend_frei`. Yes.
* The ghost entry world (1) has no C counterpart; it is a statement about which world the model's
  contract legs speak of, and is named in NOT CLAIMED (`old` and `requires` at the spawn world).
* **Missing (F2):** the model's spawn never fails, and a `start` in a loop needs unboundedly many
  slots (`Faden := Nat`). A real `clone` can fail. This was not named anywhere; it is now (3) in
  (d) and a line in NOT CLAIMED.

**Too strong, making the new legs vacuous?** No. The premises are discharged on `zStart` and
`zKind` (accepted by `akzeptiert_pruefer` by computation, (b) and (d) proved), and the legs are
then derived there (§4).

**Happens-before of spawn/join.** Not needed by the model: every starter is itself in `ws` (a
declared start, a root, or the idle root which runs nothing), so the checker already forbids
unguarded conflicting access between starter and root; data synchronise through locks only. The
spawn/join flag's own ordering in C is lane 260's, covered by "the C side of the spawn".

## 4. Vacuity and witnesses

| Witness | What it really shows (read, not quoted) |
|---|---|
| `sj_lauf` | on `rufPF`: thread 0 `start`s dormant 1, 2 holding nothing; root 1 WRITES (slot 0: 0 → 2) and finishes; root 2 unfinished, starter in `JoinWartet`; root 2 writes, finishes; `join`; starter calls and writes. A real multi-step run with memory effects. |
| `kw2_lauf` | `kind` spawns 1; parent call, child write, parent write; the parent never waits. |
| `spawn_start_ziel` | ACCEPTED unit `zStart` (roots only in `gestartet`, `ws = [haupt, haupt]`): `start` of 1, 2 by the idle root, both spawned threads step, thread 1 takes the lock, starter in `JoinWartet` — and **`gabbro_ziel` itself** (not `_g`) yields `ZielF` at that `K4`. So `ZielF` is applied on a machine where spawned threads exist and hold a lock. |
| `spawn_kind_ziel` | ACCEPTED `zKind`, a `kind` spawn, parent and child step, parent takes the lock, `ZielF` via `gabbro_ziel`. |
| `start_nicht_poolsicher_abgelehnt` (+`_spec`) | the Bool refuses a non-pool-safe root at `einzelnPoolB` alone; the same routine as an ordinary start is accepted — the refusal is about being a root. |
| `kind_unter_sperre_abgelehnt` (+`_spec`) | a root holding a lock by signature refused at `wurzelnB`. |
| `start_unter_sperre_kein_schritt`/`_zeuge` | no `start` step from a lock holder, instantiated. |

Limits, recorded and not overclaimed by the report: the two runs that go through `gabbro_ziel`
carry lock steps but no memory write (the writing runs are on `rufPF`, not an accepted unit); no
EXPORTED `.gab` with a `start` has `ZielF` derived in Lean — `faden-start-pool.gab` is compared
only through the Bool (`pruefe-akzeptiert-diff.py`, one of 22 compared programs).

## 5. The proofs of the new legs

* `fadenInv_schritt` — every constructor case read; the invariant (`schlaeft`, `joinFrei`,
  `joinLebt`, `kindLebt`, `rangSteigt`, `rangUhr`) is preserved by each step.
* `kein_warteZyklusF` — a lock edge never ends at a joiner (`joinFrei`), so a cycle is either all
  lock edges (the old `KeinWarteZyklus`) or all join edges (rank strictly climbs). Correct.
* `keine_verklemmungF` — highest waited-for lock argument for the lock case; for the all-joining
  case a rank chain bounded by the clock. Works for unboundedly many threads (no finiteness of
  `Faden` used). Correct.
* `fortschrittF_aus` — `FortschrittG` plus the `join` step / `JoinWartet`. Correct; the
  `JoinWartet` stop is honestly named as a stop, not a claim of liveness.

## 6. Findings, ranked

* **F1 (medium, OVERCLAIM — fixed).** The report said the (a) side for roots "is exactly what the
  Rust checker demands (`N458`, `N462`)", and OFFEN said "`N462` is `einzelnPoolB`". It is the
  model half: `N462` bounds touched carriers, `einzelnPoolB` written ones; `N458`'s
  parameter/result half is the exporter's; `N461` has no Bool counterpart. The measurement is one
  direction on one program. Report §2 and OFFEN corrected (commit `c7406624`). OFFEN's "the child
  is now IN THE GOAL" is qualified "at the MODEL level": no `child` program exports.
* **F2 (medium, missing named assumption — fixed).** Spawns never fail in the model, and a looping
  `start` needs unboundedly many slots. Added as (d)(3) and to NOT CLAIMED in `Spec.lean`
  (comments only; `lean-bau` green, 289 jobs).
* **F3 (low, informational).** `lean_g.rs` waives LG001 for EVERY `locks` effect of a body that
  contains a `start`, not only the ones lifted from its roots. Measured: an unrelated `locks M`
  (declared lock over its own table) on the lane's `faden-start-pool` starter is refused by Rust
  with exactly one error, `H011` ("`chef` declares `locks M` but never takes it"), and the
  exporter exports nothing with checker errors (`.tmp/probe/p3.gab`). Safe as it stands; a narrower waiver
  (effects of the roots' graphs only) would not depend on `H011`.
* **F4 (low, informational).** `GabbroZielVor`'s `PrueferVor.korrekt` ranges over all new units
  (§2.3); equivalent in substance to the old interface.
* **F5 (info).** Coverage of the thread machine by exported programs is thin (one `start` probe;
  no exported unit has `ZielF` derived in Lean). Not an overclaim — the report says what was
  measured — but it is where the next differential probes belong.

## 7. Safe to merge?

**Yes**, with this branch's review commits (`c7406624` text fixes, and this verdict). The goal
theorem is proved with standard axioms, the old statement is a proved corollary, no premise was
relaxed for an old unit, the added premises are satisfied on non-degenerate accepted witnesses,
and the only defects found were in prose. The merger re-measures the emission counters as usual;
this change touches no emission.
