# Verdict — the Spec diff of Opus lane O25c (the atomic rely IS the goal, OFFEN O25/O17)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-a2504cb87a2b94e0a`, head
`c675b235` (contains master `1800a7a3`; master has not moved since, so no merge was needed).
Report `messung/OPUS-O25C-ATOMICS.md`. Measured in the worktree through the queued wrappers only
(`./lean-bau`, `./lean-probe`, `./cargo-pruef`, `./emission-pruef`). Text fixes are committed
separately: the Spec header comment, the SATZKARTE number, and the §-references. No definition or
proof was touched. Nothing was merged into master, and nothing was pushed.*

## 0. Verdicts at a glance

| Question | Verdict |
|---|---|
| (1) Is anything of the old `GabbroZiel` lost for units the old checker accepts? | **No leg, premise or run is lost, with ONE semantic caveat, F1 (fixed in the text).** The bodies of `GabbroZielSC`/`GabbroZielVerbundSC` are **byte-identical** to `GabbroZiel`/`GabbroZielVerbund` at the merge base, compared by script (§1). Every other definition `Spec.lean` had is textually unchanged; only comments moved. `gabbro_ziel_sc_aus` and `gabbro_ziel_verbund_sc_aus` are real proofs. **F1:** `SchrittW` gained the field `rmw`, so the leg `schwach` in the verbatim text now quantifies over fewer W steps. The header's "VERBATIM" hid this, and now names it |
| (2) `NutzerPflichtA` ⇔ old duty on old-accepted units: proved? | **Proved, not assumed.** `logikPflichtA_iff_akzeptiert` = `⟨logikPflicht_of_A, logikPflichtA_of_frei (akzeptiert_liest_nicht_geteilt …)⟩`, and the `→` half holds on EVERY unit. `nutzerPflichtA_of_akzeptiert` is what `gabbro_ziel_sc_aus` uses |
| (3) Is the new admission sound? Can a contract, invariant, `folge` or handler leg depend on an atomic indirectly? | **Sound** (§3). An indirect dependency (a local copied from the atomic, a callee's `ensures` over that local, a table invariant fed by it) is exactly what the rely covers: the body obligation `execEndHA` must hold for EVERY value the read returns, and the legs are PROVED over GX runs (`zielX_aus`), where the read may return any value. `VertragsFrei` covers `requires`, `ensures` and `invOrteP` of every function. Lock invariants cannot see the atomic (`hTO`: unguarded ⇒ ∉ `S.orte`, and `SperrInvLokal`) |
| (4) Is `SchwachX` contentful? Are the `ZielFX` legs over GX runs, including spawn/join and handlers? | **Yes.** `n1_stale_x`/`n1_gx_nicht_g` give a real W stale read on an accepted unit: it is a GX step, it is no G step, and `ZielX` holds after it. `SchwachSC` is false there (`n1_schwachSC_falsch`). `FadenSchrittX` has GX in `lauf`, with `start`/`kind`/`join` word for word; `spawnSicht` and `fortschritt` are over `FadenSchrittX`; `keinKernHalt` is `KernHaltEA` over GA runs (⊇ GX, `gx_ga_lauf`), from `AkzeptiertSpecX.masken` |
| (5) Certificates | **Consistent.** 25 CERTIFIED rows = 25 imports in `Zertifikate.lean` = 25 modules. Every `gCheck` decides `akzeptiertX_pruefer.akzeptiert … = true` by `decide`, and `gP_gabbro_f` instantiates `gabbro_ziel` (the new statement). **The old meaning is kept, measured:** a probe decides the OLD checker `akzeptiert_pruefer` `= true` on all 24 certified units other than 162, and it is false on 162 (as `g162_alt_abgelehnt` pins). All 23 old units have `atomar` false or no global at all, so `nutzerPflichtA_ohne_atomar` applies. Note N1: the old-checker fact is not pinned in the build for the 23 |
| (6) Named assumptions / NOT CLAIMED | **Complete.** They name: contracts over a shared atomic (refused, `N484`); the plain payload after `awaits` (refused, P3, the O25 remainder); atomics shared across a link (`lok` unchanged, refused); the per-core merge discipline (O17); `exchange`/`awaits`/payloads/`accumulates`/atomic arrays not exported (register lines `LG001`/`LG002`/`LG004`); the counter's program side (a hypothesis, `ZaehltHoch`); and the RMW lowering as reading assumption (2). F2 (count) fixed |
| (7) Build and axioms | **Green.** `./lean-bau`: exit 0, 0 error lines, 354 jobs. `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for all 20 names probed (§6). No `sorry`, `admit`, `native_decide` or `axiom` among the added lines of `grammatik/` and `crates/`. `./cargo-pruef`: 1402 passed, 0 failed, 1 ignored. Emission and diff script: §6 |

**Verdict: SOUND** (F1 and F2 are text fixes and are committed. F3 is an instrument fix and is
committed. N1 and N2 are notes). The new
`GabbroZiel` is stronger than the old one on every unit of before, with one exception: the claim
of the `schwach` leg about W. That leg now rests on reading assumption (2), which names the RMW
lowering, and the emitter meets it (`atomic_fetch_*` / CAS loop, `emit.rs`).

## 1. (1) The statement of before, and what "verbatim" means

* **Text.** A script extracts the `Prop` bodies of `GabbroZiel` and `GabbroZielVerbund` at
  `master` (`1800a7a3`) and of `GabbroZielSC` and `GabbroZielVerbundSC` at the branch head.
  Both pairs are equal byte for byte. A line diff of the whole file shows no removed line
  outside comments and docstrings. So `Ziel`, `ZielF`, `Pruefer`, `AkzeptiertSpec`,
  `NutzerPflicht`, `SchwachSC`, `KernHaltE` and the rest keep their text. The O25b definitions
  (`GeteiltV`, `AkzeptiertSpecX`, `RennfreiBisGA`) moved into `Spec.lean` unchanged, apart from
  the `masken` field that the Opus H merge adds to `AkzeptiertSpecX`.
* **The derivation** (`gabbro_ziel_sc_aus`, read in full):
  * `C.alsX` keeps the Bool, and its soundness comes from `akzeptiertSpecX_of_spec` (every field
    is carried, `fussSX_of_fussS`);
  * `nutzerPflichtA_of_akzeptiert` gives the new (b);
  * `fadenErreichbarX_of` turns each G thread run into a GX run (`gx_aus_g`; `start`, `kind`
    and `join` are identical);
  * `geteiltV_leer` gives an empty `Tg`: an unguarded footprint carrier of an old-accepted unit
    is local by `sigB`/`lokW`, hence `GetrenntR` by `getrenntR_iff`;
  * `zielF_of_X` maps each leg: `schwach` via `gx_leer_g`, `rennfrei` via `rennfreiBis_of_GA`,
    `keinKernHalt` via `kernHaltE_of_EA`, `zeit` via `SegLauf.alsX`/`segZaehle_alsX`, and
    `sperrWechsel`/`sperrSicht` via `gx_aus_g`.

  The derivation is correct.
* **F1 (semantic caveat, fixed in the text).** `MaschineW.lean` adds the field
  `SchrittW.rmw : ∀ g, ExchangeKopf W.g u g → neu (.inr g) = (wahl (.inr g)).ts + 1`.
  * `SchwachSC` quantifies over `SchrittW` steps from `RufErreichbarW` states. The same text
    therefore now covers FEWER W steps. The old leg also said that a non-atomic RMW never left
    G on an accepted unit; the new text does not say that.
  * **Why it is acceptable.** The restriction removes only the lost update, which no C11
    execution of an `atomic_fetch_*`/CAS lowering has (RC11 atomicity). Reading assumption (2)
    now names that lowering, and `emit.rs` emits exactly those operations. W still contains G
    (`w_aus_g`, whose construction meets `rmw`).
  * **A detail the header did not say.** `ExchangeKopf` is not restricted to `atomic` globals.
    For an `exchange` of a lock-guarded plain global, the adjacency is justified by DRF and not
    by C11 RMW atomicity.
  * **The fix.** The header's "WHY NOTHING IS WEAKENED" called the statement of before
    "VERBATIM" without this; it now carries a short caveat paragraph (Spec comment only).

## 2. (2) The user's duty

`LogikPflichtA P S Q T` is `LogikPflicht` with `KoerperGutSA`/`InvGutSA`/`InvGutGrundA`. These
run `execEndHA` against every environment in `HavocA T`.

* `logikPflicht_of_A` holds for every `T`. The new duty is never weaker.
* `logikPflichtA_of_frei` needs `LiestNicht` (no body read in `T`), and
  `akzeptiert_liest_nicht_geteilt` supplies it from `AkzeptiertSpec`.
* `NutzerPflichtA` relies over `GeteiltA`, which is larger than the havocked `GeteiltV` (it
  includes shared atomics that a contract mentions). That makes the duty more demanding, never
  less sound. On such a unit (a) refuses anyway.
* `hP_rely_nicht` shows the strengthening bites: a body whose sequential triple holds fails the
  rely.

## 3. (3) Is the admission sound, including indirect dependencies?

* **What is admitted.** `GeteiltV P ws c` = `atomic` ∧ no guard lock ∧ ¬`GetrenntR` ∧
  `VertragsFrei` (no `requires`, `ensures` or owed-invariant place of ANY function mentions `c`).
* **The indirect routes asked about.**
  * *A local copied from the atomic, then used in an `ensures` or a callee's `requires`.* The
    rely demands the body triple for every value of the read, so the value reaches the contract
    only through the user's proof, which must hold for all values. The legs `vertrag`,
    `invRueck`, `invGrund` are proved over GX by `ziel_ort_atomar_voll`, which replays the
    user's proof with the recorded environment (the answer the weak memory gave).
  * *A table invariant fed by the atomic.* It is the same route. The invariant's places
    (`invOrteP`) cannot BE the atomic (`VertragsFrei`), and a value derived from it lands there
    only through a body that met the rely.
  * *A lock invariant.* `hTO` holds: a shared atomic is unguarded, so it is in no `S.orte L`
    (`sperrOrte ⇒ Bewacht`), and `SperrInvLokal` makes `S.inv L` depend on `S.orte L` only.
  * *`folge`.* It is proved over GX reachability (`folgeG_erreichbarX`). An atomic value can
    steer which call happens, and the leg is claimed for every such run.
  * *The handler leg.* `KernHaltEA` is over GA runs (every atomic answered arbitrarily), ⊇ GX.
  * *Time and progress.* `ZeitAbX` is over GX segments (a spin on an atomic is bounded by the
    budget, as before). `FortschrittG` names a stop or offers a G step, which is also a GX step.
* **Where the soundness really lives.** Every leg is a Lean theorem over `RufSchrittGX`, which
  lets the presented memory take ANY value at `Tg` (`∀ c, ¬ Tg c → TraegerGleich σ M.speicher c`,
  nothing at `Tg`). That over-approximates what W can answer, and `SchwachX` (proved) ties W to
  GX. A mismatch could only hide in `Tg` being too small. `SchwachX` is proved with exactly
  `Tg = GeteiltV`, so every W step of an accepted unit IS a GX step over it.

## 4. (4) `SchwachX` and the GX legs

* `SchwachX` has two parts: every W step from a W state over `M` is a GX step to the successor's
  G part, and the presented memory is G's outside `Tg`. The second part is the DRF content.
  With `Tg` empty it is `SchwachSC`.
* It is contentful: `n1_stale_x` is a W run on the accepted flag program `n1E` in which
  `hauptA` stores the initial `konfig` (0) after `kern` wrote 3. `g_schritt_0` says every G step
  there stores 3. So the step is GX and not G (`n1_gx_nicht_g`), and `ZielX` holds after it.
  `n1E_gabbro` applies `gabbro_ziel` itself with `n1E_nutzerPflichtA` (a theorem) and the real
  runtime start (`laufzeit_voll`).
* Thread machine: `FadenSchrittX.lauf` uses `RufSchrittGX`, and `start`/`kind`/`join` are
  FadenMaschine's. `ZielFX.spawnSicht`, `fortschritt` (`FortschrittFX`), `keineVerklemmung` and
  `keinZyklus` are stated over it.

## 5. (5) Certificates and REGISTER

* `REGISTER.txt`: 204 accepted, 25 CERTIFIED, 179 UNCERTIFIED; 25 imports; `cargo test --test
  zertifikate` green inside `./cargo-pruef`, so the register is byte-exact with the tree.
* 162 is refused by the old checker (`g162_alt_abgelehnt`, `decide`) and accepted by the new one
  (`gCheck`). It is the one certified program that exercises the rely.
* **N2 (note).** 116 has no `concurrent` block. The old checker ACCEPTS its exported unit
  (measured, §6). It is certified because the exporter now carries `atomic` items, not because
  of the rely.
* The 23 old certificates: `gCheck` now decides `AkzeptiertX`, and the closing theorems state
  `ZielFX`/`ZielX` over GX with `NutzerPflichtA` as the hypothesis. For all 23 the declaration
  has no atomic global, so (b) is the duty of before (`nutzerPflichtA_ohne_atomar`) and GX is G.
  The old checker still decides true on all of them (probe, §6), so `gabbro_ziel_sc` still
  applies with the Bool of before.
* **N1 (note).** That last fact is a review measurement, not a build fact. A one-line
  `gCheckSC` per certificate would pin it; left to the merger, because it is exporter output.
* Many UNCERTIFIED reasons changed wording: atomics now pass, and the first refusal moved to a
  later construct. That is expected; no program changed CERTIFIED/UNCERTIFIED status except
  116 and 162.

## 5b. F3: the differential test measured the Bool of before (instrument, fixed)

`instrumente/pruefe-akzeptiert-diff.py` still compared the Rust verdict with `Akzeptiert`
(footprint `fussWB`). The goal's checker is now `AkzeptiertX`. The script therefore went RED on
the branch: it reported 162 and `messung/proben/o25-flagge-atomar.gab` as "Lean refuses at
`fuss`". That is a finding in the wrong register: the Rust checker agrees with the Bool the goal
theorem actually quantifies over.

The report does not claim the script was run for this lane. The fix, committed separately:
* the `fuss` component is `Zielsatz.fussWXB`, and the whole-Bool line is
  `Zielsatz.AkzeptiertX`;
* the probe imports `Zielsatz.AtomarAkzeptiert`;
* the probe renames the export's namespace in its own copy. The new import brings
  `Export104.lean` along, whose `G104_referenz` collided with the export of 104.

After the fix: `compared=27`, `findings=0`, and `--selbsttest` is green in both directions.

## 6. Build evidence (this review)

| Measurement | Result |
|---|---|
| `./lean-bau` at `c675b235` | exit 0, 0 error lines, 354 jobs |
| `./lean-probe` `#print axioms` | `gabbro_ziel`, `gabbro_ziel_sc`, `gabbro_ziel_sc_aus`, `gabbro_ziel_verbund`, `gabbro_ziel_verbund_sc`, `gabbro_ziel_verbund_sc_aus`, `logikPflichtA_iff_akzeptiert`, `nutzerPflichtA_of_akzeptiert`, `zielF_of_X`, `geteiltV_leer`, `n1E_gabbro`, `n1_stale_x`, `n1_gx_nicht_g`, `g162_alt_abgelehnt`, G162 `gCheck`/`gP_gabbro_f`, G116 `gCheck`/`gP_gabbro_f`, `w_kein_verlust`, `w_zaehler_zwei`: all `[propext, Classical.choice, Quot.sound]`; `example : GabbroZielSC := gabbro_ziel_sc_aus gabbro_ziel` checks |
| old-checker probe (`akzeptiert_pruefer.akzeptiert gE … = true := by decide` on all 25 certified units) | true on 24; false on 162 only |
| `./cargo-pruef` | exit 0; 1402 passed, 0 failed, 1 ignored |
| `./emission-pruef` | exit 1, cut at stage 9: `312 von 312 emittierenden Dateien uebersetzen`, then `FUND: 139 statt 138 emittierende Dateien in beispiele/` -- the MARKE counter lags the new example 162 (measured 139; not edited, the merger re-measures). Stage 10 NOT measured behind the cut; ASan stage 6b not run on this machine |
| `pruefe-akzeptiert-diff.py` | as found: exit 1, `findings=2` (162 and `o25-flagge-atomar`, `lean-refuses@fuss,gesamt`) -- **F3**; after the fix: exit 0, `compared=27 skip=199 findings=0`, `fuss` true on 27/27, `masken` true on 27/27 |
| `pruefe-akzeptiert-diff.py --selbsttest` | exit 0, `SELBSTTEST: ok (both directions)`, before and after the fix |
| `./lean-bau` after the text fixes | exit 0, 0 error lines, 354 jobs |

## 7. Part 2 (merge preparation)

Master moved during the review to `c81488d4` (Opus I: the bare-metal thread runtime). It was
merged in as `6b26ca8d`. The merge was clean and automatic: AGENTS, TODO, OFFEN and the `Spec.lean`
header, where Opus I's block is comment only. Master brought no exporter and no Lean-definition
change, so the certificates were not regenerated. The register test inside `cargo test` stays
green.

One collision remained from the in-branch merge of Opus H. SATZKARTE had two `## 57.`, and
O25c's stood AFTER the end-of-file note. O25c's section is now **§58**, placed before the note,
and the note records it. The references in TODO, OFFEN and the report now say §58.

**After the merge:**

| Measurement | Result |
|---|---|
| `./lean-bau` | exit 0, 0 error lines, 354 jobs |
| `./cargo-pruef` | exit 0; 1404 passed, 0 failed, 1 ignored |
| `./emission-pruef` | exit 1 at stage 9, the MARKE count only: `312 von 312` translate, `FUND: 139 statt 138 emittierende Dateien in beispiele/` (example 162). Reported, not edited; the merger re-measures the counter. Stage 10 and later NOT measured behind the cut |

With that, the branch is ready for `opus-merge.sh`. Nothing was merged into master, and nothing
was pushed.
