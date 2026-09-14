# MUSE-REPORT-163: two guardians for the translation-validation plan

Lane 163, 2026-09-14. Both halves of the task are done, measured, and committed
green. No Lean code was added or changed (pure instrument + measurement lane);
no codes, gifts, or examples were reserved or touched.

## 1. Three states in `instrumente/pruefe-cformen.py`

`FORMS` rows are now classified by `form_state()` into (i) **lemma**, (ii) **named
assumption** (`NAMED_ASSUMPTIONS`), (iii) **without semantics**. Only state (iii)
outside the dated `KNOWN_UNCOVERED` list turns the guard red; assumption rows print
with counts every run (measured, not excused).

Assumption rows (each grep-verified against `grammatik/Grammatik/*.lean`):

| form | Lean premise(s) | basis |
|---|---|---|
| `stmt:asm` | `AxCorr` (`def`, CFormenH.lean) | stub bodies are inline asm by construction; the effect is the `AxCorr` premise of `scorr_axiomCall` / `bridge_syscallStub` (ErhaltungT4: "the kernel behind the stub is the named assumption") |
| `stmt:reg-load` | `hdev` (binder, `regLies_step`), `RegLokal` (`def`, ZielOrtGeraetSem.lean) | "the assumption at the register" linking the C device oracle to `O.regLies`; `RegLokal` is the hardware locality class |
| `expr:volatile` | `hdev`, `RegLokal` | same device read inside an expression |
| `stmt:reg-store` | `RegLokal` | a device write has no Gabbro trace (`regSchreib` returns `Unit`; `regSchreib_step` has no `hdev` analogue) -- the store side is the documented gap beside the named class |

`assumption_exists()` accepts a `theorem/def/lemma/abbrev` at line start OR a
premise binder `name :` (else every binder row would be permanently red -- a guard
crying wolf about its own table). `stmt:bind-call-foreign` stays state (iii): its
assumption shape (the `bindAxiom` analogue of `AxCorr`) does not exist (CFormenH
CUTS), and mapping it to `AxCorr` would claim a premise the closing theorem cannot
carry. `expr:call` stays (iii): the bucket is too broad for one premise.

Also in this file: `FRIST = 300` on the `emit` call (a miss counts as refused), and
one new classifier row `stmt:decl-ptr` (``T *p = e;`` -- `Platz * tz = SPEICHER;`
in 38-unveraenderlicher-zeiger.gab) with a dated 2026-09-14 `KNOWN_UNCOVERED`
entry. That statement was UNCLASSIFIED, i.e. the guard was RED before this lane
(verified by stashing my change and re-running: same RED, same statement).

Today's guardian numbers (101 emitted, 0 refused): 73 forms seen -- 48 lemma,
4 named assumption, 21 without semantics; occurrences 1797 / 187 / 367;
assumption occurrences: `stmt:asm` 93 in 7 programs, `expr:volatile` 56 in 12,
`stmt:reg-store` 22 in 8, `stmt:reg-load` 16 in 8. Verdict GREEN, exit 0.

## 2. Chain counter `instrumente/zaehle-kette.py` (new, executable)

Per tracked `beispiele/*.gab`: (a) Lean parse [pin only; `--lean` re-checks the pin
files through `./lean-probe`], (b) `gabbro lean-g` exit 0 + nonempty, (c)
`gabbro certificate` exit 0 + zero `REFUSED` lines, (d) C forms via the imported
`pruefe-cformen` table (single source of truth), (e) correspondence checked --
probed on both halves (CLI `corrcert` surface + Lean rechecker), 0 everywhere
until T2 exists, never guessed. Headline: programs passing ALL columns;
unmeasured counts as not passed. Counter semantics: exit 0 once it measured,
2 (`ABBRUCH`) when it measured nothing. Every `gabbro` call under `FRIST = 120`;
`selbsttest()` runs first in both directions (planted forms/states, planted
garbage, binder-verifies/absent-falls) and aborts with 2 when it falls.
`LC_ALL=C` on all child environments.

Booked in `messung/KETTE-2026-09-13.md`. Numbers (101 programs; `--lean` run):

* **CHAIN COUNT: 0 of 101.** Column (e) guarantees it; 104 reads `[YYYY0]`.
* (a) 1 (104 pin re-checked green), (b) 3 (104, 108, 118), (c) 14, (d) 57, (e) 0.
* Row patterns: `YYYY0` 1, `.YYY0` 2, `.FYY` 8, `.FYF` 3, `.FFY` 46, `.FFF` 41.
* The sieves are NOT nested: 11 of the 14 certificate-clean programs fail `lean-g`
  (`LG001` et al. refuse every surface form without a G counterpart -- the G
  fragment is the narrowest sieve after the missing T2); 46 programs emit only
  lemma/assumption-covered C yet fail both `lean-g` and `certificate`.

## Verification

* `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (149 jobs).` (no Lean files touched)
* `./cargo-pruef`: `== exit 0; failing tests: 0` (no Rust files touched)
* `pruefe-cformen.py`: GREEN (see numbers above)
* `pruefe-englisch.py`: `== ENGLISCH: 2 von 2228 Meldungen sind deutsch ==`, rc 0
* `pruefe-zahlen.py`: rc 0; `pruefe-waechter.py` static: rc 0
  (`pruefe-cformen.py FEHLT FRIST, SPRECHPROBE` predates this lane -- the FRIST
  half is fixed by this lane; `zaehle-kette.py` carries `selbsttest()` + FRIST)
* EMISSION MARK untouched: no `.gab` examples added, `pruefe-emission.sh` unreread.

## Open / remarks on the task

* Column (a) without `--lean` books "pin present, Lean not re-run" as not passed.
  That is the honest default (a `./lean-probe` per run would serialize the whole
  counter behind the Lean slot queue), but it means the daily number depends on a
  flag. If the merge wants one canonical invocation, make it `zaehle-kette.py
  --lean` and accept the queue wait.
* `stmt:reg-store -> RegLokal` is the thinnest mapping in the table (see gap note
  above). If stage (b) of the closing theorem names a distinct store premise
  (e.g. a profile device key), the row should name it instead.
* The three `KNOWN_UNCOVERED` entries unseen in this run (`stmt:break`,
  `stmt:store-deref`, `expr:byte-reader-other`) are pre-existing; removal is
  another lane's call.
* No Lean theorems were added, so rules 12-13 (target statements, `_zeuge`
  witnesses) have no object in this lane. New Python definitions:
  `form_state`, `assumption_exists`, `NAMED_ASSUMPTIONS` (pruefe-cformen.py);
  `selbsttest`, `pin_fuer`, `t2_vorhanden`, `rufe`, `umgebung` (zaehle-kette.py).
