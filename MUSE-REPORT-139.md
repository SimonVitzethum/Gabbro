# MUSE-REPORT-139 (lane 139: TRANSFER -- align `kosten.rs` with the Lean time bound)

Branch: `muse/139`. No `.lean` file touched, none added (`grammatik/` byte-identical;
`./lean-bau` green, 89 jobs, untouched tree).

## What was done

`KostenG.lean` §11 lists findings F1-F9 comparing the Lean step bound (`kostenStmt`,
`kosten_passt_deklaration`, hand mirror `kostenK`) against `crates/gabbro-check/src/kosten.rs`.
This lane carries the Rust side of that comparison:

**Fixed in `kosten.rs` (F1, F4, F5, F6 + the Rust half of F2):**

1. **F1 -- `StmtArt::Zuweisung` now counts its target place** (`anweisung`, `kosten.rs`):
   `1 + wert + sum(ausdruck(ix) for ix in ausdruecke_im_ort(ziel))`, i.e. what the load
   side has counted since the 2026-09-02 repair. Compound forms (`+=`, `-=`, `&=`, `|=`,
   `ZuwOp::*` except `Setzt`) additionally count the load and the arithmetic (`+2`):
   the emitter lowers them to read-compute-write. Gift probes `920` (store index,
   body 1 -> 101) and `921` (`+=`, body 3 -> 5).
2. **F4 -- `LetSonst` over a place counts the register's `requires`** (new
   `Rechner::registerlesung`): `1 + pred_kosten(requires)` where the place resolves to a
   device register carrying `requires` (`R010`/`R011`, «B26»). Resolution reuses
   `m3::geraetetabelle` + `m3::griffe_von` + `m3::ort_register` (no second register, W7);
   for that `RegInfo` grew the field `versprechen: Option<Pred>` (`m3.rs`, cloned from
   `RegDecl.requires`). `pred_kosten` never returns `Unbekannt`, so this adds no `K003`.
   Gift probe `922` (body 3 -> 5). Runtime-honest: `emit.rs::fehlbare_lesung` emits
   `if (!(pred))` per read.
3. **F5 -- `Narrow` reads its subject**: `1 + (1 + indices) + max(0, sonst)`, i.e. what
   `kostenExpr` counts over the subject. Gift probe `923` (body 1 -> 102).
4. **F6 -- `Traverse` charges `(body + invariant) x bound`**: the invariant (`Option<Pred>`,
   via `pred_kosten` in the loop-variable scope) joins every pass, as `kostenStmt` counts
   it. Gift probe `924` (body 14 -> 34). Note: the invariant is GHOST in the emitted C
   (verified: no runtime check); counting it is alignment over-count in the safe direction.
5. **F2 (Rust half) -- one pass is body PLUS `until` PLUS invariant**: `schleifenzusagen`
   (`K006`/`K007`) now checks `block(rumpf) + bis + invariante` against the promise
   (before: body only), and `durchgangskosten` (the emitter's trip-count numerator,
   `floor(N/pass)`) counts the same three, so checker and emitter divide the same pass.
   Before, the two sides measured different passes. `durchgangskosten` additionally takes
   `&FnDecl` (for the device-handle map); `emit.rs::sammle_retry` threads it through.
   New unit test `k006_haelt_den_until_dagegen` (one pass 101: silent before, `K006` after).

**Verdicts (F2/F7) and report-only (F3/F8/F9):**

- **F2 -- the CHECKER is right.** `bounded N ops` is an operations budget (rechenwerk test
  `retry_teilt_das_budget…`, `emit.rs::retry_schranken`: trips = `floor(N/pass)`, `C001`
  when the pass cost is unknown). Charging `N` with a one-pass check is sound *given the
  lowering enforces it* -- which it does. The Lean `retry n` models the LOWERED loop
  (n passes), not the surface budget; `kostenK` rightly excludes `retry` from `spiegelS`.
  Fixed on the Rust side only the one-pass/bis mismatch above. The `on_exceeded` block
  needs no charge in the caller frame (it diverges under its own `costs`).
- **F7 -- the CHECKER is right, the LEAN check is not.** SYNTAX.md: under `decreases`,
  `costs` is the promise of ONE pass and the depth stands in the measure (`K008`/`K009`
  check the necessary shape; THAT it falls is the prover's, outcome `logik (abstieg f)`).
  Charging `decl` for in-cycle calls (as `kostenPasst` does) makes every correct recursive
  function unsatisfiable -- measured 2026-08-19 (`K001` fell on all of them, which is why
  nobody wrote one). No Rust change. Proposal for a Lean lane: a `decreases`-aware
  `kostenPasst` variant costing 0 for in-cycle callees plus the separate measure argument.
- **F3 -- no change.** `forever` contributes `Unbekannt` to `costs` (`K003` fires on any
  `costs`-promising body containing one): a refusal, not an under-count. Lean bounds by
  the machine budget `passes`, which the surface names nowhere.
- **F8 -- no change.** Both sides need a type-level number; `kosten.rs` reads `costs` off
  the pointer type («B8»), the Lean signature has no cost field so `rufeS` excludes
  indirect calls. Checker-side rule stands; Lean gap stands.
- **F9 -- no change, safe direction.** `kosten.rs` folds constants to 0, `kostenExpr`
  counts operators; the hand mirror uses `kostenExpr`, so mirror >= real checker and
  `Lean <= checker + zusatz` keeps holding. Mirror imprecision, not a soundness gap.

**Deliberately NOT used:** codes 250-254 (no new refusal was needed -- tighter counts
surface as the existing `K001`/`K002`/`K006`; the unused range stays free), and no new
`M`-mutations (the five gift probes pin the refusals; the counting itself is covered by
exact-number unit tests).

## Corpus measurement (before -> after, `gabbro kosten` over `beispiele/*.gab`)

12 of the corpus files no longer fit their declared numbers (13 `K001` + 1 `K002`);
every one re-measured and re-promised with a dated note, none weakened:

| file :: fn | before | after | cause |
|---|---|---|---|
| 01 :: `einsammeln` | 831488 | **839680** | F6 (+inv/pass over the table) |
| 04 :: `faellige_wecken` | `NFAEDEN*5` | **`NFAEDEN*6`** | F1 (store index) |
| 10 :: `rechte_setzen` (+ `held KAPPEN`) | 2 / 2 | **3 / 3** | F1 |
| 12 :: `vorruecken` | 2 | **3** | F1 (`+=`) |
| 19 :: `aktive_zaehlen` | 50 | **130** | F1 (`+=`, +2/pass) + F6 (+3/pass ghost inv); `aktive_loeschen` 48 -> 64, fits exactly |
| 25 :: `byte_legen` | 2 | **3** | F1 |
| 26 :: `nur_endlich` | 3 | **4** | F5 |
| 27 :: `freigeben` | 5 | **6** | F1 |
| 37 :: `quadriere` | 6 | **7** | F1 |
| 52 :: `ablegen` | 2 | **3** | F1 |
| 57 :: `alle_anhalten` | 600 | **640** | F1 (128 slots x (4+1)) |
| 58 :: `freigeben_narrow` / `freigeben_if` | 8 / 9 | **10 / 10** | F1+F5 / F1 (the documented narrow-vs-if gap is now measured equal) |

Measurement probes outside `beispiele/` moved the same way (promises re-measured, prose
updated): `messung/fragmente/F04.gab::publish` 9 -> 10 (+ the frozen excerpt in
`dokumente/FRAGMENTE.md` moves with it -- excerpt and working file are byte-compared by
stage 4c), `messung/netz/udp-echo.gab::summe_1071` 64 -> 92,
`messung/proben/emission-141/*schreiben::schreib_dynamisch*` 4 -> 5 (lane-141 file,
re-measured by 139, verdicts untouched),
`messung/proben/probe-suchschleife-passfach::kostenprobe` 64 -> 130 (boundary table
re-measured: 16-slot 129 refused/130 accepted, 32-slot 257/258; "four ops per element"
is now eight). Numbers recorded without promise changes (refusals stand):
`probe-schleifenzusage-schatten` 1536 -> 2560, `probe-domaenenschatten` 195 -> 325
(197 at the rechenwerk probe). `fnptr-proben/p1,p6,p8` keep other errors; untouched.

Conventions noticed while measuring (for the next lane, not findings against anyone):
bare-local index/subject reads cost 1 in `kosten.rs` (`ausdruck` over `Ort`) where
`kostenExpr` costs a bare variable 0 -- checker >= Lean on indices, same convention the
09-02 repair set for loads, upper bound preserved. `held 2 -> 3` (10) moves a LATENCY
statement, not just bookkeeping -- the block really holds the lock 3 ops. `Publish`
has the same target-index blindness as F1 on both sides (Lean `publish` = `1 + e`,
checker = `1 + e`): agreed under-count, reported, not touched. `LetSonst`-over-place
indices (non-register) likewise: F4 counts the predicate only.

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (intermediate: 7 failures, all
  re-measured fixtures -- `jedes_beispiel_geht_sauber_durch`, 5 `rechenwerk`, 1 `tutorial`).
- New tests, run individually: `kosten_zaehlt_was_die_lean_schranke_zaehlt`,
  `k006_haelt_den_until_dagegen` (both `ok`); `jedes_gift_faellt_mit_seinem_code` `ok`
  (623 gift files incl. 920-924).
- `./emission-pruef`: `== exit 0` / `EMISSION: ALL PASS -- 35 durchgestochen, 230 von 230
  uebersetzen, 2 umgekehrte Probe(n)` (full log `.tmp/emission.log`, 439 lines). On the way:
  stage 4c (F04 excerpt re-synced) and the stage-9 ratchet (4 files had left emission --
  F04 `publish` 9 -> 10, udp-echo `summe_1071` 64 -> 92 + knock-on `kopfsumme` 88 -> 109,
  emission-141 `schreib_dynamisch` 4 -> 5, suchschleife `kostenprobe` 64 -> 130).
- `./lean-bau`: `== 0 error line(s) in the COMPLETE output`, `Build completed successfully
  (89 jobs)` -- `grammatik/` untouched.
- Guardians: `pruefe-kennungen` ALL PASS (358 codes, no new code), `pruefe-saetze`
  (144 sentences, exit 0), `pruefe-todo` (same 9 pre-existing findings as baseline),
  `pruefe-zahlen` (exit 0), `pruefe-englisch` (exit 0), `pruefe-konstrukte` (0 without
  probe), `pruefe-vergabe` (unchanged).
- Counts: `beispiele/gift/*.gab` 618 -> 623 (README + DONE strike-through updated).

## What remains open

- Lean side of F2/F7 (decreases-aware `kostenPasst`, trip-count model for `retry n`
  vs surface `bounded N`) -- a Lean lane's work; the Rust numbers are ready for it.
- `Publish` target indices + `LetSonst`-over-place indices: agreed under-count on both
  sides (see above).
- The `aktive_loeschen` 64/64 and `rechte_setzen` 3/3 promises now stand at zero slack;
  the next counting change touches them first.
- `probe-rekursion-in-retry.gab` carries a retry WITH invariant: `durchgangskosten`
  now divides by body+until+invariant, so its emitted trip count shrinks (conservative,
  still sound). No corpus retry carries an invariant; no emission stage covers that file.

## What I believe is wrong in the task

Nothing load-bearing. Two notes: (1) "a program whose declared costs no longer suffice
is a finding to report, not to paper over" -- read strictly, this forbids the only
action that keeps `./cargo-pruef` green (`jedes_beispiel_geht_sauber_durch` demands zero
errors over `beispiele/`). I read it as "report, don't hide": all 12+4 re-measurements
are booked above with before/after numbers and dated notes in the files. (2) F6 as
stated counts ghost work (the invariant emits nothing) into an OPERATIONS budget --
defensible only as Lean alignment, and the report says so at every promise it moves.

Co-Authored-By: muse-agent-139 <muse-agent-139@noreply.invalid>
