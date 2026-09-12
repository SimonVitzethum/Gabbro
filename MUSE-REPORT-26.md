# MUSE-REPORT-26: read-only audit of Geraet/Budget/Fristlauf/Unterbrechung/Terminierung/Zeugnis/Erhaltung

Lane 26. No existing file modified (`git status` shows only new files under
`messung/muse-audit/26/` plus this report). All demonstrations checked with
`./lean-probe` (exit 0, `#print axioms` output captured per file).

## Method

Read all seven files in full (Geraet 833 lines, Budget 721, Fristlauf 475,
Unterbrechung 306, Terminierung 260, Zeugnis 1685, Erhaltung 937). For each
theorem/definition asked: is the conclusion a premise under another name (a)?
is a premise unused / `Prop`-typed / a restated field (b)? does a definition
make a predicate trivially true/false for ordinary programs (c)? does prose
claim more than the Lean states (d)? are premises false for ordinary programs,
making the theorem vacuous (e)?

## Findings table

| # | file:line | pattern | one-sentence evidence | demo file | status | severity |
|---|-----------|---------|----------------------|-----------|--------|----------|
| F1 | Erhaltung.lean:729 (`kosten_produktion_frei`) | b,c | `costKept` is `carrier=.cerCo -> ...`, so under production it holds vacuously -- even with diverging counts 4 vs 9 | messung/muse-audit/26/F1_KostenProduktionFrei.lean | VERIFIED | medium (header admits "claims NOTHING"; but the name reads like a result) |
| F2 | Erhaltung.lean:555 (`geschlossen_immer`) + 460 (`ruledB`) | c | closure holds for EVERY cert because `ruledB_voll` tables all 19 named forms and the `.luecke` arm of `ruledB` is constantly `false`; census forms are outside the predicate | messung/muse-audit/26/F2_GeschlossenImmer.lean | VERIFIED | medium |
| F3 | Erhaltung.lean:615 (`korrespondenz_leer`) | c | all four conjuncts quantify over empty lists, so the empty cert "corresponds" -- checked vs nothing-happened indistinguishable | messung/muse-audit/26/F3_KorrespondenzLeer.lean | VERIFIED | low (header says "vacuously") |
| F4 | Erhaltung.lean:38-43 header vs 806 (`tafel_geschlossen`) | d | header still cites `tafel_nicht_geschlossen` (no longer exists) and says the contract "does not hold today"; Lean proves `satz_tafel` by `decide` | messung/muse-audit/26/F4_TafelHeader.lean | VERIFIED | medium (stale prose inverts the current truth) |
| F5 | Geraet.lean:690 (`tuerklingel_ohne_wettlauf`) | b | premise `_hr : TuerklingelRueckgabe` (underscore-named) is never read -- only `hdm : d' = m` travels; same conclusion provable with no bell at all | messung/muse-audit/26/F5_TuerklingelBell.lean | VERIFIED | medium (dead premise in a "race-freedom at the bells" theorem) |
| F6 | Geraet.lean:768-826 (`SeamPublish`/`SeamAwait`/`SeamPair`) | a | the seam layer repacks `GeraetWache` field-for-field (`SeamPair.wache` both ways); `seam_pair_ordered` = `fenster_ende`, `seam_pair_race_free` = `geraet_ohne_wettlauf` | messung/muse-audit/26/F6_SeamRepack.lean | VERIFIED | low (renaming, honestly proved; looks like a new result, is a view) |
| F7 | Unterbrechung.lean:103,120 (`handler_wettlauf_frei[_global]`) | b | `K : Korngrenze` bound as `have _ :=` (discarded), `hH : H f \/ H g` eliminated without use -- conclusion is `kein_wettlauf` alone for any threads | messung/muse-audit/26/F7_HandlerPremise.lean | VERIFIED | high (the file's "sentence" -- handler-ness plays no role; real handler content lives in `handler_nach_freigabe`/`maske_schliesst_handler_aus`) |
| F8 | Terminierung.lean:180 (`retry_beschraenkt_antwortet`) | a,c,d | `∃ o, ... = o` by `⟨_, rfl⟩` -- totality of a total function; `none` (out of fuel) satisfies it, so "cannot hang" overclaims | messung/muse-audit/26/F8_RetryAntwortet.lean | VERIFIED | medium |
| F9 | Terminierung.lean:155-175 (three instances) | a | `traverse_fallend/verbrauchend/rekursion_mass_terminiert` are `mass_faellt_schranke` with renamed binders; the falling premise (writer's logic, C2) assumed in each | messung/muse-audit/26/F9_DreiSchranken.lean | VERIFIED | low (header honest: "honestly the same argument") |
| F10 | Fristlauf.lean:395 (`sampling_closes_frist`) | a,e | `hspace : d + S <= lauf` directly contradicts the miss arm `lauf < d + S` (`Nat.not_lt.mpr`); detection burden sits in premise arithmetic, not sampling | messung/muse-audit/26/F10_SpacingMiss.lean | VERIFIED | medium (file books spacing as residual premise, but the theorem then proves little beyond it) |
| F11 | Zeugnis.lean:313 (`zeugnis_sound` concl. shape) | c | conclusion `∃ _ : Expr ..., True` is `Nonempty` of the judgment -- appealable, not computable-with; file explicit ("An ∃, not the term itself") | messung/muse-audit/26/F11_ZeugnisExists.lean | VERIFIED | low (documented witness-pair shape) |
| F12 | Budget.lean:681 (`modell_erhaltung`) | a | conjunction of `zeugnis_sound` (meaning, reused) and `senkKosten_unter_schranke` (count, needs no validity: `1 <= 17`); no meaning-count interaction proved | messung/muse-audit/26/F12_ModellErhaltung.lean | VERIFIED | medium (header "preservation" overclaims a conjunction of two independent legs) |

Zero UNVERIFIED findings: every row has a `./lean-probe`-green demo.

## What I checked and cleared (no finding)

- Geraet.lean `geraet_ohne_wettlauf`, chain theorems, `dma_uebergabe`/`kette_uebergabe`: `haussen` and `hinhalt` both used; `dma_inhalt` as `axiom ... -> Prop` (not `Prop` itself) is the goal-conform named-assumption shape. `ketteWachen_*` DO use `Ws` (membership in `KetteUeberWachen` is load-bearing for nonempty chains) -- an early suspicion of (b) was refuted by attempting the `Ws = []` instantiation, which fails.
- Geraet.lean `fenster_ende`, `glied_kante`, doorbell lemmas (except F5): premises read.
- Unterbrechung.lean `handler_nach_freigabe`, `maske_schliesst_handler_aus`, `versand_gibt_maskenordnung`, `ebenenplan_gibt_versand`: premises used; `EbenenOrdnung`/`MaskenEbene` are honest 0/1 shapes.
- Budget.lean `runOps_*`/`runPasses_*`/`per_pass_respected`/`seqPasses_*`: genuine accounting proofs; `held/bounded_respected_gilt` honestly reuse the umbrella (documented as shapes).
- Fristlauf.lean decision/exhaustiveness/grid/clock lemmas (except F10): `TickClock.mono/covers/window` proved from `advance`/`maxGap`; endpoint-coincidence `ok` is a stated convention, tested by `rfl` probes.
- Terminierung.lean `mass_faellt_terminiert`, `traverse_unbesucht_terminiert`, `endlos_schoepft_aus`, `forever_unbeschraenkt`, S005/S008/K009 witnesses: real content; S005/S008/K009 are correctly witness-shaped (existentials exhibiting checked-but-not-falling), not vacuity.
- Zeugnis.lean `intVonTyp_eq/ctxTyp_var/certRange` arms, `block_sound`, `cut3/cut4/block5_sound` with `Cut3Body/Cut4Ptr/Block5Args` supplies: supplies are `Type`-valued data (term/args carriers), not `Prop` premises; all validity hypotheses consumed by the inductions.
- Erhaltung.lean `vollB/ohneExtraB/geordnetB/geschlossenB_sound`, `korrespondenz_aus_vieren/sound`, `zeugenPaar_sound/c2Alle_decided`, `kosten_cerCo_gilt/gemessen_produktion/senkung_aus_schranke/kosten_satz_bauen`, `nachpruefer`/`tafelNeu` as declared drafts: sound; `c2Paar_gedeckt`'s `_h : p ∈ c2Paare` unused premise noted but trivial (membership check never needed since validity travels separately) -- not filed as a finding, borderline.
- No `sorry/admit/axiom/native_decide/unsafe` introduced by me; no `Prop`-typed premises found in the slice (`dma_inhalt`, `Cut3Body`, `Cut4Ptr`, `Block5Args` are all `Type`/predicate-valued, which is the conforming shape). No memory-changing "semantics" claimed in the slice (Budget/Fristlauf explicitly decline `Time`/linkage; the one world-fold-adjacent item, `GLauf.cpuAnteil`, is a projection, not a semantics).

## What I believe is wrong in the task

- The task says "add `import Grammatik.<Name>` at the end of `grammatik/Grammatik.lean`" and "put new Lean work in the NEW file named in your task" -- but a READ-ONLY AUDIT lane names no new file and forbids modifying existing files; I placed demos under `messung/muse-audit/26/` per the demonstration instruction instead, and did NOT touch `Grammatik.lean`. I also did not privilege rule 5 over the explicit read-only order.
- "Every premise of every theorem you add must be used by its proof" -- my F-demo theorems deliberately restate filed theorems (including their unused premises, e.g. F5's `_hr`) to DEMONSTRATE the finding; demanding all premises be used would forbid exhibiting an unused premise. I kept demos minimal and named the unused premise with underscore where the original does.

## Build record

- Baseline `./lean-bau` (before adding demos; demos live outside `grammatik/` and cannot affect it): `Build completed successfully (29 jobs).` (last line; full log shows only `#print axioms` info lines).
- `./lean-probe` per demo file: all 12 exit 0 after fixes (F2 needed qualified `EntscheidZiel.benannt/luecke`; F6's inverse had to be a `def`, not a `theorem`, since `SeamPair` is `Type`; F11's `Exists.fst/snd` projections do not exist -- used `obtain`).

## New definitions/theorems (all in messung/muse-audit/26/, audit-only, not part of Grammatik)

- F1: `audit26_kosten_produktion_frei_vacuous` (+ 2 examples)
- F2: `audit26_ruledB_luecke_arm` (+ 2 examples)
- F3: `audit26_korrespondenz_leer_vacuous` (+ 2 examples)
- F4: `audit26_tafel_geschlossen_holds`, `audit26_vertrag_braucht_tafel_holds`
- F5: `audit26_tuerklingel_bell_unused`, `audit26_tuerklingel_no_bell`
- F6: `audit26_seam_is_window`, `audit26_seam_ordered_is_fenster`, `audit26_window_is_seam` (def)
- F7: `audit26_handler_premise_discarded` (deliberately drops `H`/`K`; the unused-`H` linter warning IS the evidence)
- F8: `audit26_retry_answers_trivial` (+ 2 examples)
- F9: `audit26_fallend_is_schranke`, `audit26_verbrauchend_is_schranke`, `audit26_rekursion_is_schranke`
- F10: `audit26_spacing_kills_miss`, `audit26_closes_frist_shape`
- F11: `audit26_sound_is_nonempty`, `audit26_sound_true_vacuous`
- F12: `audit26_count_needs_no_validity`, `audit26_meaning_is_zeugnis`

## Open / recommended follow-ups

1. F7 is the highest-severity item: consider either deleting the handler disjunct from `handler_wettlauf_frei[_global]` (they ARE `kein_wettlauf`) or stating what handler-ness adds (masking-gated version). Read-only lane: not done here.
2. F4: refresh the Erhaltung.lean header (lines 38-43, 72-83): `tafel_nicht_geschlossen` is gone, `satz_tafel` is proved, C5's "0 open slots are proved debt" now points at nothing.
3. F5: drop `_hr` from `tuerklingel_ohne_wettlauf` or strengthen the statement to use the bell (e.g. readability of `r'`).
4. F8/F12: consider renaming to match the proved content (`retry_antwortet_reflexiv`, `modell_konjunktion`) or strengthening (name the exhaustion branch; link count to meaning).
