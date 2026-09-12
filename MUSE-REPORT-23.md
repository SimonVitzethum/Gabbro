# MUSE-REPORT-23 — Read-only audit of `grammatik/Grammatik/InterferenzAllgemein.lean`

Branch: `muse/23`. No existing file was modified (read-only audit);
new files only under `messung/muse-audit/23/`. This report is committed together
with the probe files.

Scope: the full file (2213 lines, §§1–23), read in full. Cross-checked against
`Interferenz.lean` (defs of `HaengtAb`/`Disjunkt`/`stabil`), `Satz.lean`
(`Rahmen`), `Wettlauf.lean` (`kein_wettlauf`, `HB`, `Gesittet`), and grep over
`grammatik/` for consumers of the audited names. Every finding below has a
checked Lean demonstration; probes were verified with `./lean-probe`
(no errors; only expected unused-variable linter warnings that CONFIRM the finding)
and `./lean-bau` stays green (`Build completed successfully (29 jobs)`).

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration file | status | severity |
|---|-----------|---------|----------------------|--------------------|--------|----------|
| F1 | InterferenzAllgemein.lean:426–431 | (a) conclusion repackaged premise | `invErhalt_aus_Kontext` proves `I.inv c vor ↔ I.inv c nach` as `⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩`: both directions ignore their argument; it is the conjunction "inv at vor AND inv at nach" (both from `hInv` at every chain world), not step preservation | `messung/muse-audit/23/F1_InvErhaltIgnoresArg.lean` (`audit_invErhalt_ignores_argument`) | VERIFIED | medium — every downstream user (`allgemeinStabil_invariant`, `interferenceFree_of_invariantForm`, `hinv` chain, F5) inherits "preservation" that is really "holds everywhere" |
| F2 | InterferenzAllgemein.lean:498–514 | (b) unused premises | `allgemeinStabil` takes `hInv : InvariantenKontext` and `hDeck : GeteiltGedeckt` but the proof never mentions them (docstring admits "carried, not consumed"); the identical conclusion proves without them | `messung/muse-audit/23/F2_HauptsatzNutztInvDeckNicht.lean` (`audit_allgemeinStabil_ohne_InvDeck`, `audit_allgemeinStabil_forget`) | VERIFIED | high — the "main theorem" conclusion depends on neither lock discipline nor invariant context; same erasure applies to `allgemeinStabil_invariant[_mitAusnahmen]` |
| F3 | InterferenzAllgemein.lean:178–253, 259–287 | (b)+(a)+(d) dead fields, wrapper theorems, unused defs | `GemeinsamerLauf.hPaar/.hGesittet/.hBeschraenkt/.l/.eintritt/.hEintritt/.hInvSicht/.abschnittWache/.ewig` occur in no proof in this file; `ewig_bleibt_faden` is `hE f hf`, `abschnitt_schritt_rahmen` is `J.hSchritt ...`; `AbschnittGedeckt`/`EwigGrenzeHaelt` appear in zero premise lists; `MehrphasenKoerper` feeds only an index inequality from two `abschnittWache` equations | `messung/muse-audit/23/F3_ToteFelderUndHuellsaetze.lean` | VERIFIED | medium — "N threads under lock discipline" is carried, not reasoned about; `hSchuld` is the only entry-discipline field actually consumed (`wache_aus_schuld`) |
| F4 | InterferenzAllgemein.lean:1809–1855 | (a)/(b) sidecar conjunction; "mover" is sequential composition | `serial_chain_from_run` concludes `observations ∧ ∃ j₁ j₂, HB …`: the HB half proves from `SerialLink`+`reduktion_seriell` alone, the observation half from the §21 package alone — the order never feeds the chain; `mover_nonwriter_past` proves `vor→mid→nach` transport-then-restore with no swapped world, no `g≠g'`, no writer frame | `messung/muse-audit/23/F4_ReduktionOhneKette.lean` (`audit_hb_sidecar_ohne_kette`, `audit_kette_ohne_run`, mover restatement) | VERIFIED | high — billed as "reduction/serialization" (§22 mission) but no serial schedule reaches any chain world; `reduktion_seriell` itself (HB order of two accesses) is NOT challenged |
| F5 | InterferenzAllgemein.lean:1502–1523, 1597–1624 | (b)+(d) dead `LockFrei` premise, overstating docstring | `hinv_aus_disziplin` is proved by `intro k σ h _` — the `LockFrei L σ` hypothesis is explicitly discarded, so "lock free implies invariant" is really "invariant at every chain world, unconditionally"; hence `interferenceFree_wo_frei`'s "WHERE THE LOCK IS FREE" restricts nothing | `messung/muse-audit/23/F5_LockFreiUngenutzt.lean` (`audit_hinv_ohne_frei`, `audit_hinv_forget_frei`, `wo_frei` without freedom) | VERIFIED | high — the CSL-exact claim (§21) does not hold at the statement level: lock-freedom plays no role |
| F6 | InterferenzAllgemein.lean:657–673 | (b)+(d) dummy propositions, "discharge" discharges nothing | `atomarAusgenommen_entlaedt`/`paarungAusgenommen_entlaedt` take arbitrary `S P : Prop` and conclude `… ∧ (S ∨ A ∨ P)` via the middle disjunct; instantiable with `False` — the lock side and the pairing side are never established | `messung/muse-audit/23/F6_AusnahmeEntlaedtNichts.lean` | VERIFIED | low — docstring admits "gleichgueltig was links/rechts stuende"; harmless as logic, misleading as "G4 discharge" |
| F7 | InterferenzAllgemein.lean:820–862 | (a) renamings of `Iff`/`kette_erhaelt` | `envErhalt_refl/symm/trans` are `rfl`/`Iff.symm`/`Iff.trans`; `kette_erhaelt_env`/`fadenEnv_kette_erhaelt`/`fadenEnv_letzte_erhaelt` are `kette_erhaelt` with `ρ` fixed; `envErhalt_aus_weltErhalt` assumes `∀ σ ρ, Q σ ρ ↔ P σ` ("Q ignores the environment") and concludes environment preservation — the premise IS the conclusion at two worlds | `messung/muse-audit/23/F7_EnvHuellen.lean` | VERIFIED | low — §17 honestly says "die eigene Belegung bleibt je Schritt fest"; the finding is that none of these lemmas reasons about environments |
| F8 | InterferenzAllgemein.lean:983–1018 | (a) right-disjunct-only bridge; dead `stabil` side | `interferenceFree_gives_hFremd` is `Or.inr (hFree …)` — the disjoint/`stabil` side of `allgemeinStabil`'s `hFremd` is never taken on the Owicki-Gries path, so `owickiGries_stabil` proves its conclusion with `I/hInv/hDeck/hAb` all erased (shown); `SeqTriple`/`SpecTriple` folds are construction (`and_congr`) | `messung/muse-audit/23/F8_OwickiGriesRechts.lean` (`audit_owickiGries_ohne_Ab`) | VERIFIED | medium — on its only path the theorem needs just `hSeq`+`hFree`+`hSchritt`-membership; frame-locality and discipline are dead left disjuncts |

Zero additional pattern-(c)/(e) verdicts are claimed: I did not prove any
premise false for ordinary programs (e), nor any predicate trivially
true/false by quantification (c) — the file's quantifier discipline
(`Q f` per thread at entry/return worlds, no `∀ ρ`/`∀ v` erasure) is intact,
and worlds do come from `welten` chains rather than value-free folds.
What I checked and cleared: all `SpecQ`/`InvariantForm`/`InterferenceFree`
statements quantify the contract at its place (no rule-4b violation found);
`stabil`/`stabilSchritt_gilt`/`fremdErhalt_disjunkt_aus_Disziplin` genuinely
consume `Rahmen` (memory-changing steps, no rule-4c violation);
`no sorry/admit/axiom/native_decide/unsafe` in the file (only `#print axioms`,
which report `[propext, Classical.choice, Quot.sound]`).

## What remains open (not in slice, or not provable from it)

- Whether `InvariantenKontext` (invariant at EVERY chain world) is satisfiable
  for ordinary critical sections: §21 claims section grain, but `hReturn`
  assumes re-establishment rather than deriving it from `exec`/`rufAt`, and
  `G3` (per-site held-set analysis) is still booked as remainder. F1+F5 show
  the consumers need the context *everywhere*, unconditionally.
- `hFremd`'s shared side for non-invariant `Q` (F2/F8): still owed per run
  (`R3`), i.e. the user proves interference freedom by hand exactly where it
  is hardest.
- The §22 remainder list is accurate (pairwise-only order, chain-vs-HB order
  possibly disagreeing, globals on the exception track); F4 adds that even the
  pairwise order never reaches a chain conclusion.
- F3's "never used" rests partly on grep (no `.hPaar`/`.hGesittet`/
  `.hBeschraenkt`/`.hEintritt`/`.hInvSicht`/`AbschnittGedeckt`/`EwigGrenzeHaelt`
  in any proof term of this file); other files (`Maschine.lean`,
  `MaschinenKette.lean`, `Ziel.lean`) DO construct and thread these fields,
  so the debt is local to this file's theorems, not global.

## What in the task I believe is wrong

- Nothing material. The pattern catalogue (a–e) fits the file well; every
  pattern except (c)/(e-as-false-premise) fired at least once. One caution:
  "a premise that is never used" (b) also fires on deliberate G5-style
  "carried, not consumed" bookkeeping (`hInv`/`hDeck` in F2, `S`/`P` in F6),
  where the file is honest in prose — the audit value is showing the
  *conclusion* does not depend on them, which the prose downplays.

## Build record

- `./lean-probe` on all 8 probe files: success, no errors. The only warnings
  are `linter.unusedVariables` on `hDeck` (F2), `hkn` (F4), `I` (F8) — each
  warning is itself evidence for the finding.
- `./lean-bau` last line: `Build completed successfully (29 jobs).`
- New definitions/theorems: `audit_invErhalt_ignores_argument` (F1);
  `audit_allgemeinStabil_ohne_InvDeck`, `audit_allgemeinStabil_forget` (F2);
  `audit_hb_sidecar_ohne_kette`, `audit_kette_ohne_run` (F4);
  `audit_hinv_ohne_frei`, `audit_hinv_forget_frei` (F5);
  `audit_owickiGries_ohne_Ab` (F8); F3/F6/F7 use `example`s over existing names.
  Each probe file ends with `CUTS:` + `#print axioms` as required.
