# THEOREM-MAP-C: goal-family premise map, re-measured 2026-09-12 (lane 97)

> **The C backend is removed (2026-10-18).** The Lean line for the C emitter (`grammatik/Grammatik/CBackend/`, the C correspondence chain `Korrespondenz/Kette/`, the C-certificate files, `korrOk`, `schlusssatz`, `SchablonenMetallSperre` over the C ticket lock, the C-layout half of `SchablonenT5Sem`) existed and lives in the tag `archiv/c-emitter-2026-10-17`. Sections marked "removed (C backend)" below are stubs; every other mention of the emitted C, `schlusssatz*`, `korrOk` or a deleted C file in a dated section is history, not present evidence. Moved, generic files keep their statements: `Korpus/` (was `Korrespondenz/`), `Parser/Elab/UebersetzePipeline.lean`, `Nebenlaeufigkeit/Sperren/Ressourceninvariante.lean` (was `CSLInvariante`), `Kern/Semantik/GanzzahlMatch.lean` (was `CFormMatch`), `Bausteine/Zeichenfolge/` (was `CBackend/Semantik/Zeichenfolge*`).

*Note (2026-10-17): the dated blocks below name measuring scripts; those marked "retired" were removed on 2026-10-17 (see git history, `git show 414feafc:instrumente/<name>`) and their figures are historical results. Only the four guardians run by `instrumente/abnahme.py` and `cargo test` measure today.*

Replaces the class column of THEOREM-MAP-A (§2) with the four binding classes:
(a) USER obligation, (b) HARDWARE assumption, (c) DISCHARGED by a merged
theorem (named), (d) STILL OPEN language duty. Covers every premise of every
theorem in the goal family (`grammatik/Grammatik/Kern/Syntax/Ziel.lean`: `ziel_nutzer_last`,
`ziel_seqLogic_aus_spec`, `ziel_seqLogic_aus_spec_invariantForm`,
`ziel_nutzer_last_aus_disziplin`, `ziel_nutzer_last_aus_maschine`,
`ziel_nutzer_last_aus_pc`, `ziel_nutzer_last_aus_pc_stabil`,
`ziel_nutzer_last_aus_pc_Q`) and of `csl_ressourceninvariante`
(`Ressourceninvariante.lean:305`), `EZD.eigenzustand_nur_eigene_schritteD_rep`
(`EigenZustandD.lean:1368`), `rufG_treu` (`RufMaschineG.lean:1198`).
All claims verified by reading the Lean sources cited as `file:line`.
Line numbers refer to the working tree on branch `muse/97`.

Prior maps are kept below unchanged: §§1-5 (draft A, lane 16) and §6
(wave-1 verdicts). §7 is the new classification table, §8 the next-lane
proposals for each (d) item, §9 the `#print axioms` record, §10 the
distance to the goal.

> §§7-10 are superseded by §11 (goal restated and proved over machine G, 2026-09-13); kept unchanged for history.
> **Status note, 2026-10-17.** The current goal theorem is **`gabbro_ziel`** (§58; proof file
> `Zielsatz/Atomar/BeweisAtomar.lean`, statement `Zielsatz/Kern/Spec.lean`), on exactly `propext`,
> `Classical.choice`, `Quot.sound`. `ziel_ort_ganz` (§13) is its ancestor, kept for the history of the
> premise tables. Lean paths in this file are relative to `grammatik/Grammatik/`; `file:line`
> references are as of the date of their section and are **not** re-measured (a moved line is a
> stale pointer, not a stale theorem; grep the name). Retired reports named below (`messung/OPUS-*`,
> `messung/muse/OPUS-BERICHT-*`, `messung/muse-audit/*` probe files) are gone from the tree; the verdict files (`messung/URTEIL-*`, `messung/review-*`, `dokumente/PROOF.md`) are summarised in the verdict table of `PROOF.md` and likewise leave the tree. The own/separation line of work is
> §74-§76 (`dokumente/A1-OWN-PAPER.md`).
> `OFFEN Oxx` ids are cited as they stood when their section was written; the live list is
> `TODO.md`, and an id that is no longer there is closed or moved, not forgotten.

## 7. Re-measured premise table (2026-09-12)

One row per premise of the flagship `ziel_nutzer_last_aus_pc_Q`
(`Ziel.lean:2330-2399`); the paragraph after the table books how the
seven older family members differ. "Discharged" names the exact merged
theorem that proves (or per-run constructs) the premise.

| Name | One-sentence meaning | Class | Discharging theorem or next lane |
|---|---|---|---|
| `hO : GutO O` | The oracle respects every axiom frame and never changes held locks or the trace (`Satz.lean:794`). | (b) HARDWARE, per-axiom instance (c) | `syscall_paarung` (`SyscallPaarung.lean:74`) discharges the per-syscall instance (`PaarGut`) from the kernel contract; `refO_gut` (`ReferenzB.lean:316`) is the fixture instance; event-emitting oracles stay (d) → D8 (lane 80 expected) |
| `h : PCReach …` | The machine is reachable by program-counter steps of the computed thread program. | (c) constructed per run | one-step lifters `pcSchritt_blatt_progAus_ohne_axiomCall` (`Ziel.lean:929`), `pcSchritt_blatt_progAus_axiomCall` (`Ziel.lean:1129`), `pcReach_blatt_progAus_axiomCall` (`Ziel.lean:1188`); per-step atom identity stays (d) → D1 |
| `hMSep : PCMarkSep …` | No mark code named by one thread's text is named by another's. | (d) checker text-check duty | → D2 (same-function threads still excluded, §5 B8) |
| `hCSep : PCUnsharedSep …` | Any carrier reached from two threads' texts is declared shared. | (d) checker text-check duty | → D2 |
| `hAbD` | Every carrier invariant reads only its witnessed footprint. | (a) USER | per-invariant obligation, none needed |
| `hFrameTD` / `hFrameGD` | Each footprint is a singleton frame. | (a) USER | per-invariant shape proof, none needed |
| `hGuardEx` | Every carrier has a guard lock in its watch list. | (d) STILL OPEN | → D3 (narrow to written shared carriers) |
| `hEntry` | Every carrier invariant holds at the chain head. | (a) USER | caller/sequential side, none needed |
| `hReturn` | Every writing chain step re-establishes every carrier invariant under the guard. | (a) USER, fragment (c) | `csl_ressourceninvariante` (`Ressourceninvariante.lean:305`) covers the quiescent (lock-free) reading; per-step restoration stays user-side |
| `hWatch` | Every writing chain step holds the guard lock. | (c) tables / (d) globals | tables via `wache_aus_schuld` (`InterferenzAllgemein.lean:1481`); globals → D6 |
| `hDeck : GeteiltGedeckt Nb J` | Any carrier written by two threads is shared with a common guard lock. | (a) USER discipline, fragment (c) | `kette_zwei_aus_lauf` (`KetteMehrfadenC.lean:766`) takes it as premise for the lock-only two-thread fragment; N-thread coverage → D4 |
| `hReqTAll` / `hReqGAll` / `hEnsTAll` / `hEnsGAll` | Every carrier read by `requires`/`ensures` lies in the function's write signature. | (d) checker footprint duty, folded (c) | folded into `hAb` by `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`); establishing the containment → D7 |
| `hForm : InvariantForm …` | Per thread, the contract conjunction coincides with some carrier invariant. | (a) USER | exhibit one carrier per thread; consumed by `interferenceFree_of_invariantForm` (`InterferenzAllgemein.lean:1213`) |
| `htr : PCSpur …` | The derivation fires exactly the thread sequence `tr`. | (c) DISCHARGED | `pcSpur_von_reach` (`Maschine.lean:3607`) |
| `hJw` / `hJsf` | Chain worlds / step threads equal the machine's. | (d) STILL OPEN, fragment (c) | `kette_zwei_aus_lauf` for two-thread lock-only; witnessed single-thread via `kette_aus_lauf_bezeugt_closed` (`Ziel.lean:2241`) and per-step via `kette_mit_zeugen` (`Ziel.lean:1713`); general wiring → D4 |
| `hSeedAll` | Per member thread, `QRequires` and `QEnsures` hold at the start world. | (a) USER caller side, repaired shape (c) | place-check repair `ReqAmEintritt`/`EnsAmRueck` (`VertragOrtB.lean:114/120`) with bridge `rufAt_ok_of_gates` (`:406`), call rule `hoare_call` (`HoareRuf.lean:57`), fidelity `rufF_treu` (`RufMaschineF.lean:633`) / `rufG_treu` (`RufMaschineG.lean:1198`); residual wiring → D11 |
| `hBlattAll` | Uniform per-firing preservation over every reachable intermediate machine. | (d) STILL OPEN, fragment (c) | nine memory-preserving leaves via `hBlattAll_speicherfest_aus_feuerung` (`Maschine.lean:4093`); writing leaves refuted (`BlattGegenbeispiel.lean:286`); Hoare rules (`HoareRegeln.lean`, `HoareRuf.lean`) give the per-statement repair; straight-line part → lane 84 expected (D5) |
| `hstart : c.tick 0 ≤ S` | The first clock tick is within one period. | (b) HARDWARE | per-clock fact, consumed by `TickClock.covers` |
| `hspace : deadlineSpacing S p d` | The use waits out the sampling window. | (b) HARDWARE | per-use premise, watchdog/granularity argument outside Lean |
| `hLowering : Absenkung` | A lowering witness with cap 18. | (c) DISCHARGED | measured witness `absenkung` (`Ziel.lean:97`) via `absenkung_haelt_schranke` (`:110`) |
| `hpd`/`hdl`, `hne`/`hw₁`/`hw₂` | Deadline strictly inside check-use; two exhibited accesses by distinct threads. | DATA | per-deadline / per-run witness selection |

How the seven older family members differ (all verified against the proof
terms in `Ziel.lean`):
`ziel_nutzer_last` additionally owes `hvoll`/`hvers` (per-thread `Brav`
provenance + interleaving: run DATA, closed per body by
`ziel_brav_aus_exec` (`Ziel.lean:207`) over `exec_spur` — (c) per body),
`hausschluss : ForeignExclusion` ((b) HARDWARE, `A_lock`), `hEin`/`hungeteilt`
as bare shapes ((d), discharged in the PC variant by `pc_discharge_einfaedig`
(`Maschine.lean:1619`) / `pc_discharge_unshared` (`:1704`)), `hLink` ((d),
gone from the machine variant on), `hInv` ((c) from the disziplin variant on,
via `invariantenKontext_aus_disziplin` (`InterferenzAllgemein.lean:1530`)),
`hSpec` ((a) USER triples; from the stabil variant on replaced by the
`stabil_aus_lauf` (`Maschine.lean:3879`) run premises `hMemAll`/`hSeedAll`/
`hBlattAll`, where `hMemAll` is premise-free at Q-instantiation by
`speicherVertrag_aus_Q` (`Extraktion.lean:3928`) — (c)), and `hFree` ((a) USER;
from the disziplin variant on derived inside by
`interferenceFree_of_invariantForm` from `hForm` for the invariant fragment —
(c); the non-invariant fragment still owes `hFree` — (d) → D9).
`ziel_seqLogic_aus_spec` / `..._invariantForm` are the two sequential-logic
legs (`hSpec`+`hFree` vs `hSpec`+`hForm`) with the same classes as above.

Three theorems outside `Ziel.lean`, every premise classified:
`csl_ressourceninvariante` (`Ressourceninvariante.lean:305-314`): `hO` (b);
`hGuard : Sum.inl L ∈ D.braucht t` program DATA (decidable declaration fact);
`hLokal` (a) USER locality; `hStart` (a) USER entry; `hRelease` (a) USER
release obligation; the concluded `PCReach`/`∀ g, L ∉ offen …` are run DATA.
`EZD.eigenzustand_nur_eigene_schritteD_rep` (`EigenZustandD.lean:1368-1388`):
`hO` (b); `hNurG` (other threads never name `t`) (d) checker text fact → D2
family; `hNoAx` (no oracle write of `t` on foreign steps) (d) → D12
(lane 80 expected); reachability + step are run DATA.
`rufG_treu` (`RufMaschineG.lean:1198-1203`): the only premise besides the
machine is the reachability derivation `h : RufErreichbarG …` (run DATA);
the return-fidelity conclusion is proved from the log invariant
(`rufErreichbarG_passt`, `rufLogPasstG_gedeckt`) — no user or hardware
obligation. Same shape for `rufF_treu` (`RufMaschineF.lean:633`).

## 8. Next lanes for each (d) item (fixed target proposals)

- **D1 (S12 atom identity).** Prove the counter points at the extracted atom
  for fired straight-line leaves.
  Target: `theorem pcAtom_aus_feuerung (P : Programm D) (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob) (f : Faden) (pc : PCStand) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ') : s.istBlatt = true → (Extraktion.progAus P fcode tabs globs f)[pc f]? = some (PCAtom.leaf Λ (Extraktion.stmtTraeger tabs globs s ++ Extraktion.stmtOrte s))` under an explicit scheduler hypothesis for the step. Witness on `refB_prog`.
- **D2 (checker separation/footprint facts).** Decide `PCMarkSep`/`PCUnsharedSep`
  and the `hNurG` shape per program by computation over `progAus`.
  Target: `theorem pcMarkSep_aus_verschiedenen_funktionen (P : Programm D) (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob) (code : D.Marke → Nat) : (∀ g₁ g₂, g₁ ≠ g₂ → fcode g₁ ≠ fcode g₂) → (∀ f (m : D.Marke), m ∈ markenDesKoerpers (P.rumpf (fcode f)) → code m ≠ 0) → PCMarkSep code (Extraktion.progAus P fcode tabs globs)` (same-function threads stay excluded until per-thread marks exist).
- **D3 (guard existence).** Narrow the discipline package to carriers that are
  written and shared.
  Target: `theorem invariantenKontext_aus_disziplin_bedarf (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D)) (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool) (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool) (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c)) (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t) (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x) (hGuardBedarf : ∀ c : D.Tab ⊕ D.Glob, (∃ g, g ∈ J.faeden ∧ TraegerSchreibt (J.code g) c = true) → ∃ L : D.Lock, Bewacht (D := D) c L) (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D), J.welten[0]? = some σ₀ → I.inv c σ₀) (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden) (vor nach : World D), Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach) (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden) (vor nach : World D), Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g)) : InvariantenKontext Nb J I`.
- **D4 (chain-machine wiring, N-thread).** Iterate the witnessed step
  (`kette_mit_zeugen`, `Ziel.lean:1713`) over a whole `PCReach` run.
  Target: `theorem kette_aus_lauf_voll_ohne_hlock (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand) (h : PCReach P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc) (t₀ : D.Tab) : ∃ Nb (J : GemeinsamerLauf (D := D) Nb), J.welten = M.welten ∧ ∃ tr, PCSpur P O passes (Extraktion.progAus P fcode tabs globs) (GenStart sp) M pc tr ∧ J.schrittFaden = tr` for the single shared-table lock fragment (globals stay excluded).
- **D5 (per-leaf preservation).** Replace the uniform `hBlattAll` by
  per-statement Hoare triples: straight-line leaves via lane 84 (adequacy of
  F), call leaves via `hoare_call` + `rufF_treu`, unfold leaves via the G
  adequacy to follow.
  Target: `theorem hBlattAll_aus_hoare_gerade (P : Programm D) (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : RespektiertVertraege P R) (g : Faden) (Pre Post : D.Fn → World D → Prop) (hPre : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ), s.istBlatt = true → s.istGerade = true → STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s (Pre (J.code g)) (Post (J.code g))) : …` (exact conclusion: the `hBlattAll` shape restricted to straight-line leaves; the writing-leaf refutation stays as the boundary).
- **D6 (global watches).** Checker-side discharge of `hWatch` for globals.
  Target: `theorem wache_global_aus_schuld (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (x : D.Glob) (L : D.Lock) : Sum.inl L ∈ D.gbraucht x → J.hSchuld → (global coverage) → (the `hWatch` conclusion for `.inr x`)` mirroring `wache_aus_schuld`.
- **D7 (footprint containment).** Decide `requires`/`ensures` footprint
  containment per function by computation.
  Target: `theorem vertragFuss_in_signatur (P : Programm D) (f : D.Fn) (t : D.Tab) : .inl t ∈ (P.requires f).orte → D.schreibt f t = true` from a decidable checker predicate over the contract syntax (one theorem per each of the four shapes).
- **D8 (event-emitting oracles).** Relax the `GutO` spur conjunct so DMA-like
  oracles are covered; lane 80 (GutO records oracle events) is expected to
  close this.
  Target: `theorem gutO_mit_orakelspur (O : Orakel D) (hO : GutOmitSpur O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) : Gut (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧ (O.wirkt a σ ρ).1.haelt = σ.haelt` (frame + lock preservation without spur equality; goodness of oracle events becomes a per-oracle proof obligation).
- **D9 (non-invariant fragment).** No lane yet: assertions over shared carriers
  not in invariant form still owe `hFree` per run. Smallest lane: a
  two-thread stability transfer for assertions that are stable under
  foreign steps holding the guard.
  Target: `theorem stabil_ohne_form_bewacht (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D)) (Q : Faden → World D → Prop) (hStabil : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D), g ∈ J.faeden → g ≠ f → J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach)) (σ : World D) (hletzte : J.welten.getLast? = some σ) (f : Faden) (hf : f ∈ J.faeden) : Q f σ` from per-thread head validity plus step stability (the per-run check stays user-side but no longer needs the full `InterferenceFree` shape).
- **D11 (contract place wiring).** Wire `EnsAmRueck` into the `hSeedAll`/
  `stabil_aus_lauf` head-validity shape so `Post`-at-entry is never asked.
  Target: `theorem seedAll_aus_ruf (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D) (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (g : Faden) (hf : g ∈ J.faeden) (rho : Env D (D.params (J.code g))) (hreq : ReqAmEintritt P (J.code g) (GenStart sp).start rho) : Extraktion.QRequires P (J.code g) ((GenStart sp).welten[0]?.getD default)` — i.e. entry-side requires from the gate; the ensures leg travels via `rueck_ohne_nachbedingung` at return, not at the head.
- **D12 (`hNoAx` consumption).** Lane 80 (own-state without remainder) is
  expected to close this: with oracle events recorded, foreign oracle writes
  of `t` are ruled out by the oracle frame instead of posited.
  Target: `theorem hNoAx_aus_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutOmitSpur O) (prog : PCProg D) (t : D.Tab) (M : GenMaschine D) (pc : PCStand) (h : Faden) … : (the `hNoAx` conclusion for `t`)` from `hO`'s frame clause plus the foreign-carrier program fact.

## 9. Axiom record (2026-09-12, probe `.tmp/sonde97.lean`, `./lean-probe` 0 errors)

Every theorem in the family and the three named theorems depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axiom:

- `ziel_nutzer_last`, `ziel_seqLogic_aus_spec`,
  `ziel_seqLogic_aus_spec_invariantForm`, `ziel_nutzer_last_aus_disziplin`,
  `ziel_nutzer_last_aus_maschine`, `ziel_nutzer_last_aus_pc`,
  `ziel_nutzer_last_aus_pc_stabil`, `ziel_nutzer_last_aus_pc_Q`,
  `csl_ressourceninvariante`, `EZD.eigenzustand_nur_eigene_schritteD_rep`,
  `rufG_treu` (and `rufF_treu` by the same proof shape): all
  `[propext, Classical.choice, Quot.sound]`.

## 10. Distance to the goal

(a) Count of (d) items: **11** (D1-D9 plus D11-D12). Of these, D2/D7 are pure checker-computation duties (decidable per
program, no new mathematics), D1/D4/D5/D11 are run/witness wiring with a
merged fragment each already closed, and D3/D6/D8/D9/D12 need new theorems.
(b) Wave-4 lanes running: lane 80 (GutO records oracle events + own-state
without remainder) is expected to close **D8** (the spur conjunct it relaxes
is exactly the D8 target's dropped conjunct) and **D12** (the `hNoAx`
remainder it consumes); lane 84 (adequacy of F for straight-line bodies) is
expected to close the straight-line half of **D5** and the straight-line
instances of **D1** (counter-at-atom for straight-line firings runs through
the same adequacy). Remaining after both: D2, D3, D4, D6, D7, D9, D11 and
the non-straight-line (call/unfold) half of D5.
(c) Narrowing carried, not counted as (d): C4 endpoints/absent deadlines,
C12 single-table two-access shape, same-function threads (§5 B8),
lock-free sharing (`hDeck` shape), lowering leg numeric-only (§5 B11).
(d) What the user proves at the flagship after §§7-8: their contracts at
their place (`hSeedAll` entry side, `EnsAmRueck` return side), their
invariants (`hEntry`/`hReturn`/`hAbD`/frames/`hForm`/`hLokal`/`hStart`/
`hRelease`), their per-leaf preservation for writing leaves (until D5
closes), plus the named hardware assumptions (`hO` oracle class, `hstart`/
`hspace`, `ForeignExclusion`, deadline `fortschritt`). Everything else is
carried by the theorems named in the (c) column.

---

Prior map follows (draft A §§1-5, wave-1 verdicts §6 — kept for history).

Draft A (lane 16). Independent draft; no Lean changes.
Target: `Gabbro.Grammatik.ziel_nutzer_last_aus_pc_Q`, `grammatik/Grammatik/Kern/Syntax/Ziel.lean:2324`.
All claims verified by reading the Lean sources cited as `file:line`.
Line numbers refer to the current working tree on branch `muse/16`.

Q-binder instantiation: `Pre := Extraktion.QRequires P`, `Post := Extraktion.QEnsures P`,
where `QRequires` (`grammatik/Grammatik/Kern/Syntax/Extraktion.lean:1437`) is `requires` as a world
predicate (holds for every parameter environment) and `QEnsures`
(`grammatik/Grammatik/Kern/Syntax/Extraktion.lean:1442`) is `ensures` as a world predicate
(for every return value and every parameter environment). The per-thread assertion is
`SpecQ Pre Post Nb J f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`
(`grammatik/Grammatik/Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean:1069`).

## 1. Conclusion: one sentence per conjunct

The conclusion (`Ziel.lean:2394-2416`) is a 12-way conjunction:

- **C1 (`Gesittet M.lauf`, :2394):** the generated machine run is disciplined
  (consistent, good observations, scheduler exclusion, single-thread marks, unshared separation).
- **C2 (consistency and goodness, :2395-2396):** every per-thread projected trace prefix is
  consistent, and every event observed in it is good.
- **C3 (stable contracts, :2397-2399):** at the last chain world, every member thread's
  contract conjunction (`QRequires ∧ QEnsures` for the function it runs) holds.
- **C4 (probe answers, :2400-2401):** some clock tick lands between the deadline and the use,
  and the deadline run answers the named hardware assumption `fortschritt` of that deadline.
- **C5 (lowering cap, :2402):** the supplied lowering witness expands each Gabbro primitive to
  at most 18 C forms.
- **C6 (outcome classification, :2403-2405):** the single-body outcome `o` is control flow
  (`ok`, `zurueck`, `grund`, `leave`, `next`), user logic (`logik`), or named hardware
  (`hardware`) — nothing else. This leg is unconditional (see below).
- **C7 (one mark, one thread, :2406):** the code projection of the run is single-threaded per
  mark: one mark code is never named by two threads.
- **C8 (unshared means one thread, :2407-2412):** any carrier declared unshared that is
  touched by two run steps belongs to one thread.
- **C9 (world count, :2413):** the recorded world history has exactly one world per step plus
  the start world.
- **C10 (good history, :2414):** every event in every recorded world is good.
- **C11 (live last world, :2415):** the last recorded world is some thread's world over live
  memory.
- **C12 (serial order, :2416):** two conflicting accesses to table `t₀` by distinct threads are
  happens-before ordered in one direction or the other.

Leg-to-lemma wiring (read off the proof term, `Ziel.lean:2417-2428`):
C1 by `pc_gesittet` (`grammatik/Grammatik/Kern/Semantik/Maschine.lean:1743`);
C2 by `pc_konsistent` (`Maschine.lean:1426`) and `pc_gut_obs` (`Maschine.lean:1433`);
C3 by `stabil_aus_lauf` (`Maschine.lean:3879`), whose `hFree` argument is derived inside from
`hForm` via `interferenceFree_of_invariantForm` (`grammatik/Grammatik/Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean:1213`)
over the discipline-derived context from `invariantenKontext_aus_disziplin`
(`InterferenzAllgemein.lean:1530`), with memory via `speicherVertrag_aus_Q`
(`Extraktion.lean:3924`) and frame via `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`);
C4 by `sampling_closes_frist` (`grammatik/Grammatik/Kern/Semantik/Fristlauf.lean:395`);
C5 by the `begrenzt` field of the supplied `Absenkung` (structure field, not a theorem);
C6 by `zwei_fehler` (`grammatik/Grammatik/Kern/Syntax/Satz.lean:50`, proved by case split, unconditional);
C7 by `pc_discharge_einfaedig` (`Maschine.lean:1619`) over `pcReach_markInv` (`Maschine.lean:1582`);
C8 by `pc_discharge_unshared` (`Maschine.lean:1704`) over `pcReach_carrierInv` (`Maschine.lean:1591`);
C9 by `genWelten_laenge` (`Maschine.lean:1158`) via `pcReach_gen` (`Maschine.lean:1396`);
C10 by `genWelten_gut` (`Maschine.lean:1165`) via `pcReach_gen`;
C11 by `genWelten_letzte` (`Maschine.lean:1172`) via `pcReach_gen`;
C12 by `pc_reduktion` (`Maschine.lean:1765`).

## 2. Premises: one row per premise

Classes: OWN-LOGIC = the user's own logic; NAMED-HW = named hardware assumption;
GABBRO-DUTY = discharged by checker/emitter once Gabbro is verified; OPEN = nothing discharges it.
DATA = object binder, not a proof obligation (no class applies).
"Discharge" means the exact Lean theorem that proves this premise (not merely consumes it);
"none" means no such theorem exists in the tree.

Non-premise object binders (meaning only, no class):
`P` (the program), `O` (the oracle answering `axiomCall`/registers,
`grammatik/Grammatik/Kern/Semantik/Semantik.lean:355`), `passes` (execution bound), `fcode` (thread-to-function
map), `tabs`/`globs` (carrier lists the extraction flattens over), `sp` (start memory),
`M`/`pc` (reached machine and program counters), `code` (mark-to-nat projection),
`Nb` (which thread pairs are co-declared), `J` (the joint chain), `I` (the carrier invariants),
`Wc`/`Gc` (per-carrier footprint witnesses), `tr` (thread trace), `t₀` (the one table the
reduction leg talks about), `g₁`/`g₂`/`j₁`/`j₂`/`w₁`/`w₂`/`Λ₁`/`Λ₂`/`h₁`/`h₂` (the two accesses),
`S`/`c` (sampling period and tick clock, `Fristlauf.lean:279`), `p` (check/use pair,
`Fristlauf.lean:102`), `fr` (deadline: assumption plus probe name, `Fristlauf.lean:110`),
`d` (deadline moment), `o` (the single-body outcome the C6 leg classifies).

| Name | One-sentence meaning | Class | Discharging theorem or "none" |
|---|---|---|---|
| `hO : GutO O` (:2325) | The oracle respects every axiom frame and never changes held locks or the trace (`Satz.lean:794`). | OPEN | none (per-oracle assumption; GutO oracles only, cf. the `Extraktion` §18 remainder on event-emitting oracles) |
| `h : PCReach … (progAus P fcode tabs globs) (GenStart sp) M pc` (:2328) | The machine `M` is really reachable by firing program-counter steps of the computed thread program (`Maschine.lean:1377`; `progAus` at `Extraktion.lean:2572`). | OPEN | none in general (witness-built per run; one-step lifters `pcSchritt_blatt_progAus_ohne_axiomCall` `:929` / `…_axiomCall` `:1129` extend it, they do not create it) |
| `hMSep : PCMarkSep code …` (:2330) | No mark code named by one thread's program text is named by another's (`Maschine.lean:1309`). | GABBRO-DUTY | none (per-program text check; consumed by `pc_discharge_einfaedig`, `Maschine.lean:1619`) |
| `hCSep : PCUnsharedSep …` (:2331) | Any carrier reached from two threads' program texts is declared shared (`Maschine.lean:1318`). | GABBRO-DUTY | none (per-program text check; consumed by `pc_discharge_unshared`, `Maschine.lean:1704`) |
| `hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c)` (:2336) | Every carrier invariant reads only its witnessed footprint (frame agreement implies agreement, `Interferenz.lean:80`). | OWN-LOGIC | none (per-invariant obligation over the user-supplied `I`) |
| `hFrameTD` (:2337) | Each table footprint is a singleton frame: whatever `Wc c` marks must be `c` itself. | OWN-LOGIC | none (per-invariant shape proof) |
| `hFrameGD` (:2338) | Same as `hFrameTD` for the global footprint. | OWN-LOGIC | none (per-invariant shape proof) |
| `hGuardEx : ∀ c, ∃ L, Bewacht c L` (:2339) | Every carrier, table or global, has a guard lock in its watch list (`InterferenzAllgemein.lean:1350`). | OPEN | none — FLAG (see §3) |
| `hEntry : ∀ c σ₀, J.welten[0]? = some σ₀ → I.inv c σ₀` (:2340-2341) | Every carrier invariant holds at the chain head. | OWN-LOGIC | none (caller/sequential side per program) |
| `hReturn` (:2342-2346) | Every writing chain step re-establishes every carrier invariant at its end world while holding the guard. | OWN-LOGIC | none (per-step restoration proof) — FLAG (see §3) |
| `hWatch` (:2347-2351) | Every writing chain step holds the guard lock (declared-holds, `D.haelt` shape). | OPEN | none inside this theorem; table instances discharge via `wache_aus_schuld` (`InterferenzAllgemein.lean:1481`) from `J.hSchuld` plus coverage — FLAG (see §3) |
| `hDeck : GeteiltGedeckt Nb J` (:2352) | Any carrier written by two threads is shared and both writers share a lock of its guard (`InterferenzAllgemein.lean:299`). | OPEN | none (per-chain coverage) — FLAG (see §3) |
| `hReqTAll` (:2353-2354) | Every table read by `requires` lies in the function's write signature. | GABBRO-DUTY | none (per-program footprint check; folded into `hAb` by `haengtAb_vertrag_gesamt`, `Extraktion.lean:1568`) |
| `hReqGAll` (:2355-2356) | Same as `hReqTAll` for globals read by `requires`. | GABBRO-DUTY | none (as above) |
| `hEnsTAll` (:2357-2358) | Same as `hReqTAll` for tables read by `ensures`. | GABBRO-DUTY | none (as above) |
| `hEnsGAll` (:2359-2360) | Same as `hReqTAll` for globals read by `ensures`. | GABBRO-DUTY | none (as above) |
| `hForm : InvariantForm … (SpecQ …)` (:2361-2362) | Per thread, the contract conjunction coincides at every world with some carrier invariant (the CSL fragment, `InterferenzAllgemein.lean:1204`). | OWN-LOGIC | none (exhibit one carrier per thread) — FLAG (see §3) |
| `htr : PCSpur … M pc tr` (:2364) | The reachability derivation fires exactly the thread sequence `tr` (`Maschine.lean:3594`). | GABBRO-DUTY | `pcSpur_von_reach` (`Maschine.lean:3607`, induction on `h`) |
| `hJw : J.welten = M.welten` (:2365) | The joint chain's worlds are exactly the machine's recorded worlds. | OPEN | none for two threads (`kette_aus_lauf_bezeugt_closed`, `Ziel.lean:2235`, closes only witnessed single-thread runs) — FLAG (see §3) |
| `hJsf : J.schrittFaden = tr` (:2366) | The chain's step threads are exactly the machine's fired-thread trace. | OPEN | none for two threads (same single-thread closer as `hJw`) — FLAG (see §3) |
| `hSeedAll` (:2367-2371) | Per member thread, `QRequires` and `QEnsures` both hold at the start world. | OWN-LOGIC | none (caller side) — FLAG (see §3: `Post` at entry) |
| `hBlattAll` (:2372-2384) | Uniform per-firing preservation: every leaf fired at every reachable intermediate machine preserves that thread's `Pre`/`Post` both ways. | OWN-LOGIC | partial: `hBlattAll_speicherfest_aus_feuerung` (`Maschine.lean:4093`) closes only the nine memory-preserving leaves; the seven memory-changing/oracle leaves stay owed — FLAG (see §3) |
| `hne : g₁ ≠ g₂` (:2385) | The two witnessed accesses are by distinct threads. | DATA | witness selection per use |
| `hw₁` (:2387) | Step `j₁` of the run is thread `g₁` accessing table `t₀`. | DATA | run witness per use |
| `hw₂` (:2388) | Step `j₂` of the run is thread `g₂` accessing table `t₀`. | DATA | run witness per use |
| `hstart : c.tick 0 ≤ S` (:2389) | The first clock tick is within one period (the sampling induction starts). | OPEN | none (per-clock fact; consumed by `TickClock.covers`, `Fristlauf.lean:299`) |
| `hpd : p.pruef < d` (:2391) | The deadline is strictly after the check. | DATA | per-deadline instantiation |
| `hdl : d < p.lauf` (:2391) | The deadline is strictly before the use. | DATA | per-deadline instantiation |
| `hspace : deadlineSpacing S p d` (:2392) | The use waits out the sampling window: `d + S ≤ p.lauf` (`Fristlauf.lean:388`). | NAMED-HW | none in Lean (per-use premise; a watchdog at the use or deadline granularity above `S` discharges it per run, `Fristlauf.lean:384-389`) |
| `hLowering : Absenkung` (:2393) | A lowering witness: per-primitive C-form count with cap 18 (`Ziel.lean:83`). | GABBRO-DUTY | the measured witness `absenkung` (`Ziel.lean:97`, value 17) via `ziel_l5_absenkung_zeuge` (`Ziel.lean:474`); its bound by `absenkung_haelt_schranke` (`Ziel.lean:110`) / `ziel_l5_schranke` (`Ziel.lean:478`) |

Discharge ledger for the sequential-logic leg (C3), for the checker: `hMemAll` (the
`stabil_aus_lauf` memory premise) is premise-free at Q-instantiation by
`speicherVertrag_aus_Q` (`Extraktion.lean:3924`, Q-contracts read only live memory);
the frame premise `hAb` is folded inside the `_Q` proof (`Ziel.lean:2417-2421`) from the four
footprint premises by `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`); the interference
check is derived inside from `hForm` by `interferenceFree_of_invariantForm`
(`InterferenzAllgemein.lean:1213`); the context is derived inside from
`hEntry`/`hReturn`/`hWatch` (+ frame/guards) by `invariantenKontext_aus_disziplin`
(`InterferenzAllgemein.lean:1530`).

## 3. Inapplicability flags

Every flagged premise is load-bearing (each feeds the proof term at `Ziel.lean:2425-2428`),
so the flag is about fit, not redundancy: an ordinary program that cannot meet the premise
cannot use this theorem.

1. **`hSeedAll` demands `Post` at entry (strongest flag).** `hSeedAll` (`Ziel.lean:2367-2371`)
   requires `QEnsures P (J.code g)` at the start world, because the underlying
   `SpecTriple.ensuresHead` (`InterferenzAllgemein.lean:1083`) requires the ensures-side at the
   chain head. An ordinary ensures-clause (postcondition established by running) is false at
   entry. Only ensures-clauses that already hold initially (e.g. invariant-shaped ones) fit.
2. **`hForm` restricts contracts to invariant form.** `InvariantForm`
   (`InterferenzAllgemein.lean:1204`) requires each thread's `Pre ∧ Post` to coincide, at every
   world, with some carrier invariant. Ordinary functional contracts (e.g. relating result to
   input) are not a carrier invariant; such programs keep owing the general per-run
   interference proof, which this variant exists to avoid.
3. **`hReturn`/`hWatch` quantify over all carriers and all steps.** `hReturn` requires every
   writing step to restore every carrier's invariant; `hWatch` requires every writing step to
   hold the guard. Ordinary programs with carriers outside any locking discipline, or with
   lock-free writes, meet neither. Table instances of the watch discharge via
   `wache_aus_schuld` (`InterferenzAllgemein.lean:1481`), but globals stay checker-side and the
   premise itself is still owed here.
4. **`hGuardEx` requires a guard for every carrier.** `hGuardEx` (`Ziel.lean:2339`) asks a watch
   lock for each `c : D.Tab ⊕ D.Glob`, including unshared and global carriers that ordinary
   declarations leave unguarded.
5. **`hJw`/`hJsf` assert chain-machine identity.** Equality of chain worlds with recorded
   machine worlds (`Ziel.lean:2365-2366`) is the open chain-to-machine wiring; the only closer,
   `kette_aus_lauf_bezeugt_closed` (`Ziel.lean:2235`), is single-thread, while this goal's C12
   leg needs two distinct threads. Moreover chain steps are whole critical sections
   (`InterferenzAllgemein.lean:1277-1293`) while machine worlds advance per event, so the
   equality also presumes a grain match ordinary runs do not have by construction.
6. **`hBlattAll` is uniform over all reachable machines.** It quantifies over every
   intermediate `M₀`/`pc₀` with `PCReach` (`Ziel.lean:2372-2373`), not just the executed path;
   only the nine memory-preserving leaves discharge via `hBlattAll_speicherfest_aus_feuerung`
   (`Maschine.lean:4093`). Every program whose contract touches a written slot/global owes the
   seven remaining leaf shapes per leaf.
7. **`hDeck` bans lock-free sharing.** `GeteiltGedeckt` (`InterferenzAllgemein.lean:299`) forces
   any carrier written by two threads to be shared with a common guard lock; ordinary
   programs with atomic or lock-free shared writes (or racy ones) are outside the covered class.
8. **C4/C12 legs narrow the runs covered.** The probe leg concludes expiry answered
   (`:2400-2401`), so with `hpd`/`hdl` (`:2391`) only deadlines strictly inside the open
   check-use interval fit — endpoints (`d = pruef`, `d = lauf`) are `ok` by `fristlauf`
   (`Fristlauf.lean:131-135`) and absent deadlines (`none`) are `ok` too; those runs cannot
   feed this conclusion. The reduction leg needs two exhibited same-table accesses by distinct
   threads (`hw₁`, `hw₂`, `hne`); single-threaded runs and runs without shared table accesses
   supply no such witnesses.
9. **`hO` excludes event-emitting oracles.** `GutO` (`Satz.lean:794`) forces
   `(O.wirkt …).1.spur = σ.spur`; oracles modelling DMA or other event-producing hardware do
   not satisfy it and stay open (the `Extraktion` §18 remainder).
10. **`hspace` is a per-use hardware timing proof.** `deadlineSpacing` (`Fristlauf.lean:388`) is
    never modelled, only named; each deadline of each of the 29 deadline kinds owes a watchdog
    or granularity argument outside Lean.

## 4. Cuts (what is not proved here)

This is a map, not a theorem: nothing is proved in this document. Within the mapped theorem:
C6 (`zwei_fehler`) holds unconditionally by case split, so it carries no assurance beyond
"the datatype has no fourth error"; C5 re-states the supplied witness's own field
(`hLowering.begrenzt`); the run premise `h`, the wiring `hJw`/`hJsf`, the per-leaf `hBlattAll`
(write fragment), the per-carrier discipline (`hEntry`/`hReturn`/global `hWatch`), the
per-thread form exhibit (`hForm`), the head validity (`hSeedAll`), the oracle bound (`hO`),
the separation facts (`hMSep`/`hCSep`), the footprint containments, and the per-use spacing
(`hspace`) are all owed per program, per chain, or per run. The non-invariant fragment
(assertions over shared carriers not in invariant form) is not covered by this variant at all.

## 5. Flags from the independent draft B (lane 17) that draft A does not carry

Draft B was written independently of this map; its premise table agrees with §2. These
flags are new or sharper, and each was re-read against the Lean before being folded in:

- **B8 -- `hMSep` excludes two threads running the same function.** `PCMarkSep`
  (`Maschine.lean:1309`) demands that no mark code named by one thread's program text is
  named by another's. `progAus` (`Extraktion.lean:2572`) extracts each thread's text from
  the body of the function it runs, so two threads running the same function carry the same
  atoms, and every mark named in that body appears in both texts. The most ordinary
  multithreaded shape -- the same routine on two threads -- therefore cannot reach the W4
  discharge (`pc_discharge_einfaedig`). Marks are static names (`D.Marke`), not per-thread
  instances; a per-thread mark needs an instance notion the extraction does not have.
- **B5 -- `hBlattAll` excludes break-and-restore.** The per-firing `↔` forbids a thread's own
  step from breaking its contract even temporarily (a counter mid-update, two linked fields
  updated in sequence). Only contracts that no own write can touch discharge.
- **B11 -- the lowering leg is numeric only.** `hLowering.proPrimitiv ≤ 18` says nothing about
  the 30 undecided C forms in real output (`Ziel.lean:68-73`); count preservation for the
  seven modeled ops lives downstream (`Budget.lean:681-690`).
- **B12 -- the order leg names one table and two accesses.** Conjunct 12 orders exactly
  `hw₁`/`hw₂` on `t₀`; everything else an ordinary program races on is not ordered by this
  theorem (shared globals, more than two sections, restoring writers stay open).

## 6. What the wave-1 merges established

Section 6 line numbers refer to the working tree on branch `muse/47` (the §§1-5
numbers above still refer to `muse/16` per the header).
Each row names the merged Lean artifact with exact `file:line` citations (verified by
grep against the working tree). "PROVES" means a checked Lean theorem now decides the
flagged point; "reading" means the flag still rests on statement/proof-term inspection
and no merged theorem discharges it.

| # | Merged result | Exact Lean names and locations | Effect |
|---|---|---|---|
| R1 | QLeer (lane 15) | `qRequires_nowhere` (`grammatik/Grammatik/Logik/Vertraege/QLeer.lean:133`), `qEnsures_nowhere` (`QLeer.lean:142`), `qSeedAll_unmoeglich_req` (`QLeer.lean:154`), `qSeedAll_unmoeglich_ens` (`QLeer.lean:170`) over `QRequires` (`grammatik/Grammatik/Kern/Syntax/Extraktion.lean:1437`) / `QEnsures` (`Extraktion.lean:1442`) | Proved theorems on a concrete one-function program, not a reading |
| R2 | BlattGegenbeispiel (lane 14) | `hblatt_post_falsch` (`grammatik/Grammatik/Proben/BlattGegenbeispiel.lean:242`), `hblatt_konj_falsch` (`BlattGegenbeispiel.lean:262`), `hblattall_falsch_schreibend` (`BlattGegenbeispiel.lean:286`) | Proved counterexample to `hBlattAll` for a writing leaf |
| R3 | VertragOrtB (lane 02, attempt B) | `ReqAmEintritt` (`grammatik/Grammatik/Logik/Vertraege/VertragOrtB.lean:114`), `EnsAmRueck` (`VertragOrtB.lean:120`), `VertragAmOrtB` (`VertragOrtB.lean:137`), `rufAt_ok_of_gates` (`VertragOrtB.lean:406`), `rueck_ohne_nachbedingung` (`VertragOrtB.lean:444`) | Proved place-check construction plus one-direction bridge; not wired into the goal theorem (import-cycle remainder) |
| R4 | KetteMehrfadenC (lane 11, attempt C) | `KettenSpurDeckung` (`grammatik/Grammatik/Korrespondenz/Kette/KetteMehrfadenC.lean:115`), `kette_zwei_aus_lauf` (`KetteMehrfadenC.lean:766`), `kette_aus_deckung` (`KetteMehrfadenC.lean:879`), `deckung_strikt_schwaecher` (`KetteMehrfadenC.lean:909`) | Proved chain-from-run for the two-thread lock-only fragment; N-thread discharge open |
| R5 | Audit muse/23, F2 (HIGH) | Filed: `allgemeinStabil` (`grammatik/Grammatik/Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean:498`) never consumes `hInv`/`hDeck`. Demo: `audit_allgemeinStabil_ohne_InvDeck` (`messung/muse-audit/23/F2_HauptsatzNutztInvDeckNicht.lean:25`), `audit_allgemeinStabil_forget` (`F2_HauptsatzNutztInvDeckNicht.lean:61`) | Checked demonstration, not a `Grammatik` theorem |
| R6 | Audit muse/23, F4 (HIGH) | Filed: `serial_chain_from_run` (`grammatik/Grammatik/Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean:1816`) proves its HB half from `SerialLink` + `reduktion_seriell` alone. Demo: `audit_hb_sidecar_ohne_kette` (`messung/muse-audit/23/F4_ReduktionOhneKette.lean:31`), `audit_kette_ohne_run` (`F4_ReduktionOhneKette.lean:47`) | Checked demonstration, not a `Grammatik` theorem |
| R7 | Audit muse/23, F5 (HIGH) | Filed: `hinv_aus_disziplin` (`grammatik/Grammatik/Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean:1502`) discards `LockFrei` (`intro k σ h _`), so `interferenceFree_wo_frei` (`InterferenzAllgemein.lean:1597`) restricts nothing. Demo: `audit_hinv_ohne_frei` (`messung/muse-audit/23/F5_LockFreiUngenutzt.lean:23`), `audit_hinv_forget_frei` (`F5_LockFreiUngenutzt.lean:47`) | Checked demonstration, not a `Grammatik` theorem |
| R8 | Audit muse/24, F9 (HIGH) | Filed: `QRequires` (`grammatik/Grammatik/Kern/Syntax/Extraktion.lean:1437`) / `QEnsures` (`Extraktion.lean:1442`) quantify over all envs/values at one world fed twice as entry and present (`eval σ e σ ρ`). Demo: `audit_QRequires_unfold` (`messung/muse-audit/24/Audit24.lean:80`), `audit_QEnsures_unfold` (`Audit24.lean:85`), both `rfl` | Checked demonstration, not a `Grammatik` theorem |
| R9 | Audit muse/24, F11 (HIGH) | Filed: `hmem_all` of `hwit_aus_lauf` (`grammatik/Grammatik/Kern/Syntax/Extraktion.lean:3829`, premise at `:3840`) and `hwit_alt_faltung` (`Extraktion.lean:3609`, premise at `:3621`) demands `.inl t₀ ∈ stmtTraeger tabs globs s` for every leaf, but `stmtTraeger` (`Extraktion.lean:2421`) returns `[]` for `assignVar` (`:2428`), `ite`, calls, locks, registers, marks, terminals. Demo: `assignVar`-implies-`False` example (`messung/muse-audit/24/Audit24.lean:107-112`) | Checked demonstration, not a `Grammatik` theorem |
| R10 | Audit muse/26, F7 (HIGH) | Filed: `handler_wettlauf_frei` (`grammatik/Grammatik/Nebenlaeufigkeit/Allgemein/Unterbrechung.lean:103`) and `handler_wettlauf_frei_global` (`Unterbrechung.lean:120`) discard the handler/boundary premises (`have _ :=`, `rcases hH with _ \| _`). Demo: `audit26_handler_premise_discarded` (`messung/muse-audit/26/F7_HandlerPremise.lean:17`) | Checked demonstration, not a `Grammatik` theorem |

Flag-by-flag verdicts for §§3 and 5:

- **§3.1 (`hSeedAll` demands `Post` at entry): PROVED (instantiated).**
  `qSeedAll_unmoeglich_req` (`QLeer.lean:154`) / `qSeedAll_unmoeglich_ens`
  (`QLeer.lean:170`) derive `False` from the goal theorem's `hSeedAll` shape for any run
  whose member thread runs the parameter/result function (`qRequires_nowhere`,
  `qEnsures_nowhere` supply the failing legs). Scope limit, stated in the theorems:
  runs with no member thread on that function supply `hSeedAll` vacuously. The same
  quantification defect is independently exhibited by R8 (`audit_QEnsures_unfold`).
- **§3.2 (`hForm` invariant form): stays a reading.** No merged result proves or
  discharges `InvariantForm`; R3 (`ReqAmEintritt`/`EnsAmRueck`) offers the repair
  direction (contracts evaluated at entry/return with actual values) without replacing
  the premise.
- **§3.3 (`hReturn`/`hWatch` over all carriers and steps): stays a reading.** Neither
  premise is discharged by a merged theorem. Adjacent sharpening only: R7 proves the
  neighbouring lock-freedom side-claim vacuous (`hinv_aus_disziplin` ignores `LockFrei`),
  and table watches still route via `wache_aus_schuld` exactly as §2 books it.
- **§3.4 (`hGuardEx` for every carrier): stays a reading.** Untouched by every merge.
- **§3.5 (`hJw`/`hJsf` chain-machine identity): PROVED for the two-thread lock-only
  fragment, open in general.** `kette_zwei_aus_lauf` (`KetteMehrfadenC.lean:766`)
  concludes `J.welten = M.welten` and `J.schrittFaden = tr` as theorems (never assumed)
  for two-thread lock-only programs, at the price of named extra premises (`hforeign`,
  `hlock_prog`, `hMSep`, `hCSep`, `hEintritt`, `hSchuld`, `hInvSicht`); `kette_aus_deckung`
  (`KetteMehrfadenC.lean:879`) isolates the exact N-thread premise (`KettenSpurDeckung`),
  whose discharge for leaves and N threads remains open per the file's `CUTS`.
  The grain-mismatch half of the flag (chain sections vs per-event machine worlds) is
  unaffected: the construction only threads lock steps.
- **§3.6 (`hBlattAll` uniform over all reachable machines): PROVED (refuted for writing
  leaves).** `hblattall_falsch_schreibend` (`BlattGegenbeispiel.lean:286`) falsifies the
  `hBlattAll`-shaped universal at a concrete writing leaf (`hblatt_post_falsch` flips the
  thread's own `QEnsures`); only the `QRequires` leg (`.wahr` here) survives. The §2
  booking stands confirmed in both directions: the nine memory-preserving leaves still
  discharge via `hBlattAll_speicherfest_aus_feuerung`, the writing shapes do not.
- **§3.7 (`hDeck` bans lock-free sharing): stays a reading as a premise of the goal
  theorem.** Adjacent proved fact: R5 shows `hDeck` (with `hInv`) is unconsumed by the
  `allgemeinStabil` conclusion (`audit_allgemeinStabil_ohne_InvDeck`), i.e. the
  interference-freedom leg the goal theorem routes through `hForm` does not depend on
  the deck — but `hDeck` itself is still owed wherever the goal theorem asks for it.
- **§3.8 (C4/C12 narrowing): stays a reading.** Endpoints, absent deadlines, and
  witness-less runs are still outside the conclusion. Adjacent proved fact: R6 separates
  the C12-side order from any chain conclusion (`audit_hb_sidecar_ohne_kette`), so the
  leg orders the two exhibited accesses and nothing more — exactly as flagged.
- **§3.9 (`hO` excludes event-emitting oracles): stays a reading.** Untouched by every
  merge.
- **§3.10 (`hspace` per-use timing): stays a reading.** Untouched by every merge.
- **§5 B8 (`hMSep` excludes same-function threads): stays a reading.** R4 assumes
  `hMSep` (`kette_zwei_aus_lauf` takes it as a premise) rather than removing it; no
  per-thread mark notion was added.
- **§5 B5 (no break-and-restore): PROVED (same counterexample as §3.6).**
  `hblatt_post_falsch` (`BlattGegenbeispiel.lean:242`) is exactly an own write flipping
  the thread's own `Post` mid-establishment; `hblatt_konj_falsch` (`:262`) refutes the
  full per-firing conjunction. R3's `hBlattCall` replacement proposal (per-call boundary
  premise, MUSE-REPORT-14) is the booked repair, not a merged theorem.
- **§5 B11 (lowering leg numeric only): stays a reading.** Untouched by every merge.
- **§5 B12 (one table, two accesses): stays a reading for C12 itself.** Adjacent proved
  fact on the witness side: R9 shows the `hwit_aus_lauf`/`hwit_alt_faltung` coverage
  premise `hmem_all` is uninhabitable outside the fragment where every leaf writes the
  same table (witnessed at `assignVar`, `Audit24.lean:107-112` over
  `stmtTraeger` at `Extraktion.lean:2421-2428`) — so witness production for C12-style
   accesses is itself fragment-restricted, as the flag's "restoring writers stay open"
   already suspects.

## 11. The goal over machine G (2026-09-13)

Since §§7-10 the goal was restated and proved over the repaired concurrent
call machine G (no bare lock steps; every memory step carries `HeldGenau`;
`rufG_haelt_statisch` in `RufHaeltG.lean:800`, `exklusivG` in
`ZielOrt.lean:424`). Three theorems, each subsuming the previous one on its
fragment: `ziel_ort` (`ZielOrtBeweis.lean:1098`), `ziel_ort_voll`
(`ZielOrtVoll.lean:1031`, via `ziel_ort_aus_voll` at `:1283`), and the
flagship `ziel_ort_geraet` (`ZielOrtGeraet.lean:1105`, with `ziel_ort_voll`
as the special case `ziel_ort_voll_lokal` at `:1133` on register-local
oracles). Data-race freedom is a separate proved theorem, `rennfrei_g`
(`RennfreiG.lean:64`). Line numbers below refer to branch `muse/133`.

### 11.1 Exact statement of `ziel_ort_geraet` (copied, `ZielOrtGeraet.lean:1105-1112`)

```lean
theorem ziel_ort_geraet (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutG P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      vertragAmOrtG P M
```

Conclusion (`VertragAmOrtG`, `ZielOrt.lean:67`): at every `eintritt` event of
every thread log the callee's `requires` holds with the logged actual
parameters at the logged entry world (`ReqAmEintritt`, `VertragOrtB.lean:114`);
at every `rueck` event the `ensures` holds with the logged entry world as the
`old` side, the logged return world, and the actual parameters and result
(`EnsAmRueck`, `VertragOrtB.lean:120`). Nothing is quantified away (audit
probe E, `audit_cross_thread_return`, `AuditZiel.lean:98`).

### 11.2 Every premise, classified

Classes: (a) USER obligation, (b) HARDWARE assumption, (c) decidable program
fact, (d) anything else. DATA = object binder, not an obligation.

| Premise | Meaning | Class | Justifying theorem |
|---|---|---|---|
| `P`, `O`, `passes`, `fs` | program, oracle, `forever` budget, complete member list | DATA | — |
| `sp`, `init` | start memory, boot assignment | DATA | — |
| `e0 : Ereignis D` | the declaration has a table, global or lock | (d) declaration-shape datum | load-bearing: `audit_antwortWelt_uses_e0` (`AuditZiel.lean:117`, fresh trace position of every recorded answer) |
| `hO : GutO O` | axiom answers inside declared frames, held locks and trace untouched (`Satz.lean:875`) | (b) HARDWARE | frame half via `gutO_rahmenO` (`ZielOrtVollBeweis.lean:51`); rely/locks consumed in `zielInv_schritt` |
| `hRL : RegLokal O` | register answers from its device carriers `D.rtraeger r`; `awaits g` visibility from `g` only (`ZielOrtGeraetSem.lean:48`) | (b) HARDWARE, named | transfer `regLies_gleich`/`sichtbar_gleich` (`:70`/`:76`); record closure `regLokal_orakelAus` (`:64`); exclusion `ziel_ort_register_ausgeschlossen` (`ZielOrtGeraetAus.lean`) |
| `hvoll : ∀ g, g ∈ fs` | member list complete | (c) finite enumeration check | consumed by `programmImFragmentG_ok` (`:497`) and `fussOrtGB_ok` (`:469`) |
| `hFrag : programmImFragmentG P fs = true` | every body in widened fragment `gOk`; indirect call admitted where `KandOk` holds | (c) DECIDABLE | soundness `programmImFragmentG_ok` (`ZielOrtGeraetSem.lean:497`); `kandB_kandP` (`ZielOrtVollSem.lean:132`) |
| `hFuss : fussOrtGB P fs = true` | every widened-footprint carrier (device carriers included) guarded by a signature lock of its function or written by none | (c) DECIDABLE | soundness `fussOrtGB_ok` (`ZielOrtGeraetSem.lean:469`); covers old check via `fussOrtB_of_G` |
| `hK : ∀ f, KoerperGutG P passes f` | per-function sequential triple + caller duty, for EVERY frame-respecting register-local oracle (`ZielOrtGeraetSem.lean:93`) | (a) USER | weakening chain `koerperGutG_of_V` (`:96`), `koerperGutV_of_kOk` (`ZielOrtVoll.lean:1270`); joint witnesses `ziel_ort_geraet_zeuge`, `ziel_ort_voll_zeuge`, `ziel_ort_zeuge` |
| `hStart : StartGut P sp init` | every start function's `requires` at the start world (`ZielOrt.lean:113`) | (a) USER | consumed by `zielInv_start` |
| `hex : StartExklusiv init` | no two threads start in functions sharing a signature lock (`RufMaschineG.lean:2011`) | (d) start-configuration fact (audit's corrected class, `AuditZiel.lean:12-18`) | finite collapse for constant assignments `audit_startExklusiv_const` (`:43`); exclusion `audit_same_lock_start_excluded` (`:57`); consumed by `exklusivG` (`ZielOrt.lean:424`) |
| `hr : RufErreichbarG …` (in conclusion) | the machine is reached from the start machine | run DATA | — |

The older theorems differ only in the (a)/(c) column: `ziel_ort_voll` asks
`KoerperGutV` + `programmImFragmentV` + `fussOrtB`; `ziel_ort` asks
`KoerperGut` + `programmImFragment` + `fussOrtB`. The place-check repair of
§§3.1/6-R3 is built in: contracts are checked at entry/return with actual
values, never `Post`-at-entry.

### 11.3 What the three theorems do NOT cover (every CUTS block)

- **Fragment limits.** `ziel_ort` covers only `kOk` bodies (no loops,
  exits, error channel, indirect calls, axioms, oracle forms —
  `ZielOrtBeweis.lean` CUTS; `semZ` gives those residues no meaning,
  `ZielOrtSem.lean` CUTS). `ziel_ort_voll` adds loops/exits/reasons/axioms/
  indirect calls but excludes `regLies`, `regLiesElse`, `awaits`
  (`ZielOrtVoll.lean` CUTS). `ziel_ort_geraet` admits those under `RegLokal`
  + `fussOrtGB`; the unrepaired widening is provably false
  (`ziel_ort_register_falsch`, `ZielOrtRegister.lean`; no analogous
  refutation built for `awaits`, `ZielOrtGeraetAus.lean` CUTS). Indirect
  calls stay restricted to `KandOk`: every function of the pointer's
  signature must have its contract carriers in the caller's footprint, so the
  caller must read those carriers or name them in its own contract.
- **`e0` (no carrier).** Declarations with no table, global or lock are out
  of all three: every world has the empty trace, record keys collapse to
  (callee, parameters), and the replay would need an unproved determinism
  lemma for G (`ZielOrtBeweis.lean`, `ZielOrtVoll.lean` CUTS; audit probe F).
- **Locks-block-only guards.** `fussOrtB`/`fussOrtGB` demand a guard held BY
  SIGNATURE (or no writer at all). A reader — of a footprint carrier or of a
  device carrier — that takes the lock only in a `locks` block is not covered
  (`ZielOrtGeraet.lean` CUTS).
- **Non-local oracles.** `ziel_ort_geraet` needs `RegLokal`; `ziel_ort_voll`
  for non-local oracles stays as proved and does not cover registers/awaits.
  `RegLokal`'s visibility half is minimal (awaited global only); answers
  depending on `publishes` payload globals are outside it. No asynchronous
  device step exists in G (`GeraetSchreibt` is a shape beside the run): a
  register whose answer changes between reads with no write to its carriers
  violates `RegLokal`.
- **Costs/time.** MISSING: no `KostenG.lean` exists in the tree. Per
  `ZielOrt.lean` CUTS, the repaired G has no bare lock steps, so the
  non-lock steps of a `kOk`-body frame are bounded by syntax size plus
  callees' — the natural first cost theorem once a declared bound exists. The
  `forever` budget `passes` bounds unfoldings only. Stuck states (false loop
  invariant, spent budget, `leave`/`next` in an `else` block) are not
  violations — G does not step, and `VertragAmOrtG` covers only logged steps.
- **Converse adequacy limits.** Forward adequacy (`RufAdaequatG`,
  `RufAdaequatRufG`) is existential (SOME f-only run), against the
  contract-ignoring handler `rufRumpf`, not the checking `rufAt`
  (`befund_vertrag`); calls need `Tief` depth admission (recursion past `n`
  is `logik (abstieg f)`; indirect calls not done — `D.Fn` has no
  finiteness); axioms/`bindAxiom` not simulated (no oracle premise taken);
  `ret` under `locks` excluded (untypable in bodies); TARGET B needs
  `ohneOrakel` and concludes memory-only agreement. The converse
  (`RufUmkehrRufG`: ALL runs to the first pop) covers only the loop-free,
  error-channel-free, axiom-free, oracle-free fragment (`TiefK`/`semK` give
  loop shims and waiting residues no meaning); the loop-carrying replay that
  `ziel_ort_voll` needs uses `semV` instead.
- **Lock-free sharing in race freedom.** `rennfrei_g`/`rennfrei_g_nah`
  cover guarded carriers only, in holder form (writer holds every guard
  before, excludes all others after) and adjacent double-write form. Atomic
  globals (`AtomarAusgenommen`) and published payloads
  (`PaarungAusgenommen`) are allowed races by design, excluded from
  `SchreibRasse`; unshared carriers are NOT covered (checker text-check duty
  `PCUnsharedSep`, §7 D2); no per-rule actor characterisation of `zugriffe`,
  no read/write formulation over it, no non-adjacent race with explicit
  release (`RennfreiG.lean` CUTS).
- **Witness limits.** The `voll` witness runs thread 0 only with `true`
  contracts (joint satisfiability, no frame reasoning —
  `ZielOrtVollZeuge.lean` CUTS); the `geraet` witness has no device-driven
  change and no `awaits` (declaration has no global —
  `ZielOrtGeraetZeuge.lean` CUTS); no interleaving inside a critical section
  anywhere (the lock forbids it — `ZielOrtZeuge.lean` CUTS).

### 11.4 Axiom record (probe `.tmp/sonde133.lean`, `./lean-probe` 0 errors)

```text
'Gabbro.Grammatik.ziel_ort' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_voll' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_geraet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.rennfrei_g' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no extra axiom. (`./lean-bau`: 0 error lines, 86 jobs.)

### 11.5 Distance to the goal (adversarial)

For the covered fragment — `gOk` bodies whose widened footprint check passes,
on declarations with at least one carrier — the slogan is nearly true: the
user proves per-function sequential triples plus caller duty (`KoerperGutG`)
and the boot contracts (`StartGut`), plus two named hardware assumptions
(`GutO`, `RegLokal`); everything else is carried by named theorems. Three
premises fall outside the slogan and must be named as such: `StartExklusiv`
is a start-configuration fact (undecidable over infinite `Faden` in general;
it bans the most ordinary multithreaded shape — same lock-holding routine on
two threads), `e0` is a declaration-shape datum (carrier-less programs are
out entirely), and `hvoll`/`hFrag`/`hFuss` are checker computations the
emitter must still implement and wire per program. Adversarial deductions
from the price of the repair: `KoerperGutG` quantifies over ALL
frame-respecting register-local oracles, so the user's sequential proof must
survive adversarial register answers that change between reads whenever
another thread writes the device carriers — locality may be assumed, stability
may not; reason returns (`grund`) carry no contract at all (`rufG_grund_treu`
is machine-faithfulness only); and the adequacy the user leans on relates the
machine to the contract-ignoring `rufRumpf`, never to the checking `rufAt` —
so sequential reasoning with contracts reaches G only through the handler
record, not through a proved equivalence. Outside the fragment the gaps are
total, not gradual: no costs or time anywhere, no lock-free sharing
guarantees, no stuck-state behaviour, no carrier-less declarations, no
locks-block-only readers, no non-local-register programs.

## 12. The goal against declared callee frames (2026-09-13)

The finding `r4_einzahlen_nicht_V` (`Referenz104.lean`) showed that the user
obligation of §11 fails on an ordinary corpus program: its handler class
`RespektiertVertraege` bounds a callee only by its `ensures`, never by its
declared writes. §12 repairs that. Files: `ZielOrtRahmenSem.lean`,
`ZielOrtRahmenBeweis.lean`, `ZielOrtRahmen.lean`, `Referenz104Rahmen.lean`.

### 12.1 Exact statement of `ziel_ort_rahmen` (`ZielOrtRahmen.lean`)

```lean
theorem ziel_ort_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutR P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M
```

The premises are those of `ziel_ort_geraet` (§11.1) with `KoerperGutR` in
place of `KoerperGutG`; the classification of §11.2 carries over row by row.

### 12.2 The new user obligation, classified (a) USER

`KoerperGutR P passes f` (`ZielOrtRahmenSem.lean`): the body triple and caller
duty of `KoerperGutG`, for every oracle with `RahmenO` and `RegLokal`, and
every call handler with `RespektiertRahmen P R` -- `RespektiertVertraege` AND
every normal answer `R f σ ρ = ok σ' v` satisfies
`Rahmen (D.schreibt f) (D.gschreibt f) σ σ'` and keeps the held locks
(`offen σ'.spur = offen σ.spur`). Weaker than the old obligations:
`koerperGutR_of_G`, `koerperGutR_of_V`; strictly weaker on the corpus:
`r4_rahmen_echt_schwaecher`.

The frame is NOT a premise: the machine delivers it. `rufG_rahmen`
(`ZielOrtRahmenSem.lean`) proves on every reachable machine, for every
suspended frame `F` waiting for a callee `g` entered at `s0`: `g`'s declared
writes are inside `F`'s (`RufPasst.hw`/`hg` at the push), and live memory
agrees with `s0` on every footprint carrier of `F` that `g` does not declare
written (own steps write only permitted carriers, `schritt_traeger`; other
threads are excluded by the held signature locks, `fussOrtGB`,
`StartExklusiv`). Its premises are `GutO`, `hvoll`, `fussOrtGB`,
`StartExklusiv` -- all already premises of the goal.

### 12.3 Consequences and the corpus

- `ziel_ort_geraet_aus_rahmen`: `ziel_ort_geraet` from `ziel_ort_rahmen`.
- `ziel_ort_voll_lokal_aus_rahmen`, `ziel_ort_lokal_aus_rahmen`:
  `ziel_ort_voll` and `ziel_ort` on register-local oracles.
- `ziel_ort_rahmen_ref104` (`Referenz104Rahmen.lean`): every premise holds
  jointly on the hand translation of `beispiele/104-referenz.gab`; the
  conclusion holds on every reachable machine and on the reached run
  (`ensures` of `einzahlen` at its logged return, from the theorem).

### 12.4 Not covered

`ziel_ort_voll`/`ziel_ort` for NON-local oracles and `ziel_ort_voll_ax`
(declared axiom ensures) are not derived from `ziel_ort_rahmen`; the frame
bounds normal answers only (not reason answers); the frame is a write SET
(whole tables/globals), no per-slot frame. All §11.3 cuts carry over.

> Superseded as the flagship by §13 (`ziel_ort_ganz`): the stuck hole of
> `ziel_ort_rahmen` (verdict probe A) is closed there, and `ziel_ort_voll_ax`
> on register-local oracles is now derived.

## 13. THE goal theorem: `ziel_ort_ganz` (2026-09-13)

Separation items 1 and 3 of the independent Opus verdict
(`dokumente/PROOF.md` §6). Files: `ZielOrtRahmenBeweis.lean`
(the replay made generic in a declared axiom ensures `Q`),
`ZielOrtRahmen.lean` (`zielInvR_erreichbar`), `ZielOrtGanz.lean` (obligation,
conclusion, theorem), `ZielOrtGanzZeuge.lean` (witnesses, probe A). **This is
the one theorem the goal names**; §§11-12 are its history.

### 13.1 What changed

- **The stuck hole (item 1).** G tests a `logik` condition at five places:
  a `traverse` boundary (`travNext`, `travDone`), a `forever` boundary
  (`ewigWeiter`), a `leave` out of a `traverse` body (`dannLeaveTrav`), and a
  `state` transition (a leaf, fired by `blatt`/`dannBlatt` only on an `ok`
  outcome). Where the test fails G blocks. `KoerperGutR` asked nothing about
  these outcomes, so a program whose every loop invariant is `false` met all
  premises of `ziel_ort_rahmen`, G stopped before any return was logged, and
  `VertragAmOrtG` held vacuously (probe A) -- while the emitted C, which does
  not test invariants, runs on and returns with every `ensures` false.
- **The repair is in the obligation, not in the machine.** The new clause
  `KeineLogik P passes Q f`: from `requires f`, against every oracle with
  `RahmenO`, `RegLokal`, `AxVertragO Q` and every handler with
  `RespektiertRahmen` that answers no `logik` outcome (`OhneLogik`), the body
  never ends in `logik e`. It is still a SEQUENTIAL per-function triple
  against handlers -- the user's own logic. A body's own `logik` outcomes are
  exactly `schleife` (loop invariant) and `vorzustand` (transition
  pre-state); `nachbedingung`, `invariante`, `abstieg`, `vorbedingung` arise
  only in a call (`rufAt`, `torRuf`), i.e. in the handler, which the clause
  assumes answers none. So the clause asks: "the loop invariants you wrote
  hold where they are tested, and every transition finds its pre-state."
  *Why not change G instead:* a G that ran past a false invariant (like the
  C) would leave the replay without the invariant the user's loop reasoning
  needs, and every adequacy file would have to follow a G that no longer
  means what the sequential semantics means. Keeping the tests and proving
  them turns each test into a theorem: on G's runs it always passes, so the
  C's not testing it is harmless there (to the extent G describes the C --
  verdict items 4-8, not addressed here).
- **The replay carries it.** The record handler with a hardware default
  (`rufAusL`, answers no `logik` outcome) meets the clause's handler class;
  from the replay of the head, its sequential prediction is never a `logik`
  outcome (`kopfR_keineLogik`), and at each of the five places the test
  passes at the machine world (`fadenR_prueft`, `blatt_logik`).
- **Progress at the checks** (`schritt_an_pruefung`): where the test passes
  and the head's static holdings are exactly the held locks (`HeldGenau`,
  the side condition of every reading rule of G), the rule FIRES.
- **Declared axiom ensures in the same theorem (item 3).** The frame replay
  (`KopfR`/`WarteR`/`StapelR`/`FadenR`/`ZielInvR`) carries `VertragA Q HA`,
  as the replay of `ziel_ort_voll_ax` did; the obligation quantifies over the
  oracles that meet `Q` (`KoerperGutRQ`, weaker than `KoerperGutR` --
  `koerperGutRQ_of_R` -- and than `KoerperGutA` -- `koerperGutRQ_of_A`).
  `ziel_ort_rahmen` keeps its statement (instance at the trivial ensures
  `axWahr`); `ziel_ort_rahmen_aus_ganz` and `ziel_ort_voll_ax_lokal_aus_ganz`
  derive it and `ziel_ort_voll_ax` (register-local oracles) from
  `ziel_ort_ganz_vertrag`, the contract half.
- **A decidable sufficient check** for the new clause:
  `programmLogikFrei P fs` (no `traverse`, `forever`, transition; `onTag`/
  `onGrund` refused conservatively) gives `KeineLogik` for every `Q`
  (`programmLogikFrei_ok`). For loop-free, transition-free programs the new
  clause costs the user nothing.

### 13.2 Exact statement (`ZielOrtGanz.lean`)

```lean
def KoerperGutZ (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  KoerperGutRQ P passes Q f ∧ KeineLogik P passes Q f

theorem ziel_ort_ganz (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M'
```

`KeinLogikHaltG O passes M := ∀ t, PrueftG O passes M t`: at a `traverse`
head, a `forever` head with budget `n + 1`, and a `leave` out of a
`traverse` body the invariant evaluates to `true` at the thread's machine
read world; at a leaf at the head of an end block or a block, the leaf's
outcome at the machine world is no `logik` outcome. `AnPruefungG M t`: the
head stands at one of these places (a leaf here: a `state` transition).

### 13.3 Premises, classified

| Premise | Meaning | Class |
|---|---|---|
| `P`, `O`, `passes`, `fs`, `sp`, `init`, `Q` | program, oracle, `forever` budget, member list, start memory, boot assignment, declared axiom ensures | DATA |
| `e0 : Ereignis D` | the declaration has a table, global or lock | (d) declaration-shape datum (§11.2) |
| `hO : GutO O` | axiom answers inside declared frames; held locks and trace kept | (b) HARDWARE |
| `hRL : RegLokal O` | register answers from the device carriers; `awaits` visibility from the awaited global | (b) HARDWARE |
| `hQ : AxVertragO Q O` | every axiom answer that fits its type meets the declared ensures `Q` | (b) HARDWARE (per `extern`/`asm` declaration) |
| `hlok : AxEnsLokal Q` | `Q` reads only the axiom's declared write carriers | (c) decidable per declaration |
| `hvoll` | member list complete | (c) |
| `hFrag : programmImFragmentG` | widened fragment | (c) DECIDABLE, no checker rule (verdict §1) |
| `hFuss : fussOrtGB` | widened footprint guarded by signature locks or unwritten | (c) DECIDABLE, no checker rule |
| `hK : ∀ f, KoerperGutZ P passes Q f` | per function: body triple + caller duty against frame-respecting handlers and `Q`-meeting local oracles (`KoerperGutRQ`), AND no `logik` outcome of the body (`KeineLogik`) | (a) USER -- sequential, per function; `KeineLogik` by `programmLogikFrei_ok` for loop-/transition-free bodies |
| `hStart : StartGut` | start contracts at the start world | (a) USER |
| `hex : StartExklusiv` | no two threads start under a common signature lock | (d)/(c): N240 for constant starts |

### 13.4 Tests

- **Probe A** (reconstructed, `ZielOrtGanzZeuge.lean` §3: `paP` on `zD`, every
  function `ensures false`, every body `traverse konto invariant false {};
  return`): `paP_rahmen_zertifiziert` -- `ziel_ort_rahmen` certifies it;
  `paP_nicht_keineLogik`/`paP_nicht_ganz` -- the new obligation fails (for
  every `Q`, every function); `paP_halt` -- the new conclusion fails on a
  machine reachable in two steps (`endeEntf`, `dannTrav`): the stuck state is
  now a refutation, not a certificate.
- **Corpus 104** (`ziel_ort_ganz_ref104`): every premise jointly on the hand
  translation of `beispiele/104-referenz.gab` (the new clause by
  `programmLogikFrei`), the full conclusion on every reachable machine, and
  on the reached run memory `0 -> 100` with the `ensures` of `einzahlen` at
  its logged return. (`ziel_ort_rahmen_ref104` still builds unchanged.)
- **Witnesses** (inhabitation): `ziel_ort_ganz_zeuge` (concurrent `zP`,
  thread 0's `lies` returns the `100` thread 1 wrote, `ensures` at that
  return); `ziel_ort_ganz_ax_zeuge` (`axP` with the declared ensures of
  `inc`: `result == tab[0]`, a contract `KoerperGutV` cannot prove);
  `ziel_ort_ganz_schleife` and `ziel_ort_ganz_fortschritt_zeuge` (a loop whose
  invariant `konto[0] <= 100` reads the shared table, `KeineLogik` PROVED
  against every handler and oracle; a reached machine at the `traverse`
  boundary, the invariant there from the theorem, and a step from the
  progress conjunct).

### 13.5 What is not carried, and what still blocks

- **Table and group invariants: NOT CARRIED** (CARRIED since §15.4, `ziel_ort_sperre_inv`). `Logik.invariante` arises only
  in `rufAt` at a callee's return. G does not test invariants,
  `VertragAmOrtG` states `requires`/`ensures` only, and `KeineLogik` does not
  ask for them (its handlers answer no `logik` outcome, so a callee's owed
  invariants are neither assumed nor proved). A program whose functions
  break a declared table invariant is certified.
- **Termination / `abstieg`:** G has no depth bound; a recursion that does
  not end keeps running in G, and no theorem bounds it (costs: `KostenG.lean`
  bounds a frame's own steps only).
- **Full progress is NOT proved** (PROVED since §19.2, `fortschrittG_aus`: every thread finished, waiting, at a named stop, or stepping). Proved: no reachable machine is stuck at a
  `logik` check (`KeinLogikHaltG`), and there the rule fires given
  `HeldGenau`. What else can stop a thread, rule by rule:
  1. `dannLocks`: another thread holds `L` (`RufFreiG` false) -- waiting;
     no fairness or hold-time assumption is stated (verdict item 8).
  2. `dannAwaits`: `O.sichtbar g` false -- the memory-model assumption A10.
  3. A hardware outcome at the head: an axiom answer outside its declared
     result type (`blatt` on `axiomCall`, `dannBindAxiom`), a register
     answer outside its type or against its promise (`dannRegLies`), a float
     result outside its range (`dannGleit`, `dannGleitLit`, `dannGleitVon`),
     a spent `forever` budget (`ewig 0` has no rule; sequentially
     `hardware (fortschritt a)`). Named hardware assumptions failing.
  4. (CLOSED in §15.3.) A `leave`/`next` inside an `else` end block that REPLACED the residue:
     `dannNarrowElse`, `dannPruefFalsch`, `dannGleitNarrowElse`,
     `dannRegLiesElseFalsch` and the reason pops (`err` of `let … else`)
     drop the enclosing loop's continuation, so a `leave`/`next` there has no
     rule, while the sequential semantics continues the loop. A modelling gap
     of G, neither user logic nor hardware; the obligation does not touch it.
  5. The `HeldGenau` side condition of every reading rule: its `⊆` half is
     proved on every reachable machine (`rufG_haelt_statisch`), the `⊇` half
     is not (it needs a no-duplicate fact about held locks and an exact
     stack link); the progress conjunct takes it as a hypothesis.
  6. (CLOSED in §19.2, `FormKette`.) The caller's shape at a pop: a binding pop needs the caller in
     `wartet`/`wartetSonst` with the callee's result type, a reason pop a
     `wartetSonst` caller with the callee's reason count; that suspended
     frames are always so shaped is not a proved invariant
     (`rufG_nie_wartend` covers heads only).
  7. A root frame at `ret`/`retGrund` has no caller: the thread is finished,
     not stuck.
- **Not addressed here:** verdict item 2 (lock/resource invariants; probes B
  and C stay outside `fussOrtGB`; addressed in §14), items 4-8 (checker wiring, `.gab` to
  `Programm D`, corpus sharing, model to C, time). All cuts of §§11.3/12.4
  carry over except "`ziel_ort_voll_ax` not derived" (now derived on
  register-local oracles).

### 13.6 Axiom record (`lake build`, 105 jobs, 0 errors)

```text
'Gabbro.Grammatik.ziel_ort_ganz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_fortschritt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_ref104' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_zeuge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_ax_zeuge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_schleife' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.paP_nicht_ganz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.paP_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no new `axiom`.

> Superseded as the flagship by §14 (`ziel_ort_sperre`): contracts over
> shared state across a lock boundary, readers inside `locks` blocks.
> `ziel_ort_ganz` is its instance at the empty lock-invariant family
> (`ziel_ort_ganz_aus_sperre`).

## 14. THE goal theorem: `ziel_ort_sperre` -- lock invariants (2026-09-13)

Separation item 2 of the independent Opus verdict
(`dokumente/PROOF.md` §6, probes B and C of §3). Files:
`SperreSem.lean` (the family, the class of environment moves, the
sequential semantics with acquire moves and release checks, its frame
semantics and step lemmas), `SperreFuss.lean` (stable carriers, the
footprint check, the obligation, the records of acquires),
`SperreBeweis.lean` (the replay), `SperreMaschine.lean` (the machine side:
rely, callee frames, release classification, machine lock invariant),
`ZielOrtSperre.lean` (the rule-by-rule step, the theorem),
`ZielOrtSperreZeuge.lean` (probes, witnesses). **This is the one theorem
the goal names**; §§11-13 are its history.

### 14.1 The finding, and why the repair is where it is

`fussOrtGB` (the check of `ziel_ort_ganz`) asks every footprint carrier of a
function to be guarded by a lock the function holds BY SIGNATURE for its
whole frame, or written by no function. A thread root cannot hold a lock by
signature (two threads would start holding it; N240), so every contract
at a lock boundary had to be silent about the protected carriers (probe B:
`wrap ensures konto[0] == 100` under `haupt = locks { wrap() }`), and a
read of a protected carrier inside `locks L { … }` fell (probe C, corpus
04/05/18/71). The model had no lock invariants. Two facts were NOT the
problem: G already takes and releases locks as steps (`dannLocks`,
`freiGib`, the `frei` peels of `leave`/`next`), and every access carries
all guards of its carrier in its static holdings by typing
(`Expr.orte_darf`) -- from the signature OR from an enclosing `locks`
block. What was missing is the SEQUENTIAL side: between two critical
sections other threads move the protected carriers, and the plain
sequential semantics (`execStmt`, where `locks` is just "take, run, give")
cannot say so; any proof over it that relates two critical sections is
unsound on G.

The repair is concurrent separation logic's resource invariants, kept as
a per-function SEQUENTIAL obligation:

- **A lock-invariant family** `S : SperrInv D` -- per lock `L` the carriers
  it protects for its invariant (`S.orte L`) and the invariant
  (`S.inv L : Speicher D → Bool`). Well-formed (`SperrInvOk S`): every
  listed carrier is guarded by `L`; the invariant reads only the listed
  carriers.
- **The sequential semantics with lock invariants** (`execStmtH`, identical
  to `execStmt` except at `locks`):
  `locks L { body }` at `σ` runs `body` from `(U L σ).nimmt L`, where the
  environment's move `U` is in the class `HavocOk S` -- `U L σ` differs from
  `σ` only on `S.orte L`, keeps the trace, and satisfies `S.inv L`; when the
  body ends normally, by `leave` or by `next`, the release checks
  `S.inv L` and ends in `logik schleife` if it fails (`freiH`).
- **The obligation** quantifies over the moves as it quantifies over
  handlers and oracles. So "acquire gives `I_L`, release requires it" is
  literally the obligation: the body may assume the invariant after every
  acquire (whatever other threads did) and must re-establish it at every
  release (a failed check is a `logik` outcome, which the no-`logik` clause
  excludes).
- **The machine** needs nothing new. Its side of the bargain is the machine
  lock invariant `SperrInvG S M`: every lock no thread holds has its
  invariant in live memory -- at the start by `hSstart`, kept by every step
  (a write needs all guards of its carrier, so a free lock's protected
  carriers do not move; a release re-establishes the invariant, which the
  replay derives from the obligation).

*Why not change the machine instead:* G is already a lock machine with
acquire and release steps; what it lacked was a sequential reading of a
frame that survives other threads' critical sections. Changing `execStmt`
itself would move every adequacy file and every earlier theorem;
`execStmtH` is a separate semantics that IS `execStmt` over the empty
family (`Stmt.execH_leer`) and over any body without `locks`
(`Endblock.execH_ohne`).

### 14.2 Exact statement (`ZielOrtSperre.lean`, `SperreFuss.lean`, `SperreSem.lean`)

```lean
structure SperrInv (D : Deklaration) where
  orte : D.Lock → List (D.Tab ⊕ D.Glob)
  inv : D.Lock → Speicher D → Bool

def SperrInvOk (S : SperrInv D) : Prop :=
  (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
  (∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s')

def HavocOk (S : SperrInv D) (U : Umwelt D) : Prop :=      -- Umwelt D := D.Lock → World D → World D
  ∀ L σ, (U L σ).spur = σ.spur ∧
    (∀ c, c ∉ S.orte L → TraegerGleich (U L σ).speicher σ.speicher c) ∧
    S.inv L (U L σ).speicher = true

-- execStmtH S O U passes R: as execStmt, except
--   | .locks L _ body, σ, ρ => freiH S L (execBlockH body ((U L σ).nimmt L) ρ)
-- freiH S L: .ok/.leave/.next σ ρ ↦ (release σ.gibt L) if S.inv L σ.speicher else .logik .schleife

def KoerperGutS (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) : Prop :=
  (∀ O', RahmenO O' → RegLokal O' → AxVertragO Q O' → ∀ U, HavocOk S U →
    ∀ R, RespektiertRahmen P R → OhneVorbedingung R →
      ∀ σ ρ, ReqAmEintritt P f σ ρ →
        (∀ σ' v, execEndH S O' U passes R (P.rumpf f) σ ρ = .zurueck σ' v → EnsAmRueck P f σ σ' ρ v) ∧
        (∀ g, execEndH S O' U passes (torRuf P R) (P.rumpf f) σ ρ ≠ .logik (.vorbedingung g))) ∧
  (∀ O', RahmenO O' → RegLokal O' → AxVertragO Q O' → ∀ U, HavocOk S U →
    ∀ R, RespektiertRahmen P R → OhneLogik R →
      ∀ σ ρ, ReqAmEintritt P f σ ρ → ∀ e, execEndH S O' U passes R (P.rumpf f) σ ρ ≠ .logik e)

def fussSperreB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || freiB fs c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || freiB fs c)

def SperrInvG (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ L, (∀ t, L ∉ offen (M.faeden t).spur) → S.inv L M.speicher = true

theorem ziel_ort_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M'
```

`ziel_ort_ganz_aus_sperre`: `ziel_ort_ganz` (same statement as §13.2) from
`ziel_ort_sperre` at `SperrInv.leer` (no protected carriers, invariant
`true`): `fussOrtGB` gives `fussSperreB` (`fussSperreB_of_G`, for every
family), `KoerperGutZ` gives `KoerperGutS` (`koerperGutS_leer`: every move
in the class is the identity, `havocOk_leer`, and the semantics is
`execEnd`). A body without `locks` owes nothing new for ANY family
(`koerperGutS_ohne`).

### 14.3 Premises, classified

| Premise | Meaning | Class |
|---|---|---|
| `P`, `O`, `passes`, `fs`, `sp`, `init`, `Q`, `S` | as §13.3; `S` the lock-invariant family | DATA |
| `e0` | the declaration has an event | (d) as §11.2 |
| `hO`, `hRL`, `hQ` | `GutO`, `RegLokal`, `AxVertragO Q` | (b) HARDWARE |
| `hlok`, `hvoll`, `hFrag` | as §13.3 | (c) |
| `hS : SperrInvOk S` | protected carriers guarded by their lock; invariant local to them | (c): first half decidable per declaration; second half by construction for an invariant written over the listed carriers |
| `hFuss : fussSperreB` | every footprint carrier: signature-guarded, unwritten, or protected by the invariant of one of its guards; device carriers signature-guarded or unwritten | (c) DECIDABLE, no checker rule |
| `hK : ∀ f, KoerperGutS P passes Q S f` | per function, SEQUENTIAL: triple + caller duty + no `logik` outcome, over `execEndH` for every move in `HavocOk S` | (a) USER |
| `hStart : StartGut` | start contracts | (a) USER |
| `hSstart : ∀ L, S.inv L sp` | every lock invariant at the start memory | (a) USER (boot duty) |
| `hex : StartExklusiv` | no two threads START holding a common lock | (d)/(c); trivial when roots hold no lock by signature (`startExklusiv_ohne_haelt`) |

### 14.4 How the proof goes

- **Stable carriers.** The replay keeps the sequential world equal to the
  machine world not on the whole footprint (other threads move protected
  carriers between critical sections) but on the STABLE carriers of the
  frame at its current static holdings `Λ`: `stabilS P S lok f Λ` = the
  footprint carriers guarded by a signature lock of `f` or LOCAL
  (`sicher P lok f`, `lok : D.Tab ⊕ D.Glob → Bool`), plus `S.orte L` for
  every lock `L` that `Λ` names held. The generic replay
  (`zielInvS_erreichbarL`) takes `lok` with the rely hypothesis
  `LokOk P O passes lok sp init` (no step of ANOTHER thread moves a local
  carrier of a frame); `ziel_ort_sperre` instantiates `lok := freiB fs`
  ("written by no function", `LokOk` by `lokOk_frei`), `ziel_ort_einfaden`
  instantiates `lok := fun _ => true` (§14.6). Every read is inside: a read carries all guards of its carrier in
  `Λ` (typing), a callee's contract carriers are guarded by the callee's
  signature locks = the caller's held locks (`RufPasst.hh`,
  `vertrag_stabil`), own `ensures` carriers at a return by
  `Λ.Perm ende` (`ens_stabil`), so `fussSperreB` puts them in the stable
  set (`stabil_of_fuss`).
- **Acquire** (`fadenS_locks`): at `dannLocks` the lock is free, so the
  machine lock invariant holds at the machine memory; the move "protected
  carriers of `L` from the machine" is recorded (third record `HU`, keyed at
  the pre-acquire sequential world, fresh by trace length) and is in the
  class; the stable set grows by `S.orte L`.
- **Release** (`fadenS_frei`, `fadenS_peelFrei`, `kopfS_frei_inv`): the
  head's prediction is no `logik` outcome (`kopfS_keineLogik`, the second
  clause against the record handler, oracle and move), so the release
  check passes at the sequential world, hence (the protected carriers are
  stable while the frame holds `L`) at the machine memory -- which keeps
  `SperrInvG` when the lock becomes free (`sperrInvG_schritt`,
  `freigabe_schrittG`).
- **Callee frames** (`rufG_rahmenS`): the frame fact of §12 over stable
  carriers; it needs no footprint check at all (stability is by held
  locks and `LokOk`), only `SperrInvOk`, `hvoll`, `GutO`, `StartExklusiv`,
  `LokOk`.
- **Everything else** is the replay of §13 over `execStmtH`
  (`akteurS`, `andereS`, `zielInvS_erreichbar`, `fadenS_prueft`).

### 14.5 Tests (`ZielOrtSperreZeuge.lean`)

- **Probe B, certified.** `zPB`: `zP` with `wrap ensures konto[0] == 100`
  (and `einzahlen ensures konto[0] == 100`, so the triple of `wrap` is
  provable from its callee's contract). `zPB_fussG_falsch`: `fussOrtGB` is
  false (the finding). With `zS` (the lock protects `konto`, invariant
  `true`): `zPB_fussS`, `zPB_koerper`, `zPB_zertifiziert` (every premise of
  `ziel_ort_sperre`). `zPB_lauf`: on a reached ten-step run thread 1 takes
  the lock, runs `wrap` (`lies`, `einzahlen` writes 100), and at `wrap`'s
  logged return `konto[0] == 100` holds, BY THE THEOREM.
- **Probe C, certified.** `zPC`: `haupt = locks { konto[0] = konto[0] }`.
  `zPC_fussG_falsch`, `zPC_fussS`, `zPC_zertifiziert`.
- **Two writers, one lock, a non-trivial invariant**
  (`ziel_ort_sperre_zeuge`, `sP_zertifiziert`). Declaration `sD`
  (table `konto`, two slots), every thread runs the SAME root
  `haupt(x) = locks { setze(x) }` (thread 0 `x = 30`, all others `x = 70`;
  exclusive start, `sInit_exklusiv`). Lock invariant
  `konto[0] == konto[1]`. `setze(x)` requires `konto[0] == konto[1]` and
  ensures `konto[0] == konto[1] && konto[0] == x`: `haupt`'s caller duty
  is provable ONLY from the invariant at the acquire (`sReq_iff_inv`), and
  the release check ONLY from `setze`'s `ensures` (`sInv_of_ens`,
  `sP_koerper_haupt`). On a reached sixteen-step run: thread 0's critical
  section writes `30, 30`; thread 1 enters `setze(70)` at a world holding
  those values and its `requires` holds there BY THE THEOREM; `setze(70)`
  returns with its `ensures` (`70`) BY THE THEOREM; at the end no thread
  holds the lock and its invariant holds in memory (`SperrInvG`) BY THE
  THEOREM. The old check refuses the program (`sP_fussG_falsch`).
- **Corpus 104** through the new theorem: `ziel_ort_sperre_ref104` (empty
  family). `ziel_ort_ganz_ref104` still builds unchanged.
- **Probe A stays refuted**: `paP_nicht_ganz`, `paP_halt` unchanged;
  `paP_nicht_sperre` -- the new obligation fails on `paP` for every
  well-formed family with a satisfiable invariant, `paP_nicht_sperre_leer`
  at the empty family.
- **One active thread, no footprint check** (`ZielOrtEinfadenZeuge.lean`).
  `ziel_ort_einfaden_ref104`: corpus 104 (every thread but 0 idle in
  `ruhe`, `r4_ruhig` by `decide`) certified without `fussOrtGB`.
  `eP`: an UNGUARDED table `konto` (no lock, not shared); `setze` writes
  `konto[0] = 5` and ensures it, `pruefe` REQUIRES `konto[0] == 5`,
  `haupt = setze(); pruefe(); return`. Both checks refuse it
  (`eP_fussG_falsch`, `eP_fussS_falsch`); `eP_zertifiziert`: every premise
  of `ziel_ort_einfaden`; `ziel_ort_einfaden_zeuge`: on a reached four-step
  run (start memory `konto[0] = 0`) `pruefe`'s `requires` holds at its
  logged entry, over `konto[0] = 5`, BY THE THEOREM.

### 14.6 The three consequences of verdict item 2

- **`StartExklusiv` (settled).** Its definition is already "no two threads
  start in functions sharing a SIGNATURE lock", i.e. no two threads START
  holding the same lock; nothing else in the theorem restricts sharing. A
  root that takes its lock in a `locks` block holds nothing at the start,
  so any assignment is exclusive (`startExklusiv_ohne_haelt`) and the same
  routine may run on every thread -- the two-writer witness does exactly
  that. `audit_same_lock_start_excluded` stays true and now only says: two
  threads cannot both START inside a lock.
- **Held-set equality `RufPasst.hh` (CLOSED in §15.1).** Relaxing it to "the
  callee's signature locks are among the caller's held locks" (what the
  checker accepts, verdict note T) is NOT done: every reading rule of G
  demands `HeldGenau` (static holdings EQUAL held locks), so a callee whose
  holdings are a strict subset of the thread's held locks could not step
  at all; `stmt_gut`, the race-freedom chain and the rank discipline across
  calls (a callee's `locks M` is ranked against its own holdings only) all
  rest on the equality. Moving it means changing G's side condition on
  about forty rules first. The replay of §14 itself would carry over (it
  uses `hh` only in the direction "callee's locks are held by the caller",
  `vertrag_stabil`).
- **Single-thread footprint (PROVED for one active thread; the general
  thread-local case open, named).** `ZielOrtEinfaden.lean`:
  `kein_schritt_ruhig` (a root frame at a bare `return` with an empty
  stack has no rule of G, 72 cases), `ruhig P f` (body a `return`, empty
  footprint, no signature lock; decidable), `ruhig_bleibt` (an idle
  thread stays at its start on every reachable machine),
  `lokOk_einfaden` (then EVERY carrier is local: only thread 0 steps),
  `startExklusiv_einfaden`, and

  ```lean
  theorem ziel_ort_einfaden (P) (O) (passes) (Q) (S : SperrInv D) (fs) (sp) (init) (e0)
      (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
      (hS : SperrInvOk S) (hvoll : ∀ g, g ∈ fs) (hFrag : programmImFragmentG P fs = true)
      (hRuhe : ∀ u, u ≠ 0 → ruhig P (init u).1 = true)
      (hK : ∀ f, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
      (hSstart : ∀ L, S.inv L sp = true) : <conclusion of ziel_ort_sperre>
  ```

  -- no `fussSperreB`, no `StartExklusiv`. This is the shape of every
  sequential corpus program in the model (thread 0 the driver, the rest
  idle, as `r4Init`). STILL OPEN: several ACTIVE threads with a carrier
  only one of them touches. That needs, per thread, the set of functions
  it can run (the call graph from its root, indirect calls by signature)
  and a machine invariant that every frame on that thread is in it -- a
  residue-to-body relation for calls that G does not carry. The generic
  replay already takes any `lok` with `LokOk`; what is missing is a
  decidable `lok` and the proof of `LokOk` for it.

### 14.7 What is not carried, and what still blocks

- The invariant is a semantic family, not a surface clause; no parser
  produces `S`, no checker rule computes `fussSperreB`/`SperrInvOk`.
- The environment's move at an acquire of `L` may change every carrier `L`
  protects, also one guarded by a second held lock (conservative, sound).
- Device carriers stay signature-guarded or unwritten (register reads carry
  no guard at the access).
- Waiting at `dannLocks` is the named scheduler situation; no fairness,
  hold-time or deadlock-freedom theorem (§13.5 item 1).
- All cuts of §§11.3, 12.4, 13.5 carry over (table invariants not carried,
  termination, full progress, no link to the emitted C and its lock
  primitives, weak memory, hand translation only).

### 14.8 Axiom record (`lake build`, 120 jobs, 0 errors)

```text
'Gabbro.Grammatik.ziel_ort_sperre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_ganz_aus_sperre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.akteurS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.zielInvS_erreichbar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.rufG_rahmenS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.sperrInvG_schritt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.koerperGutS_leer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.zPB_zertifiziert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.zPB_lauf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.zPC_zertifiziert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.sP_zertifiziert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_sperre_zeuge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_sperre_ref104' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.paP_nicht_sperre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.kein_schritt_ruhig' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.lokOk_einfaden' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_einfaden' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_einfaden_ref104' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.eP_zertifiziert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ort_einfaden_zeuge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no new `axiom`, no `native_decide`.

## 15. The remaining model gaps (2026-09-13)

`ziel_ort_sperre` stays THE goal theorem (statement of §14.2, unchanged).
This section records the model repairs after §14: the held set (§15.1),
`retry` (§15.2), `leave`/`next` in an `else` block (§15.3), table invariants
(§15.4); §15.5 is the updated premise table, §15.6 what remains.

### 15.1 Held set: `RufPasst.hh` is an inclusion (verdict note T)

*The finding.* The model demanded that a callee's `requires Held` set EQUAL
the caller's held set. The checker accepts a helper called both inside
`locks L { … }` and from a lock-free function; that program had no
`Programm D` term (`hilfe_alt_untypbar`, `HelferZeuge.lean`: no held set fits
both call sites).

*The repair.*

- `RufPasst.hh` (`Syntax.lean`): every lock the callee requires is held by
  the caller (`⊆`). The caller's EXTRA locks stay held for the whole callee
  frame; the callee does not name them, and G never lets it release or
  re-take them (release only through its own `frei` markers; `dannLocks`
  demands the lock is not held, `hself`).
- **Lock floors** keep the rank discipline across calls (the checker's
  interprocedural `H006`/`H003` walk). `Signatur.boden : Option Int`
  (default `none`, mirrored in `Vertrag.boden`): with `some c` the body takes
  only locks of rank at least `c` (`StufenOk P`, via `Stmt.ueberBoden`;
  decidable per program, trivial without floors: `stufenOk_ohne`).
  `RufPasst.hx`: every extra lock ranks below the callee's floor;
  `RufPasst.hb`: the caller's floor is at most the callee's. Without floors
  the relaxation would make the Satz FALSE: a callee could re-take an extra
  lock of its caller (a `nimmt` event that is not good). The floor is data
  the translation computes from the call graph, not a user clause.
- **The Satz** (`Satz.lean`): `HeldB b Λ h` (static holdings held, every
  other held lock below the floor `b`; `HeldB none` is `HeldGenau`,
  `heldB_none_iff`). `stmt_gutB`/`block_gutB`/`end_gutB` over `HeldB` and
  the floor premise; `stmt_gut`/`block_gut`/`end_gut` keep their statements
  (the exact held set); `GutR` is over `HeldB`; `rufAt_gut`, `exec_gut`,
  `exec_rahmen`, `exec_spur` (and `ziel_rahmen`, `ziel_spur`,
  `ziel_brav_aus_exec`, `rahmen_aus_exec`, `MaschinenFaden.spawn`) take
  `StufenOk P`.
- **Machine G** (`RufMaschineG.lean`): every side condition `HeldGenau Λ
  (offen spur)` (about forty rules) became `HeldIn Λ (offen spur)` -- a
  callee frame runs under its caller's extra locks. Leaves use
  `Stmt.gut_blatt` (frame and trace of a leaf under `HeldIn`).
- **The thread invariant** (`RufHaeltG.lean`): every frame's holdings are
  held, and no release marker releases a lock a lower frame names
  (`FreiLinks`); the old link `KetteLinks` (which was `RufPasst.hh` read
  backwards) is gone. `rufG_haelt_statisch`, `rufG_haelt_signatur`
  unchanged.
- **Adequacy** (`RufAdaequatRufG.lean`): the simulation carries `HeldB` at
  the frame's floor, `StmtR.locks` carries the floor condition,
  `heldB_eintritt` at a call; `rufG_adaequat_ruf` keeps its statement.
  `w_locksB` (`RufAdaequatG.lean`): `locks` under a floor. The call-free
  adequacy (`RufAdaequatG.lean`), `RufUmkehrRufG`, the race-freedom chain
  (`RennfreiG`, `RennfreiVoll`), `KostenG` and every witness carry over.
- **Progress without the `HeldGenau` hypothesis**
  (`ziel_ort_sperre_fortschritt`, `ZielOrtSperre.lean`): the rules demand
  `HeldIn`, which holds on every reachable machine, so §13.5 item 5 is
  closed: on every reachable machine a thread at a `logik` check can step.
  Witness `ziel_ort_sperre_fortschritt_zeuge`.

*The witness* (`HelferZeuge.lean`). `helfer(x) ensures result == x` (floor
`1`), `frei() = helfer(3)`, `setze() = locks L { helfer(5) }` (`L` rank 0);
thread 0 runs `setze`, the others `frei`. `ntP_zertifiziert`: every premise
of `ziel_ort_sperre`. `helfer_zeuge`: on a reached seven-step run thread 0
calls `helfer(5)` holding `L` (a frame with EMPTY static holdings while its
thread holds `L`) and thread 1 calls `helfer(3)` holding nothing; both
logged returns meet `result == x` (values `5` and `3`) BY THE THEOREM.
`ntStufen`: the floors are respected.

### 15.2 `retry`: the bound is checked after the last pass

*The finding* (T4 continuation, `CFormenW.lean` header): the sequential
`retryLauf` ran the overflow block as soon as the budget was spent,
without looking at `bis`; the emitted C checks `bis` once more after the
last pass (`if (z >= N && !(bis))`), so a pass that makes the condition
true is a success there. The emitter is right (it is what `retry until p
bounded N` promises).

*The repair.* `retryLauf`'s `0` case (`Semantik.lean`) is now `if bis
then ok else overflow` (from the world that recorded the read). Machine
G's `wiederUeber` unfolds a spent loop into `if bis {} else { overflow }`
(the existing `ite` rules do the read), so G and the sequential semantics
agree again. Carried: `retryLauf_gut` (Satz), `retryLauf_ohneLogik`
(`ZielOrtGanz`), `retryLauf_ohneAbbruch`/`_nicht_zurueck`/`_ende_none` and
the three `retry` simulations (`retryOkR`, `retryAbbR`, `retryRetR`,
`RufAdaequatRufG`), `semV_wiederUeber`/`semH_wiederUeber` (the frame
semantics of the replays of every goal theorem, flagship included), the
cost model (`KostenG`: a `retry` and its loop states pay `2 + cost(bis)`
for the last check; the loop witness's bound is now 20, not 18).
`CFormenW.lean`: `retryLaufC_eq` is now the equality `retryLaufC =
retryLauf`; `retrySemC` is defined by `retryLauf`; the old run is kept as
`retryLaufAlt` (`retryLauf_eq_alt`, `retryLauf_C_verschieden`: where the
old model ran the overflow block and the corrected one succeeds).
`scorr_retry_voll`: the emitted loop corresponds to `execStmt` for EVERY
overflow block (no `never` premise); `scorr_retry` keeps its statement.
Witnesses: `retry_unterschied_zeuge` (the old model writes `konto[1]`,
the corrected model and the C do not), `wRetry_corr` (a writing overflow
block, now covered).

### 15.3 `leave`/`next` in an `else` block reach the loop (§13.5 item 4)

*The finding.* `dannNarrowElse`, `dannPruefFalsch`, `dannGleitNarrowElse`,
`dannRegLiesElseFalsch` and the three reason pops into the `else` block of
`let … else` (`rueckGrund`, `rueckConsGrund`, `dannRetGrund`) REPLACED the
whole residue by the end block. A `leave`/`next` in it then stood as
`.ende (.leave _)` with the loop continuation gone; no rule fires there
(`ende_leave_steht`), while the sequential semantics leaves (or continues)
the loop and goes on.

*The repair* (`RufMaschineG.lean`). `Endblock.alsBlock` reads an end block
as a block (same statements, the final `ret`/`retGrund`/`leave`/`next` as a
statement over the empty block; `Endblock.execBlock_alsBlock`: the block
means the end block's outcome). A new residue layer `GRest.abbruch k`
stands between it and the old continuation `k`: an `else` step now goes to
`.dann sonst.alsBlock.2 (.abbruch k)` (a reason pop to
`.dann err.alsBlock.2 (.abbruch (.schrumpf k))`). A normal end of that
block is impossible (end blocks never end normally); a return pops as
before; two new rules `peelAbbruchLeave`/`peelAbbruchNext` hand a
`leave`/`next` to `k`, where the existing loop shims take it. The
semantics of `abbruch k` in every replay: an `ok` outcome is `sonst`, every
other outcome continues as `k` (`weiterH_abbruch_zu`, `weiterZ_abbruch_zu`).

*Carried* (full `lake build` green, no `sorryAx`):

- `RufHaeltG` (the held-lock chain through `abbruch`: `kette_abbruch`);
  `RufAdaequatG`/`RufAdaequatRufG`/`RufUmkehrRufG` (`alsRet`/`alsRetR`: the
  `else` block run as a block returns as the end block did;
  `EndG.alsBlock`/`EndR.alsBlock`; `semR_alsBlock`/`semK_alsBlock`;
  `w_peelAbbruch`), statements unchanged.
- The replays of every goal theorem (`ZielOrt`, `ZielOrtVoll`, `…Geraet`,
  `…Rahmen`, `…Ax`, `…Sperre` -- the flagship -- and `…Einfaden`): the step
  lemmas `semV_/semH_/semZ_narrowElse`, `_pruefFalsch`, `_gleitNarrowElse`,
  `_regLiesElseFalsch` now hold with the new residue BY AN EQUALITY
  (`semV_alsBlock`, `semH_alsBlock`); before they only held as a weakening
  to the end block's own result, which predicted nothing for a
  `leave`/`next`. `FortV`/`FortS` (the continuation after a reason answer)
  resume the reason block as a block (`semV_alsBlock_schrumpf`,
  `semH_alsBlock_schrumpf`); the fragment predicates carry the new residue
  (`okV_alsBlock`, `okG_alsBlock`, `okS_alsBlock`; the `abbruch` layer
  records that its held set agrees with the block's, so the stable set of
  the flagship replay transfers at `peelAbbruch`).
- The cost model (`KostenG.lean`): an `else` branch is priced by
  `kostenSonst` (the end block in block position: no unfold, a `let` pays
  its `schrumpf` layer, the final statement its empty-block tail) plus one
  step for the `abbruch` layer (two for a reason block: `schrumpf` too);
  the checker correspondence carries a matching remainder `zusatzSonst`
  (`spiegel_sonst`). The witness numbers of `KostenGZeuge` are unchanged.

*The witness* (`SonstLeaveZeuge.lean`). `fn(): retry 1 until false { if
!false { leave } }; return 7`. `sv_exec`: the sequential semantics returns
`7`. `sonst_leave_zeuge`: thread 0 of G unfolds the loop, takes the `else`
branch of the refusal -- the residue is `leave` over `abbruch` over the loop
shim `wiederRest`, the loop continuation KEPT --, peels the layer, leaves
the loop, and pops logging exactly that `7`. `ende_leave_steht_zeuge`: the
state the old rule reached on this fixture has no step.

*Not covered.* The adequacy fragments admit the `else` forms only at loop
level `false` (`BlockR.narrow_inv … l = false`, likewise `BlockG`), where no
`leave`/`next` can occur. For an `else` block INSIDE a loop the agreement of
G with the sequential semantics is shown by the replays' equalities above
(which is what the goal theorems use) and by the witness, not by a general
adequacy theorem.

### 15.4 Table and group invariants are carried (§13.5 first item)

*The finding.* `rufAt` checks, at every return of `f`, each declared
invariant `f` OWES (`schuldet f i`: `f` writes one of its carriers) and
answers `logik (invariante i)` where it is false. G tests no invariant and
`ziel_ort_sperre` said nothing about them: a program whose functions break
a declared invariant was certified (`ivPschlecht_alt`).

*The repair: obligation + conclusion, as for lock invariants* (§14). The
machine is unchanged (it tests invariants nowhere, like the emitted C);
the obligation turns the test into a theorem.

- **Footprint** (`ZielOrt.lean`): `fussOrte P f` also lists `invOrteP P f`,
  the carriers of every invariant `f` owes (`fuss_inv`). The footprint
  checks (`fussOrtGB`, `fussSperreB`) thereby cover them; every earlier
  fixture declares no invariant, so nothing else moved.
- **Obligation** `InvGutS P passes Q S f` (`ZielOrtInv.lean`, per function,
  SEQUENTIAL, over the oracle/move/handler class of `KoerperGutS`): from
  `requires f`, a normal return of the body makes every invariant `f` owes
  true at the return world. Like `rufAt`, it assumes no invariant at entry;
  an invariant needed there belongs in `requires`. Nothing new for a
  function that owes none (`invGutS_ohne`, `invGutS_leer`).
- **Conclusion** `InvAmOrtG P M`: at every logged return `rueck g rho v s0
  s1` of a reachable machine, every invariant `g` owes holds at `s1`.
- **The theorem** `ziel_ort_sperre_inv`: the premises of `ziel_ort_sperre`
  plus `∀ f, InvGutS P passes Q S f` give the conclusion of
  `ziel_ort_sperre` AND `InvAmOrtG`. Proof: induction over reachable
  machines beside the flagship's replay invariant (`zielInvS_erreichbar`);
  `invLog_schritt` classifies the six value pops; `popS_inv` (the twin of
  `popS_ens`) carries the sequential return world's invariant to the
  machine's, because the carriers of an owed invariant are stable at `ret`
  (`inv_stabil`: in the footprint, and every guard of theirs is a signature
  lock of `f` by the declaration's `invarianten_gehalten`, U003).
  `ziel_ort_sperre` itself is unchanged.

*The witnesses* (`InvZeuge.lean`): table `konto` (two slots) under lock
`L`, invariant `konto[0] == konto[1]`; `haupt` (holds `L`) calls `setze`
(holds `L`). Correct `setze` writes both slots `5`: `ivPgut_zertifiziert`
(every premise of `ziel_ort_sperre_inv`, `InvGutS` proved per function)
and `ivGut_zeuge` (a four-step run; the logged return of `setze` meets the
invariant BY THE THEOREM, both slots `5`). Broken `setze` writes only
slot `0`: `ziel_ort_sperre` certifies it (`ivPschlecht_alt`), but
`ivPschlecht_nicht_invGutS` (the new obligation fails from the zero
memory) and `ivPschlecht_verletzt` (on a machine reached in three steps
the new conclusion fails) REFUTE it -- as probe A was refuted in §13.4.

*Not covered.* A thread's start frame never pops, so an invariant owed by
a start function is not checked at the thread's end (G logs returns only at
pops); invariants are checked at returns only, not at entries or while a
frame holds the locks (the program semantics checks nothing else either).

### 15.5 Premise table (THE goal theorem is now `ziel_ort_sperre_inv`)

| Premise | Meaning | Class | Changed in §15 |
|---|---|---|---|
| `P`, `O`, `passes`, `fs`, `sp`, `init`, `Q`, `S`, `e0` | data | as §14.3 | `Signatur.boden` (lock floors, default `none`) |
| `hO`, `hRL`, `hQ` | hardware | (b) | -- |
| `hlok`, `hvoll`, `hFrag` | as §13.3 | (c) | -- |
| `hS : SperrInvOk S` | as §14.3 | (c) | -- |
| `hFuss : fussSperreB` | footprint check | (c) DECIDABLE | footprint also lists owed invariant carriers (§15.4) |
| `hK : KoerperGutS` | per function, sequential | (a) USER | -- |
| `hI : InvGutS` | per function, sequential: owed invariants at a normal return | (a) USER | NEW (§15.4); trivial without owed invariants |
| `hStart`, `hSstart`, `hex` | as §14.3 | (a)/(d) | -- |
| (syntax) `RufPasst` | call-site typing | typing | held set `⊆`, `hx`/`hb` floors (§15.1) |
| (syntax) `StufenOk P` | floors respected | (c) decidable | NEW premise of the Satz chain (§15.1), not of the goal theorem |

Conclusion: `VertragAmOrtG ∧ SperrInvG ∧ KeinLogikHaltG ∧ progress` (as §14.2)
`∧ InvAmOrtG` (§15.4). `ziel_ort_sperre_fortschritt` drops the `HeldGenau`
hypothesis of the progress conjunct (§15.1).

Axioms of every new theorem of §15 (`ziel_ort_sperre_inv`, `popS_inv`,
`inv_stabil`, `invLog_schritt`, the `InvZeuge`, `SonstLeaveZeuge` and
`HelferZeuge` witnesses): `propext`, `Classical.choice`, `Quot.sound`.
Full `lake build`: 139 jobs, no `sorryAx`.

### 15.6 What remains

- The adequacy fragments (`BlockG`/`BlockR`, and the converse) admit the
  `else` forms only at loop level `false`; for an `else` block INSIDE a loop
  the agreement of G with the sequential semantics is shown by the replay
  equalities and a witness (§15.3), not by a general adequacy theorem.
- Invariants owed by a start function are not checked at the thread's end
  (§15.4).
- `StufenOk` and the floors are model data without a checker rule that
  computes them; `InvGutS`, like `KoerperGutS`, is a user proof obligation
  without a checker.
- Everything §13.5 lists besides items 4 and 5 and the invariant item
  (termination, full progress beyond the named stops, fairness, the link to
  the emitted C, weak memory, hand translation only) is unchanged.

## 16. Concurrency: active threads, start functions, deadlock (2026-09-14)

The three concurrency gaps that kept the goal theorem from covering
ordinary concurrent programs (§14.6 "several ACTIVE threads", §15.6 "start
function invariants", §13.5 progress item 1 "a lock held by another
thread"). Files: `FadenMerkmal.lean` (a residue invariant over every rule
of G), `ZielOrtMehrfaden.lean` (item 1), `ZielOrtStart.lean` (item 2),
`Verklemmung.lean` (item 3), `MehrfadenZeuge.lean` / `MehrfadenLauf.lean`
(witnesses). **G is unchanged**, and every earlier theorem keeps its
statement (`ziel_ort_sperre`, `ziel_ort_sperre_inv`, `ziel_ort_einfaden`,
`ziel_ort_sperre_ref104`, the two-writer witness, probes A/B/C). The goal
theorem is now `ziel_ort_mehrfaden_ende` (§16.4).

### 16.1 Several ACTIVE threads with thread-local carriers

*The gap.* The generic replay (`zielInvS_erreichbarL`) took any set of
local carriers `lok` with the rely `LokOk`; the flagship instantiated it
only with "written by no function" (`freiB`), `ziel_ort_einfaden` with
"everything" (all other threads idle). What was missing: which functions
can run on which thread -- a residue-to-body relation for calls that G did
not carry.

*The repair.*

- **A residue invariant carried by every rule** (`FadenMerkmal.lean`). A
  feature set `Merkmal` (admitted direct callees, admitted signatures of
  indirect calls, admitted locks of `locks` blocks) and its hereditary
  residue predicate `GRest.mR` (also: every `abbruch` layer names the held
  set of the block it stands behind). `schrittMerk` classifies all rules
  of G: head-local (stack and function kept, predicate carried), push
  (callee admitted, suspended caller carries it), pop (caller resumes with
  it). `merkInvG_erreichbar`: for per-thread function sets `Z t` closed
  under the admitted calls (`MerkAbg`) and containing the start function,
  on every reachable machine every frame of thread `t` runs a function of
  `Z t`.
- **The call graph of a thread.** `K : Faden → D.Fn → Bool` with `AbgK P fs
  (K t)` (every body in `K t` calls only into `K t`; an indirect call
  through signature `n` admits every function of signature `n`), decided by
  `abgB`; `reachB P fs w` computes the reachable set from a start function.
- **Thread-local carriers.** `GetrenntK P K c`: no thread reaches `c` in a
  footprint while a DIFFERENT thread can write it (declared write
  permissions). `lokK P K` is this predicate; `lokOk_mehr` proves the rely:
  a step writes only what its head function may write, that function is in
  the acting thread's graph, a frame of another thread runs a function of
  that thread's graph.
- **The footprint condition** `∀ f, FussS P S (lokK P K) f`: every
  footprint carrier is signature-guarded, protected by the lock invariant
  of one of its guards, or thread-local. Decided by `fussMehrB P S fs K N`
  when every thread from `N` on is idle (`StummK`: its call graph has empty
  footprints and no writes) -- `fussMehrB_ok`. The old check is the special
  case (`fussS_frei_mehr`: a carrier written by no function is thread-local
  for every `K`).

```lean
theorem ziel_ort_mehrfaden (P) (O) (passes) (Q) (S) (fs) (sp) (init) (e0)
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g, g ∈ fs) (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f, InvGutS P passes Q S f) :
    ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
      (VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M
```

Also: `ziel_ort_sperre_invL` (the flagship generic in `lok` + `LokOk`).

### 16.2 Invariants and `ensures` owed by start functions

*The gap.* G logs a return only at a pop; a start frame has no caller and
never pops, so neither `InvAmOrtG` nor the `ensures` half of
`VertragAmOrtG` said anything about a start function.

*The decision.* The completion of a start function IS a machine state: the
stack is empty and the head stands at a `return` (`ret`, `ret` before the
rest of an end block, or of a block -- `RetKopf`). No rule applies there;
the thread is finished and stays so. The statement is a property of every
reachable machine, so G needs no new rule and no `never`/`diverges`
annotation is needed (a start function that never returns owes nothing
here):

```lean
def StartEndeG (P) (M) : Prop :=
  ∀ t, (M.faeden t).stapel = [] → ∀ l Γ Λ ρ r e, (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ →
    RetKopf e r →
    EnsAmRueck P kopf.f kopf.s0 ((M.weltVon t).lese Λ e.orte) kopf.rho (evalErg … e …) ∧
      InvAmRueck P kopf.f ((M.weltVon t).lese Λ e.orte)
```

Because it holds on EVERY reachable machine, it holds at the moment the
thread finishes and at every later one: the carriers read are stable for
the finished frame (signature-guarded -- the finished thread keeps those
locks --, protected by a lock the frame names, or local), and the replay
keeps them. The obligation is the existing one (`KoerperGutS`, `InvGutS` of
the start function). Proof: `kopfS_ret` (the replayed head at a return,
the twin of `popS_ens`/`popS_inv` without a pop). Theorems: `ziel_ort_ende`
(generic `lok`), `ziel_ort_sperre_ende` (old footprint check),
`ziel_ort_mehrfaden_ende` (§16.4).

### 16.3 Deadlock freedom from lock ranks

*The gap.* `dannLocks` fires only if the lock is not held by the thread
(`hself`), ranks above EVERY lock the thread holds (`hrang`, a check on the
machine's held set), and no other thread holds it (`RufFreiG`). Nothing
proved that `hself`/`hrang` ever hold on a reachable machine, so a thread
at a `locks` head could be stuck for a reason no scheduler resolves; and no
statement excluded a wait cycle.

*The repair* (`Verklemmung.lean`).

- `schrittRang`: every rule classified by its effect on the head's
  holdings and the held locks (keep both / take a free, unheld lock the
  residue admits / release one lock / push with the call site's `RufPasst`
  / pop at the end holdings).
- **The rank invariant** `RangInvG w z`: held locks duplicate-free; the
  rank chain `RangKette` down the stack -- every held lock is NAMED by a
  frame, or ranks below that frame's floor (an extra lock of its callers),
  or ranks at least the floor of the frame directly above (taken by a
  callee), the bottom frame has no "below floor" case; every frame's
  signature locks are named by its caller; floors rise towards the head;
  every `locks` still ahead of a frame ranks at least its floor
  (`GRest.mR (bodenM f)`, the residue form of `StufenOk`); the bottom frame
  runs the start function `w`. `rangInvG_erreichbar` (from `StufenM`, which
  `StufenOk` gives: `stufenM_of_ok`, and duplicate-free start locks).
- `sperre_rang`: at a `locks L` head every held lock ranks below `L` and
  `L` is not held -- `hself` and `hrang` hold. `schritt_an_sperre`: the step
  fires unless another thread holds `L`.
- **No wait cycle:**

```lean
theorem keine_verklemmungG (hO : GutO O) (hSt : StufenM P) (sp) (init)
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L, L ∈ ls)
    {M} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hW : ∀ t, ¬ FertigG M t → WartetG M t) : ∀ t, FertigG M t
```

`FertigG`: empty stack, head at a return. `WartetG`: the head stands at
`locks L` and every such `L` is held by another thread. Proof: the waiting
thread whose lock ranks highest waits for a lock held by an unfinished
thread (a finished thread holds only its start function's signature locks,
none by `hLeer`), which waits for a lock of strictly higher rank
(`sperre_rang`) -- contradiction on finitely many locks.
`keine_verklemmungG'`: the same as `¬ (∃ unfinished ∧ ∀ unfinished wait)`.

### 16.4 THE goal theorem: `ziel_ort_mehrfaden_ende`

Premises of `ziel_ort_mehrfaden` (§16.1); conclusion: that of
`ziel_ort_sperre_inv` AND `StartEndeG`. Deadlock freedom is the separate
theorem `keine_verklemmungG` (its premises are program facts of the same
classes).

| Premise | Meaning | Class | Changed in §16 |
|---|---|---|---|
| `P`, `O`, `passes`, `fs`, `sp`, `init`, `Q`, `S`, `e0` | data | as §14.3 | -- |
| `K` | per-thread call graphs | DATA (`reachB` computes them) | NEW |
| `hO`, `hRL`, `hQ` | hardware | (b) | -- |
| `hlok`, `hvoll`, `hFrag` | as §13.3 | (c) | -- |
| `hS : SperrInvOk S` | as §14.3 | (c) | -- |
| `hAbg : ∀ t, AbgK P fs (K t)` | call graphs closed | (c) DECIDABLE (`abgB`) | NEW |
| `hWurzel` | each start function in its thread's graph | (c) decidable per thread | NEW |
| `hFuss : ∀ f, FussS P S (lokK P K) f` | every footprint carrier signature-guarded, lock-protected, or thread-local | (c) DECIDABLE for finitely many active threads (`fussMehrB`) | REPLACES `fussSperreB` (weaker) |
| `hK : KoerperGutS` | per function, sequential | (a) USER | -- |
| `hI : InvGutS` | per function, sequential; now also covers start functions | (a) USER | conclusion extended |
| `hStart`, `hSstart`, `hex` | as §14.3 | (a)/(d) | -- |
| deadlock theorem: `StufenM P` | floors on bodies (from `StufenOk`) | (c) decidable | NEW (for `keine_verklemmungG`) |
| deadlock theorem: `hLeer`, `ls` | start functions hold no signature lock; locks finite | (c) | NEW |

> Restated in §18.4 (2026-09-14, second round): the obligations `hK`/`hI`
> are demanded at EVERY `forever` budget and the conclusion holds on the
> machines of every budget (probe D); new premise `StartOhneGrund`, new
> conjunct `KeinStartGrundG`. The statement above is now the lemma
> `ziel_ort_mehrfaden_ende_bei`.

### 16.5 Witnesses (`MehrfadenZeuge.lean`, `MehrfadenLauf.lean`)

Declaration `mD`: shared `konto` under lock `()` with lock invariant
`konto[0] == konto[1]`; UNGUARDED private tables `privA`, `privB`; table
invariant `privA[0] == privA[1]`. Thread 0: `hauptA = privA[0] = 7;
privA[1] = 7; locks { setze(30) }; pruefeA(); return` (ensures
`privA[0] == 7`, owes the invariant); `pruefeA` REQUIRES `privA[0] == 7`;
thread 1: `hauptB = privB[0] = 5; locks { setze(70) }; return`; others
idle. `setze(x)` as in §14.5.

- `mP_fussS_falsch`, `mP_fussG_falsch`: both earlier checks refuse it;
  `mP_fussMehr` (by `decide`): the new check passes; `mKA_reach`,
  `mKB_reach`: the call graphs are the computed ones.
- `mP_zertifiziert`: every premise of `ziel_ort_mehrfaden_ende` jointly
  (`KoerperGutS`, `InvGutS` proved per function; `hauptA`'s caller duty for
  `pruefeA` uses the frames of the lock's move and of `setze`);
  `mP_mehrfaden`; `mP_verklemmungsfrei`, `mP_rang`; `sP_ende_zertifiziert`
  (`ziel_ort_sperre_ende` on §14.5's `sP`).
- `ziel_ort_mehrfaden_zeuge` (items 1, 2): on a reached run both ACTIVE
  threads write their private tables, thread 0 runs its critical section,
  thread 1 runs its critical section (its `setze` return logged), then
  thread 0 enters `pruefeA` and `privA[0] == 7` holds at the logged entry
  BY THE THEOREM; thread 0 finishes, and at its final state `hauptA`'s
  `ensures` and its owed invariant hold (both `privA` slots `7`) BY THE
  THEOREM; both threads are `FertigG`.
- `keine_verklemmungG_zeuge` (item 3): at a reached machine where both
  threads stand at `locks`, thread 1's step exists by `schritt_an_sperre`;
  one step later thread 0 holds the lock, thread 1 `WartetG` and is
  unfinished, thread 0 neither waits nor is finished, and the theorem
  refutes "all unfinished threads wait".

Axioms of every new theorem (`schrittMerk`, `merkInvG_erreichbar`,
`ziel_ort_sperre_invL`, `lokOk_mehr`, `ziel_ort_mehrfaden`,
`fussMehrB_ok`, `kopfS_ret`, `ziel_ort_ende`, `ziel_ort_mehrfaden_ende`,
`ziel_ort_sperre_ende`, `schrittRang`, `stufenM_of_ok`,
`rangInvG_erreichbar`, `sperre_rang`, `schritt_an_sperre`,
`keine_verklemmungG`, `keine_verklemmungG'`, all witnesses): `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, no new `axiom`, no
`native_decide`. Full `lake build`: 160 jobs, green.

### 16.6 What remains

- **Checker link.** `K`, `AbgK`, `fussMehrB`, `StufenM` are decidable model
  facts; no Rust rule computes them (as for `fussSperreB`, `SperrInvOk`).
  Thread-locality is judged on DECLARED write permissions, not on the
  writes a body actually performs.
- **Infinitely many active threads.** `GetrenntK` quantifies over all
  thread pairs; the decision procedure needs every thread from some `N` on
  idle (as G starts all threads of `Faden = Nat` at once). A carrier touched
  by a routine that runs on two threads is never thread-local.
- **Start functions:** `StartEndeG` covers value returns (`ret`); a start
  function ending in a reason (`retGrund`) owes nothing (as `InvGutS`
  covers normal returns only). Invariants are still checked at returns only.
- **Progress beyond locks.** Deadlock freedom is not starvation freedom:
  no fairness, no bound on hold times; a thread that never releases (a
  `forever` inside `locks`) is unfinished but not waiting, so the theorem
  says nothing about the threads waiting for it. Still open from §13.5:
  `awaits` visibility (A10), hardware outcomes, spent `forever` budget, and
  the caller's shape at a pop (item 6). `keine_verklemmungG` needs start
  functions without signature locks (a finished thread keeps its start
  locks).
- Everything else of §15.6 (adequacy of `else` inside loops, the link to
  the emitted C, weak memory, hand translation only) is unchanged.

## 17. Floats in the model, in C, and nested arrays (2026-09-14)

Design record: `dokumente/FLOATING-POINT.md` §§7-9. What changed for the
goal theorems: nothing in their statements -- every theorem carried.

### 17.1 The model computes with data, not with `Float`

`Val (.fl lo hi)` holds `GFloat = Gleitkomma.GBits f64` (Typen.lean);
`gleitRechne`, `gleitPasst`, `bruch` (the literal, rounded ONCE),
`gleitAusInt`, `Expr.fllt/flle` are the kernel-computable IEEE-754 model
(round-to-nearest-even, signed zeros per IEEE 754-2019 §6.3). A `gleit`
step is still range-checked; NaN/inf fail `gleitEndlich` and take the
`hardware ieee` / `else` outcome, as with `Float`. The switch was a
one-token rename (`Float.ofInt` -> `gleitAusInt`) in 13 files; no proof
changed. New witnesses (GleitZeuge.lean): `lauf01_gespeichert` (0.1 + 0.2
runs through `execBlock` and stores exactly `0x3FD3333333333334`),
`lauf01_ueber03` (the same sum declared in `0 .. 3/10` takes `hardware
ieee` -- the check bites on the last ulp), `laufDurchNull`, `roh_trunc`.

### 17.2 The emitted C float forms -- removed (C backend)

Removed on 2026-10-18 with the C backend (`CFormen`, `CFormenF`: the correspondence of the emitted C float forms to the model). It existed and lives in the tag `archiv/c-emitter-2026-10-17`. The model side (§17.1, `Gleitkomma*`) stays.

### 17.3 Nested arrays

`[[T; N]; M]` is a table with `count M*N` and `M[i][j]` its cell `i*N +
j` (Verschachtelt.lean): `flach_bereich`, `flach_injektiv`,
`flach_zerlegung`, `nestIdx`/`eval_nestIdx`; witness `nv_lauf`, `nv_bijektiv`.
(The correspondence to C's row-major `a[i][j]`, `ev_idx_nested`/`nv_c_adresse`, was removed with the C backend.)

Axioms of every new theorem: `propext`, `Classical.choice`, `Quot.sound`
(subsets). Full build on ki-pc-fisch-101: 185 jobs, no `sorryAx`.

## 18. The `forever` budget, start reasons, the closing theorem's assumptions (2026-09-14, second round)

The model items of the two independent verdicts of 2026-09-14
(`dokumente/PROOF.md` §5 probe D and §6 items 1, 7;
`dokumente/PROOF.md` §5). Files: `Durchgaenge.lean` (new),
`ProbeD.lean` (new), `ZielOrtGrund.lean` (new), `ZielOrtStart.lean`,
`ZielOrtMehrfaden.lean`, `Schlusssatz104.lean`, `MehrfadenZeuge.lean`,
`MehrfadenLauf.lean`. **G, `rufAt`, `execStmt`/`execStmtH` are unchanged.**
The goal theorem keeps its name `ziel_ort_mehrfaden_ende`; its statement
changed (§18.4).

### 18.1 The `forever` budget is quantified, not chosen (probe D)

*The finding.* Every semantics takes `passes`, the number of passes the
environment gives a `forever` loop; at `0` the sequential run is
`hardware (fortschritt a)` before the first pass and G has no rule at
`ewig 0`. The goal theorems took `passes` as DATA and every witness fixed
`0`. At `0` the obligation says nothing about a `forever` body: probe D
(`ensures false`, body `forever () invariant false { leave }; return`) met
every premise, while the emitted C does not test the invariant and runs the
loop once. `passes` was a prover-chosen assumption classified as data.

*The decision: every budget.* The goal statements demand `KoerperGutS` and
`InvGutS` at EVERY `passes` and conclude on the machines of EVERY `passes`.
G re-arms the budget at every loop entry (`dannForever` pushes
`ewig a passes`), so a run in which each loop entry makes at most `n`
passes is a run at every budget `≥ n`: the conclusion covers every finite
run. A floor "every budget `≥ B`" would cover the same runs and cost the
user nothing less (the sequential proof of a `forever` body must handle an
arbitrary finite number of passes either way); with no budget chosen, none
can empty the obligation. The per-budget statements stay as lemmas with the
suffix `_bei` (`ziel_ort_ende_bei`, `ziel_ort_mehrfaden_ende_bei`,
`ziel_ort_sperre_ende_bei`, `ziel_ort_mehrfaden_bei`); they are not goal
statements (the conclusion at one budget describes only the runs whose
loops end within it).

*Budget independence* (`Durchgaenge.lean`). `ohneEwig` (no `forever` in a
body, decidable; `ohneEwigB P fs`). A `forever`-free body means the same at
every budget: `Endblock.execH_passes` (lock-invariant semantics),
`Endblock.exec_passes` (plain), `rufAt_passes` (the call semantics, every
depth, when no body of the program has `forever`). Hence
`koerperGutS_passes`/`invGutS_passes` and, per program,

```lean
theorem koerperGutS_alle (hvoll : ∀ g, g ∈ fs) (hE : ohneEwigB P fs = true)
    (h : ∀ f, KoerperGutS P 0 Q S f) : ∀ passes f, KoerperGutS P passes Q S f
```

(`invGutS_alle` alike). Every earlier witness is `forever`-free, so NO
witness held only at `passes = 0`: `mP_zertifiziert`, `mP_mehrfaden`,
`sP_ende_zertifiziert` (two writers), `schlusssatz_104` (§18.3) are
restated over every budget at the cost of one `decide` each.

*Probe D, rebuilt and refuted* (`ProbeD.lean`, on `zD`; `fvP false` is the
verdict's `fvP`, `fvP true` its `fwP` -- invariant `true`, the shape of
`manifest_pruefen` in `beispiele/04-schleifen.gab`):

- `fvP_koerper0`, `probeD_bei0_zertifiziert`: the per-budget lemma at `0`
  certifies both variants (the defect, kept as a theorem).
- `probeD_nicht` (every `Q`, every well-formed family with a satisfiable
  invariant), `probeD_nicht_leer`, `fwP_nicht`:
  `¬ ∀ passes f, KoerperGutS (fvP _) passes Q S f` -- at budget `1` the
  body ends in `logik schleife`, resp. returns under `ensures false`.
- `probeD_halt`: a machine of budget `1` reached in two steps stands at the
  `forever` head with a pass left and invariant `false`: `¬ KeinLogikHaltG`.
- `fwP_ende_verletzt`: a machine of budget `1` reached in five steps
  (`endeEntf`, `dannForever`, `ewigWeiter`, the `leave`, `dannLeer`) has
  thread 0 finished at `return` under `ensures false`: `¬ StartEndeG`.

*Inhabitation with a real loop* (`ewP`: `lP` of §13.4 with
`forever () invariant konto[0] <= 100 { leave }`): `ewP_koerper` (the
obligation PROVED at every budget -- budget `0` stops, every `n + 1`
passes the invariant and returns), `ewP_zertifiziert` (the budget-quantified
`ziel_ort_sperre_ende`), `ziel_ort_ewig_zeuge` (a machine of budget `1`
reached in two steps stands at the `forever` head; the invariant holds
there BY THE THEOREM and G takes the pass, `ewigWeiter`).

### 18.2 A start function may not end in a reason (Muse §5)

*The finding.* `StartEndeG` checks value returns (`RetKopf`). A start
function ending in `retGrund` owed nothing: probe `grP` on `vD` (every
thread starts in `ferr`: one reason, `ensures false`, body `return R`) met
every premise of the flagship as it stood (`grP_alt_zertifiziert`), and
every thread is finished at the START machine at a reason return with
nothing checked (`grP_fertig`).

*The decision: start functions declare no reasons* (`StartOhneGrund init :=
∀ t, D.gruende (init t).1 = 0`, class (c), decidable per start). A reason
hands a failure to the CALLER, which the typing forces to handle it
(`bindCallElse`); a thread root has no caller, and `rufAt` checks neither
`ensures` nor invariants at a reason return, so the alternative "a reason
return of a start function checks its owed invariants" would demand at a
root what no other reason return owes and still leave its `ensures`
unchecked.

*What is proved.* `wurzelFn_erreichbar`: the bottom frame of every thread
runs its start function on every reachable machine (every rule, via
`schrittMerk`). `keinStartGrundG`: with `StartOhneGrund`, no start frame
stands at a reason return (`KeinStartGrundG M`; `retGrund` needs an element
of `Fin 0`). `fertig_wert`: with `KeinStartGrundG`, every finished thread
(`FertigG`) stands at a VALUE return -- so `StartEndeG` checks EVERY
completion of a start function. The probe fails the premise (`grP_nicht`)
and the new conjunct is false on its start machine (`grP_verletzt`): no
premises whatever let the flagship certify it.

### 18.3 `schlusssatz_104`: A1 (+A2, A3) and A4 as hypotheses

```lean
theorem schlusssatz_104 (c : Cert104) (hc : certOkG c = true)
    (binEin : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1ein : ∀ st vs st' rv, binEin st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv)
    (binLies : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1lies : ∀ st vs st' rv, binLies st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv)
    (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) (hA4 : LaufzeitStart init) :
    <1 parse> ∧ <2 certificates> ∧
    <3 fragment, footprint, KoerperGutS/InvGutS at EVERY passes, rufAt budget-independent> ∧
    <4 every C run, as before> ∧
    <5 renaming, gPB behaves as gP, rufAt of gPB budget-independent,
       ∀ sp passes M, reachable from RufStartG gPB sp init →
         goal conclusion ∧ InvAmOrtG ∧ StartEndeG ∧ KeinStartGrundG> ∧
    <6 every run of binEin/binLies from related starts ends related to the
       Gabbro result, which is the same at every passes>
```

- **A4 is a Lean proposition and a hypothesis**: `LaufzeitStart init := ∀ u,
  u ≠ 0 → init u = ⟨none, .nil⟩`. Part 5 holds for every such start
  (`gPB_ziel`, via the new `ziel_ort_einfaden_ende`: one active thread,
  every budget, `StartEndeG`, `KeinStartGrundG`). Outside Lean stays only
  that the real runtime starts in this shape (the driver is not emitted).
- **A1 with A2 and A3 is one hypothesis per function**: every run of the
  binary's function (`binEin`, a parameter: the behaviour of the compiled
  code) is a run of the model's C semantics on `refCProg` at the emitter's
  layout, at the depth the call tree needs. Part 6 states EVERY run of the
  binary. Outside Lean: A1 that `binEin` IS the compiled binary (the
  compiler); A2 that the text means `refCProg` -- replaced by a Lean C parser
  for the emitter's subset, the text pinned as a `String`, and
  `parseC text = some refCProg` by `decide` (A2 then shrinks into A1: the
  compiler's front end reads the subset as `parseC`); A3 reduces to A1 + A2
  (the `_Static_assert` pins are checked by the compiler) plus one missing
  Lean lemma (the C semantics reads a `RecLay` only through the pinned
  numbers, fields `< nf`). A5 (kernel, definitions) is no proposition.
- **Every budget**: parts 3, 5, 6 as stated; `gP_rufAt_passes`,
  `gPB_rufAt_passes` lift every `rufAt … 0 …` of parts 4-5.
- **The root's `ensures` is now in the machine part**:
  `schlusssatz_104_maschine_zeuge` additionally shows the root `einzahlen`
  finished (empty stack) and its `ensures` at its completion BY THE THEOREM.
- Jointly satisfiable: `schlusssatz_104_praemissen` (the C semantics itself
  as the binary's behaviour, `bootInit`), and the `example` applying the
  theorem to them.

Chain count unchanged: **1** (`beispiele/104`); PLAN §6 restated.

### 18.4 THE goal theorem: `ziel_ort_mehrfaden_ende` (restated)

```lean
theorem ziel_ort_mehrfaden_ende (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g, g ∈ fs) (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f)
    (hStart : StartGut P sp init) (hSstart : ∀ L, S.inv L sp = true)
    (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hGrund : StartOhneGrund init) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M ∧ KeinStartGrundG M
```

Also restated the same way: `ziel_ort_ende` (generic `lok`),
`ziel_ort_sperre_ende` (`fussSperreB`), new `ziel_ort_einfaden_ende` (one
active thread); `ziel_ort_mehrfaden` over every budget (no completion, no
`hGrund`).

| Premise | Class | Changed in §18 |
|---|---|---|
| `P`, `O`, `fs`, `sp`, `init`, `Q`, `S`, `e0`, `K` | DATA | `passes` is NO LONGER a premise: it is quantified in the conclusion |
| `hO`, `hRL`, `hQ` | (b) HARDWARE | -- |
| `hlok`, `hS`, `hvoll`, `hFrag`, `hAbg`, `hWurzel`, `hFuss` | (c) | -- |
| `hK : ∀ passes f, KoerperGutS …` | (a) USER, at every budget | quantified (§18.1); free for `forever`-free programs (`koerperGutS_alle`) |
| `hI : ∀ passes f, InvGutS …` | (a) USER, at every budget | quantified (§18.1) |
| `hStart`, `hSstart` | (a) boot duty | -- |
| `hex` | (c)/(d) | -- |
| `hGrund : StartOhneGrund init` | (c) decidable per start | NEW (§18.2); no Rust rule |

### 18.5 Invariants at entry, while locks are held, at releases (item 4: named, not implemented)

*What the conclusion says today.* `InvAmOrtG`: at every logged VALUE
return (`rueck`) of every reachable machine, every invariant the returning
function owes (`schuldet f i`: its `effects` write a carrier of `i`) holds
at the logged world; `StartEndeG`: the same at a finished start frame.
Nothing at entries, nothing while a lock is held, nothing at a release,
nothing at a REASON return (`grund` is logged, but `InvAmOrtG` reads
`rueck` events only). This matches the model's own semantics: `rufAt`
checks owed invariants at value returns only, and assumes none at entry
(an invariant needed there belongs in `requires`).

*At entry: must NOT be demanded.* A caller that owes `i` may break it and
call a helper that owes `i` too (both hold every guard by signature,
`invarianten_gehalten`, U003); `breaking I { … }` is exactly such a region.
Invariants at entry are no consequence and should not be one.

*At every release of a guard: the right statement, and why it is not
cheap.* By U003 a frame that owes `i` holds every guard of every carrier of
`i` by signature, for its whole frame, and its caller holds them too
(`RufPasst.hh`). So a guard `L` of `i`'s carriers is released only by a
frame that took it in a `locks L` block and does NOT owe `i` (it could not
take a lock it holds); at that moment no owing frame is on the thread's
stack, nothing but owing frames writes `i`'s carriers, and no other thread
can (it would need `L`). The statement that follows is the table-invariant
twin of `SperrInvG`:

```lean
-- NAMED TARGET, not in Lean:
def InvRuheG (P) (M) : Prop :=
  ∀ i ∈ D.invs, (∀ c ∈ D.traeger i, D.braucht c ≠ []) →        -- guarded invariants only
    (∀ t L, (∃ c ∈ D.traeger i, .inl L ∈ D.braucht c) → L ∉ offen (M.faeden t).spur) →
    InvHaelt P i (M.speicher.welt [])                            -- at rest, it holds
```

It needs three things the theorem does not have: (1) a start premise
`∀ i, InvHaelt P i (sp.welt [])`; (2) the invariant at every REASON exit of
an owing frame -- see the finding below; (3) a machine invariant carried
by every rule ("for each thread holding a guard of `i` with no owing frame
on its stack, `i` holds in memory"), whose step classification has the size
of `sperrInvG_schritt` plus the reason pops. Estimated: several hundred
lines; not done in this round.

*Finding (reason returns; REPAIRED in §19.1, `ziel_ort_sperre_invGrund`).* `dokumente/SYNTAX.md` (lines 673-676, 1337,
1598 U006) says a function "owes `I` at every `return`". The model checks
owed invariants at VALUE returns only (`rufAt`: `.grund σ' r => .grund σ' r`;
`InvGutS` quantifies `EndAusgang.zurueck` only). So a function that owes
`i` may break it and leave by a reason; its caller (holding the guards)
handles the reason, a non-owing frame below releases the lock, and another
thread acquires it and sees `i` false -- with every premise of the flagship
met. Either the documented rule is wrong (reason returns owe nothing) or
the model is (they owe `i` too); the repair in the model is obligation +
conclusion as in §15.4 (`InvGutS` also over `EndAusgang.grund`, a reason
twin of `popS_inv`, `InvAmOrtG` also over `grund` events), without changing
`rufAt`. Not done here; no Lean probe of it yet.

### 18.6 Axiom record (full `lake build`, 183 jobs, green; `ki-pc-fisch-101`)

Every theorem named in §18 -- `Endblock.execH_passes`,
`Endblock.exec_passes`, `koerperGutS_alle`, `invGutS_alle`,
`rufAt_passes`, `wurzelFn_erreichbar`, `keinStartGrundG`,
`ziel_ort_ende_bei`, `ziel_ort_ende`, `ziel_ort_mehrfaden_ende`,
`ziel_ort_sperre_ende`, `ziel_ort_einfaden_ende`, `ziel_ort_mehrfaden`,
`fvP_koerper0`, `probeD_bei0_zertifiziert`, `probeD_nicht`,
`probeD_nicht_leer`, `fwP_nicht`, `probeD_halt`, `fwP_ende_verletzt`,
`ewP_koerper`, `ewP_zertifiziert`, `ziel_ort_ewig_zeuge`, `fertig_wert`,
`grP_koerper`, `grP_alt_zertifiziert`, `grP_fertig`, `grP_nicht`,
`grP_verletzt`, `mP_zertifiziert`, `mP_mehrfaden`, `sP_ende_zertifiziert`,
`gPB_ziel`, `gP_rufAt_passes`, `schlusssatz_104`,
`schlusssatz_104_zeuge`, `schlusssatz_104_maschine_zeuge`,
`schlusssatz_104_praemissen` -- depends on `propext`, `Classical.choice`,
`Quot.sound` (`schlusssatz_104_praemisse`: `propext`, `Quot.sound`). No
`sorry`, no new `axiom`, no `native_decide`.

### 18.7 What remains

- §18.5: invariants at releases (`InvRuheG`) and at reason returns (the latter done in §19.1).
- `StartOhneGrund`, `ohneEwigB` are decidable model facts without a Rust
  rule (as `fussMehrB`, `StufenM`, §16.6).
- Budget monotonicity (obligation at `n + 1` implies at `n`) is not proved;
  it is not needed (no budget is chosen), and "every budget `≥ B`" would be
  equivalent only with it.
- `schlusssatz_104`: the C side still at fixed call depths (no `CallAt`
  fuel monotonicity); A1/A2 outside Lean as named in §18.3; everything of
  PLAN §6 "What stays open".
- Time (waiting bound, termination, ops->cycles) and every implementation
  item of the verdicts: unchanged.

## 19. Invariants at reason returns; progress up to named stops (2026-09-14, two legs of `Ziel`)

`Zielsatz/Kern/Spec.lean` states the goal `GabbroZiel` as one statement; two of
its legs had no theorem in the model: `invGrund : InvAmGrundG P M` and
`fortschritt : FortschrittG P O passes M`. Both are proved here, against the
definitions of `Spec.lean` as they stand (no change to `Spec.lean`, none
needed). The proof of `GabbroZiel` itself is not attempted.

### 19.1 `InvAmGrundG` -- invariants at REASON returns (`ZielOrtInvGrund.lean`)

*The gap (§18.5, "Finding").* `InvGutS`/`InvAmOrtG` covered VALUE returns
only; a function owing `i` could break it, leave by a reason, and after the
release another thread saw `i` false with every premise met. Now closed as
obligation + conclusion, like §15.4:

```lean
-- Zielsatz/Kern/Spec.lean (unchanged):
def InvGutGrund (P) (passes) (Q) (S) (f) : Prop :=        -- per function, SEQUENTIAL
  ∀ O', RahmenO O' → RegLokal O' → AxVertragO Q O' → ∀ U, HavocOk S U →
    ∀ R, RespektiertRahmen P R → OhneVorbedingung R →
      ∀ σ ρ, ReqAmEintritt P f σ ρ →
        ∀ σ' (r : Fin (D.gruende f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = .grund σ' r →
            InvAmRueck P f σ'
def InvAmGrundG (P) (M) : Prop :=
  ∀ t ev, ev ∈ (M.faeden t).log → ∀ g rho r s0 s1, ev = .grund g rho r s0 s1 → InvAmRueck P g s1

-- ZielOrtInvGrund.lean:
theorem ziel_ort_sperre_invGrund … (premises of ziel_ort_sperre)
    (hIG : ∀ f, Zielsatz.InvGutGrund P passes Q S f) :
    ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M → Zielsatz.InvAmGrundG P M
theorem invAmGrundG_erreichbarL …   -- generic in the local carriers `lok`
theorem ziel_ort_mehrfaden_invGrund … (premises of ziel_ort_mehrfaden)
    (hIG : ∀ passes f, Zielsatz.InvGutGrund P passes Q S f) :
    ∀ passes M, RufErreichbarG … M → Zielsatz.InvAmGrundG P M
theorem ziel_ort_sperre_invAlle …   -- InvAmOrtG ∧ InvAmGrundG (value AND reason returns)
```

*The replay had to learn the reason channel first.* The frame results of
the replay (`ZErg`, `ZielOrtSem.lean`) knew a return, a `logik` outcome and
"anything else"; a reason exit of the frame's own function was "anything
else", so `KopfS` related no reason return of G to a sequential one. New in
`SperreSem.lean` §2a: `ZErgG` (= `ZErg` plus `grund σ r`) with `gleich`,
`folgt` and their lemmas (`folgt_grund` new), `zErgG` (keeps `grund`),
`zErgG_gleich_grund`. The lock-invariant replay (`weiterH`, `semH`, `KopfS`,
`WarteS`, `FortS`, `pushS_*`, `popS_*`, `akteurS`, …; files `SperreSem`,
`SperreBeweis`, `ZielOrtSperre`, `ZielOrtInv`) now predicts in `ZErgG`;
`weiterH` carries a reason through an `ende` node (it was `sonst`); new
`weiterH_grund`, `semH_rueckGrund`, `semH_rueckConsGrund`,
`semH_dannRetGrund`. Every theorem of the chain kept its statement (they
do not mention the result type); the older replays (`semZ`, `semV`, …) keep
`ZErg` untouched. Machine G is unchanged.

*Proof.* `popS_grund` (twin of `popS_inv`): the head's replay equation at a
reason head predicts `grund σ rg` (`semH_*Grund`), so the body's sequential
run under the recorded handlers ends in `grund σ'' rg` with `SG σ'' σ`;
`InvGutGrund` gives the owed invariants at `σ''`; their carriers are stable
at the return (`inv_stabil`: guards are signature locks, U003), where the
replay world agrees with the machine world, which is the world the pop logs
(`M.weltVon f`). `invGrundLog_schritt` classifies the three reason pops
(`rueckGrund`, `rueckConsGrund`, `dannRetGrund`); every other rule logs no
`grund` event. Induction over reachability as `ziel_ort_sperre_inv`.

*Witnesses (`ZielOrtInvGrundZeuge.lean`).* Declaration `igD` (as `ivD`,
§15.4): `setze() -> bool` declares one reason and leaves only by it; `haupt`
calls it through `let x = setze() else { r => … }` inside `breaking`.
* `igPschlecht` (`setze`: `konto[0] := 5; return R`) meets every premise of
  `ziel_ort_sperre_inv` (`igPschlecht_alt`: `setze` never returns a value,
  `InvGutS` holds vacuously), and on a machine reached in five steps the
  logged reason return of `setze` breaks `konto[0] == konto[1]`
  (`igPschlecht_verletzt`). The new obligation refutes it
  (`igPschlecht_nicht_invGutGrund`, from the zero memory: `5 ≠ 0`).
* `igPgut` (`setze`: both slots `5`, then the reason) meets every premise of
  `ziel_ort_sperre_invAlle` (`igPgut_zertifiziert`; the obligations proved
  per function, `igHaupt_fall` classifies the callee's answer), and on a
  machine reached in six steps the logged reason return meets the invariant
  BY THE THEOREM, at a world whose two slots hold `5` (`igGut_zeuge`).

### 19.2 `FortschrittG` -- progress up to named stops (`Fortschritt.lean`)

```lean
-- Zielsatz/Kern/Spec.lean (unchanged):
def FortschrittG (P) (O) (passes) (M) : Prop :=
  ∀ t, FertigG M t ∨ WartetG M t ∨ HaltBenannt O passes M t ∨ ∃ M', RufSchrittG P O passes M t M'

-- Fortschritt.lean:
theorem fortschrittG_aus (hO : GutO O) (hSt : StufenM P) (sp init)
    (hND : ∀ t, (offen (startSpur (init t).1)).Nodup)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hL : KeinLogikHaltG O passes M) :
    Zielsatz.FortschrittG P O passes M
theorem fortschrittG_sperre …     -- premises of ziel_ort_sperre + StufenM + hND
theorem fortschrittG_mehrfaden …  -- premises of ziel_ort_mehrfaden + StufenM + hND, every budget
theorem startSpur_nodup_leer …    -- hND from lock-free starts (AkzeptiertSpec.wurzeln, Ruhig)
```

No fragment restriction: `fortschrittG_aus` holds for EVERY program; the
flagship premises enter only through `KeinLogikHaltG` (a conjunct of `Ziel`
itself, proved by the flagships). `StufenM` and a duplicate-free start
trace give the rank side conditions of `locks` (`sperre_rang`); both follow
from `AkzeptiertSpec` + `StartZulaessig`.

*The case analysis* (`fortschritt_faden`, `fort_ende`, `fort_dann`,
`fort_abb`): for every head shape of a residue, either a rule of G fires
(the `w_*` builders of `RufAdaequatG`/`RufAdaequatRufG`; direct constructor
applications for `rufCallInd`, `dannCallInd`, `dannBindCallInd`,
`dannBindAxiom`) or a stop applies:
* finished: empty stack at `ret`/`retGrund` (`FertigG`, §13.5 item 7);
* waiting: `locks L` with `L` held by another thread (`WartetG`; the lock at
  the head is unique, `anSperre_kopf`); if no other thread holds it,
  `schritt_an_sperre` fires;
* named hardware stop (`HaltBenannt`): a leaf answering hardware (the only
  leaf outcomes are `ok`/`logik`/hardware, `blatt_fall`; axiom leaves extend
  the trace by accesses under `GutO`, `axiom_erw`), `bindAxiom` answer
  outside its type, register answer outside type/promise, invisible
  `awaits`, float out of range, `ewig a 0`;
* a `logik` stop is excluded by `KeinLogikHaltG` (loop invariants at
  `travNext`/`travDone`/`ewigWeiter`/`dannLeaveTrav`, `state` transitions).

*The three shapes with no rule and no stop, and the invariant that excludes
them* (`FortInvG`, carried through every rule by `fortInvG_schritt`, like
`schrittMerk`; `fortInvG_erreichbar`):
1. **The caller's shape at a pop (§13.5 item 6)** -- `FormKette`: every
   suspended frame `c` right below a frame of `g` satisfies `FormG c g`:
   `c` does not wait and `gruende g = 0` (pushed by `call`/`callInd`); or
   `c.rest = wartet restb k` with `erg g = some τ` and `gruende g = 0`
   (`bindCall`/`bindCallInd`); or `c.rest = wartetSonst n err restb k` with
   `erg g = some τ` and `gruende g = n` (`bindCallElse`). Pushes create
   exactly these, pops remove the top pair, head-local rules keep the
   function and the stack. At a value return this gives `PopArt`
   (`popArt_von`), at a reason return `PopGrund` (`popGrund_von`: a reason
   `r : Fin (gruende g)` excludes the first two shapes).
2. **An abrupt exit without a loop** -- `GRest.fOk`: an `ende` node never has
   the loop flag (`leave`/`next` there are ill-typed then); every
   loop-flagged continuation reaches a loop shim through `dann`/`schrumpf`/
   `frei`/`abbruch` layers (`GRest.absorb`, `nimmtAb`), so `leave`/`next`
   always meet `dannLeave*`/`dannNext*` or a peel rule.
3. **An `else` continuation that falls through** -- `abbruch k` has no rule:
   the block in front of an `abbruch` chain never ends normally
   (`Block.terminal`, `Endblock.alsBlock_terminal`), and no loop node,
   release marker or head is such a chain (`GRest.blockiert`).
The head is never waiting (`rufG_nie_wartend`), its holdings are held
(`rufG_haelt_statisch`).

*Witness (`FortschrittZeuge.lean`, `fortschritt_zeuge`).* On the two-writer
fixture of §16 (`mP`), at the machine where thread 0 holds the lock and
stands at the call of `setze` inside it and thread 1 stands at its `locks`:
`fortschrittG_aus` holds from the fixture's premises; thread 1 WAITS for the
lock thread 0 holds; thread 0 is neither finished nor waiting nor at a named
stop (`nicht_haltBenannt`: a call is no leaf), so the theorem gives it a
step; every idle thread is finished.

### 19.3 Axiom record (full `lake build`, 198 jobs, green; `ki-pc-fisch-101`)

`Endblock.alsBlock_terminal`, `startSpur_nodup_leer`, `igPgut_frag`,
`igPgut_fuss`: `propext`. `axiom_erw`: `propext`, `Quot.sound`. Every other
new theorem -- `popS_grund`, `invGrundLog_schritt`,
`ziel_ort_sperre_invGrund`, `invAmGrundG_erreichbarL`,
`ziel_ort_mehrfaden_invGrund`, `ziel_ort_sperre_invAlle`,
`invGutGrund_ohne`, `invGutGrund_ohneGrund`, `fortInvG_schritt`,
`fortInvG_erreichbar`, `blatt_fall`, `fort_abb`, `fort_ende`, `fort_dann`,
`fortschritt_faden`, `fortschrittG_aus`, `fortschrittG_sperre`,
`fortschrittG_mehrfaden`, `restHardware_kann`, `nicht_haltBenannt`,
`fortschritt_zeuge`, `igHaupt_fall`, `igPgut_koerper`, `igPschlecht_koerper`,
`igPgut_inv`, `igPschlecht_inv`, `igPgut_invGrund`, `igPgut_zertifiziert`,
`igPschlecht_alt`, `igPschlecht_nicht_invGutGrund`, `igVorlauf`,
`igPschlecht_verletzt`, `igGut_zeuge` -- `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, no new `axiom`, no `native_decide`.

### 19.4 What remains

- `GabbroZiel` itself: the legs `invGrund` and `fortschritt` now have
  theorems under the flagship premises; assembling `Ziel` from
  `AkzeptiertSpec` + `NutzerPflicht` + `HardwareAnnahmen` + `StartZulaessig`
  (the idle starts `Ruhig` against `StartExklusiv`/`fussMehrB`'s thread
  map, `e0 : Ereignis D` for the replay, `RennfreiBis` for unguarded
  carriers) is the next step and not done here.
- `InvRuheG` (§18.5: invariants at releases, at rest) is still only named;
  its second prerequisite (reason exits) is now available.
- `FortschrittG` classifies; it bounds nothing: no fairness, no waiting
  bound, no termination (PLAN §6, unchanged).

## 20. `gabbro_ziel : GabbroZiel` -- proved; the event `e0` removed (2026-09-14)

```lean
-- Zielsatz/Kern/Beweis.lean
theorem gabbro_ziel : GabbroZiel      -- propext, Classical.choice, Quot.sound
```

`Spec.lean` (the statement) and machine G are unchanged; no premise was
added. `ziel_aus` derives every leg of `Ziel` from the four premise groups
for any declaration, `gabbro_ziel` instantiates it with `P.mitRuhe` (as
§19.4 laid out). The former `gabbro_ziel_ereignis` (the goal under
`Nonempty (Ereignis D)`), `gabbro_ziel_teil`, `gabbro_ziel_leer` and
`ereignis_iff` are superseded and removed.

*The gap.* The lock-invariant replay (`KopfS`/`WarteS`) keyed every recorded
call answer (and axiom answer) one EVENT past its key world, so the record
stayed a function (`FunkV` via `KurzV`). A declaration with no table, no
global and no lock has no event; every world is one point (`welt_eq`), a key
is only (callee, parameters), and two calls of `g` with equal parameters
must be answered alike -- a determinism fact about G.

*The route (b/c): justified records instead of fresh keys.* In
`SperreBeweis.lean` §0b:
* `frischSpur D` -- the fresh trace piece: an event's `neutral` piece when
  one exists (classical choice), `[]` otherwise; `rahmenWeltF`, `axWeltF`
  replace `rahmenWelt e0`, `axWelt e0` in this replay (the older replays keep
  theirs).
* `Begruendet P O passes S` (inductive): the answer `a` to `g` at `κ, ρ` is
  what `g`'s body (`execEndH`, machine oracle, any move) ends in against
  every handler repeating a functional record of justified answers.
* `begruendet_eindeutig` (no event): two justified answers with one key are
  equal -- induction on the first justification; the union of both records
  is functional by the induction hypothesis, one handler (`rufAusV`) repeats
  it, both bodies end in the same outcome, worlds are one point. This IS
  the determinism, obtained from the replay rather than from the 70 rules.
* The three freshness fields of `KopfS`/`WarteS` became `KurzVB` (keys below
  the trace with an event; justified answers without one), `KurzAB` (the
  machine oracle's own answers without one: `PasstA O`), `KurzUB` (without
  an event there is no lock). Field count and order unchanged, so every
  destructuring pattern downstream stands.
* Steps: `popS_kopf` takes `hb : ¬ Nonempty (Ereignis D) → Begruendet …`,
  supplied at the nine pops of `akteurS` by `popS_begr_ok` (value) and
  `popS_begr_grund` (reason) from the returning head's replay; `fadenS_ax`
  takes `hxO` (the recorded answer is `O`'s), `rfl` at both callers;
  `funkV_appendB` joins the two cases.

`e0` is gone from `akteurS`, `zielInvS_schritt`, `zielInvS_erreichbar(L)`,
`ziel_ort_sperre(_fortschritt)`, `ziel_ort_ganz_aus_sperre`,
`ziel_ort_sperre_inv`, `…_invGrund`, `…_invAlle`,
`invAmGrundG_erreichbarL`, `ziel_ort_mehrfaden_invGrund`,
`ziel_ort_sperre_invL`, `ziel_ort_mehrfaden(_bei)`, `ziel_ort_*_ende(_bei)`,
`ziel_ort_einfaden`, `fortschrittG_sperre`, `fortschrittG_mehrfaden`,
`akzeptiert_mehrfaden`, and the witnesses' calls; the generator
`obligations_g.rs` and its output `GenOblig104.lean` drop it too (string
change only; the Rust test checks substrings that stay). The older replays
(`ziel_ort`, `ziel_ort_voll`, `ziel_ort_geraet`, `ziel_ort_rahmen`,
`ziel_ort_ganz`, `AuditZiel` F) keep `e0`; the rows "`e0` … load-bearing"
in §§11-18 describe those.

*Probes (`SpecProben.lean`, `Proben.lean`).* `Erfuellbar` now also asks that
every declared start runs on some thread (`∀ w ∈ wsRuhe ws, ∃ t, (init
t).1 = w`), and `probeB_erfuellbar`/`probeC_erfuellbar` fix `ws = [haupt]`:
the empty start list, or any list with the root on every thread, no longer
satisfies them. Re-proved (`zHaupt_laeuft`: thread 0 of `initRuhe [haupt]`);
`zweiFaeden_erfuellbar_gilt` re-proved with threads 0 and 1;
`gabbro_ziel_zeuge` now applies `gabbro_ziel`.

*Axioms (full `lake build`, 221 jobs, green, `ki-pc-fisch-101`).*
`gabbro_ziel`, `ziel_aus`, `begruendet_eindeutig`, `funkV_appendB`,
`popS_kopf`, `fadenS_ax`, `akteurS`, `ziel_ort_sperre`, every probe of
`Proben.lean`: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no
new `axiom`, no `native_decide`.

*What remains.* Review rounds (6) and (7) of PLAN §7 against `Spec.lean`;
the NOT-CLAIMED list of `Spec.lean` (termination, fairness, the C side,
weak memory beyond DRF-SC) is unchanged.

## 21. Liveness: a waiting bound under a FIFO lock and fairness (2026-09-15, KostenG TARGET 4)

PLAN-ZIELSATZ §8 (liveness): "waiting ≤ the sum of the `held` times of the threads ahead",
with a FIFO/ticket lock as a NAMED runtime assumption, and the number measured from the first
example. `FortschrittG` (§19.2) classified the stops; nothing bounded a wait.

### 21.1 The runtime assumption (`Lebendigkeit.lean`, one entry of the ONE list)

```lean
structure PlanLauf (P) (O) (passes) where     -- infinite; a stutter only where no thread can step
  M : Nat → RufMaschineG D;  akt : Nat → Option Faden
  schritt : ∀ n u, akt n = some u → RufSchrittG P O passes (M n) u (M (n + 1))
  stotter : ∀ n, akt n = none → M (n + 1) = M n ∧ ∀ u, ¬ Bereit P O passes (M n) u
def FifoSperre R := ∀ t u L a n, t ≠ u → (∀ j ∈ [a, n], AnSperre (R.M j) t L) →
    R.akt n = some u → AnSperre (R.M n) u L → ∀ j ∈ [a, n], AnSperre (R.M j) u L
def FairF R F := ∀ t n, (∀ j ∈ [n, n + F), Bereit P O passes (R.M j) t) →
    ∃ j ∈ [n, n + F), R.akt j = some t
def LaufzeitAnnahme R F := FifoSperre R ∧ FairF R F
```
FIFO: nobody overtakes a thread standing at `locks L` (a ticket lock; ties at the start are
free). Fairness: a thread runnable at `F` consecutive scheduler steps takes one (`F = 0` is
unsatisfiable). Also named, a hardware assumption: `HardwareImAbschnitt` -- no
`HaltBenannt` stop while a lock is held (an invisible `awaits`, a spent `forever` budget, a
device answer out of range inside a critical section).

### 21.2 The hold-time premise -- a premise, NOT derived

`Haltezeit R h k`: on every stretch on which `u` holds `L`, `u` takes at most `h L` own steps,
at most `k L` at a `locks` head. The checker's `held <= N ops` (`K002`) bounds OPERATIONS of
the block with callees at their declared costs; two bridges are missing: operations to G
steps (TARGET 3, F1-F9) and a potential bound for a `locks` body as a residue segment
(`frame_schritte_beschraenkt` bounds a frame from entry to return, not a block).

### 21.3 The theorem

```lean
wF 0 L = 0
wF (n+1) L = (|Ts L| - 1) * (h L * F + k L * wMaxH L (wF n) ls + F) + F
wartezeit ls Ts h k F L = wF ls.length L                  -- recursion over ranks

theorem wartezeit_schranke (hO : GutO O) (hSt : StufenM P) (sp init)
    (hLeer : ∀ t, D.haelt (init t).1 = []) (hls : ∀ L, L ∈ ls)
    (hr0 : RufErreichbarG P O passes (RufStartG P sp init) (R.M 0))
    (hL : ∀ n, KeinLogikHaltG O passes (R.M n))           -- Ziel.keinLogikHalt
    (hLZ : LaufzeitAnnahme R F) (hH : Haltezeit R h k) (hHw : HardwareImAbschnitt R)
    (hAnw : Anwaerter R Ts) (L t n0) (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + wartezeit ls Ts h k F L ∧ R.akt j = some t ∧
      L ∈ offen ((R.M (j + 1)).faeden t).spur
```
Proof (`wartezeit_kern`): per rank level (`gueltig`, induction on the fuel with
`hoeher_lt`); a holder's next own step comes within `F` or, at a nested `locks L'`
(`rang L < rang L'` by `sperre_rang`), within `W(L')` (`luecke`); so it releases within
`h·F + k·Wn` (`freigabe`); a free gap ends within `F` with the waiter's step or a new holder
who, by FIFO, stood at `locks L` since `n0` (`frei_luecke`); every thread ahead leaves the
set ahead for good (`warte_gehalten`, a strict count over `Ts L`). G facts: `sperre_schritt`
(a step at a `locks L` head takes `L`, only if free), `schritt_sperre_art`,
`nimmt_an_sperre`, `ende_ret_kein_schritt`, `abschnittAktiv_aus` (a holder can step or
stands at `locks`, from `fortschrittG_aus` + `fertig_leer` + `HardwareImAbschnitt`).

### 21.4 Witness and measurement

`LebendigkeitZeuge.lean`: a concrete 23-step run of the §16 fixture `mP`, every premise of
`wartezeit_schranke` discharged (`lZeuge`: FIFO, fairness `F = 4`, `h = 6`, `k = 0`, no
hardware stop in a section, contenders `[0, 1]`, `KeinLogikHaltG` from `mP_zertifiziert`);
`wartezeit = 32` (`lW_eq`, `decide`); thread 1 stands at `locks` from step 5 while thread 0
holds the lock at steps 6-11 and takes it at step 15 -- the theorem says before 37
(`wartezeit_zeuge`).

Measured on the corpus (`messung/WARTESCHRANKEN-2026-09-15.md` (retired report, in the history), by hand from the
declarations: `lean-g` carries no `held`): 28 programs declare `held`, 19 have an acquisition
point. Flat locks give `W/F = (c-1)(held+1)+1` own steps of the waiting thread (124/125 with
`concurrent` pairs: 102 and 66; 59 on 64 cores: 2,584). Two programs nest (05, 17): at
`c = F = 64` the outer bound is 823,096 and 165,376 own steps; a synthetic chain of depth 4
reaches 1.6·10⁹. Astronomical from three levels -- and a time-sliced `F` multiplies every row
by ~10⁷. The proposed shrink that removes the depth: **dominance** (an inner lock taken only
under the outer one has nobody ahead, nested wait ≤ `F`): 05 falls to 25,327, 17 to 2,647,
the depth-4 chain to 6,427.

### 21.5 Axiom record (full `lake build`, 223 jobs, green; `ki-pc-fisch-101`)

`sperre_schritt`, `schritt_sperre_art`, `wartezeit_kern`, `wartezeit_schranke`, `lLauf`,
`lZeuge`, `wartezeit_zeuge`: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no new
`axiom`, no `native_decide`. Machine G and `Spec.lean` unchanged.

### 21.6 What remains

- `Haltezeit` from `K002`: the ops-to-steps bridge and a residue-segment potential for a
  `locks` body.
- `Anwaerter` from `reachB` (the contenders are a run premise today).
- Dominance as a theorem variant (contenders of `L'` among threads not holding `L`), and the
  checker Bool that decides it.
- Reader (`locks shared`) acquisition: G has no reader mode (10, 13 are outside).
- Into `Spec.lean`: `LaufzeitAnnahme` and `HardwareImAbschnitt` belong in the header's ONE
  assumption list, and a leg `wartezeit` in `Ziel` over `PlanLauf` -- a reviewed diff of
  `Spec.lean`, not done here.

## 22. `GabbroZiel` repaired: one program, an owned start, payloads in the race leg (2026-09-15)

The third independent Opus verdict (`dokumente/PROOF.md`) found that the STATEMENT was
not the goal yet, and the Muse verdict (gap 7) found the same class. This section is a reviewed
diff of `Spec.lean`, re-proved. Machine G's rules are unchanged.

### 22.1 The statement, old and new

```lean
-- OLD (master 4fc0f538)
def GabbroZiel : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (ws : List D.Fn),
    C.akzeptiert P S fs.1 ls.1 cs.1 ws = true →
    NutzerPflicht P S Q →
    ∀ O : Orakel D, HardwareAnnahmen O Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe) (init : …),
      StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs.1) (wsRuhe ws) sp init →
      ∀ M, RufErreichbarG P.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M →
        Ziel P.mitRuhe S.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M

-- NEW
def GabbroZiel : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflicht E →                                           -- (b) the user, on E
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe) (init : …),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ M, RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M →
        Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M
```

New definitions (`Spec.lean`):
```lean
structure Einheit D where P : Programm D; S : SperrInv D; Q : AxEns D
  starts : List (Σ w : D.Fn, Env D (D.params w)); sp0 : Speicher D
def Einheit.ws E := E.starts.map (·.1)
def LogikPflicht P S Q := (∀ passes f, KoerperGutS … ∧ InvGutS … ∧ InvGutGrund …) ∧
  SperrInvLokal S ∧ AxEnsLokal Q                    -- the old `NutzerPflicht P S Q`
structure StartPflicht E where
  sperren : ∀ L, E.S.inv L E.sp0 = true
  req : ∀ a ∈ E.starts, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2
structure NutzerPflicht E where logik : LogikPflicht E.P E.S E.Q; start : StartPflicht E
structure Laufzeit E sp init where
  lader : sp = speicherR E.sp0
  start : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, init t = ⟨some a.1, envR a.2⟩
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → (init t).1 = none
```
Changed: `Pruefer.akzeptiert : Einheit D → List D.Fn → List D.Lock → List carriers → Bool`
(soundness into `AkzeptiertSpec E.P E.S fs.1 E.ws`); `AkzeptiertSpec` gains `einzeln :
ws.Nodup` and `renn` loses `¬ PaarungAusgenommen c`; `RennfreiBis` loses
`¬ PaarungAusgenommen c`. `StartZulaessig` stays as the proof's notion and is no longer a
premise.

### 22.2 The three repairs

**P1 (decisive): the start conditions have an owner.** `invariant false` on any lock emptied
every body obligation (`∀ U, HavocOk S U → …`, no member) and every start (`sperren`), so probe
A (`ensures false` everywhere) went through the concrete checker. `StartZulaessig.req` and
`.sperren` belonged to no premise group. Now `StartPflicht` is part of (b), over the memory
and arguments the program DECLARES, and the loader that establishes that memory is (d)
`Laufzeit.lader`.
* `probeA_falsch_inv_nicht` -- probe A with `sFalsch` (`invariant false`) refutes (b), for
  every `Q`, `starts`, `sp0`; `p1_akzeptiert` -- the checker's Bool ACCEPTS that program, so
  the refusal is (b)'s.
* `unerfuellbar_widerlegt` -- any program whose lock family no memory satisfies refutes (b).
* `havocOk_bewohnt` -- under (b) the move class is inhabited (`havocOk_misch_lokal`,
  SperreSem.lean: only the locality half of `SperrInvOk` is needed).
* `start_req_widerlegt` -- a declared start whose `requires` fails at `E.sp0` refutes (b).
* `NutzerWiderlegt P := ∀ E, E.P = P → ¬ NutzerPflicht E` -- the probe refutations
  (`probeA_`, `probeD_`, `probeD_wahr_`, `tabelle_widerlegt_gilt`) hold with NO side condition
  on the lock family any more (before: guarded carriers and "some memory satisfies it").
  `paP_nicht_sperre`, `probeD_nicht`, `fwP_nicht` now take only the locality half.

**P2: `ws`, `S`, `Q` are the program's.** They are fields of `E`; the checker computes on
`E.ws`, the hardware assumption names `E.Q`, and (d) lets a thread run only a declared start
with its declared arguments, or the root.
* `laufzeit_nur_erklaert` -- a user function runs on a thread only if it is in `E.ws`.
* `akD_kein_zweiter_schreiber` -- in ANY program over `akD` the checker accepts, no runtime
  start runs both writers `a` and `b` (they would both be declared, and are then refused).
* `akP3_ohne_starts` -- the same code DECLARING no start is accepted, and the statement then
  speaks about the root on every thread and nothing else (`laufzeit_ohne_starts`).
* `laufzeit_initRuhe`/`laufzeit_voll` -- the runtime's exact start (`initRuhe E.starts`: the
  declared starts on threads `0..k-1`, the root elsewhere) meets (d) whenever the starts are
  distinct, which the checker now demands (`einzeln`, Bool `einzelnB`). Without it
  `concurrent { f, f }` would run `f` on two threads, escape `renn` (it separates DIFFERENT
  starts), and not be covered.
* `laufzeit_ruhe` -- the root on every thread from `E.sp0` meets (d): the run class is never
  empty.

**P3: payloads are in the race leg.** The exemption is dropped from `RennfreiBis` and from
`renn` (`ausgenommenB` = guarded or `atomic`; `paarungB` removed). Why no separate pairing
conjunct: a payload one start reads (footprint) and another writes is already refused by
`fuss` (`ungeschuetzt_abgelehnt_gilt`); a guarded payload is lock-ordered by
`rennfrei_g_voll`; so the only case the exemption hid was two starts WRITING one unguarded
payload -- a C11 race on a non-atomic object, which `H013` refuses too. That case is now
refused (`zwei_schreiber_abgelehnt` without the payload clause), and `rennfreiBis_of` proves
the leg for every non-atomic carrier directly (`rennfrei_g_voll` / `rennfrei_ungeschuetzt`).
NAMED price: the publish/await hand-off of an UNGUARDED payload across threads is refused by
the checker, not covered.

### 22.3 The proof

`startZulaessig_aus` (Beweis.lean) derives `StartZulaessig E.P.mitRuhe E.S.mitRuhe (fsRuhe fs)
(wsRuhe E.ws) sp init` from `StartPflicht E` and `Laufzeit E sp init` (root: `ruhig_mitRuhe`,
`requires true`; declared start: `req_mitRuhe_iff`; invariants: `speicherZ_speicherR`).
`gabbro_ziel` then runs the old chain: `akzeptiertSpec_mitRuhe` (now also `einzeln`),
`logikPflicht_mitRuhe` (renamed), `hardware_mitRuhe`, `ziel_aus` (hypothesis `LogikPflicht`).

### 22.4 Header additions (external review, PLAN-ZIELSATZ §5)

`Spec.lean`'s header now has (1) WHAT `Ziel` ADDS OVER `NutzerPflicht`, leg by leg:
`speicherSicher`, `rennfrei`, `sperrInv` (in shared memory), `keineVerklemmung`,
`fortschritt` are not in (b); `vertrag`, `invRueck`, `invGrund`, `keinLogikHalt`,
`startEnde`, `keinStartGrund` are (b)'s sequential clauses carried to interleaved G (for a
single-threaded lock-free program nearly a restatement); `zeit` holds for every program of G
with no premise and is weak. (2) THE ONE ASSUMPTION LIST with one sentence per entry on why
it is hardware/runtime: `GutO` (foreign bodies), `RegLokal` (the device), `AxVertragO E.Q`
(foreign/device contracts, false = a false named assumption), `Laufzeit.lader` (loader),
`Laufzeit.start`/`.einmal` (thread creation). `RegLokal` is NAMED as stronger than
hardware: `register_ohne_traeger_konstant` (Proben.lean) proves a register without declared
carriers is constant in every world; a device-driven value must come through an axiom.
Not repaired: the replay (`regLies_gleich`) needs the answer to be a function of shared
carriers. Also named now: stack depth, one thread per busy start, and that the exporter fills
neither `starts` nor `sp0` nor the source `requires` today.

### 22.5 Axiom record (full `lake build`, 225 jobs, green; `ki-pc-fisch-101`)

`gabbro_ziel`, `ziel_aus`, `startZulaessig_aus`, `laufzeit_initRuhe`, `laufzeit_voll`,
`laufzeit_nur_erklaert`, `laufzeit_ohne_starts`, `laufzeit_ruhe`, every theorem of
`Proben.lean` (`gabbro_ziel_zeuge`, `probeA_widerlegt_gilt`, `probeA_falsch_inv_nicht`,
`unerfuellbar_widerlegt`, `havocOk_bewohnt`, `start_req_widerlegt`, `probeD_widerlegt_gilt`,
`probeD_wahr_widerlegt_gilt`, `tabelle_widerlegt_gilt`, `ungeschuetzt_abgelehnt_gilt`,
`zwei_schreiber_abgelehnt_gilt`, `akD_kein_zweiter_schreiber`, `akP3_ohne_starts`,
`zweiFaeden_erfuellbar_gilt`, `zweiFaeden_bewegt_gilt`, `probeB/C_erfuellbar_gilt`,
`probeB/C_erfuellbar_haupt`): `propext`, `Classical.choice`, `Quot.sound`. `p1_akzeptiert`
and `register_ohne_traeger_konstant`: `propext`. No `sorry`, no new `axiom`, no
`native_decide`.

### 22.6 What remains

- The exporter (`lean_g.rs`) must produce an `Einheit`: `concurrent` as `starts` (with
  arguments), the initializers as `sp0`, the source `requires` (today `.wahr`). Until then the
  covered programs are hand-written terms.
- The Rust checker computes neither `einzeln` nor the payload-inclusive `renn` as one Bool
  (`H013` is stricter per entry; whether `concurrent { f, f }` is refused was not checked).
- `RegLokal` for volatile registers (a per-read oracle answer would need a change to the
  replay, not to G's rules).
- The liveness entries of §21 (`LaufzeitAnnahme`, `HardwareImAbschnitt`) are not yet in the
  ONE list or in `Ziel`.

## 23. `GabbroZiel`, fourth round: floats are the user's logic, no wait cycle, the stops by kind (2026-09-15)

The fourth independent Opus verdict (`dokumente/PROOF.md`) found `GabbroZiel` to be
the goal with named gaps, one of them NOT named: F1. This section is a reviewed diff of
`Spec.lean` (and, for F1, of the sequential semantics), re-proved. Machine G's rules are
unchanged.

### 23.1 F1 (decisive): an out-of-range float is `logik bereich`, not `hardware ieee`

A float result outside its declared range ended a body in `Hardware.ieee` for EVERY oracle:
the kernel IEEE model (`gleitRechne`) decides it from the program's values. `KoerperGutS`
constrains only returns and `logik` outcomes, so probe A behind the literal `2.0` declared in
`0 .. 1` met (b), passed the concrete checker with `haupt` declared and running, and
`gabbro_ziel` certified it.

**Repair, in the model.** `Logik` gains `bereich`; `execBlock` (Semantik.lean) and
`execBlockH` (SperreSem.lean) answer `.logik .bereich` where `gleit`, `gleitLit`, `gleitVon`
fail `gleitPasst` (6 lines; `gleitNarrow` keeps its `else`). `Hardware.ieee` stays as a
constructor and is no longer produced. **Why this and not a clause `≠ hardware ieee` in
(b):** the range is the program's logic as a `state` pre-state is (`logik vorzustand`), so
the existing clause "no `logik` outcome" of `KoerperGutS` covers it without a new
obligation shape; and the replay already carries `logik` outcomes to the machine, so the
CONCLUSION gains it as well. A new clause over `hardware ieee` would have left the
conclusion's stop list untouched: `ZErgG` reads every hardware outcome as `sonst`, so the
replay could not have carried it.

* `BereichG M t` (Fortschritt.lean): at a head `gleit`/`gleitLit`/`gleitVon` the result is
  in range at the thread's world. `fadenS_bereich`: from the replay (`kopfS_keineLogik'`) --
  a failing check would make the head predict `logik bereich` at the replay's world (the
  operands read stable carriers). `bereichG_erreichbarL`/`bereichG_mehrfaden`: on every
  reachable machine. `fortschrittG_aus` takes it as a hypothesis; `FortschrittG` lists no
  float stop any more.
* Carried: `logikFrei` (a float literal is logic-free iff it is in range, `gleit`/`gleitVon`
  are not), `logikR` (`bereich ↦ bereich`), `GleitZeuge` (the two range witnesses now show
  `logik bereich`), `CFormenF`/`CFormenFZeuge` (the Gabbro side of `gsem_gleit*`,
  `klemmen_corr`: the equation's `none` branch). No C-side statement changed: a failure
  outcome carries no correspondence duty, before and after.
* Refuted: `probeF1_widerlegt_gilt` (Proben.lean) -- every program with the code `f1P`
  (`SpecProben.lean`: probe A's contracts, the crash `if true { let x = 2.0 in 0 .. 1; }` in
  front of every body) fails (b); `f1_lauf`: every body ends in `logik bereich` for every
  oracle, handler and budget; `f1_akzeptiert`: the checker's Bool ACCEPTS `f1P`, so the
  refusal is (b)'s.

### 23.2 F2: no wait cycle

`keineVerklemmung` said only that not EVERY unfinished thread waits. New leg of `Ziel`:

```lean
def WartetAuf M t u L := AnSperre M t L ∧ L ∈ offen (M.faeden u).spur
def KeinWarteZyklus M := ∀ n (ts : Nat → Faden) (Ls : Nat → D.Lock),
  (∀ i, i ≤ n → WartetAuf M (ts i) (ts (i + 1)) (Ls i)) → ts (n + 1) ≠ ts 0
structure Ziel … where … keinZyklus : KeinWarteZyklus M …
```

`kein_warteZyklusG` (Beweis.lean): along a chain the ranks rise strictly (`sperre_rang`),
and the closing link gives `rang L₀ ≤ rang Lₙ < rang L₀`.

### 23.3 F3: the stops by kind, each in the ONE list

```lean
inductive HaltArt | hardware | flagge | budget
def KopfHalt O passes σ ρ : HaltArt → Block … → Prop   -- leaf / axiom / register; awaits
def RestHalt O passes σ ρ : HaltArt → GRest … → Prop   -- + `.ewig _ 0` (budget)
def HaltBenannt O passes M (k : HaltArt) t : Prop
def FortschrittG P O passes M := ∀ t, FertigG M t ∨ WartetG M t ∨
  HaltBenannt O passes M .flagge t ∨ HaltBenannt O passes M .budget t ∨
  HaltBenannt O passes M .hardware t ∨ ∃ M', RufSchrittG P O passes M t M'
```

Before: one `HaltBenannt` over `KopfHardware`/`RestHardware` covering axiom and register
answers, `awaits`, `gleit*` and the budget, all called "hardware". In the ONE list of the
Spec header, each class with its reason: `hardware` = axiom answer outside its type
(foreign code), register outside its type or against its declared promise (the device);
`flagge` = an `awaits` whose flag is not visible -- a WAIT (not yet published / A10 / never
published), and why the never-published case is NOT made an obligation: (d) covers runs with
any subset of the declared starts, and G has no "later", so it is liveness, not claimed;
`budget` = a model artefact (every `passes` is quantified). And next to progress: a thread at
any stop while holding `L` leaves every thread needing `L` waiting forever, with every leg of
`Ziel` true.

### 23.4 Header corrections

`speicherSicher` needs only `GutO` (no checker, no user proof); "`Q := false` empties (c)"
holds for axioms WITHOUT a result -- with a result, (c) keeps oracles whose answers never fit
the type, and every call stops at `hardware`.

### 23.5 Carried outside `Zielsatz/`

`Fortschritt.lean` (`FortFaden` six-way, `fort_hw`/`fort_flagge`/`fort_budget`, the three
float cases closed by `BereichG`), `FortschrittZeuge.lean` (`restHalt_kann`, per kind),
`Lebendigkeit.lean` (`HardwareImAbschnitt` over every kind; `abschnittAktiv_aus` and
`wartezeit_schranke` take `BereichG` along the run), `LebendigkeitZeuge.lean` (per kind, and
`BereichG` from `bereichG_mehrfaden`).

### 23.6 Axiom record

Full `lake build` from the changed `Syntax.lean` up, 226 jobs, green, 19 min 44 s on
`ki-pc-fisch-101` (`~/gabbro-muse/opus-f123/`); no `sorryAx` anywhere in the log.
`gabbro_ziel`, `ziel_aus`, `kein_warteZyklusG`, `probeF1_widerlegt_gilt`, `f1_lauf`,
`fadenS_bereich`, `bereichG_erreichbarL`, `bereichG_mehrfaden`, `fortschrittG_aus`,
`fortschrittG_sperre`, `fortschrittG_mehrfaden`, `restHalt_kann`, `fortschritt_zeuge`,
`wartezeit_schranke`, `wartezeit_zeuge`, `lZeuge`, `gabbro_ziel_zeuge`, `klemmen_corr`,
`gsem_gleit`, `lauf01_ueber03`, `laufDurchNull`, `logikFrei_keineLogik`: `propext`,
`Classical.choice`, `Quot.sound`. `f1_akzeptiert`, `f1_lit_ausser`, `p1_akzeptiert`:
`propext`. No `sorry`, no new `axiom`, no `native_decide`.

### 23.7 What remains

- The `flagge` wait's end, and the never-published flag, are not covered (liveness).
- A stop inside a critical section leaves the lock's waiters waiting forever (named).
- `SYNTAX.md` (the outcome table and the float row) and `FLOATING-POINT.md` name `logik bereich`
  now; `dokumente/SYNTAX.md` and `dokumente/PLAN-TRANSLATION-VALIDATION.md` still say `hardware ieee` (the C runtime
  check `gabbro_hardware(IEEE)` is unchanged and is now a check the user proved passes).
- Everything named in §22.6.

## 24. G1: every type has a decoding, and an empty answer type is a call that does not return (2026-09-15)

The round-5 confirmation review found one more stop the MODEL decided and filed as hardware
(G1, the class of F1). This section is a reviewed diff of `Spec.lean` (`KopfHalt`, `HaltArt`,
`FortschrittG`, the ONE list; `GabbroZiel`, `Ziel` and every premise unchanged) and of the
sequential semantics' decoding, re-proved.

### 24.1 The finding

`einpassen` (Semantik.lean) holds a raw machine answer against the declared type. It answered
`none` for EVERY raw word of `.sum` (a `tagged` result, the `ok | reason` of a syscall), `.fl`
(a float) and `.fnptr` (a function pointer). Every call of an axiom with such a result ended in
`hardware (annahme a)`, every read of such a register in `hardware (register r)`, for EVERY
oracle. `KoerperGutS` does not constrain hardware outcomes, `AxVertragO` was vacuous for such
axioms, and probe A (`ensures false`) behind one such call met (b), passed the checker and
was certified by `gabbro_ziel`. It contradicted SYNTAX.md §12.1 ("`einpassen` holds the raw
answer against it") and the Spec header's justification of the hardware class ("an ill-typed
answer is the foreign code breaking its declaration" -- there was no well-typed one).

### 24.2 The decodings (Semantik.lean)

* **`.sum cs` -- `summePasst`.** The emitter lays a `tagged` value out as
  `struct { T_marke marke; union { … } last; }` (`emit.rs`, `markiert`): the case number as a C
  `enum` (cases numbered `0, 1, …` in declaration order) and the payload of that case (no
  member for a bare case). The ONE raw word is that pair packed **mixed-radix, case number in
  the low digit: `roh = marke + |cases| * last`**, so `marke = roh % |cases|`,
  `last = roh / |cases|` (Euclidean). The packing is a bijection `Int ≅ Fin |cases| × Int`, so
  every value of the `tagged` type has exactly one raw word (`summeRoh`, `summePasst_voll`); a
  bare case must carry `0` (whatever the C union holds there), a payload case a number in its
  range (`nutzPasst`). A syscall's
  `ok value | reason r` is such a sum; the generated errno decoding (`dekodiere`,
  Syscall.lean) is the emitted C that forms the pair, and an errno outside the table has no
  pair -- `hardware (annahme a)`, the kernel outside its contract (SYNTAX.md §12.1).
* **`.fl lo hi` -- `gleitWortPasst`.** The word is the IEEE-754 binary64 bit pattern
  (`0 <= roh < 2^64`, `Gleitkomma.ausBits`, the inverse of `zuBits` on well-formed triples),
  held against the range exactly like a computed float (`gleitPasst`: finite, inside). `Ty.fl`
  carries no width and the model computes binary64 (FLOATING-POINT.md §7), so an `f32` register is
  read as its binary64 value -- the same named cut. Every well-formed value in range is the
  decoding of its bits (`gleitWortPasst_voll`); every decoded value is well-formed
  (`gleitWortPasst_wf`).
* **`.fnptr m` -- `zeigerPasst`.** The word is a code address; the LOADED IMAGE names the
  function there -- a new oracle field `Orakel.zeiger : Int → Option D.Fn` (default: no
  function anywhere) -- and its signature number is checked against the declared `m`. Why the
  oracle and not the declaration: which address a function has is the linker's and loader's;
  a declared table would have to be the real layout (an unnamed assumption), while an oracle
  field is quantified in (b) like every answer, so the user's proof holds for every layout.
  Every function of signature `m` is the answer of some image (`zeigerPasst_voll`).
* `.never` has no value, hence no answer; `.int`, `.bool`, `.opt`, `.grund`, `.ptr` unchanged.

**Proved (EinpassenVoll.lean).** `einpassen_voll`: every value of every type (floats:
well-formed, `WertOk`) is the decoding of some raw word under some image;
`einpassen_wertOk`: every decoded value is such a value; hence **`antwortLeer_iff`**: the
answer class of `τ` is empty (`AntwortLeer`, no raw word decodes under any image) EXACTLY when
`τ` has no such value -- the model refuses no answer the declared type admits.
`antwortLeer_never`, `antwortLeer_grund0`, `antwortLeer_int_leer` name the empties;
`antwortLeer_keinErg`: an axiom without a result always answers.

### 24.3 `never` and the empty types: a named "does not return" stop

A call whose declared answer type is empty cannot return: there is no answer, and "the
machine answered outside the type" has no content. Decision: **its continuation is
unreachable, the obligation still covers everything before it, and the stop is named** --
`HaltArt.nieZurueck`, with `KopfHalt .nieZurueck` at an axiom (or register) head whose type is
`AntwortLeer`; `KopfHalt .hardware` there now requires `¬ AntwortLeer`, so the two kinds
partition the head's failures; `FortschrittG` lists the new kind (`fort_nie`, Fortschritt.lean,
by `by_cases` on `AntwortLeer` at the three heads). Why not "only in tail position": for
`-> never` the non-return IS the declaration -- the emitter writes `_Noreturn` on the
prototype (`emit.rs`, `Noreturn`), so the code after the call is unreachable in the C exactly
as in G; and every outcome before the call (a `logik` outcome, a failed callee `requires`) is
an outcome of the body, which `KoerperGutS` excludes. What stays vacuous is only the
unreachable continuation and the function's own `ensures` -- partial correctness, as for a
body that recurses forever. A foreign `never` body that returns breaks its declaration: a
foreign-code fact like every entry of (c), named in the ONE list. Another empty type (`.grund 0`,
an empty range) is the declaration making the call unanswerable, visible in the declaration
like `Q := false`. No fragment refusal was added: the exporter emits no axiom today
(`lean_g.rs`: `aerg := fun e => nomatch e`), and a refusal would have been a new checker
obligation, where the named stop is a statement.

**Superseded in part by §25 (W1):** the reason "unreachable in the C" holds for `-> never` only;
every other empty answer type is now REFUSED by the checker, and `nieZurueck` is an axiom
`-> never` alone.

### 24.4 The G1 probes, refuted (Zielsatz/Kern/ProbenG1.lean)

`g1D`: no table, global or lock; `haupt`; axiom `holen() -> ok (0 .. 10) | err` writing
nothing; register `temp : f64 in 0 .. 1` without device carriers.
`g1PA` = `if true { let x = holen(); } return;`, `g1PR` = `if true { let t = temp; } return;`,
both under `ensures false`; both pass the concrete checker (`g1PA_akzeptiert`,
`g1PR_akzeptiert`), so a refusal is (b)'s.

* **The oracle can answer:** `g1_holen_antwortet` -- for a declared ensures holding at some
  answer, an oracle meets ALL of (c) (`GutO`, `RegLokal`, `AxVertragO`) and its answer to
  `holen` FITS (`summeRoh`); `g1_temp_antwortet` -- an oracle meets (c) for every declared
  ensures, and `temp` answers `0.5` (`0x3FE0000000000000`, decoded by the kernel,
  `g1_temp_wort`); `g1_nicht_leer`: neither type is empty.
* **The program relying on a false `ensures` is refuted:** `g1PA_widerlegt` -- no program with
  the code `g1PA` meets (b), whenever the declared ensures of `holen` holds at SOME answer
  (if at none, `AxVertragO` admits only oracles whose answers never fit: that is `Q := false`,
  the visible false named assumption of the ONE list); `g1PR_widerlegt` (`NutzerWiderlegt`) --
  for every program with that code, whatever its lock family, ensures, starts, memory.
* **The contrast:** `g1_never_leer` -- an axiom returning `never` has an empty answer class.

### 24.5 The sweep: every outcome the model could decide independently of the oracle

Checked, per source of a non-`ok` outcome in `execStmt`/`execBlock` (Semantik.lean) and
`execStmtH`/`execBlockH` (SperreSem.lean), with the kind G reports:

| source | who decides | status |
|---|---|---|
| `bindAxiom`, answer does not decode (`Hardware.annahme`) | the oracle, for an answerable type (`einpassen_voll`); the declaration, for an empty type | REPAIRED (G1): `hardware` resp. `nieZurueck` |
| `axiomCall` (no result) | never fails: `einpassenErg _ none _ = some ()` | checked, dead branch (`antwortLeer_keinErg`) |
| `regLies`/`regLiesElse`, answer does not decode (`Hardware.register`) | as `bindAxiom` | REPAIRED (G1) |
| `regLies`, answer against `requires` (`Hardware.geraet`) | oracle answer AND the declared promise `D.rzusage`; a promise false at every value is visible in the declaration | named (ONE list), unchanged |
| `awaits`, flag not visible (`Hardware.sichtbarkeit`) | the oracle (`sichtbar`); `RegLokal` leaves `true` admissible | `flagge`, named, unchanged |
| `forever` budget spent (`Hardware.fortschritt`) | the budget, quantified in (b) and in `GabbroZiel` | `budget`, a model artefact, named |
| float out of range (`Logik.bereich`, was `Hardware.ieee`) | the program's own values | F1, the user's logic |
| a call whose callee returns `never` (`bindCall`, `bindCallInd`) | the handler has no `ok` answer, so the caller's continuation is unreachable; in G the callee frame runs and nothing is filed at the caller | checked: sound, no stop filed |
| `regSchreib`, `transition`, `publish`, `exchange` | no failure outcome (the raw write `roh` is `Unit` to the model) | checked |
| `callInd` through a `fnptr` value | the value IS a function of the signature (`Val`) | checked, no stop |
| `einpassen` for `.opt`, `.bool`, `.ptr`, `.int`, `.grund` | every value decodes (`einpassen_voll`) | checked |

The only remaining model-decided failures are the EMPTY answer types, and `antwortLeer_iff`
says they are exactly the types without a value -- named `nieZurueck`.

### 24.6 Carried

Every `einpassen`/`einpassenErg` site takes the image (`O.zeiger`; mechanical, in every file that names it);
`VertragA` takes it (the recorded answers decode with the machine's image); `GleichRS` gains
`ZeigerGleich O O'` and `orakelAus` copies the image, so the replays (`ZielOrtRahmen`,
`ZielOrtGeraet`, `SperreBeweis`/`ZielOrtSperre`) use it at the axiom and register steps; the
two older replays (`ZielOrtVollBeweis`/`ZielOrtVoll`, `ZielOrtAxBeweis`/`ZielOrtAx`) quantify
over sequential oracles with the machine's image (`ZeigerGleich O O'` in `KopfV`/`WarteV`,
`KopfA`/`WarteA`, which now take the machine oracle `O`). The idle root:
`Orakel.mitRuhe` maps the image, `Orakel.zurueck` drops the root; `zurueck_mitRuhe` (an
EQUALITY of oracles) no longer holds -- an oracle of `D.mitRuhe` may place the root at an
address -- and is replaced by `OrakelRu`/`orakelRu_zurueck`: every oracle of `D.mitRuhe`
ANSWERS like one of `D` (the root has signature `0`, which no translated `fnptr` type names,
`einpassen_ru`); `execStmtH_ru`/`execEndH_ru`/`rumpfH_mitRuhe` (MitRuheSperre.lean) are stated
for any such `O'`. `Fortschritt.lean` (`FortFaden` seven-way, `fort_nie`),
`FortschrittZeuge.lean`, `Lebendigkeit.lean` (`abschnittAktiv_aus`): one more stop kind.

### 24.7 Axiom record

CLEAN `lake build` (the build directory set aside first), 228 jobs, green, 19 min 51 s on
`ki-pc-fisch-101` (`~/gabbro-muse/opus-g1/`); no `sorryAx` anywhere in the log.
`gabbro_ziel`, `gabbro_ziel_zeuge`, `probeF1_widerlegt_gilt`, `fortschrittG_aus`,
`koerperGutS_mitRuhe`, `orakelRu_zurueck`, `g1PA_widerlegt`, `g1PR_widerlegt`: `propext`,
`Classical.choice`, `Quot.sound`. `einpassen_voll`, `antwortLeer_iff`, `summePasst_voll`,
`gleitWortPasst_voll`, `g1_holen_antwortet`, `g1_temp_antwortet`, `g1_nicht_leer`: `propext`,
`Quot.sound`. `g1PA_akzeptiert`, `g1PR_akzeptiert`: `propext`. No `sorry`, no new `axiom`, no
`native_decide`; the three facts of the decoded `0.5` (`g1HalbW`) are `decide +kernel`
(kernel evaluation, no native code) -- the elaborator's `rfl` ran out of recursion depth.

### 24.8 What remains

- **C side, not repaired:** `encW` (CSpeicher.lean) gives `.sum`, `.fl`, `.fnptr` register
  cells no integer encoding and `tyFits` refuses them, so `regLies_step` (CFormenH.lean) covers
  no register of those types -- the named CUT is unchanged. And for `option index into T` the
  emitter's `T_NONE` sentinel is `n` (`encOpt none = n`), which `einpassen` decodes as
  `hardware` (it reads `none` from a NEGATIVE word): `regLies_step`'s premises are
  unsatisfiable for a `none` answer, so the C-side lemma is vacuous there. A register of
  option type is not in the fragment's corpus; aligning `einpassen` with `encOpt` is one line
  and a re-proof of `einpassen_ru`, left open.
- `roh` (a value as a raw word for a register WRITE) is not the inverse of `einpassen` for
  sums (the case number only), floats (truncation, the old `Float` model's) and pointers (`0`);
  the model's `regSchreib` answers `Unit`, so no outcome depends on it.
- The exporter emits no axiom and no register of the G1 types; `GabbroZiel`'s programs with
  such axioms are reached by hand-written terms (as before, §22.6).
- Everything named in §23.7.

## 25. W1: the checker refuses an empty answer type other than `never` (2026-09-15)

Both round-6 reviews (dokumente/PROOF.md §3, dokumente/PROOF.md) confirmed "the
goal with named gaps -- no unnamed gap found" and reproduced one escape. This section is a
reviewed diff: `AkzeptiertSpec` gains the field `antworten`, `KopfHalt .nieZurueck` is
narrowed; `GabbroZiel` and every other premise are unchanged.

**The finding.** §24.3 named every empty declared answer type as `nieZurueck`, with the reason
"the continuation is unreachable in the C as in G". That holds only for an axiom `-> never`
(`_Noreturn` prototype). An axiom returning `.grund 0`, an empty range, a sum without a value
or `fn(sig n)` with no function of signature `n` has an ordinary prototype: the C call returns
and the continuation runs, covered by nothing; a register read never "does not return".
Probe A behind `let p = hol();` with `hol() -> fn(sig 5)` met (b), passed the checker and was
certified (the reviewers' `n_ziel`).

**The repair (option (ii) of the verdict).** A new checker component, `antworten`:
* `Block.ants` & co. (AntwortOrte.lean) collect a body's answer sites -- `bindAxiom` and
  `axiomCall` (`inl a`), `regLies` and `regLiesElse` (`inr r`); `StelleOk`: the site is an
  axiom whose declared result is `never`, or its declared answer type is not `AntwortLeer`.
* `antwortenB` (Zielsatz/Kern/Akzeptiert.lean) is the Bool, part of `Akzeptiert`;
  `antwortenB_iff` proves it decides the field exactly. Emptiness is decided by `antwortB`
  (EinpassenVoll.lean, `antwortB_iff`, through `antwortLeer_iff`): range bounds, reason count,
  sum cases, `fnptr n` over the enumerated function list, and a float range by three
  candidate witnesses (the rounded bounds and `+0`) -- complete because the kernel IEEE order
  is transitive on finite values (`flt_trans_endlich`).
* G continues only with sub-blocks of the bodies: `GRest.aR`, kept by every rule
  (`schrittAnt`, the twin of `schrittOrte`), gives `antInvG_erreichbar` -- every frame's residue
  on every reachable machine has admissible sites when every body has (`kopf_ants`).
* `fort_dann` (Fortschritt.lean) uses it at the head: an empty axiom type is `never`, an empty
  register type cannot occur. So `KopfHalt .nieZurueck` now holds ONLY at an axiom whose
  declared result is `never`; the register cases are gone. `fortschrittG_aus`,
  `fortschrittG_sperre`, `fortschrittG_mehrfaden`, `abschnittAktiv_aus`,
  `wartezeit_schranke` take the component; `ziel_aus` passes `hA.antworten`, transferred to
  `P.mitRuhe` by `akzeptiertSpec_mitRuhe` (`rumpf_mitRuhe_ants`, `antwortLeer_mitRuhe`,
  `stelleOk_mitRuhe`, Zielsatz/Faeden/Ruhe.lean).

**Corrected sentences (Spec.lean).** The ONE list's `nieZurueck` entry is now "a call of an
axiom whose declared result is `never` -- the call does not return ... The continuation is
unreachable in the C as in G", which is true; the escape is removed from the list and named as
refused. The (c) entry reads "for an `E.Q` satisfiable at a DECODABLE value (for a float: a
well-formed one, `WertOk`)". NOT CLAIMED names linking of separately compiled units
(PLAN-ZIELSATZ §10).

**Refuted (Zielsatz/Kern/ProbenW1.lean).** `w1_spec_nicht`: no lock family, function list or start
list makes the round-6 probe meet `AkzeptiertSpec`; `w1_abgelehnt`: `akzeptiert_pruefer`
refuses every program with its code; `w1_bool`/`w1_sonst_alles`: computed, the Bool is
`false` and every other component is `true`, so the refusal is `antwortenB`'s alone. The same
for an empty register range (`w1r_spec_nicht`, `w1r_bool`) and `.grund 0` (`w1g_bool`). The
contrast: behind an axiom `-> never` the code is accepted (`w1v_bool`) and the head is
`nieZurueck` (`w1v_kopf`); at `hol()` it is not (`w1_kein_nie`). Every earlier probe that
used `decide` on `Akzeptiert` (G1 float register included) still computes `true`.

**Axioms.** `gabbro_ziel`, `schrittAnt`, `antInvG_erreichbar`, `antwortB_iff`,
`w1_abgelehnt`: `propext`, `Classical.choice`, `Quot.sound`; `flt_trans_endlich`,
`gleitBarB_iff`: `propext`, `Quot.sound`; `w1_bool`, `w1v_bool`: `propext`. No `sorry`, no new
`axiom`, no `native_decide`. `lake build` on `ki-pc-fisch-101` (`~/gabbro-muse/opus-w1/`): 230 jobs,
green (a full rebuild, Semantik.lean docstrings changed), no `sorryAx` in the log.

## 26. Stage (b): the concurrent closing theorem for `beispiele/124` (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the stage-(b) concurrent closing theorem for the emitted C of `beispiele/124` (`Schlusssatz124`, `CNebenlaeufig`, `Korpus124` simulation). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 27. The closing theorem, stage (a), generic: `schlusssatz`; chain count 2 (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the generic closing theorem `schlusssatz` over the C correspondence chain (`Kette src`, `korrOk`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. The generic Lean translation pipeline `uebersetzeAllg` it contained moved to `Parser/Elab/UebersetzePipeline.lean`.

## 28. `korrOk` widened to its own lemma stock — 23 arms, chain count unchanged (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the widening of the correspondence certificate checker `korrOk` to 23 arms. The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 29. A2 discharged: a Lean parser for the emitted C subset (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the Lean parser for the emitted C subset (`CLexer`, `CParse`, `CText104`, `CText108`) that discharged assumption A2. The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 30. `korrOk` gets its BLOCK structure: `if`, `let` of a call, `traverse` (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the block structure of `korrOk` (`if`, `let` of a call, `traverse`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 31. O13 closed -- the chain source pinned as characters, the pipeline unfolded at a variable  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the pinning of the chain source as characters and the pipeline unfolded at a variable character list. The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. The generic part, `uebersetzeAllg_von_zeichen` and `except_ok_get`, lives in `Parser/Elab/UebersetzePipeline.lean`; the two corpus units are `Korpus/Programme/Einheit104.lean` and `Einheit108.lean`.

## 32. The runtime's ticket lock: a named premise becomes a theorem (2026-09-15)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the C runtime's ticket lock as a theorem (`CTicket`, `Schlusssatz124Ticket`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 33. `alloc` and `reset` get a form in the specification -- as sugar, not as constructors

*Added 2026-09-15 (Opus lane `alloc`). File: `Grammatik/Bausteine/Arena/ArenaZucker.lean` (new), imported by
`Grammatik.lean`. Rust: `crates/gabbro-check/src/lean_g.rs` (the arena refusal by name).
Report: `messung/muse/OPUS-BERICHT-ALLOC.md` (retired report, in the history). Ledger: `TODO.md` O14.*

**The finding** (`messung/muse/OPUS-BERICHT-GRAMMATIK-EMIT.md` (retired report, in the history) §2.2/§5.3): `let i = alloc A (v)
[else …];` and `reset A;` are accepted with zero diagnostics, emit C, that C compiles -- and
`Syntax.lean` had no `Stmt` constructor for either, so no program using them could ever close a
correspondence chain.

**The answer is a DERIVED form, and the reason is a measurement.** `Stmt` has 26 constructors;
30 Lean files carry 252 occurrences of the single leaf `retGrund` and 79 files name
`assignSlot`. Two new constructors would move every exhaustive match in the semantics, the
machine, race freedom, deadlock, progress, cost, the invariant families and non-interference --
and an arena would be a NEW CARRIER, so `World` would grow a field and every frame lemma with
it. **Sugar costs none of that**: an arena program is an ordinary `Block` term, so
`theorem gabbro_ziel` covers it with no new case. The shape is the emitter's own: a table of
`count = hi` slots beside a global `used` counter.

| Definition / theorem | What it says |
|---|---|
| `ArenaForm D` | what a declaration must carry: `tab` (the slots, `count tab` = the hard bound), `feld`, `zaehl` (the `used` global at `int 0 (count tab)`), `hpos : 0 < count tab`. The reservation `lo` is deliberately NOT here -- it is the checker's static count (`N212`) |
| `ArenaForm.stand A σ` | the used count, read out of a world |
| `Stmt.arenaReset` | `reset A;` = `Stmt.assignGlob zaehl 0` |
| `Block.arenaAlloc` | `let i = alloc A (v) else B;` = `Block.narrow` on the counter into `0 ..< hi` (else `B`), then `Stmt.assignSlot` at `i`, then `Stmt.assignGlob` of `i + 1` |
| `arenaReset_stand` | after `reset` the counter is `0` |
| `arenaBump_stand` | the bump raises the counter by exactly one |
| `arenaAlloc_unter_schranke` | **below the hard bound the `else` is NOT taken**, and the index bound is the old counter -- *the syntactic half of `Arena.alloc_innerhalb_reserve`, and the reason the surface form may omit the branch* |
| `arenaAlloc_an_schranke` | at the hard bound the `else` IS taken |
| `arenaAlloc_gdw_modell` | the syntax succeeds exactly when `Arena.alloc` returns `some` -- the bridge to `Arena.lean` |
| `arenaAlloc_bump_modell` | a successful step bumps the same number by one on both sides |
| `eval_umTyp`, `orte_umTyp`, `Wert.umTyp_hin_her` | the three transport lemmas, each by `subst` -- the casts are confined to two definitions |

**ZEUGE** (`namespace ArenaZeuge`, non-degenerate: four slots, a byte element type, BOTH
branches exercised): `ZD` is a concrete declaration, `Log : ArenaForm ZD`,
`welt c` a world whose counter stands at `c`. `zeuge_leer_unter` (counter 0 < 4),
`zeuge_voll_an` (counter 4 = 4), `zeuge_reset`, `zeuge_alloc_leer` (the body runs, index 0),
`zeuge_alloc_voll` (the `else` runs).

**Axioms: the standard three** for every theorem in the file, and
`#print axioms gabbro_ziel` is unchanged (`propext`, `Classical.choice`, `Quot.sound`). The
whole library builds: 250 jobs, exit 0. No `sorry`, no `native_decide`, no new `axiom`.

**What is NOT claimed, and is booked as O14:** `gabbro lean-g` still refuses an arena
declaration -- now BY NAME, naming this file and the repair, instead of through a catch-all --
so no arena program closes a chain yet. The form exists; the export does not.

## 34. The transfer chain CLOSED on two real programs -- the user's duty, proved, over the exported unit

*Added 2026-09-15 (Opus lane `pflicht`). Files: `Grammatik/Korpus/Programme/GenOblig104.lean` (REGENERATED),
`Grammatik/Korpus/Referenz/Pflicht104.lean` (migrated), `Grammatik/Korpus/Programme/GenOblig108.lean` (new, generated),
`Grammatik/Korpus/Referenz/Pflicht108.lean` (new), imported by `Grammatik.lean`. Guardian:
retired `pruefe-genlean`. Report: `messung/muse/OPUS-BERICHT-PFLICHT.md` (retired report, in the history).*

**What was missing.** Lane 198 made `gabbro lean-g` produce a full `Zielsatz.Einheit gE` and
`gabbro obligations --g` state `def nutzerPflicht := Zielsatz.NutzerPflicht gE` beside the
per-program theorem `gP_gabbro` (derived from `gabbro_ziel`, checker premise `by decide`, the
user's duty an open hypothesis). Nothing proved that hypothesis: `GenOblig104.lean` still held
the PRE-`Einheit` obligation form, and `Pflicht104.lean` proved duties over names
(`pflicht`/`pflichtInv`/`startPflicht`/`gP_ziel`) the exporter no longer writes.

**Both obligation files are now the exporter's own output, and the duty is proved for both.**

| Conjunct of `NutzerPflicht E` (`Zielsatz/Kern/Spec.lean`) | 104 | 108 |
|---|---|---|
| `logik.1` `KoerperGutS` at EVERY budget | `oblig_koerper` (`koerperGutS_ohne` + `koerperGutS_alle`; `einzahlen` by frame reasoning, `lies` by `KoerperGutV`) | `p108_koerper` (both bodies a single `return <slot>`) |
| `logik.1` `InvGutS` | `oblig_inv` (`invGutS_leer`, `gD.invs = []`) | `p108_inv` (same) |
| `logik.1` `InvGutGrund` | `oblig_invGrund` (`invGutGrund_ohneGrund`, no reasons) | `p108_invGrund` (same) |
| `logik.2` `SperrInvLokal S` | `oblig_S_lokal` (lock `M`, invariant `fun _ => true`) | `p108_S_lokal` (no lock exists) |
| `logik.3` `AxEnsLokal Q` | `oblig_ax_lokal` = `axEnsLokal_wahr` | `p108_ax_lokal` (same) |
| `start.sperren` | `oblig_start_sperren` | `p108_start_sperren` |
| `start.req` | `oblig_start_req` -- **VACUOUS**, `gE.starts = []` | `p108_start_req` -- **two declared starts**, `requires` `true` at `gSp0` |

**The closing theorems** are `oblig_ziel` and `p108_ziel`: `Zielsatz.Ziel` at every reachable
machine, with the exporter's `gP_gabbro` applied and all three of its premises discharged here
-- the duty (above), `Zielsatz.HardwareAnnahmen` (this declaration has no axiom, register or
global) and A4 `Zielsatz.Laufzeit` (`laufzeit_initRuhe`, the runtime's own start).

**ZEUGEN.** 104: `oblig_ruf_bewegt` (`einzahlen(k,0,7)` from `gSp0` ends `ok` and moves the
slot `0 -> 100`) and `oblig_ens_faellt` (the exported `ensures` FAILS on a world that lowers
the slot -- a duty no world can break would say nothing). 108: `p108_starts_laufen` (thread 0
runs `read_a`, thread 1 runs `read_c`), `p108_starts_zwei` (the two starts are two different
functions) and `p108_ruf_liest` (the readers answer slot 0 and slot 1 of the shared table).

**The one finding, and it is about the SOURCE and not repaired by weakening the duty:**
104 declares no `concurrent` and no `entry`, so the exporter writes `starts := []`, and
`Zielsatz.Laufzeit gE sp init` then admits ONLY assignments in which every thread runs the
idle root. `oblig_ziel` is therefore true about an IDLE machine. That is faithful -- 104
declares no thread -- but it means the concurrency legs of `Ziel` (`rennfrei`, no deadlock,
`KeinWarteZyklus`) carry no weight on 104. They carry weight on 108, which is why both are
here. *`beispiele/124` is not a third candidate: it does not export at all (`LG004`).*

**Axioms: the standard three** for every theorem in both files, and `#print axioms
gabbro_ziel` is unchanged. The whole library builds: 254 jobs, exit 0. No `sorry`, no
`native_decide`, no new `axiom`.

**The guardian (retired 2026-10-17, see git history; not guarded today).** `pruefe-genlean` re-ran `gabbro lean-g` / `gabbro
obligations --g` on every COMMITTED generated Lean file and compared the WHOLE FILE byte for
byte. It found its work by the generator's own first line (`-- GENERATED by \`gabbro …\``),
so there is no second register beside the tree. Measured: 2 of 2 files byte-identical, 18 582
bytes; and red on a single changed byte, green again after restoring.


## 35. Part 4's condition, halved: a certified program cannot end a call in a HARDWARE outcome  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the `schlusssatz` clauses 4b-4d (a `korrOk`-certified program cannot end a call in a HARDWARE outcome). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. The generic results stay: `Logik/Ruf/Ohne/RufOhneHardware.lean` (`hardwareFrei`, `rufAt_ohneHardware`) with its witness `RufOhneHardwareZeuge.lean`.

## 36. The handler congruence, and part 4's `logik` condition reduced to ONE frame fact  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the handler congruence as a clause of `schlusssatz` (clause 4e). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. The generic results stay: `Logik/Ruf/RufLogik.lean` (`rufAt_tiefer`, `rufAt_stabil_ab`, `rufAt_nurAbstieg`) and `HandlerKongruenz.lean`, with the witnesses `RufLogikZeuge.lean` on the units 104 and 108.

## 37. A chain for a program that touches a DEVICE: `korrOk` carries the register  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded a C chain for a program that touches a DEVICE (`korrOk` carried the register file; `KorrespondenzGeraetZeuge`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 38. The frame at every world: `rufAt` is in `RespektiertRahmen`, and part 4's condition is the depth alone  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the frame at every world as a clause of `schlusssatz` (clause 4e(ii)). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. The generic result stays: `rufAt_rahmenTreu` and `rufAt_nurAbstieg` in `Logik/Ruf/RufLogik.lean`, witnessed by `nurAbstieg_zeuge_104`/`_108` in `RufLogikZeuge.lean`.

## 39. The checked clone handoff: `stack`, `child`, and the (d)/(d2) premises (2026-09-18)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the checked clone handoff for the emitted C (`CloneHandoff`, `klon_ziel`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 40. Integer `match`: coverage denoted in Lean, refused in Rust (lane 228; fix lane F1, 2026-09-21)

**File:** `grammatik/Grammatik/Kern/Semantik/GanzzahlMatch.lean` (lane 228, corrected by fix lane F1 after
review G07 F3). **Rust:** `crates/gabbro-check/src/intmatch.rs` (`N411`-`N414`, called from
`m1.rs`).

| Theorem | What it says | Tied to |
|---|---|---|
| `trifft_mem_armKeys` | an arm matches a value iff the value is one of its `case` labels | the arm shapes of lane 222 (`IntPat`) |
| `trifft_wahl_some`, `wahl_none_weigert` | first-match dispatch over `fallListe` finds an arm iff some arm matches | `fallListe` (one label per covered value, as lane 227 writes) |
| `erschoepfendB_richtig` | the Bool check decides `erschoepfend m lo hi` | -- |
| `erschoepfend_ohne_default` | covered, no default: every value in range dispatches | the rule `N411` enforces |
| `match_exhaustive_zeuge` | witness: values `0`/`100` read from the reference fixture dispatch to arms 0/1, and the arms cover the scrutinee's range | reference fixture `ReferenzB` |

**What is NOT claimed.**

- The Rust checker does not run `erschoepfendB`. `N411` decides the same predicate by an
  interval sweep over M1's range of the scrutinee; the agreement is by reading.
- The earlier conjuncts about the fixture's reached run (`refB_erreicht`, `refB_schreibt`) were
  dropped: the fixture program has no `match`, so they were decorative (G07 F3). (The tie of
  `fallListe` to the C `switch` the emitter wrote, `swFaelle`/`sw_erschoepfend_trifft`, was removed
  with the C backend.)
- That the scrutinee's value lies in `lo .. hi` is a premise; in Rust it is M1's range,
  exactly as sound as every M1 index check.

**Axioms:** the standard ones; `#print axioms gabbro_ziel` unchanged.

## 41. Dynamic arenas: the past-ceiling stop over a run, and reset reuse (lanes 241/243; fix lane F2, 2026-09-21)

**Files:** `grammatik/Grammatik/Bausteine/Arena/ArenaDyn.lean` (lane 241, reworked by fix lane F2 after review
G08 F4), `grammatik/Grammatik/Bausteine/Arena/ArenaReset.lean` (lane 243, CUTS corrected after G08 F2).
**Rust:** `crates/gabbro-check/src/arena.rs` (`N426` against the whole-run upper bound, `N211`
across calls and parameters). **Runtime:** `laufzeit/arena_dyn.c` (`gabbro_arena_grow`).

| Theorem | What it says | Tied to |
|---|---|---|
| `dynGrow_isSome`, `dynGrow_ueber_M` | one commit succeeds iff the bumped prefix stays within `M` | the runtime's ceiling test, by name |
| `dynGrow1_gdw_alloc` | a one-slot commit agrees with `Arena.alloc` on `Kap ⟨hi, M⟩` | `Arena.lean` (`alloc_erfolg`/`alloc_fehlschlag`) |
| `dynGrowListe_gelingt` | a run's commit sequence whose total fits the room above the prefix never reaches the stop, and ends at prefix + total | the rule `N426` enforces since fix lane F2 (upper bound of the total) |
| `dynGrowListe_scheitert` | a commit sequence whose total passes the room reaches the stop, in any order | why a per-path LOWER bound was not enough |
| `dynGrowListe_gelingt_zeuge`, `_scheitert_zeuge`, `_zwilling` | `8, 8` under `max 24` reaches `24`; under `max 16` each commit fits alone and the run stops | the `paesse.rs` twins and gifts 1133/1135 |
| `reset_alloc_rumpf_zeuge` et al. (`ArenaReset.lean`) | after `reset` the next `alloc` runs its body at index `0` | `ArenaZucker.lean` sugar |

**What is NOT claimed.**

- No refinement: `DynArena` is a Nat record carrying `c <= M` as a field. The former
  `dynVerfein` (membership restating that field) and `region_verpflichtet` (tied to a run only
  through a premise its witness discharged without the run) were removed, not renamed.
- Nothing links `DynArena` to the Rust accounting or to the C by proof: the checker's per-path
  upper bound and `dynGrowListe`'s sum agree by reading. The run model the checker assumes
  (call-graph roots entered once per load) is not stated in `Spec.lean` (`TODO.md` O20).
- The PLAN §9 work (`DynForm`, the four Block-form theorems, the simulation) and the two
  `Spec.lean` (d) assumption texts do not exist (review G08 F5; `TODO.md` wave D note).
- `ArenaReset.lean`'s "no handle outlives a reset" holds in the sugar only; in the surface
  language `N211` holds it along one thread of control, not against a concurrent `reset`.

**Axioms:** `propext`, `Quot.sound` (the list theorems and witnesses); `#print axioms
gabbro_ziel` unchanged.

## 42. Gate contracts split: the caller's precondition and the hardware's ensures (lane 233; fix lane F5, 2026-09-22)

**File:** `grammatik/Grammatik/Logik/Ruf/FremdRuf.lean` §9 (lane 233's fixture, section added by fix lane
F5 after reviews G04 F2 and G10 F5). **Rust:** `crates/gabbro-check/src/rahmenlaenge.rs`,
`m1.rs` (`transfer_bound_at_call`, `N463`), `syscall.rs` (`buffer_bound`, `N464`); `beispiele/149`
(`path_nul_terminated`), `beispiele/150`.

| Theorem | What it says | Tied to |
|---|---|---|
| `axVertragOP_of_O` | the restricted premise (ensures only at calls meeting the gate's precondition) is weaker than `AxVertragO` | premise (c) of `gabbro_ziel` |
| `fremdruf_gate_gilt_pre` | at a call that meets the caller's obligation, the restricted premise gives the fitting answer's ensures and the gate's frame | the `V` obligation `gabbro obligations` counts at every gate call with `requires` |
| `mitVorbedingung_gleich` | the re-dressed oracle answers every well-formed call exactly as the machine's oracle | -- |
| `hardware_aus_vertragP` | frame, register locality and the restricted premise, plus raw words outside every declared result type, give the FULL `HardwareAnnahmen` for the re-dressed oracle | `Zielsatz.HardwareAnnahmen` (unchanged) |
| `fdObad_vertragP`, `fdObad_nicht_voll`, `fdPflicht_verletzt` | an oracle that answers garbage to an ill-formed read (a descriptor it never handed out) meets the restricted premise and breaks the full one; the ill-formed call breaks the caller's obligation | the reviewers' point: a caller bug is the caller's, not the hardware's |
| `fremdruf_gate_gilt_pre_zeuge`, `hardware_aus_vertragP_zeuge` | all premises jointly on the fixture, with the bad oracle, the precondition false elsewhere, and the open gate's terminator precondition held before and broken after its own marker write | non-degeneracy |

`fdQ` for the open gate no longer promises a nonzero descriptor (fd 0 is valid); it promises
the gate's own marker in the answer world (`fdO_open_marke`).

**What is NOT claimed.** `Spec.lean` is unchanged: premise (c) still quantifies over every
argument. No run-level theorem says that a run whose gate calls all meet their preconditions
is the same run under the two oracles; no exporter builds `AxPre` from a gate's `requires`;
a result-less gate has no raw word outside its type, so the bridge does not reach it; and the
fixture's preconditions (a terminator slot, the handed-out descriptor) are analogs of
`path_nul_terminated` and `len <= lenof(buf)`, not those clauses (`TODO.md` O23).

**Axioms:** `propext`, `Quot.sound` (section 9); `#print axioms gabbro_ziel` unchanged.

## 43. Bounded strings: the value model the checker's length rules rest on (lane 256; fix lane F6, 2026-09-22)

**File:** `grammatik/Grammatik/Bausteine/Zeichenfolge/ZeichenfolgeGebunden.lean` (lane 256's value model; the
theorems below `bkopie` added by fix lane F6 after review G12 F4/F6). **Rust:**
`crates/gabbro-check/src/zeichenfolge.rs` (`N453`-`N455`, `N465`); gifts 1118-1127,
1159-1168; `crates/gabbro-check/tests/zeichenfolge.rs`.

| Theorem | What it says | Tied to |
|---|---|---|
| `bconcat_laenge`, `bconcat_ablehnt` | a concat within the target max has the summed length; past it, `none` | `N453` |
| `bconcat_max_summe` | if the MAXES sum to at most the target max, the exact concat succeeds with the summed length | `N453`'s max-sum rule is sound (it over-approximates) |
| `bkopie_max`, `bkopie_kuerzer_scheitert` | a copy from max `m` into max `tmax >= m` succeeds and keeps the characters; a full `string max 8` does not copy into `string max 2` | `N455` (a string past its slot) |
| `bindex_innen`, `bindex_aussen` | an index below the length reads the element; at or past it, `none` | `N454` |
| `bindex_max_beweist_nichts` | an empty `string max 8` refuses index 7, though `7 < 8` | why `N454` demands a length fact (`gift/1125`, checker-clean before F6) |
| `bindex_geschuetzt`, `bindex_mindestlaenge` | `k < blaenge s`, or `n <= blaenge s` with `k < n`, gives a character | the guard forms `N454` accepts (`gift/1159`) |
| `bounded_string_zeuge` | on non-empty, distinct strings: `"hi" + "!" = "hi!"` at max 8, index 2 reads `'!'` under `2 < blaenge`, the same index is refused on the empty string, `"hi!"` copies into max 8 and not into max 2 | non-degeneracy (the earlier reference-machine conjunct was decorative, review G12 F6, and is gone) |

**What is NOT claimed.** No theorem says the Rust pass implements these rules: the link is
the gifts and the test pins, not a proof. The model has no representation (no NUL, no length
word), no literal surface, no strings in aggregates, and no upper limit on `max`
(`TODO.md` O24). No string program reaches Lean export.

**Axioms:** at most `propext` (`vergl_refl` also `Classical.choice`, `Quot.sound`); the file
imports nothing (it moved from `CBackend/Semantik/` to `Bausteine/Zeichenfolge/` on 2026-10-18, with `ZeichenfolgeZelle.lean`, restated over `BString`). `#print axioms gabbro_ziel` unchanged.

## 44. Nested arrays: the emitted read `A[i][j]` is the flat read at `i * N + j` (lane 205; fix lane F8, 2026-09-22)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded `CFormNested.lean` (the emitted C read `ld (idx (idx p i M (N*es)) j N es)` equals the flat read). It existed and lives in the tag `archiv/c-emitter-2026-10-17`. The flattening itself stays in `Nebenlaeufigkeit/Allgemein/Verschachtelt.lean` (`flach_*`, `nestIdx`, §17.3).

## 45. The stage-(b) simulation certificate for 124: the relation read from the certificate (lane 206; fix lane F8, 2026-09-22)  -- removed (C backend)

Removed on 2026-10-18 with the C backend: this section recorded the stage-(b) simulation-certificate checker for 124 (`SimPruef`). The C line existed and lives in the tag `archiv/c-emitter-2026-10-17`; nothing here is evidence of the present tree. 

## 46. Divergence of accepted never-bodies, and `KeinLogikHaltG` at the spin (lane 231; fix lane F8, 2026-09-22)

**File:** `grammatik/Grammatik/Zielsatz/Eigenschaften/Divergenz.lean` (on `NeverAsm.lean`,
`RufMaschineF.lean`, `ZielOrtGanz.lean`).

| Theorem | What it says | Tied to |
|---|---|---|
| `foreverLauf_noexit` | an exit-free step and a true guard make `foreverLauf` answer `hardware (fortschritt a)` at every fuel | the named `progress` assumption (`on_exceeded`) |
| `forever_noexit_divergiert`, `forever_noexit_kein_logik`, `forever_noexit_kein_zurueck`, `forever_leer_divergiert` | a `forever` with `NoExit` body and `InvWahr` invariant diverges as declared: never `logik`, never a return | lane 225's accepted `never-forever` shape |
| `asm_never_antwort_leer`, `asm_never_kein_ok` | a `-> never` axiom fits no answer and never continues | the axiom's reading "the asm never returns" -- an ASSUMPTION about the C lowering (review G10 F2; the C side is G04's `for(;;)` after the asm) |
| `spin_prueft` | a thread at ANY head of the empty spin `forever a invariant true {}` (`SpinKopf`: `.ewig`, the unfolded empty body, `ewigRest`) passes every clause of `PrueftG` | the per-thread content of `KeinLogikHaltG` (ZielOrtGanz.lean) |
| `ret_prueft` | a thread at a bare `return` head passes every clause of `PrueftG` | the other threads of the witness |
| `ewig_wahr_schreitet` | the `.ewig` head at budget `n + 1` with guard `true` and empty body takes its G step (`ewigWeiter`) | one step, one head shape |
| `ewig_spin_zeuge` | a REACHED G machine (two steps from `RufStartG`) with thread 0 at `.ewig () 1 .wahr .nil k`: `KeinLogikHaltG` holds for the whole machine, and thread 0 steps on | the G-machine witness review G10 F3 asked for |
| `bindAxiom_kein_blatt` | a `bindAxiom` head is no leaf head (vacuous discrimination; renamed from `nieZurueck_blatt_frei`) | nothing never-specific |
| `divergent_body_zeuge` | all divergence premises jointly on `divD`/`divP`, at loop budget 3 (budget 0 was vacuous, review G10 F1), with an F-machine run writing `konto[0]` `0 -> 100` | non-degeneracy |

**What is NOT claimed.** The spin facts are per head: no theorem shows that a thread stays
in `SpinKopf` along its steps, and only the empty body with guard `.wahr` is covered; a
`forever` with a real body or invariant meets `KeinLogikHaltG` through the general route
(`KeineLogik`), not through this file. `KeinLogikHaltG` is shown for one reached machine, not
for every reachable one. Nothing in Lean ties the never-axiom to its C lowering.
`Spec.lean` is untouched.

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` at most; `#print axioms gabbro_ziel`
unchanged.

## 47. Worker pools in the goal theorem: `einzeln := EinzelnPool`, legs proved (fix lane F10, 2026-09-22)

**A reviewed `Spec.lean` diff** (review G06 F1, OFFEN O18, Simon 2026-09-21: "switch the Spec
to PoolSicher and prove the legs"). The text of `GabbroZiel` and of `Ziel` is unchanged.

| Premise | Before | After |
|---|---|---|
| (a) `AkzeptiertSpec.einzeln` | `ws.Nodup` | `EinzelnPool P fs ws`: every routine declared twice (`Mehrfach ws w`, `[w, w] <+ ws`) is `PoolSicherW` |
| (a) `Getrennt` (inside `fuss`) | pairs `w₁ ≠ w₂` | pairs `w₁ ≠ w₂ ∨ Mehrfach ws w₁` -- start OCCURRENCES |
| (d) `Laufzeit.einmal` | two threads never run one declared start | ... unless the program declares it at least twice |
| proof's `StartZulaessig.einmal` | `Ruhig` | `Ruhig ∨ Mehrfach ws` |

**Files:** `Zielsatz/Kern/Spec.lean` (the diff, header "WHAT CHANGED ON 2026-09-22"),
`Zielsatz/Kern/Akzeptiert.lean` (component, proof changes), `Zielsatz/Faeden/Ruhe.lean` (mitRuhe transfer,
runtime start), `Zielsatz/Kern/Beweis.lean` (`startZulaessig_aus`), `Zielsatz/Faeden/PoolSym.lean`
(never-weakened statements), `Zielsatz/Faeden/PoolZeuge.lean` (witnesses).

| Theorem | What it says |
|---|---|
| `mehrfach_filter`, `mehrfachB_iff`, `nicht_mehrfach_of_nodup` | "declared twice" as a sublist, as a filter count, decided; impossible on distinct starts |
| `poolSicherWB_iff`, `einzelnPoolB_iff` | the component decides `EinzelnPool` exactly (moved from PoolSym into `Akzeptiert.lean`) |
| `getrenntW_iff` | the footprint test decides the OCCURRENCE form of `Getrennt` |
| `getrenntK_of`, `schreibGetrenntK_of` | the only two places distinctness entered the proof: a same-routine thread pair now comes from `Mehrfach`; footprints from the occurrence form of `Getrennt`, writes from pool safety (a pool graph writes no unguarded, non-atomic carrier) |
| `einzelnPool_mitRuhe`, `mehrfach_map_inj`, `mehrfach_of_getElem?` | transfer to `P.mitRuhe`; two positions with one routine make it `Mehrfach` |
| `laufzeit_initRuhe` | the runtime's exact start meets (d) with NO side condition now (the `Nodup` premise is gone) |
| `gabbro_ziel` | unchanged statement text, re-proved; axioms `propext`, `Classical.choice`, `Quot.sound` |
| `einzelnPool_of_nodup`, `einzelnPoolB_of_einzelnB` | the pool condition is vacuous on distinct starts |
| `akzeptiert_nodup_gleich`, `akzeptiert_vor_neu`, `akzeptiertVor_nodup` | on a repetition-free start list the new Bool IS the old Bool (`AkzeptiertVor`); every old acceptance stays |
| `akzeptiertSpecVor_neu`, `pruefer_vor_neu`, `laufzeit_vor_neu` | the old specification implies the new one; every old checker is a `Pruefer`; every old run is admitted -- both premise changes are relaxations |
| `pool_ziel_zeuge` | probe B's program with `haupt` declared twice: accepted by `akzeptiert_pruefer` (`zPool_akzeptiert`; the old Bool refused it, `zPool_vor_abgelehnt`), `NutzerPflicht` holds, on the runtime's start both threads run `haupt`, both step, thread 0 takes the lock, and `gabbro_ziel` gives `Ziel` there |
| `pool_abgelehnt`, `pool_abgelehnt_spec` | `hauptB` (writes `privB` unguarded) declared twice: every other component accepts, `einzelnPoolB` refuses; no `AkzeptiertSpec` |
| `pool_fuss_paart_vorkommen` | `hauptA` (reads and writes `privA`) declared twice: the new footprint component refuses, the pre-F10 one accepted |
| `pool_schreibt_nicht_voll`, `einzelnPoolB_iff_zeuge` | the lane-245 lemmas on COMPLETE member lists with a carrier the program writes (review G06 F4) |

**Rust side.** `N304` decides `EinzelnPool` (on the exported fragment exactly: the exporter
refuses `atomic` and `accumulates` items, so both sides read "every written carrier guarded");
the footprint legs `N290`-`N293` always paired thread indices, which is the occurrence form of
`Getrennt`. `N315` (idle duplicate) is retired -- an idle routine is the empty pool and the goal
covers it -- and gift 976 with it. The exporter's `LG001` for repeated starts (fix lane F4) is
lifted: `beispiele/157-worker-pool.gab` exports with both occurrences and agrees
(retired `pruefe-akzeptiert-diff`, 0 findings; its self-test runs the pool positive).

**What is NOT claimed.** Per-core writes (`accumulates … per cpu`) stay unmodelled (OFFEN
O17). A routine declared ONCE on several threads is outside (d). The run witness takes three
steps; `Ziel` at every other reachable machine is `gabbro_ziel`'s, not the witness's.

## 48. Same-core interrupt preemption: the leg `keinKernHalt` of `Ziel` (fix lane F11, 2026-09-22)

*Files: `grammatik/Grammatik/Zielsatz/Kern/Spec.lean` (`KernPlan`, `KernHaltG`, the leg),
`Zielsatz/Eigenschaften/Masken.lean` (the proofs and the discipline Bool), `Zielsatz/Eigenschaften/MaskenZeuge.lean`
(the witnesses on `Korpus59.lean`). Reviews G02 F1 and G12 F1, OFFEN O19.*

**The gap.** An `entry … via idt` dispatch root travels into the model as an ordinary start,
and G interleaves freely, so the deadlock the Rust `H102` refuses (`beispiele/gift/460`: a
handler takes, on the core it interrupted, a lock that core's thread holds without
`masks irqs`) is no deadlock in G — there the holder steps on. `D.maskiert` was read by
nothing in `Zielsatz/`.

| theorem | what it says |
|---|---|
| `KernPlan kern H ms fs n` (Spec) | the two hardware facts about ONE core, as conditions on a G run: a handler takes its FIRST step only where no other thread of its core holds a masked lock (`cli`/`sti`), and from there no other thread of that core steps while the handler is unfinished (preemption runs to completion) |
| `KernHaltG` (Spec), the new leg `Ziel.keinKernHalt` | on such a run a handler never stands at a lock a thread of its own core holds. Its own hypotheses name the handler threads, their cores, their call graphs and features, and the masking discipline (`H102`) over them |
| `kernHaltG_gilt` | the leg, PROVED for every program of G — it needs nothing from (a)–(d), like `speicherSicher` |
| `handler_sperre_maskiert` | the program side: if every lock a thread's features admit is declared `masks irqs`, that thread stands at masked locks only, at every machine of the run (carried by `MerkInvG`, whose `Merkmal.sperre` field IS "which locks a body may take") |
| `merkInvG_lauf`, `anSperre_gleich`, `anSperre_nicht_fertig`, `anSperre_ende_falsch`, `anSperre_start_falsch`, `sperre_merkmal`, `erster_index` | the helpers: the frame invariant along a run from any start machine; a lock head is a fact about the thread's own state; a thread at a lock head is unfinished; a start machine has no thread at a lock head |
| `maskenDisziplinB`, `merkAbg_maskM`, `maskM` | `H102` as a Bool over the member list, and the bridge into the leg's hypothesis |
| `masken_zeuge` | ONE core, two threads of `beispiele/59`: thread 1 takes `RING`, the handler then steps and stands at `locks TAKT` (masked) while the interrupted thread is inside its section; the leg — from `korpus59_ziel` — gives that `TAKT` is not held by that thread |
| `masken_disziplin_59`, `masken_disziplin_460` | the discipline Bool accepts `takt_verteiler`'s graph and refuses `ruf_verteiler`'s (the `gift/460` shape); both roots pass the checker, so the refusal is the handler discipline and not (a) |

**Rust side.** `H102` (`kontexte.rs`) decides the same over the handler's call-graph hull:
measured, `beispiele/gift/460` gives `[H102]` and `beispiele/59` is clean, exactly as the Lean
Bool. No code, no gift, no example was added.

**What is NOT claimed.** Which start is a handler and which core it shares is not in `Einheit`
and G has no cores, so those are hypotheses of the leg and not components of (a)/(d)
(OFFEN O19, narrowed). Rust's `H102` skips locks the unit does not declare and fires only on
`via idt` (`beispiele/57`'s IPI is silent) — both named there. The emitted C realises no
masking at all (no `cli`/`sti`).

## 49. Threads created at run time: the thread machine in the goal theorem (Opus agent A, 2026-09-26)

*Files: `grammatik/Grammatik/Nebenlaeufigkeit/Allgemein/FadenMaschine.lean` (the machine, its invariant, both bridges),
`Zielsatz/Kern/Spec.lean` (`Einheit.gestartet`, `Einheit.ws`, `ZielF`, the new `GabbroZiel`),
`Zielsatz/Faeden/Faeden.lean` (the join legs), `Zielsatz/Kern/Beweis.lean` (`zielF_aus`, `gabbro_ziel`,
`gabbro_ziel_g`), `Zielsatz/Faeden/FaedenVor.lean` (nothing weakened), `Zielsatz/Faeden/FaedenZeuge.lean`
(witnesses). OFFEN O21, O22; report `messung/OPUS-A-LAUFZEITFAEDEN.md` (retired report, in the history).*

**The gap.** `start { f, g };` (the starter joins its roots) and the `child` region of a stack
gate create threads at run time; `GabbroZiel` fixed the thread population at the start. A child
reached `Ziel` only through `klon_ziel` (§39, outside the statement), a `start` not at all.

| theorem | what it says |
|---|---|
| `FadenMaschine`, `FadenSchritt`, `FadenErreichbar`, `FadenStart` | machine G plus live set, join lists, ghost rank and clock. Steps: `lauf` (a G step of a live thread that joins nothing), `start` (a live thread holding NO lock spawns dormant slots and waits), `kind` (spawn one slot, go on), `join` (every root finished: the wait ends). No G rule changed |
| `fadenErreichbar_G`, `fadenErreichbar_von_G` | every thread-machine run is a G run from the same start machine; every G run is a thread-machine run (all live, nothing spawned) |
| `fadenInv_erreichbar` (`FadenInv`) | a dormant slot is its start thread; a joining starter is live and holds no lock; an awaited root is live and ranks above its starter; ranks are bounded by the spawn clock |
| `faden_schlafend_frei` | a dormant slot holds no lock when its root holds none by signature: a spawned thread ENTERS HOLDING NOTHING (model side of `N456`) |
| `kein_warteZyklusF` | no wait cycle through locks AND joins: a lock edge never ends at a joiner, so a cycle with one non-joiner is a lock cycle (ranks), and a joiner-only cycle climbs in spawn rank |
| `keine_verklemmungF` | if every live unfinished thread waits for a lock or an unfinished root, every live thread is finished (highest waited-for lock, or the rank bound of join chains) |
| `fortschrittF_aus` | every stop is named on the thread machine: dormant, a join wait or an enabled `join`, or `FortschrittG`'s list with the G step admitted by `lauf` |
| `zielF_aus`, `gabbro_ziel : GabbroZiel` | every leg of `ZielF` (= `Ziel` on the G state + `schlafendUnberuehrt`, `schlafendFrei`, `joinFrei`, `keineVerklemmung`, `keinZyklus`, `fortschritt`) on every reachable thread machine; axioms `propext`, `Classical.choice`, `Quot.sound` |
| `gabbro_ziel_g` | the statement of before (`Ziel` on every G run) as a corollary; every former caller of `gabbro_ziel` uses it |
| `ws_ohne_gestartet`, `startPflicht_vor_iff`, `laufzeit_vor_iff`, `pruefer_aus_vor_gleich`, `gabbro_ziel_vor` | nothing weakened: on units without run-time roots `ws`, (b), (d) are the old ones; an old checker is a new one with the same verdict; the old statement VERBATIM follows |
| `mehrfach_gestartet`, `akzeptiertSpec_gestartet` | a run-time root stands twice in `ws`, so the checker guarantees no signature lock, no reasons, pool safety (model half of `N458`/`N462`; for a lifted child `N456`/`N457`) |
| `sj_lauf` | a `start` spawns two threads, both write and finish, the starter waits (`JoinWartet`) until the join, then calls and writes; memory slot 0 moves 0 -> 2 |
| `kw2_lauf` | a `child` runs concurrently with its parent: parent call, child write, parent write; the parent never waits |
| `spawn_start_ziel`, `spawn_kind_ziel` | `ZielF` via `gabbro_ziel` on spawn runs of ACCEPTED units (probe B's lock-guarded `haupt` as a run-time root), the spawned threads stepping and taking the lock |
| `start_nicht_poolsicher_abgelehnt`, `_spec` | a `start` of a root writing an unguarded table is refused by the Bool at the pool component alone; the same routine as an ordinary start is accepted |
| `kind_unter_sperre_abgelehnt`, `_spec` | a region lifted from inside `locks` needs the lock at entry (`wrap`), refused at the root component |
| `start_unter_sperre_kein_schritt`, `start_unter_sperre_zeuge` | no step makes a thread holding a lock a joining starter (model side of `N461`), instantiated where thread 0 holds the lock |
| `klon_als_faden`, `klon_ziel_faden` | fix lane F9's clone machine is a special case: a clone spawn is a `kind` step |

**Rust side.** The exporter carries every `start` root as `gE.gestartet` (parameterless, each
once; `check_gestartet`), the statement leaves no G term, and a starter's lifted `locks` effect
is no refusal. The retired `pruefe-akzeptiert-diff` rebuilt `ws` from the source with the roots doubled,
pinned the export against it (K5), and compared `N458`/`N462` with `wurzeln`/`einzeln`; its
self-test had a positive (`messung/proben/faden-start-pool.gab`) and a negative (a root needing a
lock). A `child` still does not export: its stack gate is a foreign body (`Ax := Empty`).

**What is NOT claimed.** Per-spawn arguments (a child reading its handed values), a root
`requires` only true at the spawn world, `old`-reads at the spawn world, the end of a join
wait, the handed stack, and the C side of the spawn (lane 260's lowering).

## 50. The memory model beyond DRF-SC: machine W and the leg `schwach` of `Ziel` (Opus agent B, 2026-09-26)

*Files: `grammatik/Grammatik/Speichermodell/Maschine/Sicht.lean` (the view discipline, litmus facts),
`Speichermodell/Maschine/MaschineW.lean` (machine W over G, `w_aus_g`), `Speichermodell/Maschine/DRF.lean` (the DRF
theorem), `Speichermodell/Maschine/Zeuge.lean` (witnesses, OFFEN O17), `Zielsatz/Kern/Spec.lean` (`SchwachSC`,
the leg), `Zielsatz/Kern/Beweis.lean` (the leg proved), `Zielsatz/Eigenschaften/Schwach.lean` (the goal over W).
Report: `messung/OPUS-B-SPEICHERMODELL.md` (retired report, in the history). OFFEN O17 (narrowed), O25 (new).*

**The gap.** G is sequentially consistent, and `Spec.lean` read "the hardware is DRF-SC" as an
assumption of the reading; atomics were "ordered by A10". The emitted C is a C11 program with
relaxed, release/acquire and seq_cst atomics and `pthread_mutex` locks.

**The model.** The promise-free timestamp (view) machine of RC11 for the orders the emitter
writes: a history of messages per location, a view per thread and per lock, message views for
release writes; a read returns ANY message at or above the reader's view; a write takes a fresh
timestamp above the writer's view. `seq_cst` is modelled as release/acquire (an
over-approximation). Machine W is G over this memory, with the weak choice at the recorded reads.

| theorem | what it says |
|---|---|
| `mp_ra_verboten` | message passing, release store / acquire load: "flag seen, data not" is unreachable |
| `mp_rlx_erlaubt` | the same shape all relaxed: that outcome is reachable (non-SC) |
| `sb_erlaubt`, `sb_sc_verboten` | store buffering (release/acquire): both reads 0 reachable on the weak machine, not on the SC machine (`LSchrittSC`); `lErreichbar_sc_schwach`: every SC run is a weak run |
| `corr_verboten` | coherence read-read: after reading the second of two writes, never the first |
| `RufMaschineW`, `SchrittW`, `RufSchrittW`, `RufErreichbarW`, `RufStartW` | machine W: G's state plus histories, thread views, lock views; one step = a G step on a presented memory that holds, at every carrier the step reads, SOME message at or above the thread's view |
| `w_aus_g` | every run of G is a run of W (for every order assignment): always write on top, read the newest (`SCForm`) |
| `schrittW_kohaerent`, `schrittW_erwerb` | on EVERY program: a read's message is at or above the reader's view and the view reaches it afterwards (CoRR/CoWR); an acquire read joins the message's view (release/acquire happens-before) |
| `getrennt_of_frei` | an unguarded footprint carrier is thread-local (`FussS` leaves no other disjunct) |
| `lies_fakten` | at a read of a step, the reader's graph reads the carrier, and it holds every guard lock of it -- read off the thread states alone, before the memory is known |
| `SichtInv`, `schritt_sichtInv`, `sichtInv_erreichbar` | the view invariant: an unguarded read carrier is seen at its newest message by the one thread that reads it; a guarded one by the lock holder, or by the lock's view when free; the newest message of a read carrier carries G's value |
| `liest_neueste`, `praesentiert_g` | every read reads the newest message, and the presented memory IS G's memory |
| `schwach_ist_g`, `g_aus_w` | THE DRF THEOREM: under the premises of G's race leg (GutO, closed graphs, `FussS` with `lokK`, exclusive start) every step of W is a step of G, every W run a G run -- atomics included, every order assignment |
| `SchwachSC` (Spec), the leg `Ziel.schwach` | at every reached machine every step of W over it is a step of G; proved in `ziel_aus` from `schwach_ist_g` |
| `gabbro_ziel_schwach`, `schwach_erreichbar`, `schwach_gleich_g` | every leg of `Ziel` at every machine W reaches; on an accepted program W and G reach the same G-states |
| `w_nicht_sc`, `akzeptiert_n1_abgelehnt`, `fuss_n1_abgelehnt` | on the refused noninterference configuration 1 (`konfig` written by `kern`, read by `hauptA`, no lock) W reads the initial `konfig` after the write and stores 0 where G, on the same schedule, stores 3; the footprint component refuses it |
| `g_schritt_0`, `schwach_nicht_trivial` | (added 2026-09-26 after the Spec-diff verdict, F3) every G step of `hauptA` at that machine stores `3` (inversion over every rule of `RufSchrittG`); hence `¬ SchwachSC` there: the leg is false of some programs, as a theorem |
| `gabbro_zielF_schwach` | (merge with Opus agent A) the weak leg at every reachable THREAD machine, `ZielF.g.schwach`; W is taken over G's runs, spawn/join are not synchronisation points of W |
| `schwach_pool_zeuge` | on the accepted F10 pool, three W steps (both instances unfold, thread 0 takes the lock); every leg by `gabbro_ziel_schwach` |
| `poolSicherRust_iff`, `proKern_schreiben_akzeptiert`, `proKern_lesen_abgelehnt` | O17: with a per-core accumulator read as a relaxed atomic, the Rust `N304` pool rule IS `PoolSicher`; a pool writing one relaxed atomic is accepted (and covered by `schwach`); a start reading an atomic another start writes is refused by `fuss` |

**Rust side.** Nothing changed and nothing needed to: the DRF theorem uses no memory order, the
emitter lowers every atomic access through an explicit `atomic_*_explicit` call (lane 152) and
the driver's locks are `pthread_mutex`. retired `pruefe-akzeptiert-diff`: 19 agreements, 0 findings,
self-test both directions (the instrument now also reads the local `lean-probe`'s exit line).

**Assumptions of the reading** (Spec.lean header, five, repaired after the Spec-diff verdict,
F1/F2/F5): W over-approximates RC11 at G's step granularity; compiler and hardware implement C11
atomics; EVERY lock primitive is acquire/release (driver `pthread_mutex`; own primitives under
`N323`, orders NOT checked, OFFEN O26 -- checked since §52, `N481`-`N483`; foreign ones trusted); carriers are locations; unrecorded
reads (`Orakel.wirkt`, `regLies`, `sichtbar`) are taken over G's memory.

**What is NOT claimed.** Programs that RELY on an unguarded atomic read across threads (a flag, a
counter, a per-core cell): `fuss` refuses them, so W's non-SC outcomes occur on no accepted
program (OFFEN O25; O17's read half). That W is exactly RC11 (it over-approximates it: `seq_cst`
as release/acquire, no promises).

## 51. What a green build covers: one certificate per exported program, one list for the rest (Opus agent C, 2026-09-26)

*Files: `grammatik/Grammatik/Zertifikat/*.lean` (generated certificates), `Zertifikat/REGISTER.txt`
(the one list), `Grammatik/Korpus/Zeugnis/Zertifikate.lean` (umbrella), `crates/gabbro-check/tests/zertifikate.rs`
(the guard), `Zielsatz/Kern/Spec.lean` header "WHAT A GREEN BUILD COVERS". Report
`dokumente/PROOF.md`.*

**The gap.** `lake build` green said nothing about a real program: only 104 and 108 had their
exported unit judged by the Lean Bool in the build; 20 further exported programs were judged by
the Rust checker alone, and 176 accepted programs the exporter refuses were judged by nothing,
silently.

| theorem (per certificate) | what it says |
|---|---|
| `gCheck` | `akzeptiert_pruefer.akzeptiert gE gFs gLs gCs = true`, by `decide`, on the EXPORTED unit: premise (a) decided in Lean, the Rust verdict no longer used |
| `gFs_voll`, `gLs_voll`, `gCs_voll` | the member lists are complete (`Aufzaehlung`) |
| `gP_gabbro_f` | `GabbroZiel` on the program: `ZielF` on every reachable thread machine, from `gabbro_ziel`, with `NutzerPflicht gE` as hypothesis |
| `gP_gabbro` | its machine-G corollary (`gabbro_ziel_g`) |

23 certificates, all in the build (311 jobs green): 104, 108 (`GenOblig104/108`), 109, 118, 119,
120, 121, 124, 130, 15, 157, 16, 34, 59, 62, 69, 73, 93 and the gift clean sides 219, 414, 700,
701, 719. No `sorry`, `admit`, `native_decide` (the guard checks each file). The 176 UNCERTIFIED
programs are listed with their first refusal; the Spec names them as NOT CLAIMED through the
register. Exporter change: scalar constants travel as the checker's folded value, `const fn`
is comptime (93 certified).

## 52. Racing atomics over machine W: the memory half of O25, the language-carried legs, `N481`-`N483` (Opus lane O25, 2026-09-26)

*Standalone: `Zielsatz/Kern/Spec.lean`'s definitions, `Akzeptiert` and `gabbro_ziel` are unchanged
(two comment-only header corrections, assumption (3) and the O25 pointer in NOT CLAIMED). Files
`grammatik/Grammatik/Speichermodell/{Atomar,AtomarZeuge,Zaehler}.lean`; report
`messung/OPUS-O25-ATOMICS.md` (retired report, in the history).*

**The question.** §50's DRF theorem holds by exclusion: `fuss` refuses every unguarded read of a
carrier another thread writes, atomics included. What does machine W do when that refusal is
lifted for ATOMIC carriers only (flags, spins, counters, per-core folds)?

| theorem | file | statement |
|---|---|---|
| `FussSA`, `fussSA_of_fussS`, `getrennt_of_freiA` | Atomar | `FussS` with one more disjunct for footprint carriers, "an `atomic` global"; the old property implies it; an unguarded NON-atomic footprint carrier is still thread-local |
| `RufSchrittGA`, `RufErreichbarGA`, `schrittGA_of_g`, `ga_aus_g` | Atomar | machine GA: a step of G on a presented memory that agrees with G's at every non-atomic carrier (atomic reads answered by any value, the havoc of O25); every G run is a GA run |
| `gaInv`, `gaInv_spur`, `gaInv_orte`, `gaInv_merk`, `gaInv_exklusiv` | Atomar | a thread-only property kept by G's steps holds on every GA run: the trace invariant, the frame read bound, the feature invariant, lock exclusivity |
| `zugriff_haeltA`, `schritt_zugriffeA`, `lies_faktenA`, `frei_schreiberA` | Atomar | the static access facts of §50, from the thread invariants instead of G-reachability |
| `SichtInvA`, `schritt_sichtInvA`, `sichtInvA_erreichbar` | Atomar | §50's view invariant, `frei`/`stimmt` restricted to non-atomic carriers, G's part GA-reached |
| **`schwach_ist_gA`**, `plain_liest_neueste`, `ga_aus_w` | Atomar | **THE DRF THEOREM WITH RACING ATOMICS**: under `FussSA` every W step is a GA step whose presented memory is G's at EVERY non-atomic carrier; a plain read is the newest message; every W run's G-part is a GA run |
| `w_spur_exklusiv`, `schwach_ist_gA_vor` | Atomar | trace invariant and lock exclusivity at every machine W reaches; under the old `FussS` the old theorem and the new one both apply |
| `schrittW_freigabe`, `schrittW_hist`, `laufW_waechst`, **`hb_uebergabe`** | Atomar | release/acquire on EVERY program: a release write carries the writer's view; messages stay and views grow along W runs; **the hand-off**: an acquire read of the message `t` released makes `u`'s view reach `t`'s view before the release at every other carrier, and every later read of `u` there returns a message at or above it |
| `ga_fremd`, `schrittGA_zerlegen`, `LaufGA`, `sperre_ordnetGA`, **`rennfreiGA`** | Atomar | race freedom for every NON-atomic carrier on every GA run: guarded carriers ordered through the lock, unguarded ones write-separated |
| `fussWAB`, `fussWAB_iff`, `AkzeptiertA`, **`akzeptiertA_of_akzeptiert`** | AtomarZeuge | the Bool of `FussSA` and the checker `Akzeptiert` with it; EMBEDDING: every program `Akzeptiert` accepts, `AkzeptiertA` accepts |
| `akzeptiertA_ok`, `schwach_ist_gA_akzeptiert` | AtomarZeuge | `AkzeptiertA` and an admissible start give the memory theorem's premises (graphs `kVon`) |
| `gaInv_rang`, `kein_warteZyklusGA`, `keine_verklemmungGA`, `LaufW`, **`w_sprache_akzeptiertA`** | AtomarZeuge | **THE LANGUAGE-CARRIED LEGS OVER W**: on a program `AkzeptiertA` accepts, at every machine W reaches, `SpurInv`, lock exclusivity, no global deadlock, no wait cycle, `ZeitAb`, every W step a GA step; on every indexed W run race freedom for non-atomic carriers. NOT the contract legs |
| `n1_akzeptiertA`, `n1_start`, `n1_ga`, `n1_sprache` | AtomarZeuge | the FLAG: configuration 1 of the noninterference fixture (`kern` stores `konfig`, `hauptA`/`hauptB` read it, no lock), refused by `Akzeptiert`, accepted by `AkzeptiertA`; every W step there a GA step with plain tables SC; the language-carried legs |
| **`n1_nicht_sc_aber_ga`**, `n1_schwachSC_falsch` | AtomarZeuge | NON-DEGENERATE: W's stale read of `w_nicht_sc` happens on this accepted program and is a GA step; `SchwachSC` is false there -- a goal over `AkzeptiertA` needs the leg `schwach` in GA form |
| `faltung_abgelehnt`, `faltung_akzeptiertA`, `faltung_echt` | AtomarZeuge | the PER-CORE FOLD (O17 read half): `zaehlA` twice writing the atomic `zaehler`, `zaehlB` reading it -- refused by `Akzeptiert` at `fuss`, accepted by `AkzeptiertA` |
| `nutzlast_ohne_erwerb_abgelehnt`, `nutzlast_echt` | AtomarZeuge | the REFUSAL: a PLAIN table written by one start and read by another with no lock is refused by `AkzeptiertA` at its footprint component -- the exemption is for atomics only |
| **`zaehler_zwei`**, `zaehler_lauf`, **`zaehler_verloren`** | Zaehler | a relaxed counter, two threads, one `fetch_add(1)` each: under an ATOMIC RMW (write at the read message's timestamp + 1) the newest message is 2 on every complete run; under W's `exchange` shape (write at any fresh timestamp) the lost update (newest 1, no 2) is reachable -- W cannot prove the counter |

**Rust side (OFFEN O26 closed at the source level).** `namen.rs::sperrprimitiv_ordnung`,
sentence `namen.sperrprimitiv_ordnung`: `N481` (a take reading only relaxed atomics), `N482` (a
give writing only relaxed atomics), `N483` (a bodied take and give of one lock releasing and
acquiring on different ordered atomics). Gifts 1201 (relaxed test-and-set spinlock), 1202, 1203;
positive: snippet tests `geordneter_spinlock_besteht`, `ticket_sperre_besteht` (the runtime's
ticket lock shape). Corpus diff: only the three gifts. Measured: `N042` refuses every own or
foreign `L_nimm`/`L_gib` beside `lock L`, so on accepted programs every lock is driver-defined.
The Rust footprint legs `N290`-`N294` never counted atomics as carriers: on this component the
Rust checker decides `fussWAB`, not `fussWB` (`messung/proben/o25-flagge-atomar.gab`: accepted by
Rust, refused by the exporter, `LG001`).

**What is NOT claimed (OFFEN O25, narrowed).** The CONTRACT legs of `Ziel` over GA -- they come
from the replay of the user's sequential proof (`execEndH`), which reads an atomic from its own
world; the rely (a havoc at a shared atomic read in `execEndH`) and the replay family carrying it
are not built. Therefore no Spec diff: `GabbroZiel` still runs `Akzeptiert`, whose `fuss` refuses
racing atomics. RMW atomicity in W (`zaehler_verloren`). The payload hand-off to a PLAIN carrier
(the view transfer `hb_uebergabe` is proved; a footprint rule admitting the payload read after an
`awaits` is not).

## 53. Invariants beyond the returns: four legs of `Ziel`, one of `ZielF`, and `N496` (Opus agent D, 2026-09-26)

*Files: `grammatik/Grammatik/Zielsatz/Eigenschaften/Invarianten.lean` (proofs), `Zielsatz/Eigenschaften/InvariantenZeuge.lean`
(witnesses), `Zielsatz/Kern/Spec.lean` (definitions, the invariant block of the header),
`Zielsatz/Kern/Beweis.lean` (`ziel_aus`, `zielF_aus`); Rust `crates/gabbro-check/src/m1.rs`
(`invarianten_buchen`), `tests/invarianten_buchung.rs`, `beispiele/gift/1231`-`1234`. Report
`messung/OPUS-D-INVARIANTEN.md` (retired report, in the history).*

**The gap.** NOT CLAIMED read "invariants at entry or while locks are held (claimed at returns
only)"; OFFEN O11 said a table/group invariant no function `maintains` was booked by nothing.

| theorem | what it says |
|---|---|
| `schritt_logArt` | every step of G appends at most ONE call-log event; a return event's world carries the memory the step leaves (by cases over the 70 rules) |
| `rufLogPasstG_eind` | a call log determines its key stack |
| `schritt_schluessel` | a step leaves a thread's key stack unchanged, pushes one key, or pops the head with its `rueck`/`grund` event logged |
| `fertig_retKopf` | a finished thread stands at a VALUE return (with `KeinStartGrundG`) |
| `invRuhe_erreichbar` | on every reachable machine, an invariant that reads only its carriers (`InvTraeger`) and held at the start holds whenever no UNFINISHED thread is inside a function that owes it (`InvZu`) |
| `invSicht_aus` | a thread outside every writer that holds a guard of the invariant sees it intact (exclusivity + `U003`) |
| `sperrWechsel_aus` | every acquire of `L` goes from and to a memory with `S.inv L`; every release leaves one |
| `sperrSicht_aus` | every access of a carrier `L` protects holds `L`; no other thread moves it while `L` is held |
| `inv_ohne_schreiber` | an invariant no function writes holds at every reachable machine (the frame half of O11) |
| `faden_spawn_m` | a thread-machine step that makes a dormant slot live leaves the G state alone |
| `gabbro_ziel` (re-proved) | `Ziel` with the legs `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`; `ZielF` with `spawnSicht`; axioms `propext`, `Classical.choice`, `Quot.sound` |

**Witnesses** (program `mP`, MehrfadenZeuge.lean): `lock_gebrochen_unsichtbar` (konto `[30, 0]`
inside thread 0's section; no step of thread 1 accesses `konto` there, by `sperrSicht`);
`inv_erwerb_und_eintritt` (thread 1's acquire after the section: `konto[0] == konto[1]` before
and after, by `sperrWechsel`; thread 1's entry of `setze` after `hauptA` finished:
`privA[0] == privA[1]`, by `invRuhe`, at the memory and at the frame's entry world);
`tabelle_gebrochen` (`privA = [7, 0]` inside `hauptA`, the invariant OPEN there -- the leg claims
nothing). Refusal side of O11: `beispiele/gift/1231`-`1234` (`N496`); the model side is
`ivPschlecht_nicht_invGutS` (InvZeuge.lean): a writer that breaks an invariant fails (b).

**What is claimed, precisely.** "At every entry" is false in general (a writer's callee may see
the invariant broken); claimed is every point where no unfinished thread is inside a writer.
"While held" can only mean observation points: the holder may break a lock invariant inside its
section; no other thread touches the protected carriers there, every section starts from the
invariant and every release restores it.

**What is NOT claimed.** A table invariant false at the start (the legs' hypothesis, not (b));
one reading carriers outside its `traeger`; any invariant while an unfinished thread is inside
one of its writers. Every certified program has no table invariant (`Inv := Empty` in the
exporter), so `invRuhe`/`invSicht` are vacuous there; the lock legs are not.

**Review** (`dokumente/PROOF.md`): sound, no premise moved. A callee's
writes are its caller's, so a thread that ever writes a carrier keeps the invariant open for its
whole life (`invRuhe` bites after the writers finish); and a guarded table invariant has, by
argument, no reachable writer in the model, so `invSicht` adds nothing to `invRuhe` there.

## 54. Linking separately compiled units under the same hardware assumptions (Opus agent E, 2026-09-26)

*A SECOND statement in `Zielsatz/Kern/Spec.lean`, purely additive: `GabbroZiel` and every definition
before it are unchanged. Files `grammatik/Grammatik/Zielsatz/{Verbund,VerbundZeuge}.lean`; Rust
`crates/gabbro-check/src/verbund.rs`, `gabbro link`; report `messung/OPUS-E-LINKEN.md` (retired report, in the history).*

| theorem / definition | file | statement |
|---|---|---|
| `mitRumpf`, `verbindeP`, `verbinde`, `teilP` | Spec | the linked unit: every body from its owner (`e`), both units' starts and roots, the shared rest |
| `Verbindbar`, `Platzhalter`, `HuelleV`, `KeinRueckruf`, `LokBedarf`, `GetrenntV`, `SchreibGetrenntV`, `PoolSicherV`, `SchnittstelleSpec`, `NutzerTeil` | Spec | one link declaration; leaf placeholders; the COMPOSED hull of a root; no callback through an import; the three whole-program components over composed hulls; the user's duty over the bodies a unit owns |
| **`GabbroZielVerbund`**, **`gabbro_ziel_verbund`** | Spec, Verbund | each unit accepted alone + `Verbindbar` + `SchnittstelleSpec` + `NutzerTeil` per unit + `E₂.Q = E₁.Q` + the linked runtime -> `ZielF` on every reachable thread machine of the linked program |
| `stmtOrteP_mitRumpf` … `grundArmsOrteP_mitRumpf`, `fussOrteG_mitRumpf2`, `koerper_mitRumpf2`, `invGutS_mitRumpf2`, `invGutGrund_mitRumpf2` | Verbund | a body's footprint and its triples depend on its own text and the contracts only (structural induction over the syntax) |
| `erreichB_stabil`, **`reachB_ruft`**, `reachB_in`, `reachB_teil` | Verbund | the computed call graph is CLOSED on a complete member list (the fixpoint within `fs.length` rounds, a counting argument) -- a lemma the tree did not have |
| `huelle_of_reach`, `abg_verbinde`, **`akzeptiertSpec_verbinde`**, `nutzerPflicht_verbinde` | Verbund | the linked unit meets (a) and (b) of `GabbroZiel` |
| `schnittstelleB`, **`schnittstelleB_iff`** (+ one `_iff` per part) | Verbund | the link check as ONE Bool, deciding `SchnittstelleSpec` exactly |
| `verbinde_leer`, `verbinde_akzeptiert`, `nutzerTeil_verbinde` | Verbund | embedding: linking with an empty partner is the identity; the linked unit is accepted and carries the restricted duty, so chains link by iteration |
| **`vz_ziel`**, **`vz_lauf_zeuge`**, `vz_huelle_schreibt`, `vz_verbinde_gleich` | VerbundZeuge | POSITIVE: a library exporting the lock-guarded table writer `wrap` (`ensures konto[0] == 100`), an app calling it from two threads; each unit accepted alone; the app's own graph does not reach the writer, the composed hull does; `ZielF` on the linked program; a run where both app threads step and one holds the lock |
| **`vm_abgelehnt`**, `vm_abgelehnt_spec` | VerbundZeuge | REFUSAL: a read hidden behind an imported head (`privB`); each unit accepted alone, the link Bool false, the whole-program checker false on the linked program |
| **`vz_vertrag_zu_schwach`** | VerbundZeuge | REFUSAL: the exported contract is weaker than the importer's -- no link declaration |

**Rust side.** `verbund.rs::verbinde`, sentence `namen.verbund`: `N501` (signature, shared
declarations, one body per function, exported), `N502` (contract), `N503` (effects, callback,
threads on both sides), `N504` (costs), `N505` (hardware assumptions). Probes
`messung/proben/verbund/` 1241-1245 (each unit clean alone, the link refuses with exactly its
code), positive pair `tabelle-bib.gab` + `tabelle-app.gab`; `crates/gabbro-cli/tests/verbund.rs`.

**Note (Opus agent F, 2026-09-26, review E F1, `messung/OPUS-F-VERBUND-RENNEN.md` (retired report, in the history)).** No Lean
change. The Rust side now decides the three whole-program components of `SchnittstelleSpec`
instead of refusing around them: `verbund.rs::verbinde_alle` composes the units into the linked
program (`verbundtext`: each body from its owner, each unit's starts -- the surface of
`verbinde e E₁ E₂`) and runs the whole checker over it, so `lok`/`renn`/`einzeln` are decided by
`fusswache2.rs` over the linked call graphs, which under `KeinRueckruf` are the composed hulls
(`huelle_of_reach`). The blanket `N503` for threads on both sides is gone; `N516` refuses a
module split over two units. Per unit, an imported head's declared READS join the importer's
footprint (`fusswache2.rs`, `N291` at the call site, `N301` at the start) -- the Rust twin of
`vm_abgelehnt` (probe 1246) now falls in `gabbro check --with` already, with the one-file codes.
Contracts are compared as normal-form trees; `gabbro build` links two or more units.

**NOT claimed:** different hardware assumptions; callbacks through an import; a contract other
than the exporter's; dynamic loading; foreign C; the C link step (OFFEN O28).

## 55. The atomic rely: every leg of `Ziel` with shared atomics over machine W, standalone (Opus lane O25b, 2026-09-26)

*Standalone: `Zielsatz/Kern/Spec.lean`, `Akzeptiert` and `gabbro_ziel` are unchanged. Files
`grammatik/Grammatik/Speichermodell/{AtomarSem,SperreSemA,AtomarRec,AtomarReplay,AtomarAkteur,AtomarLauf,AtomarW,AtomarInv,AtomarRuhe,AtomarFortschritt,AtomarZiel,RMW}.lean`,
`grammatik/Grammatik/Zielsatz/{AtomarPflicht,AtomarRuheNutzer,AtomarInvarianten,AtomarMasken,AtomarAkzeptiert,AtomarAkzeptiertZeuge,AtomarZiel}.lean`;
report `messung/OPUS-O25B-ATOMICS.md` (retired report, in the history).*

**The question (OFFEN O25, the contract half).** §52 proved what machine W does on a program
whose footprints admit racing atomics, and the legs the language carries there. The contract
legs come from the replay of the user's SEQUENTIAL proof, which reads an atomic from its own
world. What must the user prove so that the contracts survive another thread (or the weak
memory) answering a shared atomic read with any value -- and does the replay carry it?

| theorem | file | statement |
|---|---|---|
| `AUmwelt`, `HavocA`, `leseA`, `execStmtHA`/`execEndHA`, `Endblock.execHA_frei`, `execEndHA_id` | AtomarSem | THE RELY: `execStmtH` with every read (`World.lese`) passed through an atomic environment that may change the read carriers of a set `T`, and nothing else; on a body reading nothing of `T` it IS `execStmtH` |
| `semHA_*` | SperreSemA | the residue semantics with the rely (the twin of `semH`) |
| `KoerperGutSA`, `InvGutSA`, `InvGutGrundA`, `mischT`, `umweltAusA`, `lese_schritt` | AtomarRec | (b) with the rely: the body triple against EVERY environment of `HavocA T`; the replay's recorded environment (key: the world after the read events) |
| `GetrenntR`, `GeteiltA`, `LogikPflichtA`, `NutzerPflichtA`, `logikPflicht_of_A`, `logikPflichtA_of_frei`, **`logikPflichtA_iff_akzeptiert`** | AtomarPflicht | the shared atomics of a unit (atomic, unguarded, not thread-local over the call closure); (b) with the rely over them; EMBEDDING: on every unit `AkzeptiertSpec` accepts the two obligations are equivalent |
| `VertragsFrei`, `FussSX`, `KopfSA`, `FadenSA`, `ZielInvSA` and the replay lemmas | AtomarReplay | the replay invariant with the rely: shared atomics in no contract, stable carriers disjoint from them |
| `akteurSA` (70 rules) | AtomarAkteur | the acting thread keeps its replay under the rely |
| `RufSchrittGX`, `RufErreichbarGX`, `gx_ga`, `gx_aus_g`, `zielInvSA_erreichbarGX`, **`ziel_ort_atomar`** | AtomarLauf | machine GX (G on a memory agreeing with G's outside the shared atomics `Tg`); the contract legs `VertragAmOrtG`, `SperrInvG`, `KeinLogikHaltG` at every machine GX reaches |
| `SichtInvX`, **`schwach_ist_gX`** | AtomarW | every W step is a GX step whose presented memory is G's at every carrier outside `Tg` |
| `inv_stabilX`, **`ziel_ort_atomar_voll`** | AtomarInv | + `InvAmOrtG`, `InvAmGrundG`, `StartEndeG`, `KeinStartGrundG` over GX |
| `rumpfHA_mitRuhe`, `logikPflichtA_mitRuhe` | AtomarRuhe, AtomarRuheNutzer | the idle root under the rely |
| `gaInvF`, `fadenSA_bereich`, `fortschrittG_GA` | AtomarFortschritt | `FortschrittG` at every GA-reached machine; no float range check fails at a replayed head under the rely |
| `gx_aus_w`, `ZielAtomarW`, **`ziel_atomar_w`** | AtomarZiel (Speichermodell) | from W's start: trace invariant, lock exclusivity, `schwach` in GX form, the seven contract/start legs, no deadlock, no wait cycle, progress, time |
| `gx_traeger`, `schritt_schluesselX`, `invRuhe_erreichbarX`, `invSicht_ausX`, `SperrWechselGX`, `SperrSichtGX`, `invarianten_atomar` | AtomarInvarianten | Opus agent D's four legs over GX (a GX step differs from a G step only at shared atomics, which no table or lock invariant reads) |
| `KernHaltGA`, `kernHaltGA_gilt`, `kernHaltG_of_GA` | AtomarMasken | the same-core interrupt leg over GA runs, for every program |
| `GeteiltV`, `AkzeptiertSpecX`, `akzeptiertSpecX_of_spec`, `fussWXB`, `vertragsFreiB`, `AkzeptiertX`, **`akzeptiertSpecX_of`**, `akzeptiertX_of_akzeptiert`, `RennfreiBisGA`, `ZielAtomar`, **`ziel_atomar_spec`**, `rennfrei_atomar_spec` | AtomarAkzeptiert | (a) with the rely: `AkzeptiertSpec` with `fuss := FussSX` over the admitted shared atomics (shared AND in no contract), its Bool, both embeddings; `ZielAtomar` = every leg of `Ziel` in its form with shared atomics; the theorem from (a), (b), (c), an admissible start |
| `akzeptiertSpecX_mitRuhe`, `geteiltA_mitRuhe_rueck`, `PrueferX`, `akzeptiertX_pruefer`, `Pruefer.alsX`, **`gabbro_ziel_atomar`**, **`gabbro_ziel_atomar_vor`** | AtomarZiel (Zielsatz) | THE GOAL WITH SHARED ATOMICS in the shape of `GabbroZiel`: checker, `NutzerPflichtA`, `HardwareAnnahmen`, `Laufzeit`, every order assignment: `ZielAtomar` at every machine W reaches; EMBEDDING: the premises of `gabbro_ziel` give it |
| `ExchangeKopf`, `RufSchrittWR`, `wr_w`, `wr_aus_g`, **`wr_kein_verlust`**, `wr_rmw_kette` | RMW | RMW atomicity as a sub-machine of W: an `exchange` writes directly above the message it read; two `exchange`s of one global never read the same message |
| `n1_akzeptiertX`, `n1_logikA`, **`n1_ziel_atomar`**, `n1_konfig_geteilt`, **`n1_stale_gedeckt`**, `n1E_ziel` | AtomarAkzeptiertZeuge | POSITIVE: the flag (configuration 1), refused by `Akzeptiert`, accepted by `AkzeptiertX`, (b) with the rely holds, `ZielAtomar` at every machine W reaches; `konfig` IS an admitted shared atomic; W's stale read happens on a covered run; `gabbro_ziel_atomar` applied with the concrete checker and the runtime's start |
| **`hP_havoc_bites`**, `hP_seq`, `hP_rely_nicht`, `hP_logikA_nicht` | AtomarAkzeptiertZeuge | THE RELY BITES: a body that reads `konfig` twice and ensures the two agree through a table is accepted by `AkzeptiertX`, meets the SEQUENTIAL obligation at every budget, and FAILS the obligation with the rely (an environment answering the second read with 5) |
| **`vertrag_atomar_abgelehnt`**, `vertrag_atomar_echt` | AtomarAkzeptiertZeuge | REFUSAL: a contract over the shared `konfig` is refused by `AkzeptiertX` at `fussWXB`, accepted by `AkzeptiertA` |
| `faltung_akzeptiertX` | AtomarAkzeptiertZeuge | the per-core fold (O17) is admitted by `AkzeptiertX` |

**Rust side: `N484`** (`fusswache2.rs::vertrag_atomar`, sentence `wirkungen.vertrag_atomar`): a
`requires`/`ensures` reading an unguarded atomic that one started thread reaches and another may
write is refused -- the contract condition `vertragsFreiB`. Before it, such a contract passed with
0 errors (the footprint legs never counted atomics; `messung/proben/o25b-vertrag-atomar.gab`).
Gift 1204; snippet tests in `tests/fusswache2.rs` (body-only shared read, thread-local atomic,
single thread stay silent). Corpus diff: only the gift. With it, the Rust footprint legs decide
`fussWXB` (atomics exempt as before, contracts over shared atomics refused), i.e. the Rust checker
is the Bool of `AkzeptiertX` on this component -- measured by gift and snippets, not by
retired `pruefe-akzeptiert-diff`, which cannot compare atomic programs (the exporter refuses them,
`LG001`; the script lists `N484` under `fuss`, 22/22 agree, self-test ok).

**What is NOT claimed, and why `Spec.lean` is unchanged.** The thread machine (`ZielF`: spawn,
join, `spawnSicht` over GX) and the linked statement (`GabbroZielVerbund`) are not re-proved with
the rely, and no atomic program exports (`LG001`), so the Rust/Lean agreement on `AkzeptiertX`
is not differentially measured; a Spec diff without the thread machine would drop legs
`GabbroZiel` has today, so none was made (a partial one was ruled out). RMW atomicity is a sub-machine (`RufSchrittWR`), not yet a condition of `SchrittW`; the
payload rule for a plain carrier read after an `awaits` and the exporter for `atomic` items
(`LG001`) are open. The per-core fold is covered as a shared atomic (`faltung_akzeptiertX`), but not exported.

## 56. The four obligations of OFFEN O1 over machine G: the leg `folge`, and `N531`/`N532` (Opus agent G, 2026-09-26)

*OFFEN O1 booked `L24`, `L34`, `L50`, `L52` as unstatable because `Body.lean`'s `exec` is
big-step. The goal theorem's semantics is machine G: small-step, with a per-thread access trace
and a per-thread CALL LOG. All four are statable there. `L24` (read observationally) and `L34`
(an existence statement) are the invariant legs of §53 and their witness; `L50` and `L52` are one
shape, "an event DIRECTLY behind a return in the call log", and `Ziel` gains the leg `folge` for
it. Premise-free; no premise of `GabbroZiel` moved. Files `grammatik/Grammatik/{Folge,FolgeBeweis,
FolgeZeuge,Zielsatz/FolgeZiel}.lean`; Rust `kbedingung.rs` (`N531`, `N532`); report `messung/OPUS-G-O1.md` (retired report, in the history).*

| theorem / definition | file | statement |
|---|---|---|
| `Folge` (`vor`, `ruf`, `ind`, `ende`), `fNach`, `fS`/`fB`/`fE`/`fArms`/`fGArms`, `GRest.fR`, **`FolgeOk`** | Folge | an order specification; the static check (one armed bit per block: a call of `g` arms iff `vor g`, a leaf keeps the bit, a compound/indirect call/sub-block starts unarmed; a `ruf` call and an `ende` return demand the bit); its residue form over G's continuation layers |
| `Armiert`, `Pflichtig`, **`FolgeLog`**, **`FolgeG`** | Folge | the log is armed (newest event a return of a `vor`); an ordered event; every ordered event but the start entry DIRECTLY behind a `vor` return; the leg: for every `Φ` the program passes, every thread's log ordered, a finished `ende` thread armed |
| `fB_mono`, `fE_mono`, `fR_mono`, `fB_alsBlock`, `fB_armWahlG`, `fB_grundWahlG`, `fR_anRueck`, `fNach_blatt`, `fNach_entf` | FolgeBeweis | the check is monotone in the bit and stable under arm selection and `else` blocks; a residue at a return demands the bit |
| `FolgeStapel`, `FolgeInvG`, **`folgeInvG_schritt`** | FolgeBeweis | the thread invariant (head residue at the log's bit, each suspended caller at `vor` of its callee, the log ordered) is kept by EVERY rule of G |
| `folgeInvG_start`, `folgeInvG_erreichbar`, **`folgeG_erreichbar`** | FolgeBeweis | on every reachable machine; the leg with no premise but reachability |
| **`folgeLog_nicht_schwach`** | FolgeBeweis | the order is strictly stronger than "both happened" |
| `Ziel.folge` | Spec, Beweis | the leg in the goal (`ziel_aus`: `folgeG_erreichbar sp init hr`); `#print axioms gabbro_ziel` = `propext`, `Classical.choice`, `Quot.sound` |
| `Folge.mitRuhe`, `ruS_fNach`, `ruS_fS`/`ruB_fB`/`ruEnd_fE`/`ruArms_fArms`/`ruGArms_fGArms`, **`folgeOk_mitRuhe`** | Zielsatz/FolgeZiel | an order specification over `D` lifted past the idle root; the check commutes with the body translation (structural induction over the syntax) |
| **`gabbro_ziel_folge`** | Zielsatz/FolgeZiel | under the premises of `GabbroZiel`, for every `Φ` over the user's declaration the program passes: every thread of every reachable THREAD machine has its call log ordered by `Φ.mitRuhe`, and a finished `ende` thread ended directly behind a `vor` return |
| `Φ50`, `Φ52`, `eP_folge50`, `eP_folge52` | FolgeZeuge | L50's and L52's shape on the fixture `eP` (`haupt` = `setze(); pruefe(); return`) |
| **`folge50_zeuge`** | FolgeZeuge | NON-DEGENERACY: a reached machine whose newest log event is the entry of `pruefe`, directly behind the return of `setze`, whose write (`konto[0]`: 0 -> 5) is in the entry world; the leg there |
| **`folge52_zeuge`** | FolgeZeuge | thread 0 FINISHED in `haupt`; by the leg its log ends directly behind the return of `pruefe` |
| **`eP2_folge50_falsch`**, **`folge50_gegen`** | FolgeZeuge | the calls swapped: the check refuses, and a reached run has an entry of `pruefe` AND a return of `setze` in its log while the order fails |

**`L24` and `L34`.** `L24` literally ("no third state exists") is false in G for any two-statement
write; its content -- no OTHER thread sees the pair half set -- is `invSicht` (table/group
invariants) and `sperrSicht` + `sperrWechsel` (lock invariants), §53. `L34` is an existence
statement about one program; `tabelle_gebrochen` (§53) is its shape.

**Rust side.** `N531` (`kbedingung.breaking-rests-here`): a `breaking I` block without calls that
writes no carrier of `I` is named for the wrong invariant -- the case `D013`'s sentence called
open (*"a `breaking` on the wrong-but-existing invariant still passes"*). `N532`
(`kbedingung.breaking-blocks-maintainers`): no call of a function that `maintains I` inside
`breaking I` (LANGUAGE.md §8.3). Gifts 1291, 1292; clean sides examples 53 and 55;
`crates/gabbro-check/tests/breaking_region.rs` pins both directions of both rules.

**NOT claimed:** an order of effects outside the call log (axioms, registers); an order across a
compound statement, an indirect call or a lock block (refused by the check, not weakened); an
order "sometime before"; the name-bound promises of `breaking` (region, restoration at the
block's end) -- G unfolds the block without the name; which `Φ` a source program means (not in
`Einheit`; the exporter emits none).

## 57. Handlers in the unit: the leg `keinKernHalt` carried by (a) (Opus agent H, 2026-09-26)

*Files: `grammatik/Grammatik/Kern/Syntax/Syntax.lean` (`Programm.unterbricht`), `Zielsatz/Kern/Spec.lean`
(`NurMaskiert`, `MaskenDisziplin`, `AkzeptiertSpec.masken`, `HandlerVon`, `KernHaltE`, the leg,
`Verbindbar.unterbricht`, `SchnittstelleSpec.masken`), `Zielsatz/Kern/Akzeptiert.lean` (`maskenB`),
`Zielsatz/Eigenschaften/Masken.lean` (the discharge), `MitRuheStatisch.lean` (`mE_und`),
`Zielsatz/Eigenschaften/MaskenZeuge.lean` (witnesses), `lean_g.rs` (the export). OFFEN O19; report
`messung/OPUS-H-KERNE.md` (retired report, in the history).*

**The gap.** §48's leg was unconditional (`kernHaltG_gilt`): which threads are handlers, their
graphs and `H102` were hypotheses of the leg, so the conjunct added no content
(URTEIL-SPECDIFF-2026-09-23, F1).

| theorem / definition | what it says |
|---|---|
| `Programm.unterbricht` (Syntax) | the function is entered by hardware (`entry … via idt`); default `fun _ => false`; `mitRuhe` carries it, the idle root is none |
| `MaskenDisziplin P fs`, `AkzeptiertSpec.masken` (Spec) | every function the graph of a handler root reaches takes only `masks irqs` locks (`mE (NurMaskiert D)`) — the Rust `H102` |
| `maskenB`, `maskenB_iff`, `maskenB_ohne` (Akzeptiert) | the component of `Akzeptiert`, decides the field exactly; `true` on a program with no handler |
| `HandlerVon P M0 t`, `KernHaltE` (Spec), the leg `Ziel.keinKernHalt` | for every core assignment and every run the core hardware admits (`KernPlan`, the named assumption), a thread whose root the program declares a handler never stands at a lock another thread of its core holds |
| `kernHaltE_aus` (Masken) | the leg from (a): `abg` + `masken` give `MerkAbg` for `maskM` (`mE_maskM`, via `mE_und`/`mE_mono`), `merkInvG_start` at the start machine, then `kernHaltG_gilt` |
| `kernHaltE_ohne_handler` | embedding: with no handler the leg holds with nothing from (a) |
| `mE_und` (MitRuheStatisch) | a body admitted by two feature sets is admitted by their meet |
| `akzeptiertSpec_mitRuhe`, `akzeptiertSpec_verbinde`, `schnittstelleB_iff` | the new field transfers to the idle-root program and across a link (composed hull) |
| `akzeptiert_nodup_gleich`, `akzeptiert_vor_neu`, `pruefer_vor_neu` (PoolSym) | the old Bool is the new one without `maskenB`; an old checker is a `Pruefer` conjoined with `maskenB` |
| `masken_zeuge`, `masken_59`, `kM0_handler` | example 59: the handler set is `{takt_verteiler}`, accepted; the handler preempts thread 1 inside `RING` and stands at `locks TAKT` — the leg of `korpus59_ziel` (from (a)) says `TAKT` is not held there |
| `kPv_ohne_handler`, `handler_abgelehnt`, `kernHaltE_verletzt` | the `gift/460` shape (the handler takes unmasked `RING`): accepted with no handler declared, refused by `maskenB`, and the leg is FALSE on a real admitted run of it — the leg is contentful |

**Rust side.** `H102` unchanged; the exporter writes `gP.unterbricht` for every `via idt` root
(only `beispiele/59` among the certified programs; every other certificate changed by one header
line). the retired `pruefe-akzeptiert-diff` gained the component `masken` ↔ `H102`, pin K6 (exported
handler set = source `via idt` roots), and a self-test pair (59 accepted; 59 without the mask =
gift 460 refused at `masken` alone).

**What is NOT claimed.** No `cli`/`sti` in the C (translation validation has nothing to relate
`KernPlan` to); no pinning (the leg holds for every core assignment); handler re-entry and
handler-on-handler preemption; a thrown entry without `via idt`.

## 58. The atomic rely IS the goal: `GabbroZiel` over machine GX, RMW atomicity in W, payload-free atomics certified (Opus lane O25c, 2026-09-26)

*The ONE Spec diff of OFFEN O25: `GabbroZiel` quantifies a checker for the rely (`PrueferX`,
sound against `AkzeptiertSpecX`), the user's logic with the rely (`NutzerPflichtA`), and concludes
`ZielFX` on every reachable thread machine over GX; the statement of before is `GabbroZielSC`,
derived. Files `grammatik/Grammatik/Speichermodell/{GXMaschine,ZaehlerW}.lean`,
`Zielsatz/Atomar/{BeweisAtomar,AtomarGoalZeuge,AtomarZertifikatZeuge}.lean` (`Zielsatz/BeweisAtomar.lean` is a pinned one-line re-export shim), the atomic-rely block of
`Zielsatz/Kern/Spec.lean`; `MaschineW.lean` (`SchrittW.rmw`); Rust `lean_g.rs` (`read_atomic`,
`Stmt.publish`), `obligations_g.rs` (certificates over the new statement); report
`messung/OPUS-O25C-ATOMICS.md` (retired report, in the history).*

| theorem / definition | file | statement |
|---|---|---|
| `FadenSchrittX`, `FadenErreichbarX`, `FadenInvX`, `fadenErreichbarX_of`, `fadenErreichbarX_GX`, `fadenErreichbarX_von_GX`, `gx_leer_g` | GXMaschine | the thread machine over GX; every G thread run is a GX one; GX over an empty set is G |
| `SegLaufX`, `segZaehleX`, `aktivVorX`, **`frame_schritte_beschraenktX`** | GXMaschine | the time bound over GX segments |
| `SchwachX`, `ZeitAbX`, **`ZielX`**, `FortschrittFX`, **`ZielFX`**, **`GabbroZiel`**, `GabbroZielSC`, `NutzerTeilA`, **`GabbroZielVerbund`**, `GabbroZielVerbundSC` | Spec | the legs over GX, the goal with the rely, the statements of before (moved into Spec from the O25b files: `GetrenntR`, `GeteiltA`, `GeteiltV`, `AkzeptiertSpecX`, `PrueferX`, `LogikPflichtA`, `NutzerPflichtA`, `RennfreiBisGA`, `SperrWechselGX`, `SperrSichtGX`, `KernHaltGA`) |
| `keine_verklemmungFX`, `fortschrittFX_aus`, `folgeG_erreichbarX`, `kernHaltEA_aus`, `kernHaltE_of_EA`, **`zielX_aus`**, **`zielFX_aus`** | BeweisAtomar | every leg at every GX-reachable machine and thread machine, from the premise groups with the rely |
| `geteiltV_mitRuhe_eq`, **`gabbro_ziel`**, `gabbro_ziel_gx`, `nutzerPflichtA_ohne_atomar` | BeweisAtomar | THE GOAL (axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `ziel_of_X`, `zielF_of_X`, `geteiltA_leer`, **`gabbro_ziel_sc_aus`** | BeweisAtomar | the statement of before, verbatim, is a corollary |
| `akzeptiertSpec_verbindeX`, **`gabbro_ziel_verbund`**, **`gabbro_ziel_verbund_sc_aus`** | BeweisAtomar | linked units with the rely, and the linked statement of before derived |
| `ExchangeKopf`, `exchangeKopf_glob`, **`SchrittW.rmw`**, `w_kein_verlust`, `wr_iff` | MaschineW, RMW | RMW atomicity in W itself; no lost update |
| `ZaehltHoch`, `KetteInv`, `w_kette`, **`w_zaehler`**, `w_zaehler_zwei` | ZaehlerW | the counter on W: gap-free chain, newest = start + number of writes |
| `n1E_gabbro`, `n1_stale_x`, **`n1_gx_nicht_g`** | AtomarGoalZeuge | `gabbro_ziel` on the flag; the stale read is a covered GX step and no G step |
| `g162_alt_abgelehnt`, `g162_neu_akzeptiert` | AtomarZertifikatZeuge | example 162: refused by the checker of before, certified under the new one |

(End of file — §11 added 2026-09-13, lane 133; §12 added 2026-09-13; §13 added 2026-09-13; §14 added 2026-09-13; §15 added 2026-09-13; §16 added 2026-09-14; §17 added 2026-09-14 (floats); §18 added 2026-09-14 (budget, start reasons); §19 added 2026-09-14 (reason-return invariants, progress); §20 added 2026-09-14 (gabbro_ziel proved, e0 removed); §21 added 2026-09-15 (waiting bound); §22 added 2026-09-15 (GabbroZiel repaired: one program, owned start, payloads); §23 added 2026-09-15 (fourth round: floats as logic, no wait cycle, stops by kind); §24 added 2026-09-15 (G1: every type decoded, the non-return stop); §25 added 2026-09-15 (W1: empty answer types refused, `nieZurueck` is `never`); §26 added 2026-09-15 (stage (b): the concurrent closing theorem for 124); §27 added 2026-09-15 (the generic closing theorem `schlusssatz`, chain count 2); §28 added 2026-09-15 (`korrOk` widened to its own lemma stock, 23 arms, chain count unchanged); §29 added 2026-09-15 (A2 discharged: the emitted C text parsed in Lean); §30 added 2026-09-15 (`korrOk` gets its block structure: if, let of a call, traverse); §30 added 2026-09-15 (korrOk gets its block structure); §31 added 2026-09-15 (O13 closed: 72 GB -> 6,86 GB, the fuel claim withdrawn); §32 added 2026-09-15 (the runtime's ticket lock: the lock premise becomes a theorem, two findings); §33 added 2026-09-15 (the arena as sugar: alloc/reset get a Lean form without a new constructor); §34 added 2026-09-15 (the transfer chain closed on 104 and 108: the user's duty proved over the exported unit, and a guardian on the generated Lean); §35 added 2026-09-15 (part 4's condition halved: no hardware outcome for a certified program, the residue named, the adequacy fragment measured); §36 added 2026-09-15 (the handler congruence of execEnd, depth monotonicity of rufAt, and part 4's logik condition reduced to ONE frame fact); §37 added 2026-09-16 (a chain for a program that touches a device: `korrOk` carries the register store, the register read and the checked read, with the hardware profile as a named premise); §38 added 2026-09-15 (the frame fact holds at every world; the lock hypothesis is gone); §39 added 2026-09-18 (lane O-1: the checked clone handoff -- `stack`, `child`, (d)/(d2), `C185`); §40 added 2026-09-21 (fix lane F1: integer `match` -- CFormMatch claims corrected, `N411`-`N414`); §41 added 2026-09-21 (fix lane F2: dynamic arenas -- ArenaDyn reworked, `N426` upper bound, `N211` across calls); §42 added 2026-09-22 (fix lane F5: gate contracts split -- caller precondition vs hardware ensures, `N463`/`N464`); §43 added 2026-09-22 (fix lane F6: bounded strings -- the length-fact index rule, `N465`); §44-§46 added 2026-09-22 (fix lane F8: nested-array read witness, the 124 certificate relation, divergence and the spin); §47 added 2026-09-22 (fix lane F10: worker pools in the goal theorem, `einzeln := EinzelnPool`); §48 added 2026-09-22 (fix lane F11: same-core interrupt preemption, the leg `keinKernHalt`); §49 added 2026-09-26 (Opus agent A: threads created at run time, the thread machine in `GabbroZiel`); §50 added 2026-09-26 (Opus agent B: the memory model beyond DRF-SC, machine W, the leg `schwach`); §51 added 2026-09-26 (Opus agent C: one certificate per exported program, the register of the rest); §52 added 2026-09-26 (Opus lane O25: racing atomics over W -- the memory half, the language-carried legs, `N481`-`N483`); §53 added 2026-09-26 (Opus agent D: invariants beyond the returns, four legs of `Ziel`, `ZielF.spawnSicht`, `N496`); §54 added 2026-09-26 (Opus agent E: linking separately compiled units, `GabbroZielVerbund`, `N501`-`N505`); §55 added 2026-09-26 (Opus lane O25b: the atomic rely, every leg of `Ziel` with shared atomics over W, standalone); §56 added 2026-09-26 (Opus agent G: the four obligations of OFFEN O1, the leg `folge`, `N531`/`N532`; §55 on its branch, renumbered at the merge beside Opus lane O25b); §57 added 2026-09-26 (Opus agent H: handlers in the unit, the leg `keinKernHalt` carried by (a)); §58 added 2026-09-26 (Opus lane O25c: the atomic rely IS the goal, `GabbroZiel` over machine GX, `SchrittW.rmw`, payload-free atomics certified; §57 on its branch, renumbered at the review beside Opus agent H); §§1-10 history above.)

## 59. The masking promise is realised in the C, and the handler trigger is a `via` word (server lane, 2026-09-28, TODO §0e K3)

**No new theorem.** What moved is the relation between §57's leg and the artefact, plus one
component's premise; both are recorded here because §57 reads differently now.

| | |
|---|---|
| **before** | `masks irqs` was a promise about the environment with nothing keeping it in the emitted C, and `Kontext::unterbricht` -- the premise of `maskenB`/`H102` -- was the literal path word `idt` |
| **now** | the RUNTIME keeps the promise per flavour: bare metal `METALL_SPERRE_MASKIERT` (Opus agent J), Linux kernel module the MASKED pair the program bound (`laufzeit/kmodul/sperre.h` over `bindung.h`; `raw_spin_lock_irqsave` in `bibliothek/linux-kmod`, under the named assumption `kern_bindung_maskiert` -- K7, 2026-09-28). `unterbricht` is "the entry carries a `via` path", in `kontexte.rs` and in `lean_g.rs` alike |
| **why it is strictly stronger** | more dispatch roots become handlers, so `maskenB` has to hold over more programs. 0 corpus diff: nine `via` words at an `entry`, all `idt`. Witnesses `beispiele/gift/1364` (0 errors before, `H102` after) and `beispiele/166` (the same with `masks irqs`, clean and CERTIFIED as `G166_eintritt_irq_maskiert`) |
| **measured** | retired `pruefe-akzeptiert-diff`: all ten pins on 29/29 comparable programs, `--selbsttest` green both ways (`masken` accepts 59, refuses the `gift/460` shape at `masken` alone). In QEMU, retired `pruefe-kernelmodul` probe `takt`: `ticks=26 landed=0` -- 26 hardirq arrivals, none inside a critical section on the holding core -- and the unmasked mutation does not finish |
| **what is still NOT claimed** | `KernPlan` is not RELATED to the C in translation validation: the C is measured to keep the promise, and the chain does not prove it. The vector, the registers and the steps still have no form in `Einheit`, and handler re-entry stays outside (OFFEN O19) |

## 60. Premise (b) for EVERY source text: the duties are computed in Lean (parser lane, 2026-09-30, P6)

**The principle** (Simon, 2026-09-30): nothing in the compiler or the checker is there for particular
programs; GabbroV is proved always right by GENERIC theorems over every source text. This section is
that statement for premise (b) of the goal theorem, in `bruecke/Bruecke/Quelle.lean` (Mathlib-free, on
`grammatik`'s toolchain; `bruecke/Bruecke/Vorlage.lean` writes the template).

| Lean name | File | What it says |
|---|---|---|
| `uOf`, `nullB`, `nullSp`, `einheitAllg` | Quelle | the elaborated program of a text; the zero memory exists (`nullB`); the unit built from the front end's output (no lock invariant, trivial axiom ensures, no declared start) |
| **`Pflichten src`** | Quelle | THE STATEMENT, computed: `uOf src = some u`, the shape checks (`nullB`, `stimmigB`, `rangB`) and `meetsU` of every function. Nothing printed by Rust is in it |
| `lower_of_uebersetze`, `uOf_eq` | Quelle | the lowering is the last stage of `uebersetzeAllg`; the parse of a text is its `uOf` |
| **`nutzer_aus_quelle`**, `nutzerA_aus_quelle` | Quelle | `Pflichten src → uebersetzeAllg src = .ok ⟨u, P, fs⟩ → ∃ hn, NutzerPflicht (einheitAllg u P hn)` -- **over every `src`**; the atomic-rely twin. Axioms `propext`, `Classical.choice`, `Quot.sound` |
| `pflichten_104`, `pflichten_108`, `nutzer_generisch` | Instanz104/108 | WITNESSES (non-degeneracy): `Pflichten` holds on two real programs, with GabbroV's own duty proofs |
| `vorlage` | Vorlage | `gabbro prove --template --source`: the person's file pinned to the text, the duties as the computed statement, the stage outputs as hints the kernel checks |

**What is NOT claimed:** the fragment premises -- no lock invariants, no axiom ensures, no declared
starts, no atomics, `requires` lowered to `true`, the `ensures` forms `== < <=` with `and/or/not`,
zero initial memory, no arithmetic in the bridge (refused by name: `sideExpr` is `none`). Each is a
construct the Lean front end REFUSES by name; the plan to lift each is `STAND-P.md` (retired report, in the history) /
`messung/PARSER-LANE-REPORT.md` (retired report, in the history).

## 61. A foreign call at the top level of a body: `Endblock.bindAxiom` (C-free lane, 2026-09-30)

**The gap.** A body is an `Endblock`, and `Endblock` had no binder for a foreign call: an axiom's
answer could be bound only inside a nested `Block` (`Block.bindAxiom`). Every `syscall` gate of the
corpus and of the network stack is called at the top level of a body, so all of them stood outside
the model (the exporter's LG004 "`Endblock` has no such constructor").

| Lean name | File | What it says |
|---|---|---|
| `Endblock.bindAxiom` | Syntax | the premises of `Block.bindAxiom` (answer type, the four frame proofs), an END-BLOCK rest |
| `execEnd` (arm) | Semantik | the block form's meaning: the oracle answers, `einpassenErg` decides, the rest runs or the head stops at `.hardware (.annahme a)` |
| `RufSchrittG.endeBindAxiom` | RufMaschineG | the machine rule: `dannBindAxiom` with the rest in `ende` position |
| `Zielsatz.RestHalt` (two arms) | Zielsatz/Spec | the SAME stops `KopfHalt` names at `Block.bindAxiom` -- `hardware`, `nieZurueck` -- at `.ende (.bindAxiom ..)`; reviewed diff in the header block "end-block gate". No stop kind, premise or conclusion moves |
| `fort_ende` (arm) | Fortschritt | progress: such a head steps (`endeBindAxiom`), or stands at a named stop -- `nieZurueck` only for an axiom `-> never` (`antwortenB`, via `Endblock.ants`), `hardware` otherwise |
| arms in ~40 files | RahmenTreu, Satz, SperreSem, AtomarSem, ZielOrt*, KostenG, Nichtinterferenz/*, MitRuhe*, ... | every property of an end block carried through the new constructor, each a mirror of its `Block.bindAxiom` arm |
| `beispiele/181` | Zertifikat/G181_gate_at_top_level | WITNESS: a certified program whose value gate binds at the top level and whose unit body ENDS in a `-> never` gate (behind it the body's own implicit return, dead in G as in the C) |

**Four catch-all definitions were wrong for the new constructor and now name it** (a `| _ => true`
that would have skipped the rest): `Endblock.ueberBoden` (Satz), `Endblock.ohneLocks` (SperreSem),
`Endblock.ohneEwig` (Durchgaenge), `Endblock.ohneOrakel` (RufAdaequatG). Found by a scan of every
definition over `Endblock` with a wildcard arm, not by the compiler -- *a catch-all compiles.*
Two step functions answered `none` for it and had to learn it (`Nichtinterferenz/Schritt.lean`'s
`kEnde`, for the theorem that every machine rule computes `kSchrittK`).

**What is NOT claimed:** a `-> never` call that ENDS an `else` which must not fall off, and a
fallible gate (`or R`) anywhere -- both still refused by name (LG004, LG007). The bridge to GabbroV
(`bruecke/`) builds unchanged; the new form is outside its fragment, as every gate is.

## 62. The reason channel of a foreign body: `bindAxiomElse` and the template `tor.fehlbar` (C-free lane, 2026-09-30)

**The gap.** A fallible `syscall` gate (`-> T or R`) answers a value or a reason, and `D.Ax` had no
channel for the reason (`aerg : Option Ty`); the exporter refused every unit with such a gate
(LG007) -- among them every OS call of the network stack.

| Lean name | File | What it says |
|---|---|---|
| `Deklaration.agruende` | Syntax | the channel's reason count of a foreign body; default `fun _ => 0`, so every declaration of before is unchanged |
| `Block.bindAxiomElse`, `Endblock.bindAxiomElse` | Syntax | `bindCallElse`'s shape over a foreign body: the value binds and `rest` runs, or the reason binds and `err` (an end block) runs |
| `sonstPasst`, `axiomAntwortSonst`, `axiomAntwortSonst_fst` | Semantik | the raw word carries the pair packed like a `tagged` value (`summePasst`'s convention: case 0 the value, case `i + 1` reason `i`); the world is `axiomAntwort`'s, so every frame lemma carries over |
| `dann/endeBindAxiomElseOk/Grund` | RufMaschineG | four machine rules; the reason case runs `err` in block position (`.dann err.alsBlock.2 (.abbruch (.schrumpf k))`, as `rueckGrund` for a call) or as the end block (`.ende err`) |
| `KopfHalt`/`RestHalt` (one arm each) | Zielsatz/Spec | the stop `hardware` where the word decodes to neither value nor reason; reviewed in the header block "end-block gate" (second slice). The answer class always holds the reasons, so no `nieZurueck` case and no new `antwortenB` clause |
| `fort_dann`/`fort_ende` (arms) | Fortschritt | progress: such a head steps (value or reason) or stands at the named `hardware` stop |
| `sonstPasst_ru`, `axiomAntwortSonst_ruG` | MitRuheSemantik | the idle-root translation keeps the channel (`D.mitRuhe.agruende := D.agruende` -- a defaulted field would have dropped it silently) |
| `axiomAntwortSonst_rel` | Nichtinterferenz/Lokal | noninterference: related worlds decode to the same outcome |
| **`tor_fehlbar`** (+ `_wert`, `_grund`, `_zeuge`) | SchablonenOhneLibc §3 | THE TEMPLATE: for every kernel word and every errno table, the stub's decoding (`dekodiere`, Syscall.lean), packed (`packe`), is decoded by G exactly so -- value, reason, or the hardware stop. Row `tor.fehlbar` in `schablonen.rs`, every premise bound |
| arms in ~55 files | ZielOrt*, Rennfrei*, KostenG, SperreSem, AtomarSem, MitRuhe*, Folge*, ... | every property of blocks and end blocks carried through the new constructors; the replay proofs of the `Ziel` legs (`ZielOrtVoll`, `-Ax`, `-Geraet`, `-Rahmen`, `-Sperre`, `AtomarAkteur`) gained real cases, since the fragment predicates (`vOk`, `gOk`, `rOk`) admit the form |
| `beispiele/182` | Zertifikat/G182_fallible_gate | WITNESS: a certified program with a fallible gate called at the top level |

**Measured after the slice:** the five corpus programs that stopped at LG007 (74, 90, 149, 163, 164)
now stop at their next wall, LG003 (a gate `requires`). **Not claimed:** an `else` that returns or
matches the reason itself (`return e;`, `match e { … }`) -- an end block has no case split over a
reason yet -- and a fallible gate whose answer is not an integer range; both refused by name.

## 63. A gate that hands over a REGION: the template `tor.region` (C-free lane, 2026-09-30)

**The decision.** Simon, 2026-09-30: memory from outside comes as a region, never from a number;
no int->ptr conversion enters the language; in Lean ONE generic form, "a foreign routine hands over
a new region". A `syscall` answering `ptr<normal, …> u8 or R` was accepted by the checker and
refused by the emitter (`C183`); it lowers now, and the extent its contract names is held.

| Lean name | File | What it says |
|---|---|---|
| `regionStumpf` | SchablonenOhneLibc §4 | the emitted stub (`emit.rs`, `Antwort::Region`) statement by statement: the `-4095` fence, the errno comparisons in table order, the zero test, the address |
| **`tor_region`** | SchablonenOhneLibc §4 | THE TEMPLATE: for every word an `int64_t` holds and every errno table, the stub IS `dekodiere` (Syscall.lean) over the range `1 .. 2^63 - 1` -- the decoding `tor_fehlbar` proves against G's reason channel |
| `tor_region_adresse`, `tor_region_fehler_kein_zeiger` | SchablonenOhneLibc §4 | the address handed over is the kernel's word and never zero; no error word becomes an address |
| `Region`, `RegionVertrag` | SchablonenOhneLibc §4 | the generic form: the answer reaches at least `n` bytes and shares none with a region live at the call -- the gate's `ensures n <= lenof(result)` plus its assumption's sentence, user logic, no operating system |
| **`region_zugriff`** (+ `_grenze`) | SchablonenOhneLibc §4 | what `N571` makes of the contract: an index with `i + 1 <= n` lies inside the new region and inside no other live one; the boundary witness shows the premise is not decoration |
| `tor_region_zeuge` | SchablonenOhneLibc §4 | WITNESS: `mmap`'s table, a word of each kind, a 4096-byte region beside a live one |

**The checker side** (no new `N` code): the extent clause of a body-less callee's `ensures … <=
lenof(result)` is booked on the name a `let … else` binds the answer to (`m1.rs`,
`ergebnis_ausdehnung`), if that name is bound once and never assigned and the arguments name only
constants and parameters the body leaves alone; `N571` and `N463` (the bare form too) read it like a
`requires` clause. Gifts `1383`-`1387`, example `183` (built `nolibc`, runs, imports nothing).
**Not claimed** (OFFEN O37): machine G has no byte pointers, so 183 stays `UNCERTIFIED` (first `LG003`, the gate's `ensures`; behind it `LG002`);
nothing releases a region; a Gabbro body cannot pass an extent on.

## 64. The hosted arena runtime as a generated template: `arena.dyn` (C-free lane, 2026-09-30)

**The gap.** `laufzeit/arena_dyn.c` was handwritten C behind premise (d) `Laufzeit.reserve` /
`.commit`, handing the binding addresses as numbers. The generated hosted driver writes that
runtime now (`treiber.rs`, `ARENA_LAUFZEIT`; `gabbro runtime arena` prints the same bytes for a
harness), and the binding's storage and report calls are Gabbro (`bibliothek/linux/linux.gab`:
`gabbro_os_reserve` over a region gate, `gabbro_os_commit` over a protection gate under
`requires bytes <= lenof(stelle)`, `gabbro_os_melden` over a write gate and constant tables,
`gabbro_os_ende` over an exit gate, `-> never`).

| Lean name | File | What it says |
|---|---|---|
| `aufrunden`, `abrunden`, `spanne`, `commitStart`, `commitEnde` | SchablonenArena | the template's arithmetic, as the C writes it |
| **`arena_spanne_passt`** | SchablonenArena | the span covers every slot, is whole pages, and no `uint64_t` intermediate wraps (32-bit `max`/`elem`, page at most `2^32`) |
| **`arena_commit_bereich`** | SchablonenArena | a commit range covers the new slots, lies on pages and inside the span -- the binding's `requires` at the template's call |
| `arena_commit_monoton`, `arena_ueber_der_decke` | SchablonenArena | the prefix only grows; one slot past the ceiling needs a byte past an exact span |
| `arena_zeuge` | SchablonenArena | WITNESS on the os-probe's arena (8-byte slots, ceiling 65536, grown by 1024) |

`Zielsatz/Kern/Spec.lean`: comment only, header block "arena runtime"; (d) `Laufzeit.reserve` and
`.commit` reworded (the storage is the program's binding under the proved template; no definition,
premise or conclusion moves). Measured: retired `pruefe-os-bindung` GREEN and all 8 harness gifts
caught; retired `miss-arena-decke` GREEN (10 MiB and 32 GiB ceilings, same binary); retired `pruefe-osfrei`
0 tokens (3 before, the Spec's own). Hosted C0 1174 -> 818 lines.

## 65. Hosted locks and the page return without C: `sperre.ticket`, `region.leeren` (C-free lane, 2026-09-30)

**Locks.** The hosted driver writes the ticket lock `CTicket.lean` proves (THEOREM-MAP §32) in place
of the binding's `pthread_mutex_t`: `treiber.rs::SPERRE_TICKET`, the four instructions word for word,
a zero `static` as the free lock (no initialiser any more), and every 64 spins the program's yield
(`gabbro_os_nachgeben`, a Gabbro function over a `pure` gate) -- a stutter of `dreht`. Register row
`sperre.ticket` cites `ticket_ausschluss`, `erreichbarT_exklusiv`, `ticket_fifo`,
`ticketLP_sperrAbstrakt`, `schrittT_proj`, `ticket_frame`; the 2^32-ticket premise is bound to the
thread count. The hand drivers `laufzeit/start.c`, `start_pool.c` (pthread-era originals of the
generated driver) are deleted.

**The page return.** `reset X at i count n;`'s emitted helper computes the whole pages itself and
hands them to the program's `gabbro_os_seiten_zurueck(stelle, bytes)` (Gabbro, over a `madvise`
gate) as a region:

| Lean name | File | What it says |
|---|---|---|
| `leerenVon`, `leerenBis` | SchablonenArena §2 | the helper's offsets of the whole pages |
| **`leeren_teilung`** | SchablonenArena §2 | edges and pages cover the range exactly, the pages fit the rest (the binding's `requires`), both ends on a page |
| `leeren_zeuge`, `leeren_ohne_seite` | SchablonenArena §2 | WITNESS (10000 bytes from 5000); a range inside one page has no whole page |

Measured: retired `pruefe-seiten-zurueck` GREEN (RSS 2504 -> 1608 KiB bound, stays unbound, poison
caught -- the numbers of the C binding it replaces); retired `pruefe-os-bindung` GREEN with the ticket
lock, gifts 1-8 caught. Hosted C0 818 -> 687 lines.

## 66. Hosted threads without pthread: `tor.trampolin` and `faden.laufzeit` (C-free lane, 2026-09-30)

**The gap.** Hosted threads were `pthread_create`/`pthread_join` in `bibliothek/linux/linux.c` (the
driver's roots) and a raw `clone` in the same C file behind `laufzeit/faden.c` (the run-time
`start`). Now every gate that claims a stack gets a C-only TRAMPOLINE from the emitter (the
gate's `syscall`; in the child the root, then the end, on the handed stack), and the generated
thread runtime starts every root through the program's stack gate `gabbro_os_klon_tor`
(`linux.gab`), with the root and the program's `-> never` thread end handed as C designators in
two callee-saved registers the gate neither binds nor destroys (`C187` otherwise).

| Lean name | File | What it says |
|---|---|---|
| `nachSyscall`, `kindPfad` | SchablonenFaden §1 | the kernel's hand-over and the trampoline's child path |
| **`trampolin_kind`** | SchablonenFaden §1 | the child calls root then end, each with `rsp + 8` 16-aligned inside the 24 bytes below the handed top; `ud2` only if the end returns |
| `trampolin_ohne_bewahrung`, `trampolin_eltern` | SchablonenFaden §1 | without preserved registers the child jumps to 0; the parent gets the kernel's word |
| `wort`, `vertragsSpur` | SchablonenFaden §2 | the join word under the gate's contract (id before the child runs, 0 after its end) |
| **`faden_warte_korrekt`** | SchablonenFaden §2 | the wait returns only after the thread's end, for every child length and every look |
| `faden_warte_ohne_eltern`, `faden_zeuge` | SchablonenFaden §2 | the order is load-bearing; WITNESS |

The driver's stacks are regions of the binding (`gabbro_os_reserve`/`_commit`) with the lowest page
left unwritable. Found on the way: `N572` (every stack-gate call hands to a `child` region) and
the clone trap's store order (OFFEN O38). Measured: retired `pruefe-os-bindung` GREEN (the os-probe's
two roots, arena and lock, no pthread), 8 gifts caught; retired `pruefe-emission` ALL PASS including
the 200000-round join race and the concurrent twin (20 of 20); hosted C0 687 -> 28 lines.

## 67. The `child` triple's region outlined: `tor.kind` (C-free lane, 2026-09-30, OFFEN O38)

Lane 260 lowered `let v = g(…) else …; if v == 0 { child { … } }` to an `asm goto` that jumped, in
the child, to a label inside the parent's function: the region's C then read the handed value
through the parent's frame. Now the region is `gabbro_kind_<nr>(T handed)`, and the trap's child path
moves the handed value out of the stack register, aligns the handed stack and CALLS it.

| Lean name | File | What it says |
|---|---|---|
| `kindNachSyscall`, `kindRuf` | SchablonenFaden §3 | the child's registers after the gate, and the one call it makes |
| **`kind_region`** | SchablonenFaden §3 | the region is called with exactly the handed value, SysV-aligned strictly below the handed top, and `ud2` never runs for a region that does not return |
| `kind_region_rueckkehr`, `kind_region_zeuge` | SchablonenFaden §3 | a returning region would run into the trap's `ud2`; WITNESS |

Measured on hosted Linux with a real `clone` (`kratz/c/s10/kind`): a triple whose region reads the
handed top and ends the process with 42 exits 42 at `-O0` and `-O2`. `tests/klon_faden.rs` pins the
new shape (no `asm goto`, no label, one call, one region function).

## 68. The kernel-module runtime as generated text: `arena.modul` and `modul.lebenslauf` (C-free lane, 2026-09-30, C2)

**The gap.** Every `.ko` a `module` unit became carried `laufzeit/kmodul/` -- `kmodul.c` (the
loader's entry points), `arena.c` (a `vzalloc` per arena with a `module_param` budget),
`sperre.h`, `bindung.h`, five type shims -- and, with an `atomic`, the 273-line LKMM table
`bibliothek/linux-kmod/stdatomic.h`. Now `gabbro build` writes the module driver itself
(`treiber.rs::erzeuge_kmod`): the arena storage is a static pool of the manifest's `provision`, the
loader's two entry symbols and the licence note are MANIFEST words (`kmod <kbuild> <load>
<unload>`, `note .modinfo license=…`), the type headers and `<stdatomic.h>` are generated from the
compiler's own predefined types and C11 builtins. No kernel header and no kernel name in the
driver; every kernel call below the unit is the program's binding.

| Lean name | File | What it says |
|---|---|---|
| `spanne`, `reserve`, `grow`, `Inv` | SchablonenModul §1 | the pool arithmetic of `KMOD_ARENA` |
| **`arena_modul_inv_reserve`**, **`arena_modul_inv_grow`** | SchablonenModul §1 | a reservation establishes and every grow keeps `committed <= max`, `committed * elem <= span <= V` |
| **`arena_modul_slot_im_lager`** | SchablonenModul §1 | every reachable slot lies inside the static pool |
| `arena_modul_kein_ueberlauf`, `arena_modul_monoton`, `arena_modul_ueber_der_decke` | SchablonenModul §1 | no 64-bit wrap; the prefix only grows; past the ceiling is the stop |
| `arena_modul_zeuge` | SchablonenModul §1 | WITNESS: the `halde` probe, two grows committed, the third refused below the ceiling |
| `bindeAlle`, `laden`, `entladen` | SchablonenModul §2 | the two entry points' order |
| **`laden_erfolg`**, `laden_init_erst_nach_bindung`, `laden_ruft_kein_exit`, `laden_start_nach_init`, **`laden_verweigert_wartet`**, `entladen_wartet_vor_exit` | SchablonenModul §2 | bind, lock, init, start; the init only after every arena; never the exit on load; roots only after a good init; a refused load waits for every root it started; the unload waits before the exit |
| `lebenslauf_zeuge_*` | SchablonenModul §2 | WITNESSES: the three probes, gift 4's stop, a refused reservation |

`Zielsatz/Kern/Spec.lean`: comment only -- (M11) now names the compiler's C11 atomics instead of the
LKMM table (review: `messung/SERVER-0E-SPEC-DIFF.md` (retired report, in the history) Part IV), and (d) `Laufzeit.reserve` names
the static pool. Measured: retired `pruefe-kernelmodul` GREEN on all three probes (halde:
refuse-on-full at the provision; takt: `landed=0` over 38 ticks; atomar: 512/256/0/3), 12 of 12
gifts caught; retired `zaehle-c` kmod runtime share 1344 -> 0 lines (what stays is the
binding's `linux-kmod.c` and the probes' own C).

## 69. Code a generated driver hands in: `entry fn`, and the kernel thread start without C (C-free lane, 2026-10-01, C2 slice 3, OFFEN O39)

**The gap.** The kernel-module binding started a root's thread in C (`linux-kmod.c`): the generated
driver handed the root wrapper's address as a `u64` to `gabbro_kern_faden_start`, and the C cast
the number back to a function and joined it with a `struct completion`. Nothing kept a Gabbro
caller from handing any two numbers (OFFEN O39). Now the binding is Gabbro: `gabbro_kern_faden_start(lauf
: entry fn(ptr<normal, rw> u8) -> i32, nummer : u32)` over `kthread_create_on_node` (variadic,
`N573`; its `ERR_PTR` decoded in Gabbro) and `wake_up_process`; the join is a word per root
stored by the driver's wrapper after the root and awaited through `gabbro_kern_schlafe` over
`msleep`. The type `entry fn(…) -> R` is the one shape in which code reaches a foreign body:
values only from generated C (`N576`: a function taking one has no Gabbro caller), handed on once,
whole, outside every loop (`N577`), standing only as a parameter's own type with a contract-free C
signature (`N575`). The exporter refuses a function taking one by name (`LG001`: G has no code
values). The binding's core number went too -- it fed only a holder record a probe read -- so
`linux-kmod.c` is DELETED.

| Lean name | File | What it says |
|---|---|---|
| `FEreignis`, `fwort`, `fSpur` | SchablonenModul §3 | the join word's events: 1 before the start, the start's answer, the root's steps, the wrapper's 0 (or the driver's after a failed start) |
| **`faden_modul_warte_korrekt`** | SchablonenModul §3 | a wait that begins after the start and reads 0 saw the root's whole run, or a failed start and no step of the root |
| `faden_modul_ohne_eins`, `faden_modul_null_zuerst` | SchablonenModul §3 | without the store of 1 (the word is a zeroed static) the wait returns before the root ran; with the 0 stored first it returns while steps remain |
| `faden_modul_zeuge` | SchablonenModul §3 | WITNESS: a good start of five steps read at the end and midway, and a failed start |

NOT proved: the wrapper's instructions after its store run in module text (the unload window the
completion had too), and that the binding keeps `kern_faden_vertrag` (user logic, premise (c)).
`Zielsatz/Kern/Spec.lean` unchanged: the goal's runtime premise (d) already says the declared starts
run; what moved is who writes the start (the binding, in Gabbro) and the driver's join.

## 70. The bare-metal image's generated pieces: `metall.speicher` and `arena.metall` (C-free lane, 2026-10-05, C3 slice 1)

**The gap.** Every bare-metal image linked `laufzeit/metall/arena.c` (one shared static reserve
carved by a counter, a commit budget), `include/math.h`, `include/string.h` and the four memory
functions at the head of `kern.c` -- handwritten C. Now the metal driver writes the PROVED
`arena.modul` pool runtime (§68) behind a reservation by list position, and the build writes the
four memory functions (`<unit>.metall.speicher.c`) and the two header names beside the image
(`treiber.rs::metall_arena`, `METALL_SPEICHER`, `metall_koepfe`; `gabbro runtime metal-arena`,
`metal-memory`, `metal-include <dir>` for harnesses).

| Lean name | File | What it says |
|---|---|---|
| `Sp`, `schreib`, `vor`, `rueck`, `setze`, `vgl` | SchablonenMetall §1 | memory as a function, and the four C loops |
| **`memcpy_korrekt`** | SchablonenMetall §1 | without overlap the destination holds the source; nothing else moves |
| **`memmove_korrekt`** | SchablonenMetall §1 | for EVERY overlap the destination holds the source's original bytes |
| `memmove_vorwaerts_waere_falsch` | SchablonenMetall §1 | the backward branch is load-bearing |
| `memset_korrekt` | SchablonenMetall §1 | every destination byte is `c mod 256`; nothing else moves |
| **`memcmp_null`**, `memcmp_kleiner` | SchablonenMetall §1 | 0 exactly on equal ranges; -1 exactly at a first difference with the smaller left byte |
| `metall_speicher_zeuge` | SchablonenMetall §1 | WITNESS: copy, both memmove branches on overlaps, set, compare both ways |
| `stelle`, `reserviere` | SchablonenMetall §2 | `gabbro_arena_reserve` by list position |
| **`arena_metall_eigene_stelle`**, **`arena_metall_getrennt`**, `arena_metall_fremd` | SchablonenMetall §2 | the pool of the descriptor's own position; two descriptors never share one; a descriptor outside the list gets none |
| `arena_metall_lager_getrennt` | SchablonenMetall §2 | the pools are disjoint byte ranges (with `arena_modul_slot_im_lager`: every reachable slot inside its own arena's pool) |
| `arena_metall_zeuge` | SchablonenMetall §2 | WITNESS: three descriptors, two pools granted, a refused third, a stranger |

NOT proved: that the compiler calls the memory functions only with ranges it owns, and that the
loader zeroes `.bss` (the bare-metal block's `lader`). `Zielsatz/Kern/Spec.lean` unchanged (the arena
on metal is still the static storage premise (d) names; its parenthesis naming `arena.c` in the
Opus agent L block is a dated remark). Measured: retired `pruefe-metall` 18 images booted
on `qemu -smp 4`, every expectation held, 8 gifts bite (158-else with a pool of exactly the floor
answers 1); retired `pruefe-freistehend` 338 of 338; retired `zaehle-c` metal 2090 -> 1879 lines, 7 -> 4
files.

## 71. The bare-metal image's locks and rcu read sides: `sperre.metall`, `sperre.maskiert`, `rcu.metall` (C-free lane, 2026-10-05, C3 slice 2)

**The gap.** The Gabbro-facing locks of a bare-metal image (`METALL_SPERRE`, `_GETEILT`,
`_MASKIERT`, `_MASKIERT_GETEILT`), the rcu read side `METALL_RCU` and the flag helpers were 140
handwritten lines of `laufzeit/metall/metall.h`. They are now the generator's header
`<metall_sperren.h>` (`treiber.rs::METALL_SPERREN`), written by `gabbro build` and `gabbro runtime
metal-include <dir>` beside `<math.h>`/`<string.h>` and included last by `metall.h`; the bytes of
every macro are unchanged.

| Lean name | File | What it says |
|---|---|---|
| `MSchritt` | SchablonenMetallSperre §1 | one step of the generated spin: a `CTicket` step, or the yield (only with `darf`, IF = 1 at the call) |
| **`mschritt_ticket_oder_stotter`**, `metall_sichtbar_ist_ticket` | SchablonenMetallSperre §1 | the yield changes no lock word and is invisible; a visible step is a ticket step (so `ticketLP_sperrAbstrakt` covers it) |
| **`metall_ausschluss`**, `minv_erreichbar` | SchablonenMetallSperre §1 | `TInv` and mutual exclusion on every reachable state of the generated lock |
| **`abgabe_nur_mit_if`** | SchablonenMetallSperre §1 | with IF = 0 the spin takes no yield |
| `sperre_metall_zeuge` | SchablonenMetallSperre §1 | WITNESS: two draws and a real yield on a reachable state |
| `Kern`, `KSchritt`, `MInv` | SchablonenMetallSperre §2 | the holder's core: IF, the local flags, the lock's flag word; a delivery/yield/preemption needs IF = 1 |
| **`maskiert_keine_zustellung`** | SchablonenMetallSperre §2 | IF = 0 from the clearing instruction through draw, spin, section and release |
| **`maskiert_flaggen_zurueck`** | SchablonenMetallSperre §2 | after `L_gib` IF is the caller's |
| **`flaggen_eigen`** | SchablonenMetallSperre §2 | the shared flag word hands every holder back its own store under the abstract lock |
| `sperre_maskiert_zeuge`, `flaggen_zeuge` | SchablonenMetallSperre §2 | WITNESSES: a whole masked claim from IF = 1; two holders in turn |
| **`rcu_gnade_korrekt`**, `rcu_inv_erreichbar` | SchablonenMetallSperre §3 | the count is the readers' total depth; a zero read means nobody inside |
| `rcu_ende_ohne_start_waere_falsch` | SchablonenMetallSperre §3 | without the start/end pairing the count reads 0 under a live reader |
| `rcu_zeuge` | SchablonenMetallSperre §3 | WITNESS: nested reads of two threads, reachable, count 3 |

NOT proved: the C11 orderings (the C and the hardware), counter wrap at 2^32, starvation of a
grace wait (OFFEN O32), and the runtime's own side of the yield (`metall_abgeben` and the
scheduler stay `kern.c`, wall C of `messung/C3-WAENDE.md` (retired report, in the history)). `Zielsatz/Kern/Spec.lean` unchanged: the
goal's lock premise is `LaufzeitC.sperre`, which `ticketLP_sperrAbstrakt` discharges, and the
generated lock refines it step for step.

## 72. The bare-metal image's interrupt descriptor table: `idt.metall` (C-free lane, 2026-10-05, C3 slice 3)

**The gap.** The IDT -- the 256 gate descriptors, the encoding of one gate, the runtime's slots,
`lidt`, and the two installers a metal driver calls for the program's entries -- was a part of
`laufzeit/metall/kern.c`. It is now the generator's `<unit>.metall.idt.c`
(`treiber.rs::METALL_IDT`; `gabbro runtime metal-idt` for harnesses), compiled and linked as a
translation unit of its own; `kern.c` calls `metall_idt_bau`/`metall_idt_lade`, and the timer
and wake vectors are one register (`METALL_TAKT_VEKTOR`, `METALL_WECK_VEKTOR` in `metall.h`).

| Lean name | File | What it says |
|---|---|---|
| `kodiere`, `dekodiere` | SchablonenMetallIdt §1 | the three address fields of a gate, and the CPU's reading of them |
| **`kodiere_dekodiere`** | SchablonenMetallIdt §1 | the gate points at the stub, for every 64-bit address |
| `art_ist_interrupt_gate` | SchablonenMetallIdt §1 | `0x8E` is a present DPL-0 interrupt gate (IF cleared on entry) |
| **`fehlercode_c_ist_die_liste`** | SchablonenMetallIdt §2 | the C test `hat_fehlercode` is exactly the SDM's error-code list |
| `bau`, `nimmt`, `nimmtFc`, `installiere`, `installiereAlle`, `Passt` | SchablonenMetallIdt §3 | the build, the two installers (ending the machine = `none`), what every table satisfies |
| **`installieren_bewahrt_laufzeit`** | SchablonenMetallIdt §3 | after any sequence of installs that return, the timer, wake and spurious vectors are the runtime's |
| **`installieren_passt`** | SchablonenMetallIdt §3 | every program stub sits on a vector of its own error-code kind |
| `installieren_ohne_wache_waere_falsch` | SchablonenMetallIdt §3 | without the refusals a plain stub lands on #GP and the timer is overwritten |
| `idt_metall_zeuge` | SchablonenMetallIdt §3 | WITNESS: entries on 2, `0xF0`, `0x80` and (error-code twin) 13 installed; the timer and a twin on 2 refused; a high-half address encoded and read back |

NOT proved: the SDM's gate format on real silicon (the hardware assumption every metal image
names), that every core executes `lidt` before its first interrupt (the runtime's bring-up order,
`kern.c`), and the stubs (`start.S`, `eintritt_asm.h`, wall D). `Zielsatz/Kern/Spec.lean` unchanged.

## 73. The bare-metal thread runtime: `faden.metall` (C-free lane, 2026-10-05, C3 slice 4)

**The gap.** The section "Cores and threads" of `laufzeit/metall/kern.c` -- per-core run queues,
the scheduler loop, the yield and the timer's C half, the first frame of a new thread, the
thread start and the join -- was handwritten C. It is now the generator's
`<unit>.metall.faden.c` (`treiber.rs::METALL_FADEN`; `gabbro runtime metal-threads`), a
translation unit of its own; `kern.c` keeps the bring-up (LAPIC, ACPI, SMP) and reaches the
cores through the interface in `metall.h` (`metall_kern_setze`, `metall_kern_apic_setze`,
`metall_kern_stapel_oben`, `metall_kern_angekommen`, `metall_kern_schleife`,
`metall_faden_anlegen`; the thread runtime wakes a core through `metall_ipi_senden`).

| Lean name | File | What it says |
|---|---|---|
| `Q`, `Folge`, `Kette`, `haenge`, `nimm` | SchablonenMetallFaden §1 | a core's queue: head, tail, links; the list it holds; the two C operations |
| **`haenge_kette`**, **`nimm_kette`**, `nimm_leer`, `schlange_fifo` | SchablonenMetallFaden §1 | the linked queue refines a list: append behind the tail (duplicate-free), take the head; FIFO |
| `schlange_zeuge` | SchablonenMetallFaden §1 | WITNESS: three threads queued on a fresh core, one taken, a fourth queued |
| `schritt`, `nachSchritten`, **`schleife_fair`** | SchablonenMetallFaden §1 | a pass of the loop takes the head, buries or re-queues it; a thread at position `p` runs after `p` passes |
| `schleife_zeuge` | SchablonenMetallFaden §1 | WITNESS: a thread that ends and three that do not |
| `rahmen`, `schalteAuf`, **`rahmen_korrekt`** | SchablonenMetallFaden §2 | the first frame, popped by `metall_schalte`: zero registers, reset MXCSR/FCW, the entry, SysV alignment |
| `platz_im_bereich` | SchablonenMetallFaden §3 | round robin names a core that checked in |
| `Ereignis`, `wort`, `spur`, **`warte_korrekt`** | SchablonenMetallFaden §4 | a join that begins after the start and reads zero saw the whole run and the burial |
| `warte_ohne_vorbelegung_waere_falsch` | SchablonenMetallFaden §4 | without the store before the queueing a join reads zero with every step still ahead |
| `faden_metall_zeuge` | SchablonenMetallFaden §4 | WITNESS: a thread of five steps read midway, before the burial and at the end; a frame; a placement |

NOT proved: the switch (`metall_schalte`, `start.S`: the register file and stack as the hardware
keeps them -- wall D), the C11 orderings of the join word, and preemption's timing (the LAPIC
timer in `kern.c`, wall A). `Zielsatz/Kern/Spec.lean` unchanged: the goal's runtime premise (d) says
the declared starts run, each on its own thread; what moved is who writes the scheduler.
*Lesson of the proof:* `decide` on 64-bit literal arithmetic (`(0x1F80 + 0x037F * 2^32) % 2^32`)
drove the elaborator past 4 GB and was killed (exit 137); `simp` with the literal simprocs
proves the same in milliseconds.

## 74. Separation at a call boundary: `ParamGetrennt` (`own`/separation slice 2, 2026-10-17, `dokumente/A1-OWN-PAPER.md`)

**The question.** Slice 1 (`R014`, `m3.rs::getrennte_wurzeln`) refuses a call whose two pointer
arguments share a root when one callee parameter is writable or `own`. What does the model need?
In machine G a pointer type `Ty.ptr n rw` names its carrier STATICALLY (table `D.tabNr n`), and a
pointer value is `Unit`. So the argument-to-carrier map of a call is fixed by the callee's
signature, the same at every call site, and `own` reaches the model as read-write (`lean_g.rs`,
`param_ty`). `ParamGetrennt` is therefore a property of the callee.

| Lean name | File | What it says |
|---|---|---|
| `traegerVon`, `zaehltFuerTrennung` | Getrennt §1 | the carrier a parameter type names; writable (incl. `own`) |
| `ParamGetrenntL`, `ParamGetrennt`, `paramGetrenntB`, **`paramGetrennt_iff`** | Getrennt §2 | the parameter-to-carrier map is injective on pairs with a writable side; decided by a Bool |
| **`getrennt_paarweise`**, **`getrennt_schreiben_trennt`** | Getrennt §3 | such parameters name disjoint carriers; a slot store through the one leaves every slot of the other |
| `RahmenUeberParams`, `getrennt_nicht_geschrieben` | Getrennt §4 | the frame is declared over the writable parameters; then a read-only parameter's carrier is not written |
| **`getrennt_lesesicht_bleibt`** | Getrennt §4 | for every frame-keeping call handler (`TreuR`): the read-only parameter's carrier is unchanged |
| **`getrennt_ruf_rahmen`** | Getrennt §4 | the same at `rufAt`, every depth, every world (through `rufAt_treu`, no lock premise) |
| `leihe_wurzel`, **`leihe_nicht_getrennt`** | Getrennt §5 | a re-view at one pointer type answers its argument's root; two names of one root (one writable) are not `ParamGetrennt` |
| `zeuge_aendern_nicht_getrennt`, `zeuge_aendern_lauf`, **`ohne_getrennt_nur_versprechen`** | GetrenntZeuge | COUNTER-MODEL: `aendern(k : ptr rw T, w : ptr r T)`, frame over the parameters, one real `rufAt` run moves `w`'s object from 0 to 5 -- without `ParamGetrennt` the per-parameter frame is false |
| `zeuge_getrennt`, **`getrennt_ruf_rahmen_zeuge`**, `zeuge_getrennt_lauf`, `getrennt_schreiben_trennt_zeuge`, `leihe_wurzel_zeuge` | GetrenntZeuge | WITNESS: `getrennt(k : ptr rw T, q : ptr r U)` is `ParamGetrennt` (decided); every run leaves `U`; the concrete run really writes `T` |

NOT proved, and why (obstructions, not gaps to be closed by a premise): **roots are finer than
carriers** -- two pointer parameters of one table type are one carrier in the model whatever their
roots, so `R014`'s S-1/S-2 (distinct roots) has no model statement to discharge, and an S-1-clean
callee over one table is not `ParamGetrennt` (the counter-model has two distinct parameter names);
**re-views across types do not reach the model** -- pointers to records and foreign re-views are
refused by the exporter (`LG005`, `LG001`; `beispiele/1163` is `UNCERTIFIED LG001`), so the
borrow rule is the model's reading only at one pointer type; **a frame that names a table directly**
(a static root beside a parameter) is outside `RahmenUeberParams`. `Zielsatz/Kern/Spec.lean` unchanged;
`gabbro_ziel` untouched.

## 75. Objects below a table: `ObjGetrennt` (`own`/separation slice 2b, 2026-10-17, `dokumente/A1-OWN-PAPER.md`)

**The question.** Slice 2 (§74) separates carriers: two pointer parameters of one table type are one
carrier in machine G whatever their roots, so `R014`'s distinct roots had no model statement. Simon's
decision of 2026-10-17: the model gets finer objects below a table. **The choice:** an object is a SLOT
(`Obj` = carrier + identity, every field of slot `nr` of `tab`). G's world is already indexed this way,
so nothing in G changes; a pointer to one object is the pair of parameters G already has (capability
`ptr n rw` + index into its table, `ObjPar`, positions from the bottom of the context), so the identity
is a value the caller chooses.

| Lean name | File | What it says |
|---|---|---|
| `Obj`, `storeObj_andere` | Objekte §1 | an object is a slot; a store into one object leaves every field of every other |
| `ObjGetrenntL`, `objGetrennt_paarweise`, **`objGetrennt_schreiben_trennt`**, `objGetrennt_nicht_bei_einem` | Objekte §2 | the argument-to-object map is injective on pairs with a writable side; a store through one leaves the other's object; two positions on one object are not separated |
| **`objGetrennt_ein_obj_iff`**, `getrennt_objGetrennt` | Objekte §3 | with one object per carrier `ObjGetrennt` IS `ParamGetrennt` (§74); carrier separation implies object separation |
| `Var.unten`, `Env.unten`, `ObjPar`, `ObjParTreu`, `objVon`, `ObjGetrennt`, `WVon`, `SlotRahmen` | ObjektRahmen §1-2 | bottom positions; the object a pair names in an environment; the declared frame over the writable object parameters |
| `SchreibOk`, `VarFrei`, `ObjRufOk`, `KeinTabAx`, `oS`/`oB`/`oE`/`oA`/`oG`, `ProgObjOk` | ObjektRahmen §3 | the object discipline over the whole grammar (indirect calls and `schreibBytes` refused) |
| `stmt_obj`, `block_obj`, `end_obj`, `arms_obj`, `grund_obj` | ObjektRahmen §7 | the induction: a run changes no slot outside the writable parameters' objects, and index variables keep their values |
| **`rufAt_obj`** | ObjektRahmen §8 | the model's call keeps the frame over objects at every depth and world (premise `TreuO` only) |
| **`obj_ruf_rahmen`** | ObjektRahmen §8 | under `ObjGetrennt` every run leaves every field of every read-only parameter's object -- also inside the written table |
| **`umsicht_behaelt`** | ObjektRahmen §9 | a body `return k;` answers the object it was handed (the borrow rule as a theorem) |
| `Herkunft`, `Herkunft.wurzeln`, `R014Rein`, `Bedeutet`, `bedeutet_wurzel` | ObjektWurzel §1-2 | the provenance as the checker computes it, the paper's roots (unknown = every root), what a provenance denotes |
| `ParamVerschieden`, `FrischNeu`, `RechteOk`, `HerkunftTreu` | ObjektWurzel §3 | the four NAMED hypotheses: S-2 / `R015`, allocation discipline, rights, faithful provenance |
| `wurzel_getrennt_obj`, **`r014_objGetrennt`**, **`r014_ruf_rahmen`** | ObjektWurzel §4 | disjoint roots give `ObjGetrennt` under the four hypotheses; composed with `obj_ruf_rahmen` |
| `allocStrom_neu`, `allocStrom_inj`, **`frischNeu_aus_arena`** | ObjektWurzel §5 | `FrischNeu` as a theorem for the model's allocator (`ArenaDyn.freiAlloc`, duplicate-free free list) |
| `Herkunft.wurzelnR`, **`rust_lesart_luecke`** | ObjektWurzel §6 | FINDING, **repaired in the checker 2026-10-17 (commit `a6a2e2d6`)**: the first Rust reading (untraced name = no root, pair skipped) was unsound in the model; now an untraceable pointer is UNKNOWN and equals every root (§76) |
| `zeuge_obj_nicht_getrennt`, `zeuge_lauf_gleich`, **`ohne_objGetrennt_nur_versprechen`** | ObjektZeuge | COUNTER-MODEL: `aendern(kp : ptr rw T, k, wp : ptr r T, w)` at `k = w = 0`; one real run moves `w`'s object 0 -> 5 |
| `zeuge_prog`, `zeuge_objGetrennt`, **`zeuge_obj_ruf_rahmen`**, `zeuge_lauf_getrennt`, `zeuge_nicht_paramGetrennt`, **`zeuge_obj_feiner`** | ObjektZeuge | WITNESS: the same function at `k = 0, w = 1`, ONE table: `ObjGetrennt`, every run leaves `T.slots[1]`, the run writes `T.slots[0]`, `ParamGetrennt` fails |
| `zeuge_umsicht`, `zeuge_sicht_lauf`, `zeuge_leihe_nicht_getrennt`, `zeuge_r014_leihe` | ObjektZeuge | borrow rule on `sicht(p, k) -> index T { return k; }`; `aendern(k, sicht(k))` never separated, refused by `R014Rein` |
| `zeuge_r014_frisch`, `zeuge_S2`, `zeuge_frischNeu`, **`zeuge_r014_ruf_rahmen`**, `zeuge_r014_lauf` | ObjektZeuge | the bridge end to end: `aendern(k, f)` with `f` the allocator's first fresh slot |

NOT proved, and why: **objects are single slots** -- a record over a byte buffer (a `format`, n slots)
is not one object, so `udp-echo`'s cross-type re-view `kopfworte_von` still has no model statement
(needs range objects and `schreibBytes` in the discipline); **the checker's walk over `let`s** is not
formalised over G syntax, its correctness is the premise `HerkunftTreu`; **the discipline is a `Prop`**,
no Bool the exporter could compute; **`LG005`/`LG001` stay** (the stretch was not clean, see
A1-OWN-PAPER.md §6, slice 2b). `Zielsatz/Kern/Spec.lean` unchanged; `gabbro_ziel` untouched.

## 76. Own, slices 3 and 4: the `R014` repair, the `R015` boundary hint, `noalias` (2026-10-17, `dokumente/A1-OWN-PAPER.md`)

No new Lean theorem: this section books what the checker and the LLVM emitter did with §74/§75.

| What | Where | Status |
|---|---|---|
| **The repair of the slice-2b finding.** `getrennte_wurzeln` no longer skips a pair with an untraced name: a field read, an index, an indirect call, an unresolved callee, an argument that is no bare name and a re-view of an untraced pointer are `UNBEKANNT`, a root equal to every root; a fresh root is only for an answer that comes from no pointer argument. Pairs of two read-only parameters stay free | `crates/gabbro-check/src/m3.rs`, sentence `m3.zeiger_wurzel` (`saetze.rs`), `tests/wurzeln.rs` (10 rows, three of them new: function-pointer re-view, field pointer, read-only twin), probe `beispiele/gift/1444-alias-sicht-und-quelle.gab` | measured: 0 new `R014` over every tracked `.gab` except the probe |
| **`R015`**, the boundary: a function that assumes two pointer parameters distinct (one writable or `own`) and is `pub` or called by no body of its unit says so | `m3.rs`, sentence `m3.zeiger_wurzel_grenze` | a HINT, not a refusal; it is the Rust face of the hypothesis `ParamVerschieden` of `r014_objGetrennt` (§75) |
| **`noalias`** on a writable pointer parameter of an *internal* function the checker holds the whole call of (not `pub`, has a body, called from a body of the unit, address never taken, named by no entry/boot/concurrent item, `effects` naming nothing but its own pointer parameters) | `crates/gabbro-check/src/llvm.rs`, `tests/noalias.rs` (one positive row, four refusing twins), `dokumente/LLVM-BACKEND.md` | measured: 10 `noalias` over `beispiele/` + `messung/*/` (was 2), IR verified with `opt`; **not a Lean judgment**: the model side is §74/§75, the rule itself is a Rust checker rule |

NOT proved: the `let` walk of the checker over G syntax (the premise `HerkunftTreu`); `R004`/`R007` as
special cases of `R014` (they stay separate rules); records over byte buffers (range objects, `LG005`/
`LG001`). `Zielsatz/Kern/Spec.lean` unchanged; `gabbro_ziel` untouched.

## 77. The Lean parser as a measured front end: coverage matrix, no new theorem (Track P, 2026-10-17)

Statement-level facts: `lex_keywords` and `wortschatz_248` hold over the 248 words of `kw.rs` (five were missing);
`u104parse`, `u104elab`, `u104lower`, `lowerAllg104*`, `lowerAllg108*` and the `ElementTiefProben1..7` probes hold over the
changed readers (`lockT` 7 fields, `globT` 7, `arenaT` 6, `SSyscall` = `SWay` + `SGate`, `SAnw.each` structured).
Statics (2026-10-18): `declOf` carries `Glob := Fin u.globs.length` (`gdarf_globs`: no static is guarded), the call rule
checks the written statics (`sigGSchreibt_eq`, `vGSchreibt_eq`), the initial memory starts each static at its
initialiser (`sp0GlobWert`, `sp0Of_glob`, `sp0OkB_glob`) and an initialiser outside its type has none
(`sp0_glob_luecke`); `gv_startPflicht_zeuge` holds on the array unit and on the static unit `uStatik`;
`gvLuecke_fragment_ohne_atomar` (a unit without an `atomic` item has no atomic carrier; `atomar` is the flag of the
static, payload-free atomics elaborate) and `gvLuecke_statik_ohne_form` (a placement or a
`shared` word on a static is refused) replace the `Glob = Empty` statements. `GvParserFragment3`/`4` and the wrappers
`elabU02`..`elabU05` are deleted (they dropped items the elaborator now reads or refuses). Probes: `UebersetzeProben4`..`12`
(`let`, `if`, `return`, `traverse`, `locks`, statics; each with a refused twin). Measured, not proved: 170 of 170 corpus
files parse as a whole, 19 elaborate and lower (`Parser/Cover/Census.lean`, `instrumente/parser-deckung.py`); 429 of 429
function bodies and 1287 of 1287 leaf items print and read back as the same tree (`Print/Stmt`, `Print/Item`,
`Print/Proben`). Proved: the expression round trip on the `gut` shapes and, new, the statement round trip of the
straight-line core: `parseStmt_einfach`, `parseStmts_einfach`, `rundlauf_block_einfach` (a block of `return`, `leave`,
`next` and number `let` over `gutPrim` expressions, hypothesis `EndeGut`; witness `rundlauf_block_einfach_zeuge`, planted
defect `schliesse_ende_noetig`; `Round/RundlaufAnw`..`3`). NOT proved: a round-trip theorem for the other statements
(assignments, calls, `if`, nested blocks) or for items; elaboration beyond tables, locks, statics and `impl fn` over integers with
`let`/`if`/`traverse`/`return`. `Zielsatz/Kern/Spec.lean` unchanged; `gabbro_ziel` untouched.

## 78. `Code`: the target-independent low-level language and the lowering refinement (Track L, 2026-10-18, `PLAN-TRANSLATION-VALIDATION.md` 9a)

`grammatik/Grammatik/Code/` (Model, Lower, Refine, Conc). `Code` is a language of our own, **not LLVM** and
ISA-neutral by construction: unbounded locals, no flags, a branch tests a word, explicit-width
wraparound arithmetic, preconditions (stuck steps) wherever x86, AArch64 and RISC-V differ (division by
zero, `INT_MIN / -1`, shifts by the width, unaligned access), five atomic orderings on word-sized cells
with abstract read-modify-write, abstract call frames, and the word width and byte order as the
PARAMETER `Conf` (run at 64 bit little endian and 32 bit big endian in the witness).

| Statement | File | Hypotheses |
|---|---|---|
| block memory, aligned byte access, round trips (`load_store_int/ptr/flt/dbl`), frame lemma `load_store_other`, `alloc` fresh | `Model/Cells`, `Model/Memory` | `[Conf]` |
| small-step semantics `step`, oracle only at the atomic load (`step_indep`), SC determinism `step_sc_det`, `exec_reach` | `Model/Semantics`, `Step`, `Facts` | `[Conf]` |
| the link to the weak memory: `Order.toOrdnung`, `Sees.weak`, `sees_sc_weak`, `step_mono` | `Model/Weak` | `[Conf]` |
| witness: loop, call, `gep`, atomic `armw`, computed by the kernel at both configurations, and `weak_two_successors` | `Model/Witness` | none |
| what `Code` guarantees (`code_pre_div`, `_sdiv`, `_shift`, `_align_*`) and `Need`, the list of obligations a CPU model must provide | `Model/Need` | `Need` is a statement, not an instance |
| widths: `Fits`, `wid`, exact modular arithmetic, width changes, comparisons | `Lower/Arith` | |
| representation relation `Rep`, `EnvRep`, store lemmas; layout assumptions `LayoutOk` | `Lower/Rep`, `Refine/Env` | `LayoutOk` (hypothesis, not axiom) |
| `lowerE` and `lowerE_ok`: a lowered expression computes what `eval` computes (constants, variables, globals, slots, widening, `+ - *`, negation, `/` and `%` on non-negative numerators and denominators `>= 1` with an unsigned instruction whose precondition is a fact of the ranges, comparisons, `&& || !`) | `Lower/Expr`, `Refine/Frag`, `Refine/Expr` | `LayoutOk`, success of the lowering |
| `lowerS`/`lowerB`/`lowerEnd` and `lowerS_ok`/`lowerB_ok`/`lowerEnd_ok`: assignments, `if`, `let`, `check`, `narrow`, `return`, `leave`/`next`, the loops `forever`, `traverse`, `retry`, the calls `call` and `let x = f(..)`. One clause per SOURCE outcome (`OutOk`/`EndOk`: ok, return, leave, next), each with the FRAME of the run (`Fr`) | `Lower/Stmt`, `Refine/Stmt`, `Refine/StmtOk` | `LayoutOk`, `InM`, `KOk`, `LvOk`, `FnOk`, `CallRef` |
| the frame `Fr` (registers below the entry bound untouched, memory only grows, existing non-table non-global non-local blocks keep their contents), its composition, `Keep` | `Refine/Frame`, `Refine/Stmt` | |
| the labels of a lowering are distinct and in the counter's range (`LblWf`, `lowerS/B/End_lbl`) | `Refine/Struct/Labels` | `lb < st.l` |
| the loops: `forever_ok` (induction on the fuel), `traverse_loop` (induction on the index list, counter in a register), `retry_loop` (induction on the passes left, bounded counter) | `Refine/Loops/Loop`, `Refine/Loops/Traverse`, `Refine/Loops/Retry` | the refinement of the body (`IHb`), of the overflow block |
| calls: `FnOk`, `CallRef` (the callees refine the source meaning `R` of a call: result image, returned world, `Keep` of the caller's memory), the callee frame (`callee_frame`), `call_core`/`call_run_none`/`call_run_some` | `Refine/Calls/CallDef`, `Refine/Calls/CallRun` | `FnOk`, `CallRef` |
| `prologue_ok`; `lowerFn`; `lowerFn_nodup` (label uniqueness is PROVED, no hypothesis); **the closing function theorem `lowerFn_run`/`lowerFn_runs`**: a body that returns `v` in machine G makes the IR function return the image of `v` and leave a memory that represents the returned world and keeps the caller's | `Refine/Calls/Func`, `Lower/Func` | `LayoutOk`, the module holds the lowering, `FnOk`, `CallRef` |
| **the recursion is closed**: `fnOk_of_lowerFn`, `rufAt_ok_inv`, `lowerFn_callref`: for EVERY recursion depth `n` the lowered functions refine the source meaning of a call `rufAt n`, by induction on `n` with `lowerFn_run` as the step | `Refine/Calls/Closure` | the module holds the lowering of every function |
| the witness: a hand-built program (table, `get`, `put`, `wipe` with `traverse`, `main` with `let`-call, `narrow`, `retry`, calls) at 64-bit little endian and 32-bit big endian: `LayoutOk`, the lowering covers it (block counts 8 and 17), `lowerFn_callref` INSTANTIATED, the source meaning of `get` and `main` is an `ok` (the premise of `CallRef` is inhabited) | `Refine/Witness` | none |
| **`match`** (2026-10-18): `opt n` is the word `-1` (absent) or the index (signed width), `why n` the reason number, `sum cs` ONE word `i + L * (n - lo)` (`L` the number of cases, carried at `Ar.wid 0 (L * S)` bits). The expressions `none`, `some`, `istSome`, `why`, `case` (`lowerE_ok` cases; `numCode_frag`), the statements `onOption` (a signed compare with zero, the index a new local), `onWhy` (a `switch` on the reason, `lowerGA`) and `onTag` (`urem` for the case number, a `switch`, `payCode` takes the payload apart with one `udiv` and one wrapping add: `payCode_frag`): `onOption_ok`, `onWhy_ok`, `onTag_ok`, with `arm_ok`, `lowerGA_get`, `lowerAr_get`, `scope_ok` and the structural companions `lowerGA_ok`/`lowerAr_ok` inside the mutual theorem | `Lower/Sum`, `Lower/Stmt`, `Refine/Match/{Opt,Case,Scope,OnOption,Why,PayCode,Arms,Tag}`, `Refine/Struct/{Shape,Labels}` | `LayoutOk`, success of the lowering, `BOk` of the arms |
| **sdiv, srem, `&`, `\|`, `^`, `<<`, `>>`** (2026-10-18): each is carried out at the width of a range chosen so that the instruction's PRECONDITION is a fact of G's ranges (`opRest`, `jsdiv`, `jsrem`, `jbit`, `jshl`, `jshr`): the signed range reaches one below the least number of every operand and of the result (the dividend is never `INT_MIN`, the divisor is nonzero by the form's premise), shifts include `2 ^ h2` (the width exceeds the largest shift amount), bit operations hold both operands and the result. `sdiv_hop`, `srem_hop`, `band_hop`, `bor_hop`, `bxor_hop`, `shl_hop`, `shr_hop`; `opRest_frag`; `lowerE_ok` cases. The ones that do not fit 128 bits are refused | `Lower/Expr`, `Refine/Bits/{Ops,OpRest,Forms}`, `Refine/Expr` | success of the lowering |
| **the failure channel** (2026-10-18): a function with `n > 0` reasons answers ONE word (`Lower/Fail`: a value `(n+1)*(v-lo)`, the reason `r` is `r+1`); `return`/`return why` lower (`lowerRet`, `lowerWhy`), the why outcome is a real clause of `OutOk`/`EndOk` (`RunRet` carries the answer image), `CallRef` has a `why` clause, `lowerFn_run_why`, `rufAt_why_inv`, `lowerFn_callref` proves both clauses for every depth. The caller `let x = f(..) else (r) { .. }` (`bindCallElse`): `lowerElse` takes the case number apart (`else_after_call`), the value arm (`payCode`) and the reason arm (the case number minus one) bind a new local; `bindCallElse_ok` uses `CallRef.ok` and `CallRef.why` (`scope_ok`, `scope_end_ok`) | `Lower/Fail`, `Lower/Stmt`, `Refine/Post`, `Refine/Calls/*`, `Refine/Match/Else` | `failOk` (answer void or a non-empty integer range) |
| **L3 start** (2026-10-18, `Code/Conc/`, NOT in `lowerS`): `publish` is a RELEASE store into the cell of the atomic global, `await` an ACQUIRE load (`lowerPublish`, `lowerAwait`; the cell must be word-sized, `atomicG`). `publish_ok` for EVERY interface `S` (a store does not consult it); `await_ok`: if `S` allows the image of the world's value at the cell, the lowered code refines G's `await` on that world (the continuation's refinement is `lowerB_ok`: no premise about it; a continuation `lowerB` refuses, e.g. one that itself awaits, has no lowering); `await_ok_sc` the exact SC refinement for an unshared global; `await_ok_gx` reads it on a PRESENTED world of machine GX (`PresentedAt`) | `Conc/{Lower,Publish,Await}` | `atomicG`, `Rep` of the presented world |
| **L3 (1), the shared atomics** (2026-10-18): `Layout.shared` (machine GX's `Tg`, `LayoutOk.shAtomic`: shared implies atomic); **`Rep` keeps only the EXISTENCE of a shared cell** (a word of the right type), the strong equation for every other cell, and every refinement proof of `Refine/` carries this one relation (no second `RepX`, no copy of the strong form). `lowerE` refuses a plain read of a shared global (only `await` reads it). `rep_agree` (worlds that agree outside the shared atomics are represented alike), `rep_presented`, `rep_successor`, **`rep_gx`**: the memory half of the GX simulation (the IR memory represents the machine's memory, hence every presented one; if it represents the memory of G's step on the presented memory it represents the memory the GX step leaves), `Sees.shared` (the GX interface: any value of the type at a shared cell, the memory's elsewhere), **`await_ok_shared`**: for a shared global the lowered `await` refines G's `await` on `σ[g := xg]` for EVERY `xg`, the memory representing the actual world | `Lower/Rep`, `Conc/{Present,Shared}` | `TgShared lay Tg`, `LayoutOk`, `FnOk`, `CallRef` against `Sees.shared lay` |
| **L3 (2), the thread machine** (2026-10-18): `Th`, `TM` (one shared memory, a thread table), `TStep`, `TReach` (an interleaving step of `Step` of one thread); `treach_solo` (a run of one thread is a machine run in which only it moves, `upd_other`); **`stmt_gx`**: a GX step of a statement that ends normally (`blatt`/`dannBlatt` of G, any statement the lowering covers) is matched by thread-machine steps: the thread reaches the continuation label, the shared memory represents the successor memory, the locals are `ρ'`, every other thread is as it was, with the frame `Fr`; `envRep_other` (another thread's locals survive a run) | `Conc/{Thread,GXStep}` | `lowerS_ok`'s hypotheses, `TgShared`, the presented memory agrees with the machine's outside `Tg` |
| **L3 (3), the ticket lock** (2026-10-18): `Layout.lblk`/`lsrv` (the two word cells of each lock, `LayoutOk.lkT/lkG/lkX/lkN/lkS`; `Fresh` and `WfL` exclude them). `lockTake` (`armw add` on the next cell, acquire), `lockSpin` (`aload` the serving cell, `brc eq`), `lockRel` (`astor` serving `rt + 1`, release); the thread runs `take_run`, `spin_enter`, `spin_wait`, `rel_run`. The invariant over all threads `LockRel` (ghost `Tkt`: tickets served and handed out, the owner of each ticket, `inside`; the cells hold them modulo `2^wbits`; G's held locks, counted in `offen`, are exactly the holder). The steps: `take_step`, `spin_wait_step` (G silent), **`spin_enter_step`** (G's `dannLocks`: `RufFreiG` is DERIVED, the relation holds after the `nimmt`), **`release_step`** (`freiGib`), `lockRel_exclusive` (two holders are one), `lock_store_post` (a lock cell is no table, no global, no local: `Rep`, `WfL`, every thread's `EnvRep` survive) | `Conc/{Lock,LockRel}` | the named assumption: fewer than `2^wbits` tickets outstanding on a lock at once (premise of `take_step`); thread-local premises (the ticket register, the thread is not queued) |
| the L3 witnesses (2026-10-18): `SharedWitness` (`LayoutOk` with a shared global, a `Rep` that disagrees at the shared cell and its failure without sharing, the refused plain read, **`await_shared_zeuge`**: the GX `await` instantiated on a module, cell `0`, world `5`, read `7`), `GXWitness` (**`stmt_gx_zeuge`**: two threads, the shared atomic presented as 9 and left as 3, cell 0), `LockWitness` (**`lock_witness`**: two threads contend on one lock; take, take, enter, wait, release, enter; `LockRel` after every step, `RufFreiG` twice, G holds the lock in thread 1 only at the end, cells `next = 2`, `serving = 1`) | `Conc/{SharedWitness,GXWitness,LockWitness}` | none |
| the witnesses (2026-10-18): `Refine/Witness` has four more functions (`mt`: the three matches; `bits`: the seven arithmetic forms; `fail`/`callf`: a failure channel taken at both arms), all lowering at both targets, their source meaning an `ok` (kernel); `Conc/Witness` lowers `publish` and `await` at both targets | `Refine/Witness`, `Conc/Witness` | none |

NOT proved: the memory forms sampling and the page return; indirect calls; `bindCallInd`, `bindAxiom(Else)`, `regRead`, `float*` and `getBytes`/`putBytes`/`shift`; a failure-channel function that answers `bool`, a pointer, an option, a reason or a tagged value (refused by name, `failOk`); a `match` or an expression whose type is `ptr` in a failing function's answer; **concurrency beyond the steps above**: the STRUCTURAL half of the GX simulation (the steps that unfold a compound or call, `ite`, `match`, loops, `locks`, call/return, move the G residue and no memory; their correspondence with an IR position, the label the lowering of the continuation starts at, is open), the converse direction (every IR interleaving is covered by a GX run: a reduction argument), the lowering of `publish`/`await`/`locks` INSIDE `lowerS`/`lowerB` (the integrated theorem needs a hypothesis on the interface, `S` answers what `Rep` says at an atomic cell, threaded through every refinement theorem), the structured `locks L { .. }` statement with its five outcome clauses (release on `leave`/`next`/`return`), the reader/writer lock (the model has none: `Lock` carries only `rang` and `maskiert`), masked acquisition (`masks irqs` needs an interrupt-mask instruction, a hardware form with a named assumption, L4); views, `child` and `join` are not needed (G's threads are all declared starts and GX presents an arbitrary memory at the shared atomics); `Code -> bytes`. Arenas, `free`, the free list and `grow` need no lowering of their own: `ArenaZucker`/`ArenaDyn`/`ArenaFrei` define them as SUGAR over the existing assignments (no new `Stmt` constructor), so they lower, with the proved refinement, as soon as the elaboration expands them (Track P). The refinement is stated for the fragment the lowering covers; every other form lowers to `none` (refused by name). The witnesses exercise the layout, the lowering and the instantiated closing theorem; they do not run a concrete memory through `lowerFn_runs` (a concrete `Rep` of a byte memory is not built); the L3 theorems are instantiated on kernel-built witnesses (`await_shared_zeuge`, `stmt_gx_zeuge`, `lock_witness`), the ticket lock's thread-local premises (ticket register, not queued) are supplied by the future `locks` statement theorem.
`Zielsatz/Kern/Spec.lean` unchanged; `gabbro_ziel` untouched.

## 79. Invariants over live slots: `ListOk`, `BaumOk` and the allocator (Phase A step 2, 2026-10-18, `PLAN-DYNAMIC.md` 8a.1)

`grammatik/Grammatik/Bausteine/Arena/Struktur/` (ArenaKette, ArenaBaum, ArenaLebt, ArenaFremd, ArenaListe, ArenaBaumWelt, ArenaDynZeuge; second pass below: ArenaAuf, `Formen/` ArenaAllocForm, ArenaLinkForm, ArenaBaumForm, ArenaWachs, ArenaFormZeuge, `Erkenner/` ArenaErkenner, ArenaErkennerLemmas, ArenaErkennerBeweis, ArenaErkennerZeuge, ArenaSibling, ArenaHash; third pass below: ArenaRahmen, ArenaBaumWurzel, ArenaBaumUnter, `Formen/` ArenaBaumFormG, ArenaBaumFormZug, ArenaSibForm, ArenaSibZug, ArenaHashForm, ArenaHashZug, ArenaHashZeuge, `Erkenner/` ArenaDekl, ArenaErkFallAlloc, ArenaErkFallListe, ArenaErkFallBaum, ArenaErkFallSchleife, ArenaErkEnde, ArenaErkZeugeBaum, ArenaErkZeugeKombi, ArenaErkZeugeSchleife, ArenaErkZeugeSib, ArenaErkZeugeEnde; step 3 below: `Sperre/` ArenaSperreTraeger, ArenaSperreOhne, ArenaSperreAbschnitt, ArenaSperreRuf, ArenaSperreMaschine, ArenaSperreInv, ArenaSperreWelt, ArenaSperreZeuge, ArenaSperreWachs, ArenaSperreWachsZeuge, ArenaSperreBruecke, ArenaSperreAbdeckung, ArenaSperreMaschZeuge).
Links are indices into one arena table, `count` is the nil marker. A slot is LIVE when it is below the used counter and
not on the free list (`Lebt`). `ListOk`/`BaumOk` say: the chain/tree from the head/root exists (finite, links in range),
its slots are pairwise distinct (acyclic list, tree shape) and every one is live.

| Statement | File | Hypotheses |
|---|---|---|
| `push_ok`, `pop_ok`, `unlink_ok`, `push_doppelt_bricht` | `ArenaKette` | live and unlinked slot; head below `count`; predecessor on the chain |
| `einfuegen_ok`, `blatt_aus_ok`, mirrors `*_rechts_ok`, `einfuegen_doppelt_bricht`, `InBaum.links` | `ArenaBaum` | empty child place; leaf with no children |
| `lebt_bump`, `lebt_abheb`, `lebt_frei` | `ArenaLebt` | facts the executed free-list blocks give (`FreiOk` before) |
| `freiRumpf_fremd`, `freiNimm_fremd`, `frischRumpf_fremd`; `frisch_lebt`, `nimm_lebt`, `frei_lebt` | `ArenaFremd` | `k.n = stand` for the counter branch; `kopf < count` for the list branch; slot live for `free` |
| `liste_frisch`, `liste_nimm`, `liste_frei`, `liste_push/pop/unlink`, `liste_pop_frei` | `ArenaListe` | `ListOk`, `FreiOk` before; link-store facts as hypotheses |
| `baum_frisch`, `baum_nimm`, `baum_frei`, `baum_einfuegen_*`, `baum_blatt_aus_*`, `baum_frei_nach_blatt` | `ArenaBaumWelt` | likewise |
| witnesses `pop_zeuge`, `einfuegen_zeuge`, `nimm_zeuge` (executed), `listOk_w0`, `baumOk_w0`, `freiOk_w0`; defect `liste_defekt_bricht` | `ArenaDynZeuge` | none (a concrete full arena, slot 1 on the free list) |

Second pass (2026-10-18, `PLAN-DYNAMIC.md` 8a.1):

| Statement | File | Hypotheses |
|---|---|---|
| executed link forms `Block.linkPush/linkPop/linkUnlink/linkKopfBind/linkNachBind`; `linkPush/Pop/Unlink_ausfuehren` (the store facts, for ANY continuation); `liste_push_zug`, `liste_pop_zug`, `liste_unlink_zug` (the list invariant ON THE EXECUTED BLOCK, plus the new head/link and which slots are members); guard failure `linkPop_voll`, `linkUnlink_voll`, `linkKopfBind_voll`, `linkNachBind_voll` | `ArenaLinkForm` | live unlinked slot / non-empty list / member `p` (each a fact of the abstract state in the recognizer) |
| executed tree forms `Block.blattEin/blattAus` (left, right); `blattEin_ausfuehren`, `blattAus_ausfuehren`; `baum_einfuegen_links/rechts_zug`, `baum_blatt_aus_links/rechts_zug` | `ArenaBaumForm` | member `p`, empty child place, live slot not in the tree, leaf (hypotheses on the world BEFORE the move); the two child fields are two fields |
| `LinkKopf.h3`, `Fremd` names `komm`; `nachGrow_gleich`; `grow_liste`, `grow_baum` (the executed `grow` keeps `FreiOk`, every liveness, `ListOk`/`BaumOk`); `dynGrow_voll` | `ArenaWachs`, `ArenaListe`, `ArenaFremd` | committed word + `n` within the ceiling (what `narrow` decides) |
| `Block.freiVar` (`free` of any bound index), `freiVar_ausfuehren`, `freiVar_lebt`; `arenaRumpf_ausfuehren`, `frischAlloc_ausfuehren`, `frischAlloc_voll`, `nimmAlloc_fakten`, `nimmAlloc_ausfuehren`, `nimmAlloc_voll` | `ArenaAllocForm` | `FreiOk`; the slot live; `stand < count` / `kopf < count` |
| `auf_push_vor/nach/kopf`, `auf_pop_vor`, `auf_unlink_vor`: who is on the chain after a move | `ArenaAuf` | the hypotheses of `push_ok`/`pop_ok`/`unlink_ok` |
| the LIST recognizer of the second pass (`Erk FA LL LG`, `StrukturOk`, `StrukturPasst`, `StrukturPost`, `erk_erhaelt`, `erk_koerper`) -- REPLACED in the third pass by the combined recognizer below (the list-only case is `baum := none`); its witnesses `nimmPush_konkret`, `kopfUnlinkFrei_konkret`, `nimmPushPush_abgelehnt`, `nimmFreiFrei_abgelehnt`, `nimmFreiPush_abgelehnt`, `pushFremd_abgelehnt` live on, restated over `KL` | `ArenaErkennerZeuge` | see below |
| witnesses: `nimmPush_konkret`, `kopfUnlinkFrei_konkret` (accepted bodies RUN on the real arena), the forms RUN (`push_zeuge`, `pop_zeuge'`, `unlink_zeuge`, `blattEin_zeuge`, `blattAus_zeuge`, `grow_zeuge`); planted defects with NO derivation: `nimmPushPush_abgelehnt`, `nimmFreiFrei_abgelehnt`, `nimmFreiPush_abgelehnt`, `pushFremd_abgelehnt` (through `erk_koerper` and a real run that breaks the invariant: `liste_schleife_bricht`, `FreiForm.schleife_bricht`, `liste_freigegeben_bricht`) | `ArenaErkennerZeuge`, `ArenaFormZeuge` | none |
| sibling consistency `SibF`; `einfuegen_mitglieder`, `einfuegen_rechts_mitglieder`, `blatt_aus_mitglieder`; `sib_einfuegen_links/rechts`, `sib_blatt_aus_links/rechts`; `sib_ohne_vater_bricht`; witness `sib_einfuegen_zeuge`, defect `sib_defekt_bricht` | `ArenaSibling` | the parent store of the move; abstract link functions |
| hash chains `HashOkF`; `hash_push` (slot on no bucket), `hash_pop`, `hash_unlink`; witness `hash_push_zeuge`, defect `hash_defekt_bricht` | `ArenaHash` | abstract link function, bucket heads as a function |

NOT proved in the second pass (the third pass below closes most of it): the recognizer for TREE bodies and for bodies with loops, executed forms for the parent store, `revoke` and a bucket head in a table field; the open list now stands at the end of this section.

Third pass (2026-10-18, `PLAN-DYNAMIC.md` 8a.1; sub-folders `Formen/` and `Erkenner/`):

| Statement | File | Hypotheses |
|---|---|---|
| `LinkRahmen A fs gs σ σ'` (every link field outside `fs` and head outside `gs` reads as before) with `refl/lese/schreibSlot/schreibGlob/trans/mono`; carried as a conjunct by every executed form | `ArenaRahmen` | none |
| `InBaum.wurzel`, `wurzel_ein_ok` (the first node), `wurzel_aus_ok` (the tree becomes empty) | `ArenaBaumWurzel` | tree empty / root a fresh leaf |
| guarded tree forms `Block.haengen`, `abschneiden`, `wurzelSetze`, `wurzelEin`, `wurzelAus`; `execBlock_check_wahr/falsch`; `leerTest_wahr`, `blattTest_wahr`, `wurzelLeer_wahr` | `ArenaBaumFormG` | none |
| `abschneiden_ausfuehren`, `wurzelSetze_ausfuehren`, `wurzelAus_ausfuehren`, the failing guards `abschneiden_voll/nichtblatt`, `wurzelAus_voll/nichtblatt`; `baum_abschneiden_links/rechts_zug`, `baum_wurzel_ein_zug`, `baum_wurzel_aus_zug`; `baum_einfuegen_*_zug`/`baum_blatt_aus_*_zug` now also give the frame and the member facts | `ArenaBaumFormZug`, `ArenaBaumForm` | member `p`, guard facts, live slot not in the tree |
| **the arena declaration and its invariant:** `ListDekl`, `BaumDekl`, `Dekl` (`getrennt`), `Dekl.InL/InB/LOk/BOk/Ok` (free list, list, tree and their DISJOINTNESS), the frames `GlL`, `GlB`, `Ok.gleich` | `ArenaDekl` | none |
| **the combined recognizer** `Erk K a b a'` (statuses `frei`/`liste`/`baum`/`offen`; list moves `push/pop/unlink/kopf/nach`, allocator moves `frisch/nimm/frei/wachs`, guards `pruefe`, payload store `nutzlast`, branches `ite`, tree moves `wurzelEin/wurzelKopf/kind/haengen/abschneiden/wurzelAus`, loops `forever/traverse/retry`); `Rein` (only `return`/`return why`); `StrukturPasst`, `StrukturPost`, `Folgt`; cases `fall_*`; **`erk_erhaelt`**, **`erk_koerper`**, `erk_koerper_lauf`: every accepted body keeps `K.Ok` at EVERY exit, meets its abstract state when it falls off, never ends in `leave`/`next` | `ArenaErkenner`, `ArenaErkennerLemmas`, `ArenaErkFall{Alloc,Liste,Baum,Schleife}`, `ArenaErkennerBeweis` | `K.Ok` and `StrukturPasst K a` at entry (`StrukturPasst K Abs.leer` is trivial for a function) |
| `ErkE K a e` on END blocks (function bodies); **`erkE_erhaelt`**, **`erkE_koerper`** | `ArenaErkEnde` | likewise |
| `unterbaum_aus_ok`, `unterbaum_aus_rechts_ok`, `sib_unterbaum_aus_links/rechts` (cut a whole subtree: the remaining tree is well formed and sibling-consistent; the subtree's slots are no members) | `ArenaBaumUnter` | member `p` with child `i`; parent field untouched |
| `SibOk`; `Block.blattEinErst`, `blattEinBruder`; `parStore_ausfuehren`, `blattEin{Erst,Bruder}_ausfuehren`; `sib_haengenErst_zug`, `sib_haengenBruder_zug`, `sib_abschneiden_links/rechts_zug`, `baum_unterbaum_aus_links/rechts_zug` (`revoke`: the cut subtree's slots are live orphans) | `ArenaSibForm`, `ArenaSibZug` | as the tree moves; parent field distinct from the child fields |
| `BucketKopf`, `HashOk`; `Block.hashPush/hashPop/hashKopf`; `hashPush/hashPop/hashUnlink_ausfuehren`, `hashPop_voll`, `hashKopf_ausfuehren`; `hash_push_zug`, `hash_pop_zug`, `hash_unlink_zug` | `ArenaHashForm`, `ArenaHashZug` | slot live and on NO bucket (push); non-empty bucket (pop); member of bucket `b0` (unlink) |
| witnesses (RUN on real worlds, soundness theorem applied) and planted defects: `baumHang_zeuge`, `baumSchnitt_zeuge`, `doppelHang_abgelehnt`, `fremdHang_abgelehnt`, `frischFrei_abgelehnt`; `kombiHang_zeuge`, `kombiVersetzen_zeuge`, `doppelGlied_abgelehnt` (a slot in both structures), `kombiEnde_zeuge`; `drain_zeuge`, `drainForever_zeuge`, `fuell_zeuge`, `schiebeSchleife_abgelehnt`; `erst_zeuge`, `bruder_zeuge`, `revoke_zeuge`, `bruderOhneVater_defekt`, `freiOhneSchnitt_defekt`; `push_zeuge`, `pop_zeuge`, `push_defekt` | `ArenaErkZeuge{Baum,Kombi,Schleife,Sib,Ende}`, `ArenaHashZeuge` | none |

NOT proved: the recognizer is not a component of `Akzeptiert` and no generic statement says every accepted unit's structure writers are
`ErkE`-derivable (8a.3 is a proposal, revised: an arena as an invariant name, the derivation a certificate in the unit); no `Block` the Rust
checker accepts is translated to a derivation (no exporter for these forms); a recognized body calls no function; a walk that releases EVERY
slot of a revoked subtree (only the cut and the release of one orphan are proved); recognizers for hash chains and for the sibling demand
(`SibOk`/`HashOk` have executed forms and witnesses only: the recognizer's `haengen` does not track the parent store); `leave`/`next` in loop
bodies; a copy of an owned index (alias) and any other store into a link field have no derivation; concurrency (design note 8a.2). These
modules are not imported by `Zielsatz/`; `Spec.lean` unchanged; `gabbro_ziel` untouched.

## 80. Message passing with a plain payload: happens-before over a payload, the counter-models and the litmus tests (Phase B item 1, 2026-10-18, `PLAN-DYNAMIC.md` §11)

*Files: `grammatik/Grammatik/Speichermodell/Payload/{PayloadHb,PayloadLitmus,PayloadLB}.lean`. Model only: `Spec.lean`, the Rust checker and the exporter are unchanged, `gabbro_ziel` is untouched (nothing imports these modules; `Grammatik.lean` does). Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` (the litmus file needs only `propext`, `Quot.sound`).*

| Statement | File | Hypotheses |
|---|---|---|
| `HbSeen W u c m` (the write `m` of `c` is in the history and `m.ts ≤ W.sicht u c`), `HbRace` (its complement), `hbSeen_not_race`, `hbSeen_or_race`, `hbSeen_laufW` (monotone along W runs), `hbSeen_lesen` (a read of a seen write returns a message at or above it) | `PayloadHb` | none |
| `payload_schreib`: the writer sees its own write; the message is at the head of the history, carries the memory after the step, lies above every message the writer had seen | `PayloadHb` | a W step that writes `c` |
| `MpAblauf` (the run of the pattern), `MpAblauf.lauf`; **`payload_mp`**: the payload write happens before the reader after the await and on every later state; `payload_mp_lesen` (a read after the await is at or above the write); `payload_kein_rennen` (no `HbRace` after the await) | `PayloadHb` | the run `MpAblauf`; flag of order `freigabe`; built on `hb_uebergabe` |
| **`payload_mp_wert`**: the reader's presented memory at the payload is the memory the writer wrote; `hist_gleich_lauf`; `gesehen_einzelschreiber` (only `t` writes `c` implies `t` has seen every message of `c`), `still_of_kein_schreiben` (no later write step implies no later message) | `PayloadHb` | single writer, nothing writes `c` after the write |
| **`erwartet_bestaetigt`**: a reader that branched on a value no earlier flag message carries read the message the publish added (LANGUAGE 11.5 rule 2, "visibility is a branch fact") | `PayloadHb` | confirming predicate on the flag; flag untouched between publish and await |
| run checker `lauf`, `gehe_schritt` (a checked step is an `LSchritt`), `erlaubt_of` (a computed outcome is reachable) | `PayloadLitmus` | none |
| witness `mp_zeuge` (flag and payload seen), `mp_alt_abgelehnt` (the stale payload read is refused there) | `PayloadLitmus` | none |
| COUNTER-MODELS (kernel-checked reachable outcomes where the conclusion fails): `mp_vor_erwartung_erlaubt` (payload read before the await), `mp_flagge_lesen_entspannt_erlaubt`, `mp_flagge_schreiben_entspannt_erlaubt` (relaxed flag read / written; both relaxed is `mp_rlx_erlaubt`, `Sicht`), `mp_umgeschrieben_erlaubt` (payload rewritten after the publish: reader sees the newer value) | `PayloadLitmus` | none |
| `iriw_erlaubt` (IRIW release/acquire: allowed; also for `seq`, the model has no `seq_cst` order); `lb_verboten` (LB: both reads 1 is unreachable, invariant `LBInv`) | `PayloadLitmus`, `PayloadLB` | none |

Existing litmus facts used as the yardstick (`Speichermodell/Maschine/Sicht.lean`): `mp_ra_verboten`, `mp_rlx_erlaubt`, `sb_erlaubt`, `sb_sc_verboten`, `corr_verboten`.

NOT proved: a concrete two-thread run of machine W/GX over a program with a plain payload and a payload flag (no such `Programm D` exists in the fixtures; the generic theorems apply to any W run with the pattern, and `mp_zeuge` is the witness on the view machine whose primitives W shares); the `Spec.lean` legs (`pubSicht`, the premise on `ord`, the rely over payload carriers, the component `pub`) and everything the proposal D1-D6 in `PLAN-DYNAMIC.md` §11.3 lists as obligations (the frame invariant `Merkmal.erwartet`, the `SichtInvA` extension, the replay instantiation); the static dominance and single-epoch rules in Lean (`PubRegel`) and in the checker (§11.4); re-publication of the payload cell (item 5); a flag written more than once; table cells as payload (`D.nutzlast` names globals only); `seq_cst` total order.

**§79 continued (placed after §80 by the merge).** Step 3 (2026-10-18, `PLAN-DYNAMIC.md` 8a.2; sub-folder `Sperre/`, 13 modules; they import `Spec.lean`, nothing in `Zielsatz/` imports them): a SHARED arena is a lock invariant.

| Statement | File | Hypotheses |
|---|---|---|
| `Dekl.orte`, `lesGlobs`; **`ok_gleich_wort`** (`Dekl.Ok` reads only table + `lesGlobs`: premise `dekl_ok_traeger`), `ok_spur`; the lock family `Dekl.sperr K L0` (`inv L0 = Dekl.Ok`), `sperr_inv_iff'`, `sperr_lokal` (= `SperrInvLokal`), `sperr_ok` (= `SperrInvOk`) | `ArenaSperreTraeger` | `Bewacht c L0` for every arena carrier (the checker's `sperrOrte`) |
| `Rein.ohneLocks`, `erk_ohneLocks`, `erkE_ohneLocks`, `erkE_execEndH`, `erk_execBlockH`, `erk_erhaeltH`, **`erkE_koerperH`** (the soundness theorems over `execBlockH`/`execEndH`) | `ArenaSperreOhne` | `K.Ok` at entry |
| `freiH_post`; **`abschnitt_erk`** (inline section), `abschnitt_start`; `Rufe`, `RErhaelt`, `rufe_post`, **`abschnitt_rufe`** (call section) | `ArenaSperreAbschnitt` | `HavocOk (K.sperr L) U`; the body is `Erk K Abs.leer` / a run of recognized calls |
| **`rufAt_erk`** | `ArenaSperreRuf` | the callee's body is `ErkE K Abs.leer`; the world at the call meets `K.Ok` |
| `arena_ruhe`, `arena_wechsel`, `arena_sicht`, `komm_nur_halter`, `arena_ziel` (the legs `sperrInv`/`sperrWechsel`/`sperrSicht` of `Ziel` for `S := K.sperr L`) | `ArenaSperreMaschine` | the legs |
| `lesGlobs_ne_komm`, **`grow_ok_iff`, `grow_atomar`**, `komm_wachstum`, **`grow_gesperrt`** | `ArenaSperreWachs` | the commit fits (`narrow`'s guard); `0 ≤ n` for monotonicity |
| `InvHaeltD2`, `InvAmRueckD2`, `InvGutSM`, `invGutS_iff_M`, **`invGutSD2_arena`**, `invGutSD2_ohne` | `ArenaSperreInv` | owed arena invariants have `ErkE`; the arena is whole at entry (`hein`); the user's obligation for the others |
| **`erkE_maschine`** | `ArenaSperreBruecke` | `EndR A (Tief P A n) b` (coverage) and `ErkE K Abs.leer b` (certificate); the thread's world meets `K.Ok` at entry; the machine premises of `rufG_adaequat_ruf` |
| `Block/Stmt/Endblock.schleifenfrei`, `schleife_nicht_frei`; **`erk_blockR`, `erkE_endR`** (a loop-free derivation IS machine-covered); **`erkE_maschine_erk`** (the bridge with ONE certificate) | `ArenaSperreAbdeckung` | `l = false`, `schleifenfrei`; the machine premises |
| witnesses: `FDL`/`KLL`/`w0L`/`ok_w0L`/`sperr_ok_zeuge`; `havoc_U0`, `abschnitt_zeuge`, `erk_nimmPushL`; `grow_zeuge_L`, `grow_ueber_decke`; `erkE_maschine_zeuge`, `rErhaelt_PL`, `abschnitt_rufe_zeuge`, `abschnitt_rufe_lauf`; planted defects: `stray_bricht`, `abschnitt_defekt_schleife` (the release check fires), `stray_abgelehnt` (no derivation), `stray_kein_havoc`; planted gap `wachs_negativ_schrumpft` | `ArenaSperreWelt`, `ArenaSperreZeuge`, `ArenaSperreWachsZeuge`, `ArenaSperreMaschZeuge` | none |

NOT proved in step 3 (named in `PLAN-DYNAMIC.md` 8a.2/8a.3): the ABA ownership predicate; the commit bound `stand <= komSt` in the lock invariant (the recognized alloc is guarded by `hi` not `komSt`, the forms' frames do not name `zaehl`/`komm`; `Erk.wachs` now demands `0 ≤ n`); the footprint of a pure `pop`/`wurzelAus` (`schuldet` counts tables only); the arena at ENTRY of a writer (premise `hein`); the machine correspondence of writers with loops;
the migration D1 (analysed, not built); the exporter; `Spec.lean` unchanged, the diff D1-D5 stays a proposal.

## 81. The per-core interrupt-mask state of machine G, `KernHaltE` derived, and the mask as `Code` (O19 rest, 2026-10-18, `PLAN-DYNAMIC.md` 8a.4)

*Files: `grammatik/Grammatik/Zielsatz/Eigenschaften/{KernMaske,KernMaskeGleich,KernMaskeZeuge}.lean`, `grammatik/Grammatik/Code/Conc/{Mask,MaskNeed,MaskRel,MaskWitness}.lean`, `Code/Model/{Syntax,Semantics}.lean` (one instruction). Model only: `Spec.lean`, the Rust checker, the exporter and the LLVM backend are unchanged, `gabbro_ziel` is untouched (nothing in `Zielsatz/` imports these modules; `Grammatik.lean` does). Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` at most.*

| Statement | File | Hypotheses |
|---|---|---|
| `fertig_kein_schritt` (a finished thread has no step), `fertig_bleibt`, `fertig_lauf` | `KernMaske` | none |
| `MaskeKern`, `maskEintr`, `maskeNach`, `MaskeOk` (a pair is in a core's list iff the thread runs on it, holds the lock, the lock is declared `masks irqs`), **`maskeOk_schritt`**, **`maske_nichtleer_iff`** (a core is masked iff one of its threads holds a masking lock: nesting included), `mask_leer_ohne`, `maskeOk_leer_ohne` | `KernMaske` | `D.maskiert L = false` for the last two |
| `KernZ`, `KernSchritt` (entry only when unmasked, run to completion, acquisition masks / release unmasks), `KernLauf`, `KernStart`, `KernZ.weiter`, `kernSchritt_weiter`; **`kernLauf_laufG`** (a guarded run is a G run); `kernLauf_maskeOk`, `kernLauf_begonnen` | `KernMaske` | `KernStart` |
| **`kernPlan_aus_lauf`**: every guarded run meets `KernPlan` (the schedule is DERIVED) | `KernMaske` | `KernStart` |
| `KernHaltM`; **`kernHaltM_aus`** (= `kernHaltE_aus` with the schedule proved) | `KernMaske` | closure `abg`, discipline `masken`, `hvoll` |
| **`laufG_kernLauf`** (no handler: every G run lifts, machine for machine), `kernLauf_ungemaskt` (no masking lock: no core is ever masked) | `KernMaske` | no handler / `maskiert = false` |
| **`kernPlan_lift`** (every run `KernPlan` admits is a guarded run), **`kernHaltE_iff_M`**: `KernHaltE ↔ KernHaltM`, so replacing the leg is no weakening | `KernMaskeGleich` | no thread of the start holds a masking lock |
| witnesses: `ohne_maske_verklemmt` (unmasked lock: the handler enters at a held lock, waits, nothing steps, `¬ KernHaltM`; `w_masken_falsch`), `mit_maske_verweigert` (masked: the mask is set, the model refuses the entry step; the planted defect is that step, a step of plain G), `mit_maske_nach_freigabe`, `mit_maske_sicher`, `mit_maske_sicher_E`, `einbettung_zeuge`; the fixture `wD m` (one program, two declarations, `maskiert := fun _ => m`) | `KernMaskeZeuge` | none |
| `Instr.imsk` (`stepI`: word exchange on the mask cell), `maskOn`/`maskOff`, `stepI_imsk`, `maskOn_run`, `maskOff_run`, `tk_one_ne` | `Mask` (+ `Model/`) | cell holds a word |
| the NAMED assumption `MaskHw` (H1 the mask word is the register, H2 interrupts only on an unmasked core, H3 no thread switch on a masked core; ISA-neutral) | `MaskNeed` | none (an obligation structure, not an instance) |
| `MaskCells` (cover: G masked implies the word is nonzero), `MaskDisj`, `maskCells_store_other`, **`maskCells_ticket`**, `lockRel_mask_store`, **`mask_on_step`**, **`maskCells_nach`**, **`mask_off_step`**, **`irq_guard`** (with `MaskHw`: a handler entry on core `c` happens only where `mk c = []`, the premise `eintritt` of `KernSchritt`) | `MaskRel` | layout facts `MaskDisj`; `hex`/`hx` ghost premises |
| witnesses: **`mask_witness`** (one thread through the lowered section: `LockRel` and `MaskCells` at both stops), `maskHw_witness` (satisfiable), `maskHw_planted` (planted defect: a CPU that interrupts a masked core meets no `MaskHw`), `irq_refused_inside`; fixture `mD`/`mLay`/`mMod` | `MaskWitness` | none |

NOT proved: the `Spec.lean` restatement (a PROPOSAL, `PLAN-DYNAMIC.md` 8a.4: move the layer into `Spec.lean`, `KernHaltE := KernHaltM`, drop `KernPlan`), its GA twin `KernHaltEA`; the composition of the `Code` steps with the interleaving of ALL threads of a core (H3 is a named premise; the restore step has a ghost premise); handler re-entry and handler-on-handler preemption (a begun handler blocks every other thread of its core, as in `KernPlan`); a Rust/LLVM emitter for `imsk` (Lean first); several cores in the `Code` witness (one core).

## 82. The reader/writer lock: the layer `RwSchritt` over machine G, its legs, and the lowering as `Code` (2026-10-18, `PLAN-DYNAMIC.md` 8a.5)

*Files: `grammatik/Grammatik/Zielsatz/Eigenschaften/{RwSchritt,RwRang,RwOrdnung,RwInv,RwZeuge,RwZeugeLeser}.lean`, `grammatik/Grammatik/Code/Conc/{RwLock,RwLockRel,RwLockWitness}.lean`. Model only: `Spec.lean`, the Rust checker, the exporter and the LLVM backend are unchanged, `gabbro_ziel` is untouched (nothing in `Zielsatz/Kern/` imports these modules; `Grammatik.lean` does). Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` at most.*

| Statement | File | Hypotheses |
|---|---|---|
| `Lese`, `ohneFremde` (+ `ohneFremde_self`, `_frei`), `RwAcq` (a shared acquisition = G's own `dannLocks` step in the blank machine), `RwSchritt` (a G step or a shared acquisition), `RwLauf`; `rwSchritt_of_G`, `rwLauf_of_laufG` | `RwSchritt` | none |
| **`rwSchritt_ohne_leser`, `rwLauf_ohne_leser`** (no reader: the layer is machine G, its runs are `LaufG`), `rwExkl_ohne_leser` | `RwSchritt` | `lese = fun _ _ => False` |
| `rwSchritt_akteur`, `rwSchritt_fremd`, `rwSchritt_delta`, `rwAcq_speicher`, **`rw_nimmt`** (a lock that enters the actor's held set was free, or the actor is a reader and every other holder is) | `RwSchritt` | `GutO O` |
| **`RwExkl`** (two holders are both readers), **`rwExkl_schritt`, `rwExkl_lauf`**, `rwExkl_start`, `rw_schreiber_allein`, `rw_leser_unter_sich`; `rwLauf_nil`, `rwLauf_schritt` (run builders) | `RwSchritt` | `GutO O`; `StartExklusiv` for the start |
| `rangInvG_rw`, **`kein_warteZyklus_rw`** (no wait cycle on every layer run), `WartetAufRw`, `KeinWarteZyklusRw`, `keinWarteZyklusRw_aus`, `anSperre_ohneFremde`, **`rw_leser_geht`** (a reader at a lock held only by readers has a step) | `RwRang` | `GutO O`, `StufenM P`, the start holds nothing |
| `LeserLos`, `spurInv_rw_schritt`, `spurInv_rw_lauf`, `rwSchritt_traeger`, `ereignis_haelt_rw`, `zugriff_haelt_rw` (an access holds the guard) | `RwOrdnung` | `GutO O`, `SpurInv` at the start |
| `GeordnetRw`, **`sperre_ordnet_rw`** (the order through the lock when one side is a writer), **`rennfrei_rw`**, **`rennfreiRw_aus`** (no write-write, no write-read race on a guarded carrier), **`rwSicht_schritt`** (`sperrSicht` of a shared lock: only a holder accesses; while any other thread holds, nobody changes the carrier) | `RwOrdnung` | `LeserLos` (a PREMISE: readers write nothing their lock guards), `RwExkl` and `SpurInv` at the start, every non-atomic carrier has a guard (`hG`) |
| `SperrInvRw`, `sperrInvRw_start`, **`sperrInvRw_schritt`, `sperrInvRw_lauf`** (only a WRITER's release owes the invariant), **`leser_sieht_inv`** (a reader sees `S.inv L` in its section), `schreiber_erst_frei` | `RwInv` | `SperrInvOk`, the writer's release obligation `hwr`, the readers' discipline |
| witnesses: **`leser_schreiber_lauf`** (twelve layer steps: two readers hold at once, G alone refuses the second, the writer has no step, both leave, the writer holds alone, a late reader is held back, `GeordnetRw` at the reader-then-writer pair); planted defects: **the writer admitted without `andere`** (last conjunct: `RwExkl` fails), **`leser_rekursiv_verweigert`** (the recursive read lock: the rank premise `hr` is unprovable); fixture `wD false` of `KernMaskeZeuge` | `RwZeuge` | none |
| planted defect: **`leser_schreibt_rennt`** (two readers hold the lock by signature and both write `konto[0]`: the accesses are unordered, `¬ LeserLos`, derived from `rennfrei_rw`); fixture `ivD` of `Proben/InvZeuge` | `RwZeugeLeser` | none |
| `Code`: the blocks `wrTake`, `wrRel`, `rdLoad`, `rdTake`, `rdRel` (ONE state word `lblk`: `0` free, `2k` readers, `1` writer; `cas`/`aload`/`armw sub`/`astor`, release/acquire), the instruction lemmas `stepI_cas_ok/fail`, `stepI_sub2`, `stepI_add2`, `stepI_astor_opd`, and the runs `wr_take_ok/fail`, `wr_rel_run`, `rd_load_wait/go`, `rd_take_ok/fail`, `rd_rel_run` | `RwLock` | cells hold words |
| **`RwRel`** (ghost readers and writer, the word, G's held locks counted, the mode), `rwRel_step`, **`rwRel_exkl`** (it implies `RwExkl`), the steps **`rd_take_ok_step`** (= the layer's shared acquisition), **`wr_take_ok_step`** (= G's `dannLocks`, `RufFreiG`), **`rd_rel_step`**, **`wr_rel_step`** (= G's `freiGib`), the silent `rd_load_wait_step`, `rd_load_go_step`, `rd_take_fail_step`, `wr_take_fail_step`, `rw_store_post` | `RwLockRel` | `LayoutOk`; the ONE named assumption `hroom` (fewer than `2 ^ (wbits - 1) - 1` readers at once) |
| witness **`rw_witness`** (two readers and a writer on the lowered blocks: a winning take, a LOSING take, both readers hold, the writer's take fails, both release, the writer takes alone; `RwRel` after every step); fixture `cD`/`cLay` | `RwLockWitness` | none |

NOT proved: the `Spec.lean` change (a PROPOSAL, `PLAN-DYNAMIC.md` 8a.5: the mode in G, recommended; or a layer statement) and the syntax (`lock L rank N rw`, `reads L { ... }`, the signature clause `reads L`: proposals); the legs of `Ziel` that are proved by induction over `RufErreichbarG` and have no layer twin (`schwach`, `vertrag`, `invRueck`, `invGrund`, `invRuhe`, `invSicht`, `folge`, `fortschritt`, `zeit`, `keinKernHalt`: a layer-reachable machine is not G-reachable); the checker rule that DERIVES `LeserLos` (a PREMISE here); one mode per (thread, lock) in the layer; fairness (a stream of readers can starve a writer; a writer-preference bit is not modelled); the composition of the `Code` steps with ALL interleavings (the steps are per-thread, as the ticket lock's); a Rust/LLVM emitter (Lean first).

## 83. Comments: `//`, nesting `/* */`, `///` doc trivia (Simon's decision, 2026-10-18; lexical syntax, `SYNTAX.md` `comment`)

*Files: `grammatik/Grammatik/Parser/Lex/{Lexer,LexerVertrauen,LexerDoku}.lean`, `crates/gabbro-syntax/src/lex.rs`. Model only for the lexer; `gabbro_ziel` is untouched (the statement does not mention comments).*

| Statement | File | Hypotheses |
|---|---|---|
| `nimmZeile`, `ueberBlock` (depth counter: `/*` opens one level, `*/` closes one, depth 0 ends the comment; `none` = the text ended inside), `ueberBlock_schliesst`, `ueberBlock_oeffnet`, `ueberBlock_null`; `scan` handles `//`, `////`+, `///` and `/*` before any other mark, so a marker inside a string is text (the `"` arm reads the whole string first) | `Lexer` | none |
| witnesses: `lex_kommentar`, `lex_block`, **`lex_block_verschachtelt`** (`/* x /* y */ still comment */`), `lex_block_tief` (depth three), `lex_block_leer`, `lex_marker_im_text`, `lex_text_im_kommentar`, `lex_block_streuende_ende` (a stray `*/` is `*` `/`), **`lex_alter_strich_kein_kommentar`** (`--` is two minus marks) | `Lexer` | none |
| refusals: **`lex_block_offen`**, `lex_block_offen_verschachtelt` (`.offenerKommentar`, Rust `L008`) | `Lexer` | none |
| doc trivia: `lexDoku` keeps `///` as `Token.doku` (text after the three slashes), `lex_doku`, `lexDoku_doku`, `lexDoku_vier_striche` (`////` is ordinary), `lexDoku_zwei_striche`, `lexDoku_doku_im_block`, `lexDoku_doku_am_ende` | `Lexer` | none |
| **`lex_ohne_doku`** (for EVERY source text, `lex` never holds a `Token.doku`: a doc comment cannot change what the parser reads), `scan_ohne_doku`, witness `lex_ohne_doku_zeuge` (a source whose `lexDoku` differs from `lex`), `lex_ohne_doku_beispiel` | `LexerDoku` | none |
| planted defect: `ueberBlock_verschachtelt_flach` (the flat variant stops at the inner closer and differs from `ueberBlock`: the nesting witness is not vacuous), `ueberBlock_verschachtelt` | `Lexer` | none |
| the trust gate (`codeZeichen`) skips both comment forms the way `scan` does: `quelle_kommentar_sauber`, `quelle_blockkommentar_sauber`, `quelle_bidi` (a bidi character is refused inside a comment too) | `LexerVertrauen` | none |

NOT proved: that `lex_ohne_doku` is the only way a comment is invisible to the parser (the parser reads `lex`, so it holds by construction); the Rust lexer's agreement with `scan` beyond the probes (`gift/1471`, the Rust unit tests, the corpus rewritten to `//`). A tool that attaches doc comments to items does not exist yet.

## 84. Hardware-neutral gates: region provider, trap clause, process exit, join order, targets as data, the `Code` gate (2026-10-18, `PLAN-HARDWARE.md` §16, `LLVM-BACKEND.md` §11)

*Files: `grammatik/Grammatik/Hardware/{Anbieter/Region,Anbieter/Arena,Tor/Abi,Tor/Ende,Neutral}.lean`, `grammatik/Grammatik/Code/Gate/{Gate,Provider,Bruecke,Zeuge,Maske}.lean`. Layers and new files only: `Deklaration`, machine G, `Akzeptiert` and `Spec.lean` are untouched; `gabbro_ziel` is on `propext`, `Classical.choice`, `Quot.sound`. The syntax (`pool`, `trap`, `proc`, `task`, `space`, `mask`, `conv`/`stub`, profile entries) is a PROPOSAL.*

| Statement | File | Hypotheses |
|---|---|---|
| the provider machine `PStep` (reserve/commit/page return/end, the contract as the step premises), the invariant `Gut`, **`gut_nach`**, `lauf_gut`, `lebend_getrennt`; **no RAM before use**: `hole_ram_gleich`, **`hole_neu_aus`**, `hole_neu_null`; **no RAM without a commit**: **`ram_gefuellt`**, `ram_nur_gefuellt`, `kein_zugriff_ohne_fuell` | `Region` | the pool's contract (the premises of `PStep`) is the NAMED assumption |
| planted defects: `ueberlapp_verweigert` (an overlapping answer), `fuell_draussen_verweigert`, `hole_mit_ram_sichtbar` (a reserve that fills); witnesses `zeuge_lauf_geht`, `hole_neu_null_zeuge` | `Region` | none |
| the arena through the provider: `ArenaGut`, **`arena_start`**, **`arena_grow_geht`** (`dynGrow` = ONE commit of the template's range, legal under the contract), `slot_resident`, `slot_in_region`, `arena_exklusiv`, `region_exklusiv`, `gib_nichts_resident`; witness **`arena_zeuge`** (six 8-byte slots, 16-byte pages, resident exactly below the page-rounded prefix); planted defect `grow_ueber_decke_verweigert` | `Arena` | the template arithmetic of `SchablonenArena` and `ArenaDyn` |
| the thread stack with a guard: `StapelGut`, `stapel_start`, **`stapel_waechst`**, **`stapel_wache_kein_zugriff`** (an overflow into the guard is a stop), `stapel_wache_exklusiv`; planted defect `fuell_in_wache_bricht` | `Arena` | none |
| the trap clause as data: `RegName`, `Falle`, `TorAbi`, `TorAbi.gut`, **`belegung_nodup`**, `belegung_nummer`, `belegung_param`, `loese_text_unabh`, `Tor.mitFalle_bed` (the clause changes no meaning), **`sysabi_zu_tor`** (the x86_64 `SysAbi` is an instance); witnesses `schreib_gut`, `schreib_deckt`, `belegung_zeuge` (x86_64, aarch64 and a made-up `ecall` architecture); planted defects `defekt_aus_zerstoert`, `defekt_ein_doppelt`, `defekt_nummer_ist_eingabe` | `Abi` | none |
| targets as data: `ZielDaten`, `ZielDaten.gut`, `conf` (the `Code.Conf` it determines), `TorAbi.passtZu`; witnesses `ziele_gut`, `schreib_passt`, `conf_folgt` (32-bit big endian and 64-bit little endian); planted defects `defekt_fremdes_register`, `defekt_wort_48` | `Abi` | the layout string is opaque (checker rule, not Lean) |
| process exit: `startSpur`, `start_code`, **`start_ende_gut`** (nothing after the end event), `start_ohne_rueckkehr`; witness `start_zeuge`; planted defects `ohne_exit_kein_ende`, `nachlauf_nicht_ende_gut` | `Ende` | the exit gate is declared `-> never` (existing) |
| thread join and stack release: `JoinGut`, **`kein_kind_nach_gib`** (no child step follows the stack release); witness `join_zeuge`; planted defect `join_defekt` (a wait that returned before the clear) | `Ende` | the spawn gate's contract (clear after the end) is the named assumption |
| `Code`: a user gate is a call past the module's own functions with a contract (`GateSpec`), `GateStep`, `StepG`, `ReachG`, `step_stuck_am_tor`, **`stepG_gdw_step`**, **`reachG_gdw_reach`** (a gate-free module keeps its meaning), **`GateNeed`** (what a CPU model must provide for user-declared traps), **`gate_verfeinert`**, `gate_laeuft` | `Gate` | `GateNeed` is the named hardware assumption |
| `Code`: the provider roles over block memory (`holeSpec`, `fuellSpec`, `gibSpec`; `hole_frisch`, `hole_andere`, `fuell_lokal`, `gib_weg`, `gib_haengt`) and **`Entspricht`** (address-level contract and block memory describe one world), `entspricht_hole`, `entspricht_gib`, `entspricht_ram`, **`entspricht_getrennt`** (distinct live blocks have disjoint address ranges: a consequence of freshness); witness `bruecke_zeuge`; planted defect `aliasing_verweigert` | `Provider`, `Bruecke` | none |
| `Code`: the reference CPU meets `GateNeed` (`ref_need`, `erfuellbar`), **`tor_zeuge`** (`gate_verfeinert` on a module that calls the reserve gate, all premises jointly); planted defect **`schlecht_verletzt`** (a CPU whose reserve returns an existing block violates `GateNeed`) | `Zeuge` | none |
| the interrupt mask as a user gate: `maskSpec`, **`maskSpec_eindeutig`**, **`maskSpec_ist_imsk`**, `imsk_ist_maskSpec` (the exchange gate IS `Instr.imsk`) | `Maske` | `MaskHw` of `MaskNeed` stays the gate's assumption |
| **neutrality**: `GabbroZielZ Z`, **`gabbro_ziel_zusatz`** (for EVERY family of extra named assumptions the statement holds), **`gabbro_ziel_leer`** (`GabbroZielZ (fun _ _ => True) ↔ GabbroZiel`); `AnbieterAnnahme`, `anbieter_leer`, `anbieter_praefix`, `lauf_append`, planted defect `anbieter_verletzt`, witness `anbieter_zeuge` | `Neutral` | none |

NOT proved (open, named in `PLAN-HARDWARE.md` §16.11/§16.12): the bridge from ghost-carrier contracts to `PStep` (O-H1) and the run-level projection of the provider log (O-H2); the `Profil.lean` text/list entries (O-H3); the `Code`-side bridge has no resident bit, so commit and page return are shown to KEEP the correspondence but residency is not a `Code` fact; that any user text does what its gate says (that is the falsifier's job); frames larger than the stack guard; the layout/word consistency of a target (a checker rule); L5 stubs and the port-space accessors are design only; the Rust parser, checker and compiler are not changed.

## 85. Adequacy of a test set: sufficiency, minimality and the count for Gabbro (Phase C item 8, 2026-10-19, `CHECKER.md` §16)

*Files: `grammatik/Grammatik/Adaequanz/{Baum,Schichten,Hinlaenglich,Minimal,Gegenmodell,Ueberdeckung,Muster,Zeugen}.lean`, `grammatik/Grammatik/Adaequanz/Gabbro/{Signatur,Zaehlung}.lean`. New folder, nothing of the model changed; the abstract theorems import only Mathlib, the Gabbro files read `Kern/Syntax` and `Gen/Familie`. `gabbro_ziel` is untouched.*

| Statement | File | Hypotheses |
|---|---|---|
| `Sig`, `Baum`, `Kontext.ein`, `Automat` (deterministic bottom-up tree automaton with output: the class of program-neutral implementations), **`lauf_ein`** (a context sees the plugged tree only through its state), `sem_ein` | `Baum` | none |
| `tupel`, `mem_tupel`, `tupel_laenge`; layers `schicht` (access trees, then every constructor over the layer below), `testmenge W d`; **`testmenge_laenge`** (`|W| * N d`, `N 0 = n`, `N (d+1) = N d + Σ_k N d ^ ar k`), `anzahl_eins` (`m = n`: `n + Σ_k n ^ ar k`) | `Schichten` | none |
| **THEOREM 1 `hinlaenglich`**: every automaton with at most `m` states that agrees with the spec on `testmenge W (m - n + 1)` agrees on every tree; steps `trennt_schicht`, `erreicht_null`, `erreicht_stopp`, `erreicht_abgeschlossen`, `vertreter`, `vertreter_spez`; `hinlaenglich_groesse` | `Hinlaenglich` | `Spezifiziert`: complete lists, access trees, `W` separates the spec's states and holds the hole |
| `Zelle`, `zelle`, `zeuge`; **`wurzelMutant`** (`n + 1` states) wrong exactly on the trees rooted at the cell (`wurzelMutant_sem`, `_besteht`, `_falsch`); **THEOREM 2a `wurzel_noetig`, `wurzel_schranke`** (`m ≥ n + 1`: every cell rooted in a test, `|M| ≥ Σ_k n ^ ar k`); **`flaggenMutant`** (`2 n` states) wrong exactly on the trees containing the cell (`flaggenMutant_sem`); **THEOREM 2b `flagge_noetig`** (`m ≥ 2 n`: every cell covered) | `Minimal` | access trees only (no separation needed); `kipp` has no fixed point |
| counter-models: `hoehe`, `zaehlerModell` (`zaehler_sem`: wrong exactly above height `h`), **`kein_endlicher_test`** (no finite set is sufficient without a state bound), **`zaehler_ueber_m`** (against a set sufficient for `m` the counter needs more than `m` states), `turm`, `hoehe_turm`; **`sonderfall_nicht_neutral`** (a program-specific branch is no automaton with at most `m` states) | `Gegenmodell` | a constructor of arity 0 and one of arity at least 1 |
| **THEOREM 3** (cell-local compiler, no masking): **`deckung_iff`** (sufficient iff covering), `deckung_schranke` (exclusive cells), `deckung_konstruktion` | `Ueberdeckung` | the per-cell correctness (`lowerS_ok` shape) and no masking are the class |
| **THEOREM 4** (conjunctive checker): **`muster_hinlaenglich`** (canonical programs suffice), **`schlecht_noetig`** (an isolable refusal cell needs its own single-fault test), `schlecht_getrennt`, **`gut_noetig`** (an accepted cell needs a valid test), **`muster_schranke`** (`|M| ≥ isolable refusal cells + 1`) | `Muster` | the verdict is a conjunction over cells (the class of TODO item 8) |
| witnesses: a 3-constructor lock checker, `spezifiziert`, **`testmenge_zahl`** (32 tests), **`falsch_faellt`** (a planted wrong checker fails one), **`hinlaenglich_zeuge`**, **`wurzel_noetig_zeuge`**, `wurzel_schranke_zeuge` (13 ≤ \|M\|), **`kein_endlicher_test_zeuge`**, `deckung_zeuge` | `Zeugen` | none (kernel `decide`) |
| Gabbro: the constructor table of the term families checked against the model at elaboration (`Signatur`); root-cell counts **`wurzel_z0`** (1 650), **`wurzel_z1`** (657 922 500), `wurzelFamilie`; pattern atoms of the ten components, `musterZellen_wert` (≤ 4 540) | `Gabbro/Signatur`, `Gabbro/Zaehlung` | the dimension table (H2, H3, H6) is a reading of the model, on paper |

NOT proved: that the Rust checker and compiler are in any of these classes (hypotheses H1-H8 of `CHECKER.md` §16.1, an assumption about the code, measured by metamorphic tests); the Myhill-Nerode index of `AkzeptiertX` (only the presentation upper bound is computed); `|W| ≤ n - 1` and the witness height `m + n - 1` (paper); the exact minimum for `m = n` (open); that every presentation combination is reachable in a given declaration.
