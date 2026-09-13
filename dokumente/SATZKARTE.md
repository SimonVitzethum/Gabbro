# SATZKARTE-C: goal-family premise map, re-measured 2026-09-12 (lane 97)

Replaces the class column of SATZKARTE-A (§2) with the four binding classes:
(a) USER obligation, (b) HARDWARE assumption, (c) DISCHARGED by a merged
theorem (named), (d) STILL OPEN language duty. Covers every premise of every
theorem in the goal family (`grammatik/Grammatik/Ziel.lean`: `ziel_nutzer_last`,
`ziel_seqLogic_aus_spec`, `ziel_seqLogic_aus_spec_invariantForm`,
`ziel_nutzer_last_aus_disziplin`, `ziel_nutzer_last_aus_maschine`,
`ziel_nutzer_last_aus_pc`, `ziel_nutzer_last_aus_pc_stabil`,
`ziel_nutzer_last_aus_pc_Q`) and of `csl_ressourceninvariante`
(`CSLInvariante.lean:305`), `EZD.eigenzustand_nur_eigene_schritteD_rep`
(`EigenZustandD.lean:1368`), `rufG_treu` (`RufMaschineG.lean:1198`).
All claims verified by reading the Lean sources cited as `file:line`.
Line numbers refer to the working tree on branch `muse/97`.

Prior maps are kept below unchanged: §§1-5 (draft A, lane 16) and §6
(wave-1 verdicts). §7 is the new classification table, §8 the next-lane
proposals for each (d) item, §9 the `#print axioms` record, §10 the
distance to the goal.

> §§7-10 are superseded by §11 (goal restated and proved over machine G, 2026-09-13); kept unchanged for history.

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
| `hReturn` | Every writing chain step re-establishes every carrier invariant under the guard. | (a) USER, fragment (c) | `csl_ressourceninvariante` (`CSLInvariante.lean:305`) covers the quiescent (lock-free) reading; per-step restoration stays user-side |
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
`csl_ressourceninvariante` (`CSLInvariante.lean:305-314`): `hO` (b);
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
Target: `Gabbro.Grammatik.ziel_nutzer_last_aus_pc_Q`, `grammatik/Grammatik/Ziel.lean:2324`.
All claims verified by reading the Lean sources cited as `file:line`.
Line numbers refer to the current working tree on branch `muse/16`.

Q-binder instantiation: `Pre := Extraktion.QRequires P`, `Post := Extraktion.QEnsures P`,
where `QRequires` (`grammatik/Grammatik/Extraktion.lean:1437`) is `requires` as a world
predicate (holds for every parameter environment) and `QEnsures`
(`grammatik/Grammatik/Extraktion.lean:1442`) is `ensures` as a world predicate
(for every return value and every parameter environment). The per-thread assertion is
`SpecQ Pre Post Nb J f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`
(`grammatik/Grammatik/InterferenzAllgemein.lean:1069`).

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
C1 by `pc_gesittet` (`grammatik/Grammatik/Maschine.lean:1743`);
C2 by `pc_konsistent` (`Maschine.lean:1426`) and `pc_gut_obs` (`Maschine.lean:1433`);
C3 by `stabil_aus_lauf` (`Maschine.lean:3879`), whose `hFree` argument is derived inside from
`hForm` via `interferenceFree_of_invariantForm` (`grammatik/Grammatik/InterferenzAllgemein.lean:1213`)
over the discipline-derived context from `invariantenKontext_aus_disziplin`
(`InterferenzAllgemein.lean:1530`), with memory via `speicherVertrag_aus_Q`
(`Extraktion.lean:3924`) and frame via `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`);
C4 by `sampling_closes_frist` (`grammatik/Grammatik/Fristlauf.lean:395`);
C5 by the `begrenzt` field of the supplied `Absenkung` (structure field, not a theorem);
C6 by `zwei_fehler` (`grammatik/Grammatik/Satz.lean:50`, proved by case split, unconditional);
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
`grammatik/Grammatik/Semantik.lean:355`), `passes` (execution bound), `fcode` (thread-to-function
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
| R1 | QLeer (lane 15) | `qRequires_nowhere` (`grammatik/Grammatik/QLeer.lean:133`), `qEnsures_nowhere` (`QLeer.lean:142`), `qSeedAll_unmoeglich_req` (`QLeer.lean:154`), `qSeedAll_unmoeglich_ens` (`QLeer.lean:170`) over `QRequires` (`grammatik/Grammatik/Extraktion.lean:1437`) / `QEnsures` (`Extraktion.lean:1442`) | Proved theorems on a concrete one-function program, not a reading |
| R2 | BlattGegenbeispiel (lane 14) | `hblatt_post_falsch` (`grammatik/Grammatik/BlattGegenbeispiel.lean:242`), `hblatt_konj_falsch` (`BlattGegenbeispiel.lean:262`), `hblattall_falsch_schreibend` (`BlattGegenbeispiel.lean:286`) | Proved counterexample to `hBlattAll` for a writing leaf |
| R3 | VertragOrtB (lane 02, attempt B) | `ReqAmEintritt` (`grammatik/Grammatik/VertragOrtB.lean:114`), `EnsAmRueck` (`VertragOrtB.lean:120`), `VertragAmOrtB` (`VertragOrtB.lean:137`), `rufAt_ok_of_gates` (`VertragOrtB.lean:406`), `rueck_ohne_nachbedingung` (`VertragOrtB.lean:444`) | Proved place-check construction plus one-direction bridge; not wired into the goal theorem (import-cycle remainder) |
| R4 | KetteMehrfadenC (lane 11, attempt C) | `KettenSpurDeckung` (`grammatik/Grammatik/KetteMehrfadenC.lean:115`), `kette_zwei_aus_lauf` (`KetteMehrfadenC.lean:766`), `kette_aus_deckung` (`KetteMehrfadenC.lean:879`), `deckung_strikt_schwaecher` (`KetteMehrfadenC.lean:909`) | Proved chain-from-run for the two-thread lock-only fragment; N-thread discharge open |
| R5 | Audit muse/23, F2 (HIGH) | Filed: `allgemeinStabil` (`grammatik/Grammatik/InterferenzAllgemein.lean:498`) never consumes `hInv`/`hDeck`. Demo: `audit_allgemeinStabil_ohne_InvDeck` (`messung/muse-audit/23/F2_HauptsatzNutztInvDeckNicht.lean:25`), `audit_allgemeinStabil_forget` (`F2_HauptsatzNutztInvDeckNicht.lean:61`) | Checked demonstration, not a `Grammatik` theorem |
| R6 | Audit muse/23, F4 (HIGH) | Filed: `serial_chain_from_run` (`grammatik/Grammatik/InterferenzAllgemein.lean:1816`) proves its HB half from `SerialLink` + `reduktion_seriell` alone. Demo: `audit_hb_sidecar_ohne_kette` (`messung/muse-audit/23/F4_ReduktionOhneKette.lean:31`), `audit_kette_ohne_run` (`F4_ReduktionOhneKette.lean:47`) | Checked demonstration, not a `Grammatik` theorem |
| R7 | Audit muse/23, F5 (HIGH) | Filed: `hinv_aus_disziplin` (`grammatik/Grammatik/InterferenzAllgemein.lean:1502`) discards `LockFrei` (`intro k σ h _`), so `interferenceFree_wo_frei` (`InterferenzAllgemein.lean:1597`) restricts nothing. Demo: `audit_hinv_ohne_frei` (`messung/muse-audit/23/F5_LockFreiUngenutzt.lean:23`), `audit_hinv_forget_frei` (`F5_LockFreiUngenutzt.lean:47`) | Checked demonstration, not a `Grammatik` theorem |
| R8 | Audit muse/24, F9 (HIGH) | Filed: `QRequires` (`grammatik/Grammatik/Extraktion.lean:1437`) / `QEnsures` (`Extraktion.lean:1442`) quantify over all envs/values at one world fed twice as entry and present (`eval σ e σ ρ`). Demo: `audit_QRequires_unfold` (`messung/muse-audit/24/Audit24.lean:80`), `audit_QEnsures_unfold` (`Audit24.lean:85`), both `rfl` | Checked demonstration, not a `Grammatik` theorem |
| R9 | Audit muse/24, F11 (HIGH) | Filed: `hmem_all` of `hwit_aus_lauf` (`grammatik/Grammatik/Extraktion.lean:3829`, premise at `:3840`) and `hwit_alt_faltung` (`Extraktion.lean:3609`, premise at `:3621`) demands `.inl t₀ ∈ stmtTraeger tabs globs s` for every leaf, but `stmtTraeger` (`Extraktion.lean:2421`) returns `[]` for `assignVar` (`:2428`), `ite`, calls, locks, registers, marks, terminals. Demo: `assignVar`-implies-`False` example (`messung/muse-audit/24/Audit24.lean:107-112`) | Checked demonstration, not a `Grammatik` theorem |
| R10 | Audit muse/26, F7 (HIGH) | Filed: `handler_wettlauf_frei` (`grammatik/Grammatik/Unterbrechung.lean:103`) and `handler_wettlauf_frei_global` (`Unterbrechung.lean:120`) discard the handler/boundary premises (`have _ :=`, `rcases hH with _ \| _`). Demo: `audit26_handler_premise_discarded` (`messung/muse-audit/26/F7_HandlerPremise.lean:17`) | Checked demonstration, not a `Grammatik` theorem |

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

(End of file — §11 added 2026-09-13, lane 133; §§1-10 history above.)
