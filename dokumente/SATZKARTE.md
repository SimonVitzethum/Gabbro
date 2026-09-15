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
> **The current goal theorem is `ziel_ort_ganz`, §13.**

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
(`messung/URTEIL-OPUS-2026-09-13.md` §6). Files: `ZielOrtRahmenBeweis.lean`
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
(`messung/URTEIL-OPUS-2026-09-13.md` §6, probes B and C of §3). Files:
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

Design record: `dokumente/GLEITKOMMA.md` §§7-9. What changed for the
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

### 17.2 The emitted C float forms

CFormen.lean has four float forms (`CX.fbin/fcmp/fvon/fin`) computing
C11 Annex F by the same model; CFormenF.lean relates them to Gabbro:
`gsem_gleit`, `gsem_gleitLit`, `gsem_gleitVon`, `ecorr_fllt/flle/flgt/
flge`, `gsem_gleitNarrow` with `narrowCondF_ge_le` (`if (!(x >= LO && x <=
HI))`) and `narrowCondF_endlich` (`if (!isfinite(x))`). The NAMED
ASSUMPTION is `gleitkomma_ieee u` over the machine's `FloatUnit` (inhabited
by `annexF`); `maschine_*` bridge it per operation. Witness on a corpus
program: `klemmen_corr` (`beispiele/26-gleitkomma.gab`, both branches,
every context); `klemmen_maschine` uses the assumption.

Cuts: `float` (binary32) has C forms but no correspondence (`Ty.fl` has
no width); floats in memory (table fields, globals) have none (`encW`
has no float case); an inline float literal is covered per program, not
by a general lemma (the model binds it, C inlines it).

### 17.3 Nested arrays

`[[T; N]; M]` is a table with `count M*N` and `M[i][j]` its cell `i*N +
j` (Verschachtelt.lean): `flach_bereich`, `flach_injektiv`,
`flach_zerlegung`, `nestIdx`/`eval_nestIdx`; C's row-major `a[i][j]` is
the flat access (`ev_idx_nested`); witness `nv_lauf`, `nv_c_adresse`.
The memory relation of a static C array stays the pre-existing uncovered
`expr:array-read`.

Axioms of every new theorem: `propext`, `Classical.choice`, `Quot.sound`
(subsets). Full build on ki-pc-fisch-101: 185 jobs, no `sorryAx`.

## 18. The `forever` budget, start reasons, the closing theorem's assumptions (2026-09-14, second round)

The model items of the two independent verdicts of 2026-09-14
(`messung/URTEIL-OPUS-2026-09-14.md` §5 probe D and §6 items 1, 7;
`messung/URTEIL-MUSE-2026-09-14.md` §5). Files: `Durchgaenge.lean` (new),
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

`Zielsatz/Spec.lean` states the goal `GabbroZiel` as one statement; two of
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
-- Zielsatz/Spec.lean (unchanged):
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
-- Zielsatz/Spec.lean (unchanged):
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
-- Zielsatz/Beweis.lean
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

Measured on the corpus (`messung/WARTESCHRANKEN-2026-09-15.md`, by hand from the
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

The third independent Opus verdict (`URTEIL-OPUS-2026-09-15.md`) found that the STATEMENT was
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

The fourth independent Opus verdict (`URTEIL-OPUS-2026-09-15b.md`) found `GabbroZiel` to be
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
- `SYNTAX.md` (the outcome table and the float row) and `GLEITKOMMA.md` name `logik bereich`
  now; `PLAN-GRAMMATIK.md` and `PLAN-UMSETZUNG.md` still say `hardware ieee` (the C runtime
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
  carries no width and the model computes binary64 (GLEITKOMMA.md §7), so an `f32` register is
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

### 24.4 The G1 probes, refuted (Zielsatz/ProbenG1.lean)

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

Both round-6 reviews (URTEIL-OPUS-2026-09-15d.md §3, URTEIL-MUSE-2026-09-15d.md) confirmed "the
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
* `antwortenB` (Zielsatz/Akzeptiert.lean) is the Bool, part of `Akzeptiert`;
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
  `stelleOk_mitRuhe`, Zielsatz/Ruhe.lean).

**Corrected sentences (Spec.lean).** The ONE list's `nieZurueck` entry is now "a call of an
axiom whose declared result is `never` -- the call does not return ... The continuation is
unreachable in the C as in G", which is true; the escape is removed from the list and named as
refused. The (c) entry reads "for an `E.Q` satisfiable at a DECODABLE value (for a float: a
well-formed one, `WertOk`)". NOT CLAIMED names linking of separately compiled units
(PLAN-ZIELSATZ §10).

**Refuted (Zielsatz/ProbenW1.lean).** `w1_spec_nicht`: no lock family, function list or start
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

## 26. Stage (b): the concurrent closing theorem for `beispiele/124` (2026-09-15)

Translation validation, stage (b) of PLAN-UEBERSETZUNGSVALIDIERUNG §3 item 4, closed for ONE
program; the plan's §7 is the long form. Files: `CNebenlaeufig.lean` (generic),
`Korpus124.lean`, `Schlusssatz124.lean`.

### 26.1 The statement

`schlusssatz_124 passes LP K0 hLZ Echt hDRF : ∃ w, K0 = startC c124 w st0 ∧ Laufzeit kE … ∧
RennfreiC c124 LP K0 ∧ (∀ K, ErreichbarC c124 LP K0 K → ∃ M, RufErreichbarG PR OR passes (M0 w)
M ∧ R124 w K M ∧ Ziel PR kE.S.mitRuhe OR passes (M0 w) M) ∧ ∀ b, Echt b → ∃ K M, … beobC K = b
…`. One sentence per conjunct:
* **start**: the C start is the runtime's start for some root assignment `w`, and the
  corresponding G start meets (d) of the goal theorem;
* **race freedom**: the emitted C is data-race free under the real lock primitive -- PROVED;
* **every SC run**: every SC configuration of the emitted C is related (memory `corrW`, locks,
  every thread) to a reachable machine of G where `Ziel` holds;
* **every real run**: every real observation is that of such a configuration.
Read in the C memory (`schlusssatz_124_c`): a free lock means `konto[0] == konto[1]`, a
returned `hauptA` thread means `privA[0] == 7`.

### 26.2 Premise map

| premise | class | discharged by / named as |
|---|---|---|
| `hDRF : DRFSC c124 LP K0 Echt` | (b) HARDWARE + compiler: the C11 DRF-SC theorem with its region corollary, and the compiler's mapping to the hardware profile | named premise, ONE proposition; its hypothesis `RennfreiC` is PROVED (`rennfreiC_aus_sim`) |
| `hLZ.faeden : FadenStartC c124 [2,3] st0 K0` | runtime (A4): thread creation | named premise; yields (d) `Laufzeit` (`laufzeit_w`) |
| `hLZ.sperre : ∀ …, LP … → sperrAbstrakt …` | runtime: the ticket lock | named premise; `sperrAbstrakt_nur_eigen`: reveals nothing but held or free |
| (a) checker | (c) DISCHARGED | `kP_akzeptiert` (`decide`) |
| (b) user's logic | (c) DISCHARGED | `kE_nutzerPflicht` |
| (c) hardware | (c) DISCHARGED, empty | `kO_hw` (no axiom, register or device) |
| `Echt` | parameter, not a premise | the observations of the compiled program (like `binEin` of stage (a)) |

`LaufzeitC` is the runtime list of PLAN §5 and NICHTINTERFERENZ §10, one list; its scheduler
entries are premises of noninterference only.

### 26.3 How it is proved

A simulation certificate (`SimC`, generic): every SC step of the C from a reachable related
pair is matched by a segment of G steps of the SAME thread that ends related, covers the C
footprint by G accesses and places G releases/acquires only at C lock calls. `sim_lauf` lifts
every C run; `rennfreiC_aus_sim` transfers G's `RennfreiBis`; `schluss_b` assembles. For 124,
`sim124` covers every SC run from every admitted start; the segments are `gBlatt` (store),
`gNimm` (`L_nimm`), `gSetze` (`setze(n)`), `gGib` (`L_gib`), `gPruefe` (`(void)pruefeA()`), and
none for splits and returns; the C blocks run from every related state (`cStore_lauf`,
`cSetze_lauf`, `cPruefe_lauf`), and by `exec_det` every run of a block is that one.

### 26.4 Witness and measurement

`schlusssatz_124_zeuge`: every premise jointly, race freedom by the theorem, and a 20-step SC
run in which thread 1 stands at `L_nimm();` and CANNOT step while thread 0 holds the lock, the
lock then passes from thread 0 to thread 1, both return, and the final C memory shows the
invariant and `privA[0] == 7` by the theorem (0 at the start). `rennfreiC_zeuge_124`: the
same run indexed (`laufC_snoc`); its two critical sections (steps 10 and 15) conflict on
`konto`, and the proved race freedom orders them (release at 12, acquire at 13). Measured: of the six
multi-thread corpus programs only 108 exports (`lean-g`) and it takes no lock; 124's G program
is written from the source (`Korpus124.lean`), because the hand model `mP` lacks `pruefeA`'s
read of `privA`. Finding: the source's `setze` contract is too weak for premise (b) (the
release check fails); `kP` keeps `mP`'s stronger `ensures`.

### 26.5 Axiom record

`schlusssatz_124`, `schlusssatz_124_bei`, `schlusssatz_124_c`, `schlusssatz_124_zeuge`,
`rennfreiC_zeuge_124`,
`sim124`, `schrittA`, `schrittB`, `r124_start`, `gSetze`, `k124_ziel`, `kE_nutzerPflicht`,
`sim_lauf`, `rennfreiC_aus_sim`, `schluss_b`, `ev_zform_blk`: `propext`, `Classical.choice`,
`Quot.sound`; `kP_akzeptiert`: `propext`, `Quot.sound`; `c124_direkt`: `propext`;
`sperrAbstrakt_rahmen`, `sperrAbstrakt_nur_eigen`: none. No `sorry`, no new `axiom`, no
`native_decide`. Built on `ki-pc-fisch-101` (`~/gabbro-opus-nb/`): full `lake build`, 233
jobs, green, no `sorryAx` in the log.

### 26.6 What remains

Region serialisability (inside `DRFSC`; needs a fine-grained C semantics); footprint
soundness in general (`FussTreu`, needs an access-instrumented `Exec`; key lemma
`ev_zform_blk` proved); the ticket lock refining `sperrAbstrakt`; a checker for concurrent
correspondence certificates (T2 for stage (b)); the exporter for 124 and parse fidelity; the
emitted text as data (no C parser); lock calls inside loops, branches or callees, volatile and
foreign calls in blocks, and atomics as a source of ordering (an atomic access counts like a
plain one in `RennfreiC`, and no A10 ordering yet). The chain count stays 1 (PLAN §7.6).

## 27. The closing theorem, stage (a), generic: `schlusssatz`; chain count 2 (2026-09-15)

PLAN-UEBERSETZUNGSVALIDIERUNG §6 (rewritten). `schlusssatz_104` (§ of 2026-09-14, Schlusssatz104.lean)
is about ONE program by hand; this section is the same statement for every source text whose
chain data check.

### 27.1 The pieces

| Piece | File | Generic in |
|---|---|---|
| the pipeline `uebersetzeAllg` (lex, parse, `pre108`, `elabU`, `lowerAllg` onto `declOf u`) | Schlusssatz.lean | the source text |
| T2 proper: `korrOk EL fnum c P fs` (decidable), `korrOk_fnCorr` (every depth), `korrOk_jeder_lauf` (every C run, by `exec_det`), `argsTo_of` (the argument passing of any call), `scorr_assignSlotVia` | KorrespondenzAllg.lean | the declaration, the program, the certificate |
| `EinFadenStart` (A4, one active thread), `einfaden_ziel` (the machine, from `ziel_ort_einfaden_ende` on `E.P.mitRuhe`) | Schlusssatz.lean | the unit `E : Einheit D` |
| `Kette src` (a closed chain), `schlusssatz` | Schlusssatz.lean | the source text |
| `kette_104`, `kette_108` | Kette104.lean, Kette104Satz.lean, Kette108.lean | -- (instances) |
| witnesses, the check seen failing | SchlusssatzZeuge.lean, Kette104Satz.lean, Kette108.lean | -- |

### 27.2 The statement

    theorem schlusssatz {src : String} (K : Kette src)
        (O : Orakel (declOf K.u)) (hH : HardwareAnnahmen O K.E.Q)
        (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional)
        (bin : (declOf K.u).Fn → CSt → List CVal → CSt → Option CVal → Prop)
        (tief : (declOf K.u).Fn → Nat)
        (hA1 : ∀ f st vs st' rv, bin f st vs st' rv →
          CallAt K.EL.lay orc XR (kProg K.zert) (tief f) (fnNr f) st vs st' rv)
        (sp …) (init …) (hA4 : EinFadenStart K.E sp init) :
      uebersetzeAllg src = .ok ⟨K.u, K.E.P, K.fs0⟩ ∧                         -- 1 parse
      (akzeptiert … = true ∧ AkzeptiertSpec … ∧ korrOk … = true) ∧            -- 2 certificates
      NutzerPflicht K.E ∧                                                     -- 3 model judgement
      (∀ passes n f k, … → rufAt … .istFehler = false →                        -- 4 every C run
        (∃ C run) ∧ ∀ C run, RufOut K.EL (rufAt …) st' rv) ∧
      ((∀ passes n, RufRu (rufAt K.E.P O passes n) (rufAt K.E.P.mitRuhe O.mitRuhe passes n)) ∧
       (∀ passes M, reachable from init → SpurInv M ∧ contract legs ∧ StartEndeG ∧ …) ∧
       (∀ passes sp' init', Laufzeit K.E sp' init' → ∀ M, reachable → Ziel …)) ∧ -- 5 machine
      (∀ passes f k, … → ∀ st' rv, bin f st vs st' rv → RufOut …)              -- 6 binary

`Kette src` holds: `u`, `E : Einheit (declOf u)`, `fs0`, `uebersetzt : uebersetzeAllg src = .ok
⟨u, E.P, fs0⟩`, enumerations `fs ls cs`, `akzeptiert` (the checker's Bool, (a)), `nutzer :
NutzerPflicht E` ((b)), `EL : EmitLay (declOf u)`, `zert : KCert (declOf u)`, `zertOk : korrOk EL
fnNr zert E.P fs = true`.

### 27.3 What `korrOk` covers and what makes it `false`

Statements: `assignDurch`, `assignSlot` (row `storeSlot` through any pointer form, or
`storeNamed`), `assignVar` (`setVar`), `call` (`call fc cargs none`, `fc = fnum g`, arguments by
`exOk` and `declOk`, the callee's map = its parameter list), `bind` (`bindLet`, fresh local),
`(void)x;` (`void`), `ret` (`ret cr` by `ergOk`; falling off a `void` body). Expressions: `lit`,
`var`, `weiter`, `slot`/`durch` (`.ld (.slotA base ci n ss off) τc`, base a named table, a map
pointer or a pointer variable, the layout numbers `EL`'s), `ptrOf`. Everything else: `false`.
`korrOk_faellt` (by `decide`): a field offset `1` for `0`, a stored `99` for `100`, `refD`'s
index-fixed map (`ks = [(1, 0)]`), a missing call row -- each refused.

### 27.4 Instances and witnesses

* `kette_104 : Kette src104real` -- the real text with comments, the generic lowering, no
  declared start; user logic `ein4_R` (the argument of `gP_einzahlen_R` over `declOf uExp104`)
  and `lies4_V`; `zert104` pasted from `gabbro corr-lean` (third section). Witness
  `kette_104_zeuge` = `schlusssatz_zeuge`: `einzahlen(k, 0, 7)` from the zero state, through the
  generic theorem, the slot `0 -> 100` in Gabbro and in EVERY C run.
* `kette_108 : Kette src108` -- two declared concurrent starts, accepted; `zert108` pasted (the
  named-table loads). Witnesses `kette_108_zeuge` (`read_a()` returns `42` in Gabbro and in
  EVERY C run) and `kette_108_nebenlaeufig` (the declared concurrent start meets (d); part 5's
  `Ziel` holds at its machine).
* `korrOk_zeuge` (the check holds and its C run moves memory), `einfaden_ziel_zeuge` (the
  premises of `einfaden_ziel` hold jointly with thread 0 running `einzahlen`, a lock-holding
  writer the runtime premise (d) would refuse as a start).

### 27.5 Axiom record

`korrOk_fnCorr`, `korrOk_jeder_lauf`, `exOk_sound`, `stOk_sound`, `enOk_sound`, `argsTo_of`,
`einfaden_ziel`, `schlusssatz`, `kette_104`, `kette_108`, `kette_104_zeuge`, `kette_108_zeuge`,
`kette_108_nebenlaeufig`, `korrOk_zeuge`, `einfaden_ziel_zeuge`, `schlusssatz_zeuge`: `propext`,
`Classical.choice`, `Quot.sound`; `ptrOk_sound`, `korrOk_faellt`: `propext`, `Quot.sound`. No
`sorry`, no `native_decide`, no new `axiom`. `lake build` on `ki-pc-fisch-101`
(`~/gabbro-opus-tv/`): 236 jobs, green.

### 27.6 The counter

`instrumente/zaehle-kette.py` counts a chain as closed only for a program with a Lean-checked
instance of `schlusssatz`: a `CHAIN-INSTANCE <program> <name>` marker, `def <name> : Kette <src>`
with `<src>` byte-identical to the file, the instance's certificate text-identical to the
printer's `KCert`, an application `schlusssatz <name>`, and with `--lean` a green `lake build`
plus sieve (a) (the pipeline evaluated in Lean over every program) and (d). Measured on
`ki-pc-fisch-101`: **CHAIN COUNT 2 of 111** (104, 108; before: 1 of 101). On the way, the C-form
census read 104's `(void)lies(k, i);` as a call inside an expression; repaired in
`pruefe-cformen.py` (PLAN §6.3).

### 27.7 What remains

Sieve (a) (T3) is binding: 20 corpus programs stop at the Lean parser, 89 at the elaborator
(PLAN §6.3). `korrOk`'s missing forms are one arm each over existing T4 lemmas. Part 4 is
conditional on the Gabbro call ending without a model error; A2 and the non-Lean parts of
A1/A3/A4 stay outside; the adequacy chain and stage (b) are untouched (PLAN §6.5).

## 28. `korrOk` widened to its own lemma stock — 23 arms, chain count unchanged (2026-09-15)

*Files: `grammatik/Grammatik/KorrespondenzAllg.lean` (the check and its soundness),
`grammatik/Grammatik/KorrespondenzWeitZeuge.lean` (new: the fixture, the probes, the witness).
Report: `messung/muse/OPUS-BERICHT-KORROK.md`. Plan: PLAN-UEBERSETZUNGSVALIDIERUNG §6.2, §6.5.*

### 28.1 The finding

**The correspondence check was narrower than the stock of lemmas already proved for it.**
`ecorr_add` … `ecorr_shr`, `ecorr_lt` … `ecorr_eq`, `ecorr_nicht`, `ecorr_und`, `ecorr_oder`,
`ecorr_wahr`, `ecorr_falsch`, `ecorr_glob`, `scorr_assignGlob` and the four `Zucker` compound
assignments all stood in `CFormenI.lean`/`CFormenM.lean`, and all fell through `exOk`'s and
`stOk`'s `_ => false`. Nothing in the model was missing; the arms were.

### 28.2 What moved inside

**21 expression arms** (`wahr`, `falsch`, `glob` plain, `add`, `sub`, `mul`, `div`, `rem`,
`sdiv`, `srem`, `band`, `bor`, `bxor`, `shl`, `shr`, `lt`, `le`, `eq`, `und`, `oder`, `nicht`)
= 23 accepted C node shapes, because `lt` also accepts `.cmp .gt` with the operands swapped and
`le` also `.cmp .ge`. **2 statement arms**: `assignGlob` against `GRow.storeGlob`, and
`assignVar` against the additional row `GRow.setOp` (the compound assignments — the same C
statement, `growRow (.setOp x τc op t ce) = .set x τc (.bin op t (.var x) ce)`).

Coverage: `exOk` 6 → **27 of the 42 `Expr` constructors**; `stOk` 4 → **5 of the 27 `Stmt`
constructors**.

**The ONE new lemma is `ecorr_geSwap`** — `ExprCorr (.cmp .ge t ca cb) (.le b a)`, i.e. the C
operator `>=` for the way Gabbro spells `a >= b` (`Zucker.ge a b = le b a`). It is `ecorr_cmp`
with its operator fact (`fun _ _ => rfl`). No new model reasoning.

**The side conditions are DECIDED, not assumed**: `randOk t l1 h1 l2 h2` (the C computation type
holds BOTH operand ranges — the signed/unsigned pitfall `-1 < 1u` as a sieve), the result-range
condition `M104` at `+ - *` and `<<`, and `sgnMin_sound` at `sdiv`/`srem` (unsigned type, or the
dividend's range starts above the type's minimum — which excludes `INT_MIN / -1`, C11 6.5.5p6).

### 28.3 Seen failing

`KorrespondenzWeitZeuge.lean`: a fixture `wD` (one table of four `u32` slots; a plain global `G`
and an `_Atomic` `A` at adjacent block numbers; the exporter's map), and for **every** new arm a
positive probe beside a PLANTED DEFECT — a computation type too narrow for the result, the wrong
C operator, a `>`/`>=` without the operand swap (the opposite comparison), `INT_MIN / -1` not
excluded, the wrong local, the wrong global block, the wrong cell type, an `_Atomic` global taken
for a plain one. 14 probe theorems, all `decide`.

**Witness** `ecorr_geSwap_zeuge`: the new lemma instantiated through `exOk_sound` on a C state
whose two locals differ, at BOTH answers — `b >= a` gives `1` at `(5, 9)` and `0` at `(9, 5)`.

### 28.4 Axiom record

`exOk_sound`, `stOk_sound`, `enOk_sound`, `argsTo_of`, `korrOk_fnCorr`, `korrOk_jeder_lauf`,
`ecorr_geSwap`, `ecorr_geSwap_zeuge`: `propext`, `Classical.choice`, `Quot.sound`;
`ptrOk_sound` and the 14 probes: `propext`, `Quot.sound`. No `sorry`, no `native_decide`, no new
`axiom`.

### 28.5 The chain count did NOT move

**2, before and after.** Sieve (a) — the Lean parser and elaborator — binds: the corpus programs
that stop there never reach a certificate, and the two that do (104, 108) were already checked.
*Arms added and chain count are two numbers and are reported separately.* What `korrOk` still
refuses, each with its reason, is in PLAN §6.5 and in the file's CUTS; the largest item,
`if`/`traverse`, needs a check over `Block` that stays STRUCTURAL (a `decide` must reduce in the
kernel), and the note there says how to build it without a mutual block.

## 29. A2 discharged: a Lean parser for the emitted C subset (2026-09-15)

*Files: `grammatik/Grammatik/CParser/CLexer.lean` (the C lexer), `CParser/CParse.lean`
(`parseC`), `CParser/CProben.lean` (the refusals), `CParser/Bruecke.lean` (`A2`, `kFuns`,
`schlusssatz_text`), `CText104.lean` + `CText104Zeuge.lean`, `CText108.lean`, and the two
theorems added at the end of `Kette104Satz.lean`. Guardian:
`instrumente/pruefe-ctext.py`. Plan: PLAN-UEBERSETZUNGSVALIDIERUNG.md §6.6.*

### 29.1 What was assumed, and what is proved instead

The closing theorem's C side is `kProg K.zert` -- the unit the CORRESPONDENCE CERTIFICATE
elaborates to. That the emitted TEXT means the same thing was assumption **A2**, a hand
transcription nobody checked (§6.4 of the plan, and PLAN §6.3 records the transcription
going stale in spelling once already).

Now, for the two closed chains:

```
a2_104 : parseC ctext104 = some (kFuns zert104)     -- by `rfl`, kernel
a2_108 : parseC ctext108 = some (kFuns zert108)     -- by `rfl`, kernel
```

`ctext104`/`ctext108` are the emitted texts as DATA, pinned line by line, byte-identical to
`gabbro emit` (the guardian re-emits and compares). What stays of A2 is "the C compiler's
front end reads this subset as `parseC` does" -- a part of A1, not an assumption of its own.

### 29.2 The parser, and what it refuses

`parseC : List Char → Option (List CFun)` reads exactly the forms the emitted C of the
closed chains uses: the prelude (four `#include`s and the TWO `_Static_assert` pins, both
REQUIRED), `#define NAME <int>`, the two table `typedef struct`s, `static T T_speicher;`,
`void f(void);` (foreign), `static` declarations and definitions with `__attribute__((word))`;
statements `(void)x;`, `p->slots[i].f = e;`, `T_speicher.slots[i].f = e;`, `f(args);`,
`(void)f(args);`, `return;`, `return e;`; expressions: literals, locals, slot reads.
Everything else is `none` -- `CProben.lean` probes seven refusals (`if`, arithmetic, `let`,
volatile, a missing pin, a declared-but-undefined function). The table geometry (`2 4 0`)
is COMPUTED from the declarations through `natLay`, not transcribed, and the C function
numbers, the C locals and the table block numbers come from the order the text declares
them.

### 29.3 The theorem with A2 discharged

`schlusssatz_text` (Bruecke.lean) is `schlusssatz` with ONE premise different: `hA1` speaks
about `cProgC s`, the C unit of the emitted TEXT, instead of `kProg K.zert`. Its conclusion
is written out, so a change to `schlusssatz` breaks the build instead of silently promising
the old thing. Per program: `kette_104_binaer_text` and `kette_108_binaer_text` (part 6 of
the closing theorem, the binary's runs), and the witnesses `kette_104_zeuge_text` (the slot
`0 -> 100` in Gabbro and in EVERY C run of the emitted text) and `kette_108_zeuge_text`
(`read_a()` returns `42` both ways).

### 29.4 Negative witnesses

`a2_104_gegenprobe_programm`/`_korr`/`_keine` and `a2_108_gegenprobe`: with ONE line of the
emitted text changed, `parseC` answers with a DIFFERENT program -- the stored value `99`,
the slot count `3` (the geometry is read, not remembered), 108's index `2` -- and `korrOk`
then REFUSES that program against the parsed Gabbro program; or it answers `none` (a
deleted `_Static_assert` pin, an undeclared field, a deleted table object).

### 29.5 Axiom record

`a2_104`, `cprog_104`, `a2_108`, `cprog_108`, `kProg_kFuns`, `a2_kProg`, `a2_hA1`,
`schlusssatz_text`, `kette_104_binaer_text`, `kette_104_zeuge_text`, `kette_108_binaer_text`,
`kette_108_zeuge_text`, the `gegenprobe` theorems and the `CProben` refusals: `propext`,
`Classical.choice`, `Quot.sound` (`kProg_kFuns`, `a2_104_gegenprobe_korr`: `propext`,
`Quot.sound`). No `sorry`, no `native_decide`, no new `axiom`. `lake build` on
`ki-pc-fisch-101`: 247 jobs, green, peak 2,9 GB.

### 29.6 The cost, measured -- and O13

Kernel-reducing a parse of 1419 bytes cost **44,6 GB** at first, and the reason was not the
parser: in Lean 4.33 `String.toList` goes through the array representation, and forcing the
FIRST character of one 1419-byte string literal costs **33,7 GB / 217 s**. Splitting the
literal into 45 short ones joined by `++` does not help (`String.append` goes through the
array too); the SAME text as a `List Char` built from 45 short `"…".toList` pieces costs
**3,3 GB**. A second pathology: a MUTUAL recursion through a fuel argument compiles to a
mutual `Nat.brecOn`, and reducing that is exponential in the fuel -- one seven-token probe
grew to 112 GB before it was killed. Both are avoided by construction now (the pins are
lists of lines; the expression parser has no recursion), and `dokumente/OFFEN.md` O13 has
the measurement, because the same `String.toList` stands in the Gabbro-side pins that cost
72 GB.

(End of file — §11 added 2026-09-13, lane 133; §12 added 2026-09-13; §13 added 2026-09-13; §14 added 2026-09-13; §15 added 2026-09-13; §16 added 2026-09-14; §17 added 2026-09-14 (floats); §18 added 2026-09-14 (budget, start reasons); §19 added 2026-09-14 (reason-return invariants, progress); §20 added 2026-09-14 (gabbro_ziel proved, e0 removed); §21 added 2026-09-15 (waiting bound); §22 added 2026-09-15 (GabbroZiel repaired: one program, owned start, payloads); §23 added 2026-09-15 (fourth round: floats as logic, no wait cycle, stops by kind); §24 added 2026-09-15 (G1: every type decoded, the non-return stop); §25 added 2026-09-15 (W1: empty answer types refused, `nieZurueck` is `never`); §26 added 2026-09-15 (stage (b): the concurrent closing theorem for 124); §27 added 2026-09-15 (the generic closing theorem `schlusssatz`, chain count 2); §28 added 2026-09-15 (`korrOk` widened to its own lemma stock, 23 arms, chain count unchanged); §29 added 2026-09-15 (A2 discharged: the emitted C text parsed in Lean); §§1-10 history above.)

