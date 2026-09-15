/-
  File:      Grammatik/Pflicht104.lean
  Subject:   THE USER'S HALF for `beispiele/104-referenz.gab`, proved once,
             over the EXPORTED UNIT.

  `GenOblig104.lean` is what `gabbro obligations --g` states over the
  program: the unit `gE : Zielsatz.Einheit gD` (bodies, contracts, the lock
  invariant family `gS`, the axiom `ensures`, the declared starts, the
  declared initial memory `gSp0`), the stated duty `nutzerPflicht :=
  Zielsatz.NutzerPflicht gE`, the decided member lists and checker premise,
  and the closing theorem `gP_gabbro` -- the goal theorem `gabbro_ziel`
  applied to this program, with the user's duty as its one open hypothesis.

  This file is the person's half: `oblig_nutzer : Zielsatz.NutzerPflicht gE`,
  COMPLETE -- every conjunct of `LogikPflicht` at EVERY budget and both
  conjuncts of `StartPflicht`, with nothing assumed. `oblig_ziel` then closes
  the chain "tool states -> user proves -> `Ziel` holds" on a concrete run,
  with only the named hardware assumption (`HardwareAnnahmen`, discharged
  here for the empty oracle) and the runtime assumption A4
  (`Zielsatz.Laufzeit`, discharged here by `laufzeit_initRuhe`) beside it.

  MIGRATED 2026-09-15 (from the pre-`Einheit` obligation form). Until then
  this file opened `pflicht`/`pflichtInv`/`startPflicht`/`gP_ziel`, which the
  exporter no longer writes; §1 and §2 port unchanged (the exported bodies,
  contracts and `gS` did not move), §3 is new -- the old `oblig_chain` kept
  `StartExklusiv` as a hypothesis and reached a hand-assembled conclusion,
  where `gP_gabbro` needs no start-configuration hypothesis at all: the goal
  theorem derives exclusivity from the DECLARED starts (here: none, 104
  declares no `concurrent` and no `entry`).

  What is NOT claimed: `gE.starts = []` -- 104 declares no thread start --
  so `Zielsatz.Laufzeit gE sp init` admits only assignments in which every
  thread runs the runtime's idle root. The theorem below is therefore TRUE
  AND ITS MACHINE IS IDLE. That is what the SOURCE declares, not a weakness
  of the duty: the concurrent instance of the same chain is `Pflicht108.lean`
  (`beispiele/108-disjoint-start-locks.gab`, two declared starts). That the
  program itself is not trivial is witnessed here by `oblig_ruf_bewegt`
  (a call of `einzahlen` moves the slot `0 -> 100`).
-/
import Grammatik.GenOblig104
import Grammatik.Durchgaenge
import Grammatik.ZielOrtGanz
import Grammatik.ZielOrtRahmenBeweis
import Grammatik.ZielOrtRahmenSem
import Grammatik.SperreFuss
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtInvGrund
import Grammatik.ZielOrtStart
import Grammatik.RufAdaequatG
import Grammatik.ZielOrtVollZeuge

namespace Gabbro.Grammatik

open G104_referenz_oblig (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies gD gP gFs gLs gCs gS gSp0 gE gP_gabbro)

/-! ## 1. The `KoerperGutZ` proofs (after `Schlusssatz104.lean` §4) -/

/-- A call of a `requires true` function through the gate never fails the
    gate when the handler blames nobody (over `gD`). -/
theorem oblig_call_tor {V : Vertrag G104_referenz_oblig.gD} {l : Bool} {Γ : Ctx}
    {Λ : List (Res G104_referenz_oblig.gD)} (O : Orakel G104_referenz_oblig.gD) (passes : Nat)
    (R : ∀ f : G104_referenz_oblig.gD.Fn, World G104_referenz_oblig.gD → Env G104_referenz_oblig.gD
      (G104_referenz_oblig.gD.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : G104_referenz_oblig.gD.Fn) (args : Args G104_referenz_oblig.gD Γ Λ (G104_referenz_oblig.gD.params g))
    (hp : RufPasst G104_referenz_oblig.gD V (G104_referenz_oblig.gD.signatur g) Λ)
    (hr : G104_referenz_oblig.gD.gruende g = 0) (σ : World G104_referenz_oblig.gD)
    (ρ : Env G104_referenz_oblig.gD Γ) (g' : G104_referenz_oblig.gD.Fn) :
    execStmt O passes (torRuf G104_referenz_oblig.gP R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf G104_referenz_oblig.gP R g σ1 ρ1 = R g σ1 ρ1 :=
    fun _ _ => if_pos (by cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | grund σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

/-- `lies` meets its obligation: the returned value is the slot. -/
theorem oblig_koerper_lies : KoerperGutV G104_referenz_oblig.gP 0 g_lies := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz_oblig.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : G104_referenz_oblig.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun

/-- **`einzahlen` meets the obligation against declared frames**: the write
    sets the slot to `100`, `lies` declares no write (every
    frame-respecting answer keeps the slots), so `old(stand) <= stand` is
    `old(stand) <= 100`, true by the range. -/
theorem oblig_einzahlen_R : KoerperGutR G104_referenz_oblig.gP 0 g_einzahlen := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz_oblig.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 g_lies _ _ σ2 w hRv).1.1 GTab.Konto rfl
      simp only [execStmt] at h1
      cases h1
      show decide ((σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.dort .hier)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := G104_referenz_oblig.gD) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : G104_referenz_oblig.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact oblig_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem oblig_voll : ∀ g : G104_referenz_oblig.gD.Fn, g ∈ G104_referenz_oblig.gFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem oblig_logikFrei :
    programmLogikFrei G104_referenz_oblig.gP G104_referenz_oblig.gFs = true := by decide

/-! ## 2. The `LogikPflicht` conjuncts, at every budget -/

/-- Neither body holds a `locks` block, so neither owes the new semantics
    anything beyond the old obligation (at budget `0`, lifted below). -/
theorem oblig_ohne_einzahlen :
    (G104_referenz_oblig.gP.rumpf g_einzahlen).ohneLocks = true := by decide

theorem oblig_ohne_lies :
    (G104_referenz_oblig.gP.rumpf g_lies).ohneLocks = true := by decide

/-- The `KoerperGutS` duties at budget `0`, per function. -/
theorem oblig_koerper_0 : ∀ f : G104_referenz_oblig.gD.Fn,
    KoerperGutS G104_referenz_oblig.gP 0 (axWahr G104_referenz_oblig.gD)
      G104_referenz_oblig.gS f := by
  intro f
  cases f
  · exact koerperGutS_ohne G104_referenz_oblig.gS oblig_ohne_einzahlen
      ⟨koerperGutRQ_of_R _ oblig_einzahlen_R,
        programmLogikFrei_ok oblig_voll oblig_logikFrei 0 _ _⟩
  · exact koerperGutS_ohne G104_referenz_oblig.gS oblig_ohne_lies
      ⟨koerperGutRQ_of_R _ (koerperGutR_of_V oblig_koerper_lies),
        programmLogikFrei_ok oblig_voll oblig_logikFrei 0 _ _⟩

/-- No body contains a `forever` loop, so the budget-`0` duty is the duty
    at every budget (`Durchgaenge.lean`). -/
theorem oblig_ohneEwig :
    ohneEwigB G104_referenz_oblig.gP G104_referenz_oblig.gFs = true := by decide

/-- **CONJUNCT 1 of `LogikPflicht`, first component**: the body triple holds
    per function at EVERY budget. -/
theorem oblig_koerper : ∀ (passes : Nat) (f : G104_referenz_oblig.gD.Fn),
    KoerperGutS G104_referenz_oblig.gP passes (axWahr G104_referenz_oblig.gD)
      G104_referenz_oblig.gS f :=
  koerperGutS_alle oblig_voll oblig_ohneEwig oblig_koerper_0

/-- **CONJUNCT 1, second component**: the owed table invariants at a value
    exit. The declaration owes none (`gD.invs = []`). -/
theorem oblig_inv : ∀ (passes : Nat) (f : G104_referenz_oblig.gD.Fn),
    InvGutS G104_referenz_oblig.gP passes (axWahr G104_referenz_oblig.gD)
      G104_referenz_oblig.gS f :=
  fun _ f => invGutS_leer rfl f

/-- **CONJUNCT 1, third component**: the owed table invariants at a REASON
    exit. Neither function declares a reason, so there is no such exit. -/
theorem oblig_invGrund : ∀ (passes : Nat) (f : G104_referenz_oblig.gD.Fn),
    Zielsatz.InvGutGrund G104_referenz_oblig.gP passes (axWahr G104_referenz_oblig.gD)
      G104_referenz_oblig.gS f :=
  fun _ f => invGutGrund_ohneGrund (by cases f <;> rfl)

/-- **CONJUNCT 2 of `LogikPflicht`**: the exported lock invariant reads
    nothing, so it reads only its protected carriers. -/
theorem oblig_S_lokal : Zielsatz.SperrInvLokal G104_referenz_oblig.gS :=
  fun L _ _ _ => by cases L; rfl

/-- **CONJUNCT 3 of `LogikPflicht`**: the exported axiom `ensures` (`gD` has
    no axiom; the exporter writes the constantly true family) reads only the
    carriers the axiom declares. -/
theorem oblig_ax_lokal : AxEnsLokal (axWahr G104_referenz_oblig.gD) := axEnsLokal_wahr

/-- **THE BODIES' LOGIC**, all three conjuncts together. -/
theorem oblig_logik : Zielsatz.LogikPflicht G104_referenz_oblig.gE.P
    G104_referenz_oblig.gE.S G104_referenz_oblig.gE.Q :=
  ⟨fun passes f => ⟨oblig_koerper passes f, oblig_inv passes f, oblig_invGrund passes f⟩,
    oblig_S_lokal, oblig_ax_lokal⟩

/-! ## 3. The start obligation, and the whole duty -/

/-- **`StartPflicht.sperren`**: the exported family answers `true` at the
    DECLARED initial memory (it answers `true` everywhere). -/
theorem oblig_start_sperren : ∀ L, G104_referenz_oblig.gE.S.inv L G104_referenz_oblig.gE.sp0 = true :=
  fun L => by cases L; rfl

/-- **`StartPflicht.req`**: 104 declares no thread start (`gE.starts = []`),
    so there is no start `requires` to meet. VACUOUS, and said so: the
    non-vacuous instance of this conjunct is `Pflicht108.lean`. -/
theorem oblig_start_req : ∀ a ∈ G104_referenz_oblig.gE.starts,
    ReqAmEintritt G104_referenz_oblig.gE.P a.1 (G104_referenz_oblig.gE.sp0.welt []) a.2 :=
  fun _ ha => absurd ha List.not_mem_nil

/-- **THE USER'S DUTY ON 104, PROVED** -- exactly the `def nutzerPflicht`
    that `gabbro obligations --g beispiele/104-referenz.gab` states, with no
    hypothesis of any kind. -/
theorem oblig_nutzer : Zielsatz.NutzerPflicht G104_referenz_oblig.gE where
  logik := oblig_logik
  start := ⟨oblig_start_sperren, oblig_start_req⟩

/-- The stated `def` and the proved theorem are the same proposition -- the
    tool's word and the user's proof, held against each other. -/
theorem oblig_nutzer_ist_stated : G104_referenz_oblig.nutzerPflicht := oblig_nutzer

/-! ## 4. The chain, closed -/

/-- The oracle of `gD`: no axiom, register or global exists. -/
def oO : Orakel G104_referenz_oblig.gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- **THE NAMED HARDWARE ASSUMPTION, discharged on this declaration**: `gD`
    has no axiom, no register and no global, so every oracle -- this one
    included -- meets it. -/
theorem oblig_hw : Zielsatz.HardwareAnnahmen oO G104_referenz_oblig.gE.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g)) (axVertragO_wahr oO))

/-- **THE NAMED RUNTIME ASSUMPTION (A4), discharged for the runtime's own
    start**: the loader establishes `gE.sp0`, and every thread runs the idle
    root -- 104 declares no start, so that IS the runtime's exact start. -/
theorem oblig_laufzeit :
    Zielsatz.Laufzeit G104_referenz_oblig.gE (speicherR G104_referenz_oblig.gE.sp0)
      (initRuhe G104_referenz_oblig.gE.starts) :=
  laufzeit_initRuhe G104_referenz_oblig.gE (by decide)

/-- **THE CHAIN, CLOSED ON 104**: what the exporter states, the user proved
    above, and so the goal holds at every reachable machine of the run the
    runtime starts -- with NO open hypothesis. `gP_gabbro` is the exporter's
    own theorem; `oblig_nutzer`, `oblig_hw` and `oblig_laufzeit` are its
    three premises, all three discharged here. -/
theorem oblig_ziel (passes : Nat) (M : RufMaschineG G104_referenz_oblig.gD.mitRuhe)
    (hr : RufErreichbarG G104_referenz_oblig.gE.P.mitRuhe oO.mitRuhe passes
      (RufStartG G104_referenz_oblig.gE.P.mitRuhe (speicherR G104_referenz_oblig.gE.sp0)
        (initRuhe G104_referenz_oblig.gE.starts)) M) :
    Zielsatz.Ziel G104_referenz_oblig.gE.P.mitRuhe G104_referenz_oblig.gE.S.mitRuhe
      oO.mitRuhe passes
      (RufStartG G104_referenz_oblig.gE.P.mitRuhe (speicherR G104_referenz_oblig.gE.sp0)
        (initRuhe G104_referenz_oblig.gE.starts)) M :=
  gP_gabbro oblig_nutzer oO oblig_hw passes _ _ oblig_laufzeit M hr

/-! ## 5. Witnesses (rule 13) -/

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def rho7 : Env G104_referenz_oblig.gD (G104_referenz_oblig.gD.params g_einzahlen) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

/-- **THE EXPORTED PROGRAM IS NOT TRIVIAL**: `einzahlen(k, 0, 7)` from the
    DECLARED initial memory ends `ok` and moves the slot `0 -> 100`. Without
    this the duties above would be duties over a program that does nothing.
    (The machine of `oblig_ziel` is idle only because 104 declares no start;
    the program it would run is this one.) -/
theorem oblig_ruf_bewegt :
    ∃ σ' : World G104_referenz_oblig.gD,
      rufAt G104_referenz_oblig.gE.P oO 0 2 g_einzahlen (G104_referenz_oblig.gE.sp0.welt []) rho7
          = .ok σ' () ∧
        ((G104_referenz_oblig.gE.sp0.welt []).slots GTab.Konto 0 GKontoFeld.stand).n = 0 ∧
        (σ'.slots GTab.Konto 0 GKontoFeld.stand).n = 100 :=
  ⟨_, rfl, rfl, rfl⟩

/-- A memory with the slot at its top value, for the counter-direction
    below. -/
def sp100 : Speicher G104_referenz_oblig.gD :=
  ⟨fun t _ f => match t, f with | .Konto, .stand => ⟨100, by decide, by decide⟩,
    fun g => nomatch g⟩

/-- **THE DUTY IS NOT VACUOUS**: the exported `ensures` of `einzahlen`
    (`old(stand) <= stand`) is a real constraint -- it FAILS on the return
    world that lowers the slot from `100` to `0`. A duty that no world can
    break would say nothing about the body. -/
theorem oblig_ens_faellt :
    ¬ EnsAmRueck G104_referenz_oblig.gE.P g_einzahlen (sp100.welt [])
      (G104_referenz_oblig.gE.sp0.welt []) rho7 () := by
  unfold EnsAmRueck
  decide

#print axioms Gabbro.Grammatik.oblig_logik
#print axioms Gabbro.Grammatik.oblig_nutzer
#print axioms Gabbro.Grammatik.oblig_ziel
#print axioms Gabbro.Grammatik.oblig_ruf_bewegt
#print axioms Gabbro.Grammatik.oblig_ens_faellt

end Gabbro.Grammatik
