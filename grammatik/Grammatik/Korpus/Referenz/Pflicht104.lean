/-
  The exported 104 program's functional and start duties are proved here.
  Its original old-memory postcondition remains a real, nontrivial obligation:
  the actual deposit moves a slot from 0 to 100, while lowering it would break
  the postcondition. All of these program-logic proofs are retained.

  The strict checker currently refuses this correct program: outside the
  decidable fragment: old-memory postconditions (`oldS`). The proved user
  duty does not replace that gate. `oblig_korrekt_abgelehnt` records both
  the semantic duty and the actual refusal; no checked goal corollary is
  claimed for this unchanged export.
-/
module
public import Grammatik.Korpus.Programme.GenOblig104
public import Grammatik.Kern.Semantik.Evaluation.Durchgaenge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrund
public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik

open G104_referenz_oblig (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies gD gP gFs gLs gCs gS gSp0 gE)

/-! ## 1. The `KoerperGutZ` proofs -/

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
  | why σ' r => exact (Fin.cast hr r).elim0
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
    · simp only [execStmt, List.append_assoc, Int.reduceSub, reduceCtorEq] at h1
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
      show decide ((σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.there .here)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := G104_referenz_oblig.gD) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : G104_referenz_oblig.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp only [execStmt, List.append_assoc, Int.reduceSub, reduceCtorEq] at h1
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

/-- The exported targets require true; their pointer interfaces retain the actual defaults. -/
theorem oblig_ptr_verfeinert : PtrVerfeinert G104_referenz_oblig.gP :=
  ptrVerfeinert_trivial (fun f _ _ => by cases f <;> rfl) (fun _ => rfl)

/-- **THE BODIES' LOGIC**, all conjuncts together. -/
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
    that `gabbro obligations --g beispiele/0104-referenz.gab` states, with no
    hypothesis of any kind. -/
theorem oblig_nutzer : Zielsatz.NutzerPflicht G104_referenz_oblig.gE where
  logik := oblig_logik
  start := ⟨oblig_start_sperren, oblig_start_req⟩

/-- **THE USER'S DUTY WITH THE ATOMIC RELY** (the goal's (b) since Opus lane O25c): `gD` has no
    global, so no read of a shared atomic exists and the duty of before is it
    (`nutzerPflichtA_ohne_atomar`). -/
theorem oblig_nutzerA : Zielsatz.NutzerPflichtA G104_referenz_oblig.gE :=
  Zielsatz.nutzerPflichtA_ohne_atomar (fun g => nomatch g) oblig_nutzer

/-- The stated `def` and the proved theorem are the same proposition -- the
    tool's word and the user's proof, held against each other. -/
theorem oblig_nutzer_ist_stated : G104_referenz_oblig.nutzerPflicht := oblig_nutzerA

/-! ## 4. Runtime data and the strict checker refusal -/

/-- The oracle of `gD`: no axiom, register or global exists. -/
def oO : Orakel G104_referenz_oblig.gD where
  wirktL := fun a => nomatch a
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

/-- The empty oracle meets the oracle clauses of the named hardware assumption;
    the native CPU contract is supplied explicitly. -/
theorem oblig_hw [RootNativeFloat.Hardware] : Zielsatz.HardwareAnnahmen oO G104_referenz_oblig.gE.Q :=
  ⟨(fun a => nomatch a), ⟨(fun r => nomatch r), (fun g => nomatch g)⟩,
    axVertragO_wahr oO, inferInstance⟩

/-- **THE NAMED RUNTIME ASSUMPTION (A4), discharged for the runtime's own
    start**: the loader establishes `gE.sp0`, and every thread runs the idle
    root -- 104 declares no start, so that IS the runtime's exact start. -/
theorem oblig_laufzeit :
    Zielsatz.Laufzeit G104_referenz_oblig.gE (speicherR G104_referenz_oblig.gE.sp0)
      (initRuhe G104_referenz_oblig.gE.starts) :=
  laufzeit_initRuhe G104_referenz_oblig.gE

/-- Capability gap: outside the decidable fragment: old-memory postconditions.
    The program's actual semantic duty is proved, while the checker refuses it. -/
theorem oblig_korrekt_abgelehnt :
    Zielsatz.NutzerPflichtA G104_referenz_oblig.gE ∧
    Zielsatz.akzeptiertX_pruefer.akzeptiert G104_referenz_oblig.gE
      G104_referenz_oblig.gFs G104_referenz_oblig.gLs G104_referenz_oblig.gCs = false :=
  ⟨oblig_nutzerA, G104_referenz_oblig.gCheck⟩

/-! ## 5. Witnesses (rule 13) -/

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def rho7 : Env G104_referenz_oblig.gD (G104_referenz_oblig.gD.params g_einzahlen) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

/-- **THE EXPORTED PROGRAM IS NOT TRIVIAL**: `einzahlen(k, 0, 7)` from the
    DECLARED initial memory ends `ok` and moves the slot `0 -> 100`. Without
    this the duties above would be duties over a program that does nothing.
    (The declared runtime is idle because 104 declares no start;
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
#print axioms Gabbro.Grammatik.oblig_korrekt_abgelehnt
#print axioms Gabbro.Grammatik.oblig_ruf_bewegt
#print axioms Gabbro.Grammatik.oblig_ens_faellt

end Gabbro.Grammatik
