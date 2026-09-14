/-
  File:      Grammatik/Pflicht104.lean
  Subject:   THE USER'S HALF for `beispiele/104-referenz.gab`, proved once.

  `GenOblig104.lean` is what `gabbro obligations --g` states over the
  program: per function the `KoerperGutS` duty (`<fn>_pflicht`) and the
  `InvGutS` duty (`<fn>_invPflicht`), the lock invariants at the start
  memory (`startPflicht`), and the closing theorem `gP_ziel` from them.
  This file is the person's half: the duties hold (the `KoerperGutS`
  proofs follow `Schlusssatz104.lean` §4 -- the bodies hold no `locks`,
  so `koerperGutS_ohne` carries the `KoerperGutZ` proofs to the exported
  family `gS`; the declaration owes no table invariant, so `invGutS_leer`
  closes the rest), and the chain "tool states -> user proves -> theorem
  follows" is shown once (`oblig_chain`).

  What is NOT shown: no G theorem applies to a machine of `gP` alone.
  Every function of `gD` holds `M` by signature, so no start assignment
  is exclusive (`Schlusssatz104.lean`: `gP_kein_exklusiv`, proved there);
  `oblig_chain` therefore keeps `StartExklusiv` as a hypothesis. The
  runtime supplies the idle root (`Schlusssatz104.lean` §5: `gPB_ziel`).
-/
import Grammatik.GenOblig104
import Grammatik.Durchgaenge
import Grammatik.ZielOrtGanz
import Grammatik.ZielOrtRahmenBeweis
import Grammatik.ZielOrtRahmenSem
import Grammatik.SperreFuss
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtStart
import Grammatik.RufAdaequatG
import Grammatik.ZielOrtVollZeuge

namespace Gabbro.Grammatik

open G104_referenz_oblig (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies gD gP gFs gS pflicht pflichtInv startPflicht gP_ziel)

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

/-! ## 2. The stated duties hold, at every budget -/

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

/-- **THE STATED `KoerperGutS` DUTIES HOLD**, per function, at every
    budget. -/
theorem oblig_koerper : ∀ f : G104_referenz_oblig.gD.Fn, pflicht f := by
  intro f
  cases f
  · show ∀ passes, KoerperGutS G104_referenz_oblig.gP passes
      (axWahr G104_referenz_oblig.gD) G104_referenz_oblig.gS g_einzahlen
    exact fun passes =>
      koerperGutS_alle oblig_voll oblig_ohneEwig oblig_koerper_0 passes g_einzahlen
  · show ∀ passes, KoerperGutS G104_referenz_oblig.gP passes
      (axWahr G104_referenz_oblig.gD) G104_referenz_oblig.gS g_lies
    exact fun passes =>
      koerperGutS_alle oblig_voll oblig_ohneEwig oblig_koerper_0 passes g_lies

/-- The `InvGutS` duties at budget `0`: the declaration owes no table
    invariant. -/
theorem oblig_inv_0 : ∀ f : G104_referenz_oblig.gD.Fn,
    InvGutS G104_referenz_oblig.gP 0 (axWahr G104_referenz_oblig.gD)
      G104_referenz_oblig.gS f :=
  fun f => invGutS_leer (D := G104_referenz_oblig.gD) rfl f

/-- **THE STATED `InvGutS` DUTIES HOLD**, per function, at every budget. -/
theorem oblig_inv : ∀ f : G104_referenz_oblig.gD.Fn, pflichtInv f := by
  intro f
  cases f
  · show ∀ passes, InvGutS G104_referenz_oblig.gP passes
      (axWahr G104_referenz_oblig.gD) G104_referenz_oblig.gS g_einzahlen
    exact fun passes =>
      invGutS_alle oblig_voll oblig_ohneEwig oblig_inv_0 passes g_einzahlen
  · show ∀ passes, InvGutS G104_referenz_oblig.gP passes
      (axWahr G104_referenz_oblig.gD) G104_referenz_oblig.gS g_lies
    exact fun passes =>
      invGutS_alle oblig_voll oblig_ohneEwig oblig_inv_0 passes g_lies

/-- **THE STATED BOOT DUTY HOLDS** at every start memory: the exported
    family answers `true` everywhere. -/
theorem oblig_start : ∀ sp : Speicher G104_referenz_oblig.gD, startPflicht sp := by
  intro sp L
  cases L
  rfl

/-- The exported family is well-formed: its one protected carrier is
    guarded by its lock, and its invariant reads nothing. -/
theorem oblig_hS : SperrInvOk G104_referenz_oblig.gS := by
  refine ⟨fun L c hc => ?_, fun L s s' _ => by cases L <;> rfl⟩
  cases L
  rw [List.mem_singleton.mp hc]
  exact List.mem_singleton.mpr rfl

/-! ## 3. The chain, shown once -/

/-- The oracle of `gD`: no axiom, register or global exists. -/
def oO : Orakel G104_referenz_oblig.gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem oO_gut : GutO oO := fun a => nomatch a

theorem oO_lokal : RegLokal oO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- The zero memory of `gD`: the slot `0`, no globals. -/
def sp0 : Speicher G104_referenz_oblig.gD :=
  ⟨fun t _ f => (match t, f with | .Konto, .stand => ⟨0, by decide, by decide⟩),
    (fun g => nomatch g)⟩

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def rho0 : Env G104_referenz_oblig.gD (G104_referenz_oblig.gD.params g_einzahlen) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

/-- Every thread starts `einzahlen` on those arguments (the `requires` is
    `.wahr`, so the start contracts hold anywhere). -/
def init0 : Faden → Σ f : G104_referenz_oblig.gD.Fn,
    Env G104_referenz_oblig.gD (G104_referenz_oblig.gD.params f) :=
  fun _ => ⟨g_einzahlen, rho0⟩

theorem start0 : StartGut G104_referenz_oblig.gP sp0 init0 := by
  intro t
  rfl

/-- No start function declares a reason (`einzahlen` has none). -/
theorem oblig_ohneGrund : StartOhneGrund init0 := by
  intro t
  rfl

/-- The declaration has a lock: a trace event exists. -/
def e0104 : Ereignis G104_referenz_oblig.gD := .nimmt GLock.M []

/-- **THE CHAIN, SHOWN ONCE**: with the stated duties proved above, the
    flagship's conclusion follows at every budget for every reachable
    machine -- up to the start-configuration fact no program of `gP` alone
    can supply (every function holds `M` by signature; see
    `gP_kein_exklusiv` in `Schlusssatz104.lean`). -/
theorem oblig_chain (passes : Nat) (M : RufMaschineG G104_referenz_oblig.gD)
    (hr : RufErreichbarG G104_referenz_oblig.gP oO passes
      (RufStartG G104_referenz_oblig.gP sp0 init0) M)
    (hex : StartExklusiv init0) :
    ((VertragAmOrtG G104_referenz_oblig.gP M ∧ SperrInvG G104_referenz_oblig.gS M ∧
      KeinLogikHaltG oO passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG G104_referenz_oblig.gP oO passes M t M') ∧
    InvAmOrtG G104_referenz_oblig.gP M) ∧ StartEndeG G104_referenz_oblig.gP M ∧
    KeinStartGrundG M :=
  gP_ziel oO sp0 init0 e0104 oO_gut oO_lokal (axVertragO_wahr oO) oblig_koerper oblig_inv
    start0 (oblig_start sp0) hex oblig_hS oblig_ohneGrund passes M hr

#print axioms Gabbro.Grammatik.oblig_koerper
#print axioms Gabbro.Grammatik.oblig_inv
#print axioms Gabbro.Grammatik.oblig_chain

end Gabbro.Grammatik
