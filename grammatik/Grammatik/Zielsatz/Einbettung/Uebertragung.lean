import Grammatik.Zielsatz.Einbettung.Pflicht
import Grammatik.Zielsatz.Kern.Spec

/-!
  File:      Grammatik/Zielsatz/Einbettung/Uebertragung.lean
  Subject:   **A project's proof holds in every program that links it** (stage E3).

  A project `P` over its own declaration `D` has proved its user obligation (`LogikPflichtA P S Q T`:
  every body against every handler, oracle, lock move and atomic environment in the classes over
  `D`). A program `P'` over `D'` links it through an embedding `E : D ↪ D'` that keeps what the
  project declared (`Uebernahme`: the bodies and contracts are the images, the image locks protect
  the images of the carriers under the same invariants, the program's rely is no larger on the
  image, the axiom ensures agree on the image, and an invariant over an image table is an image
  invariant). Then every image function meets the obligation of `P'` -- with nothing re-proved
  (`koerperGutSA_E`, `invGutSA_E`, `invGutGrundA_E`, collected in `logikPflicht_E`).

  The proof runs the image body beside the body (`sim_end`), takes the `D`-handlers the run of
  `D'` induces through the keys (`phiAus`), shows them lawful (`Pflicht.lean`), applies the
  project's obligation to them, and carries the conclusion back to `D'` (`ens_E`, `req_E`).

  What it needs of `D`: no function pointer comes in from outside (`ZeigerfreiD`; callbacks are
  stage E4), and a neutral trace piece (`PadOk`: `D` declares a table, a global or a lock) --
  without one, `D`'s worlds cannot tell two calls of a foreign function apart.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D D' : Deklaration}

/-- An end outcome transported along an equation of its contract. -/
def castEndV {D₀ : Deklaration} {V₁ V₂ : Vertrag D₀} {l : Bool} {Γ : Ctx} (h : V₁ = V₂)
    (o : EndAusgang V₁ l Γ) : EndAusgang V₂ l Γ := h ▸ o

section Um

variable {D₀ : Deklaration} (S : SperrInv D₀) (O : Orakel D₀) (U : Umwelt D₀) (A : AUmwelt D₀)
  (passes : Nat) (R : ∀ f : D₀.Fn, World D₀ → Env D₀ (D₀.params f) → RufAusgang f) {l : Bool}

theorem execEnd_umV {V₁ V₂ : Vertrag D₀} {Γ : Ctx} {Λ : List (Res D₀)} (h : V₁ = V₂)
    (b : Endblock D₀ V₁ l Γ Λ) (σ : World D₀) (ρ : Env D₀ Γ) :
    execEndHA S O U A passes R (Endblock.umV h b) σ ρ = castEndV h (execEndHA S O U A passes R b σ ρ) := by
  subst h; rfl

end Um

theorem castEndV_zurueck {D₀ : Deklaration} {V₁ V₂ : Vertrag D₀} {l : Bool} {Γ : Ctx} (h : V₁ = V₂)
    {o : EndAusgang V₁ l Γ} {σ : World D₀} {v : ErgVal D₀ V₂.erg} (e : castEndV h o = .zurueck σ v) :
    ∃ v₀, o = .zurueck σ v₀ ∧ v = castV (congrArg Vertrag.erg h) v₀ := by
  subst h
  exact ⟨v, e, rfl⟩

theorem castEndV_why {D₀ : Deklaration} {V₁ V₂ : Vertrag D₀} {l : Bool} {Γ : Ctx} (h : V₁ = V₂)
    {o : EndAusgang V₁ l Γ} {σ : World D₀} {r : Fin V₂.gruende} (e : castEndV h o = .why σ r) :
    ∃ r₀ : Fin V₁.gruende, o = .why σ r₀ ∧ r.val = r₀.val := by
  subst h
  exact ⟨r, e, rfl⟩

theorem castEndV_logik {D₀ : Deklaration} {V₁ V₂ : Vertrag D₀} {l : Bool} {Γ : Ctx} (h : V₁ = V₂)
    {o : EndAusgang V₁ l Γ} {e : Logik D₀} (h' : castEndV h o = .logik e) : o = .logik e := by
  subst h
  exact h'

theorem castEnd_zurueck {D₀ : Deklaration} {V : Vertrag D₀} {l : Bool} {Γ Γ' : Ctx} (h : Γ = Γ')
    {o : EndAusgang V l Γ} {σ : World D₀} {v : ErgVal D₀ V.erg} (e : castEnd h o = .zurueck σ v) :
    o = .zurueck σ v := by
  subst h; exact e

theorem castEnd_why {D₀ : Deklaration} {V : Vertrag D₀} {l : Bool} {Γ Γ' : Ctx} (h : Γ = Γ')
    {o : EndAusgang V l Γ} {σ : World D₀} {r : Fin V.gruende} (e : castEnd h o = .why σ r) :
    o = .why σ r := by
  subst h; exact e

theorem castEnd_logik {D₀ : Deklaration} {V : Vertrag D₀} {l : Bool} {Γ Γ' : Ctx} (h : Γ = Γ')
    {o : EndAusgang V l Γ} {e : Logik D₀} (h' : castEnd h o = .logik e) : o = .logik e := by
  subst h; exact h'

namespace Einbettung

variable (E : Einbettung D D') (hZ : ZeigerfreiD D) (hS : E.SigTreu)

/-- **What a linking program keeps of a project.** -/
structure Uebernahme (P : Programm D) (S : SperrInv D) (Q : AxEns D) (T : D.Tab ⊕ D.Glob → Prop)
    (P' : Programm D') (S' : SperrInv D') (Q' : AxEns D') (T' : D'.Tab ⊕ D'.Glob → Prop) : Prop where
  fort : E.Fortsetzung hS P P'
  orte : ∀ L, S'.orte (E.lock L) = (S.orte L).map E.ortE
  inv : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')
  atom : ∀ c, T' (E.ortE c) → T c
  ax : ∀ a (W' : World D') (v : ErgVal D (D.aerg a)),
    Q' (E.ax a) W' (castV (E.aerg a).symm (E.ergE _ v)) = Q a ((E.speicherZ hZ W'.speicher).welt []) v
  invBild : ∀ i' t', t' ∈ D'.traeger i' → (E.tabZ t').isSome = true → ∃ i, E.inv i = i'

theorem inv_anfang (σ' : World D') :
    E.Inv [] ((E.speicherZ hZ σ'.speicher).welt []) σ' :=
  ⟨by rw [speicher_welt_speicher]; exact E.treu_speicherZ hZ σ',
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

section Lauf

variable {P : Programm D} {S : SperrInv D} {Q : AxEns D} {T : D.Tab ⊕ D.Glob → Prop}
  {P' : Programm D'} {S' : SperrInv D'} {Q' : AxEns D'} {T' : D'.Tab ⊕ D'.Glob → Prop}
  (hU : E.Uebernahme hZ hS P S Q T P' S' Q' T') {pad : List (Ereignis D)} (hp : PadOk pad)

include hU hp in
/-- The handlers of `D'` meet `Bed` whenever the call handler blames only images. -/
theorem bed_von {U' : Umwelt D'} {A' : AUmwelt D'}
    {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hA' : HavocA T' A') (hU' : HavocOk S' U')
    (hv : ∀ g σ ρ g', R' (E.fn g) σ ρ = .logik (.vorbedingung g') → ∃ g₀, g' = E.fn g₀) :
    E.Bed hZ pad S T S' T' U' A' R' :=
  ⟨hp, hA', hU.atom, hU', hU.orte, hU.inv, hv⟩

include hU in
/-- **The image body beside the body**: one key list, one outcome of `D` that every map
    repeating the keys produces, beside the image's outcome. -/
theorem rumpf_sim (passes : Nat) {O' : Orakel D'} {U' : Umwelt D'} {A' : AUmwelt D'}
    {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hB : E.Bed hZ pad S T S' T' U' A' R') (f : D.Fn) (σ' : World D')
    (ρ' : Env D' (D'.params (E.fn f))) :
    ∃ (M : List (World D × World D')) (o : EndAusgang (vertragVon D f) false (D.params f)),
      (∀ Φ, Passt Φ M → execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
          (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (P.rumpf f)
          ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') = o) ∧
      execEndHA S' O' U' A' passes R' (P'.rumpf (E.fn f)) σ' ρ' =
        castEndV (vertragVonE hS f) (castEnd (paramsE hS f) (execEndHA S' O' U' A' passes R'
          (exEnd hS (P.rumpf f)) σ' (castE (paramsE hS f).symm ρ'))) ∧
      E.EndRel M o (execEndHA S' O' U' A' passes R' (exEnd hS (P.rumpf f)) σ'
        (castE (paramsE hS f).symm ρ')) := by
  have hρ : E.EnvR (E.parZ hZ hS f ρ') (castE (paramsE hS f).symm ρ') := by
    have := E.envR_envE (E.parZ hZ hS f ρ')
    rwa [parZ, E.envE_envZ] at this
  obtain ⟨M, o, _, hΦ, hR⟩ := E.sim_end hZ hS pad S T S' T' O' U' A' passes R' hB (P.rumpf f) []
    _ σ' _ _ (E.inv_anfang hZ σ') hρ
  refine ⟨M, o, hΦ, ?_, hR⟩
  rw [hU.fort.rumpf f]
  unfold rumpfE
  rw [execEnd_umV, execEnd_umΓ, execEnd_umΛ]

end Lauf


/-! ## The obligation carries over -/

section Uebertragung

variable {P : Programm D} {S : SperrInv D} {Q : AxEns D} {T : D.Tab ⊕ D.Glob → Prop}
  {P' : Programm D'} {S' : SperrInv D'} {Q' : AxEns D'} {T' : D'.Tab ⊕ D'.Glob → Prop}
  (hU : E.Uebernahme hZ hS P S Q T P' S' Q' T') {pad : List (Ereignis D)} (hp : PadOk pad)
  (hSL : SperrInvLokal S) (hQL : AxEnsLokal Q)

include hU in
/-- An owed invariant of an image function is the image of one the function owes. -/
theorem invAmRueck_E {σ : World D} {σ' : World D'} (h : E.Treu σ.speicher σ') (f : D.Fn)
    (hI : InvAmRueck P f σ) : InvAmRueck P' (E.fn f) σ' := by
  intro i' hi' hs
  have hs' := hs
  unfold schuldet at hs'
  obtain ⟨t', ht', hw⟩ := List.any_eq_true.mp hs'
  have hz : (E.tabZ t').isSome = true := by
    unfold Deklaration.schreibt at hw
    rw [hS.signatur] at hw
    simp only [sigE] at hw
    revert hw
    cases E.tabZ t' with
    | none => intro hw; cases hw
    | some _ => intro _; rfl
  obtain ⟨i, rfl⟩ := hU.invBild i' t' ht' hz
  have hi : i ∈ D.invs := (E.invs i).mp hi'
  have hsch : schuldet f i = true := by
    unfold schuldet at hs ⊢
    rw [E.traeger, List.any_map] at hs
    rw [← hs]
    congr 1
    funext t
    show (D.signatur f).schreibt t = (D'.signatur (E.fn f)).schreibt (E.tab t)
    rw [hS.signatur]
    simp only [sigE, E.tabZ_tab]
  have hh := hI i hi hsch
  unfold InvHaelt at hh ⊢
  rw [hU.fort.invariante i]
  unfold invarianteE
  rw [eval_umΛ]
  have he := E.eval_exE h h (P.invariante i) Env.nil
  rw [show E.envE (Env.nil : Env D []) = Env.nil from rfl] at he
  rw [he]
  exact hh

variable (passes : Nat) (f : D.Fn)

include hU hp hSL hQL in
/-- **The body triple, caller duty and no `logik` outcome carry over.** -/
theorem koerperGutSA_E (hP : KoerperGutSA P passes Q S T f) : KoerperGutSA P' passes Q' S' T' (E.fn f) := by
  refine ⟨fun O' hRO hRL hAV U' hU' A' hA' R' hRR hOV σ' ρ' hreq => ⟨fun σ'' v' hrun => ?_, fun g' hrun => ?_⟩,
    fun O' hRO hRL hAV U' hU' A' hA' R' hRR hOL σ' ρ' hreq e' hrun => ?_⟩
  · have hB := E.bed_von hZ hS hU hp hA' hU' (R' := R')
      (fun g σ ρ g' h => absurd rfl (hOV (E.fn g) σ ρ _ h g'))
    obtain ⟨M, o, hΦ, heq, hR⟩ := E.rumpf_sim hZ hS hU passes hB f σ' ρ'
    rw [heq] at hrun
    obtain ⟨v₀, hv₀, rfl⟩ := castEndV_zurueck _ hrun
    rw [castEnd_zurueck _ hv₀] at hR
    cases o with
    | zurueck σe ve =>
        obtain ⟨hI, hv⟩ := hR
        have hk := hI.keyOk E
        have hT := E.phiAus_treu hk σ'.speicher
        have hreqD : ReqAmEintritt P f ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') := by
          unfold ReqAmEintritt
          rw [← E.req_E hS hU.fort (E.inv_anfang hZ σ').treu, E.paramsUm_parZ]
          exact hreq
        have hens := (hP.1 _ (E.orakelΦ_rahmen hZ hT hRO) (E.orakelΦ_regLokal hZ hT hRL)
          (E.orakelΦ_axVertrag hZ hAV hU.ax hQL) _ (E.umweltΦ_ok hZ hT S hSL hU.inv hU') _
          (E.aumweltΦ_ok hZ T A') _ (E.rufΦ_rahmen hZ hS hU.fort hp hT hRR)
          (E.rufΦ_ohneVorbedingung hZ hS hOV) _ _ hreqD).1 σe ve (hΦ _ (E.phiAus_passt hk σ'.speicher))
        unfold EnsAmRueck at hens ⊢
        have key := E.ens_E hS hU.fort (E.inv_anfang hZ σ').treu hI.treu f (E.parZ hZ hS f ρ')
          (ve : ErgVal D (D.erg f))
        rw [E.paramsUm_parZ] at key
        subst hv
        exact key.trans hens
    | _ => simp only [EndRel] at hR
  · have hB := E.bed_von hZ hS hU hp hA' hU' (R' := torRuf P' R') (fun g σ ρ g' h => by
      unfold torRuf at h
      split at h
      · exact absurd rfl (hOV (E.fn g) σ ρ _ h g')
      · cases h; exact ⟨g, rfl⟩)
    obtain ⟨M, o, hΦ, heq, hR⟩ := E.rumpf_sim hZ hS hU passes hB f σ' ρ'
    rw [heq] at hrun
    rw [castEnd_logik _ (castEndV_logik _ hrun)] at hR
    cases o with
    | logik e =>
        obtain ⟨hl, hk⟩ := hR
        obtain ⟨g₀, rfl, rfl⟩ := hl g' rfl
        have hT := E.phiAus_treu hk σ'.speicher
        have hreqD : ReqAmEintritt P f ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') := by
          unfold ReqAmEintritt
          rw [← E.req_E hS hU.fort (E.inv_anfang hZ σ').treu, E.paramsUm_parZ]
          exact hreq
        have hrunD := hΦ _ (E.phiAus_passt hk σ'.speicher)
        rw [E.rufΦ_torRuf hZ hS hU.fort hT R'] at hrunD
        exact (hP.1 _ (E.orakelΦ_rahmen hZ hT hRO) (E.orakelΦ_regLokal hZ hT hRL)
          (E.orakelΦ_axVertrag hZ hAV hU.ax hQL) _ (E.umweltΦ_ok hZ hT S hSL hU.inv hU') _
          (E.aumweltΦ_ok hZ T A') _ (E.rufΦ_rahmen hZ hS hU.fort hp hT hRR)
          (E.rufΦ_ohneVorbedingung hZ hS hOV) _ _ hreqD).2 g₀ hrunD
    | _ => simp only [EndRel] at hR
  · have hB := E.bed_von hZ hS hU hp hA' hU' (R' := R')
      (fun g σ ρ g' h => absurd h (hOL (E.fn g) σ ρ _))
    obtain ⟨M, o, hΦ, heq, hR⟩ := E.rumpf_sim hZ hS hU passes hB f σ' ρ'
    rw [heq] at hrun
    rw [castEnd_logik _ (castEndV_logik _ hrun)] at hR
    cases o with
    | logik e =>
        obtain ⟨_, hk⟩ := hR
        have hT := E.phiAus_treu hk σ'.speicher
        have hreqD : ReqAmEintritt P f ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') := by
          unfold ReqAmEintritt
          rw [← E.req_E hS hU.fort (E.inv_anfang hZ σ').treu, E.paramsUm_parZ]
          exact hreq
        exact hP.2 _ (E.orakelΦ_rahmen hZ hT hRO) (E.orakelΦ_regLokal hZ hT hRL)
          (E.orakelΦ_axVertrag hZ hAV hU.ax hQL) _ (E.umweltΦ_ok hZ hT S hSL hU.inv hU') _
          (E.aumweltΦ_ok hZ T A') _ (E.rufΦ_rahmen hZ hS hU.fort hp hT hRR)
          (E.rufΦ_ohneLogik hZ hS hOL) _ _ hreqD e (hΦ _ (E.phiAus_passt hk σ'.speicher))
    | _ => simp only [EndRel] at hR

include hU hp hSL hQL in
/-- **Owed invariants at a value return carry over.** -/
theorem invGutSA_E (hP : InvGutSA P passes Q S T f) : InvGutSA P' passes Q' S' T' (E.fn f) := by
  intro O' hRO hRL hAV U' hU' A' hA' R' hRR hOV σ' ρ' hreq σ'' v' hrun
  have hB := E.bed_von hZ hS hU hp hA' hU' (R' := R')
    (fun g σ ρ g' h => absurd rfl (hOV (E.fn g) σ ρ _ h g'))
  obtain ⟨M, o, hΦ, heq, hR⟩ := E.rumpf_sim hZ hS hU passes hB f σ' ρ'
  rw [heq] at hrun
  obtain ⟨v₀, hv₀, rfl⟩ := castEndV_zurueck _ hrun
  rw [castEnd_zurueck _ hv₀] at hR
  cases o with
  | zurueck σe ve =>
      obtain ⟨hI, _⟩ := hR
      have hk := hI.keyOk E
      have hT := E.phiAus_treu hk σ'.speicher
      have hreqD : ReqAmEintritt P f ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') := by
        unfold ReqAmEintritt
        rw [← E.req_E hS hU.fort (E.inv_anfang hZ σ').treu, E.paramsUm_parZ]
        exact hreq
      exact E.invAmRueck_E hZ hS hU hI.treu f (hP _ (E.orakelΦ_rahmen hZ hT hRO)
        (E.orakelΦ_regLokal hZ hT hRL) (E.orakelΦ_axVertrag hZ hAV hU.ax hQL) _
        (E.umweltΦ_ok hZ hT S hSL hU.inv hU') _ (E.aumweltΦ_ok hZ T A') _
        (E.rufΦ_rahmen hZ hS hU.fort hp hT hRR) (E.rufΦ_ohneVorbedingung hZ hS hOV) _ _ hreqD σe ve
        (hΦ _ (E.phiAus_passt hk σ'.speicher)))
  | _ => simp only [EndRel] at hR

include hU hp hSL hQL in
/-- **Owed invariants at a reason return carry over.** -/
theorem invGutGrundA_E (hP : InvGutGrundA P passes Q S T f) :
    InvGutGrundA P' passes Q' S' T' (E.fn f) := by
  intro O' hRO hRL hAV U' hU' A' hA' R' hRR hOV σ' ρ' hreq σ'' r' hrun
  have hB := E.bed_von hZ hS hU hp hA' hU' (R' := R')
    (fun g σ ρ g' h => absurd rfl (hOV (E.fn g) σ ρ _ h g'))
  obtain ⟨M, o, hΦ, heq, hR⟩ := E.rumpf_sim hZ hS hU passes hB f σ' ρ'
  rw [heq] at hrun
  obtain ⟨r₀, hr₀, _⟩ := castEndV_why _ hrun
  rw [castEnd_why _ hr₀] at hR
  cases o with
  | why σe re =>
      obtain ⟨hI, _⟩ := hR
      have hk := hI.keyOk E
      have hT := E.phiAus_treu hk σ'.speicher
      have hreqD : ReqAmEintritt P f ((E.speicherZ hZ σ'.speicher).welt []) (E.parZ hZ hS f ρ') := by
        unfold ReqAmEintritt
        rw [← E.req_E hS hU.fort (E.inv_anfang hZ σ').treu, E.paramsUm_parZ]
        exact hreq
      exact E.invAmRueck_E hZ hS hU hI.treu f (hP _ (E.orakelΦ_rahmen hZ hT hRO)
        (E.orakelΦ_regLokal hZ hT hRL) (E.orakelΦ_axVertrag hZ hAV hU.ax hQL) _
        (E.umweltΦ_ok hZ hT S hSL hU.inv hU') _ (E.aumweltΦ_ok hZ T A') _
        (E.rufΦ_rahmen hZ hS hU.fort hp hT hRR) (E.rufΦ_ohneVorbedingung hZ hS hOV) _ _ hreqD σe re
        (hΦ _ (E.phiAus_passt hk σ'.speicher)))
  | _ => simp only [EndRel] at hR

end Uebertragung

include hS in
/-- **A project's logic holds at every image function, without a new proof.** -/
theorem logikPflicht_E {P : Programm D} {S : SperrInv D} {Q : AxEns D} {T : D.Tab ⊕ D.Glob → Prop}
    {P' : Programm D'} {S' : SperrInv D'} {Q' : AxEns D'} {T' : D'.Tab ⊕ D'.Glob → Prop}
    (hU : E.Uebernahme hZ hS P S Q T P' S' Q' T') {pad : List (Ereignis D)} (hp : PadOk pad)
    (hL : LogikPflichtA P S Q T) :
    ∀ (passes : Nat) (f : D.Fn), KoerperGutSA P' passes Q' S' T' (E.fn f) ∧
      InvGutSA P' passes Q' S' T' (E.fn f) ∧ InvGutGrundA P' passes Q' S' T' (E.fn f) := by
  intro passes f
  obtain ⟨h1, h2, h3⟩ := hL.1 passes f
  exact ⟨E.koerperGutSA_E hZ hS hU hp hL.2.1 hL.2.2 passes f h1,
    E.invGutSA_E hZ hS hU hp hL.2.1 hL.2.2 passes f h2,
    E.invGutGrundA_E hZ hS hU hp hL.2.1 hL.2.2 passes f h3⟩

end Einbettung

end Gabbro.Grammatik.Einbettung
