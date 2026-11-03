module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStartBasis
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A scoped head's expression has the same checked read footprint as a
    plain return. The final residue never re-evaluates this expression. -/
theorem scopedWert_orte {P : Programm D} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg}
    {R : RueckRessourcen D V Λ} {S S' : List (D.Tab ⊕ D.Glob)}
    (hok : r.okS P S S') (h : r.scopedWert = some (e, R)) : e.orte ⊆ S := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;> subst r
  · simpa only [endblockOrteP] using hok.2
  · simpa only [stmtOrteP] using (okS_ende_cons hok).2.1
  · simpa only [stmtOrteP] using (okS_dann_cons hok).2.1

section Replay

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- The replay establishes ensures and owed function invariants at the
    pre-release read world, at every stack depth. This is a release-step
    guarantee; it deliberately does not extend expression-based `RetKopf`. -/
theorem kopfS_scopedRet (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hI : ∀ f, InvGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) l Γ Λ} (hr : G.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (R : RueckRessourcen D (vertragVon D G.f) Λ) (hret : r.scopedWert = some (e, R)) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
        (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) ∧
      InvAmRueck P G.f (W.lese Λ e.orte) := by
  have hmono : stabilS P S lok G.f (vertragVon D G.f).ende ⊆ stabilS P S lok G.f Λ :=
    stabilS_mono fun L hL => R.genau.symm.mem_iff.mp (List.mem_append_left _ hL)
  have he := erg_stabil (hFS G.f) e (scopedWert_orte (kopfS_okS hG hr) hret)
  have hens := ens_stabil (hFS G.f) (List.Perm.refl ((vertragVon D G.f).ende))
  have hcheckW := kopfS_scopedWert_inv hO hRL hQ hS hsp hK hG hr e R hret
  have hheld : ∀ L ∈ R.scopes, Res.held L ∈ Λ := by
    intro L hL
    exact R.genau.symm.mem_iff.mp
      (List.mem_append_right _ (List.mem_map.mpr ⟨L, hL, rfl⟩))
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  -- The guard belongs to this replay world, not to an arbitrary callback world.
  have hcheck : scopesInvH S R.scopes (σ.lese Λ e.orte) = true := by
    change scopesInvH S R.scopes σ = true
    change scopesInvH S R.scopes W = true at hcheckW
    exact (scopesInvH_gleich hS hg R.scopes hheld).trans hcheckW
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich
    (semH_scopedWert S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusV H)
      r e R hret σ ρ hcheck)))
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := ((hK G.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertrag hQ hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq).1 σ' _ hex
  have hInv := (hI G.f) (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertrag hQ hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ' _ hex
  have hgl : GleichAuf (stabilS P S lok G.f Λ) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  have hfinal : GleichAuf (stabilS P S lok G.f Λ) σ' (W.lese Λ e.orte) :=
    (gleichAuf_SG hsg).trans hgl
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  refine ⟨ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => hmono (hens h)) hfinal), ?_⟩
  intro i hi hs
  have h3 := hInv i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i)
    (fun _ h => hmono (inv_stabil (hFS G.f) (List.Perm.refl _) hi hs h)) hfinal .nil]
  exact h3

/-- The all-head release-step property, including roots. The saved-answer
    invariant carries this guarantee into `StartEndeG` after cleanup. -/
def ScopedRueckGutG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg)
    (R : RueckRessourcen D (vertragVon D (M.faeden t).kopf.f) Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → r.scopedWert = some (e, R) →
      EnsAmRueck P (M.faeden t).kopf.f (M.faeden t).kopf.s0 ((M.weltVon t).lese Λ e.orte)
          (M.faeden t).kopf.rho
          (evalErg ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ) ∧
        InvAmRueck P (M.faeden t).kopf.f ((M.weltVon t).lese Λ e.orte)

/-- Every reachable release source has the return guarantee, provided the
    replay invariant has been preserved through every G rule. -/
theorem ziel_ort_scoped_rueck_bei (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f, InvGutS P passes Q S f) :
    ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M → ScopedRueckGutG P M := by
  intro M hreach t l Γ Λ ρ r e R hhead hret
  have hZ := (zielInvS_erreichbarL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex M hreach).1
  exact kopfS_scopedRet hO hRL hQ hS hSstart hK hI hFS (hZ.1 t).1 hhead e R hret

end Replay

/-- A root of an accepted start cannot take either reason-return rule or
    contain a saved reason. This uses the channel's empty type, without
    enlarging the immutable `GrundKopf`/`KeinStartGrundG` statements. -/
theorem start_scopedGrund_unmoeglich {P : Programm D} {O : Orakel D} {passes : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hG : StartOhneGrund init) {M : RufMaschineG D}
    (hreach : RufErreichbarG P O passes (RufStartG P sp init) M) {t : Faden}
    (hst : (M.faeden t).stapel = [])
    (grund : Fin (vertragVon D (M.faeden t).kopf.f).gruende) : False := by
  have hw := wurzelFn_erreichbar hreach t
  unfold wurzelFn at hw
  rw [hst] at hw
  have hf : (M.faeden t).kopf.f = (init t).1 := hw
  have h0 : (vertragVon D (M.faeden t).kopf.f).gruende = 0 := by
    change D.gruende (M.faeden t).kopf.f = 0
    rw [hf]
    exact hG t
  exact (Fin.cast h0 grund).elim0

/-- The expression-based clause excludes saved answers. `StartEndeG` checks
    them with its separate `StartScopedEndeG` conjunct instead. -/
theorem zurueckgekehrt_nicht_retKopf {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D) (e : ErgExpr D Γ V.ende V.erg) :
    ¬ RetKopf e (.zurueckgekehrt (l := l) a) := by
  rintro ⟨hp, h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩⟩ <;> cases h

end Gabbro.Grammatik
