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
  refine ⟨popS_ens hO hRL hQ hS hsp hK hG hr e he
      (fun c hc => hmono (hens hc)) (fun O' calls U σ =>
        semH_scopedWert S O' U passes calls r e R hret σ ρ), ?_⟩
  apply popS_inv hO hRL hQ hS hsp hI hG hr e
  · intro i hi hs c hc
    exact hmono (inv_stabil (hFS G.f) (List.Perm.refl _) hi hs hc)
  · intro O' calls U σ
    exact semH_scopedWert S O' U passes calls r e R hret σ ρ

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
