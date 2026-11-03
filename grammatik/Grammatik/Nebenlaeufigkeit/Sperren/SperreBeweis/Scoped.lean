module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T3
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}

/-- Cleanup checks transfer on the protected, stable carriers of every named scope. -/
theorem scopesInvH_gleich (hS : SperrInvOk S) {f : D.Fn} {Λ : List (Res D)}
    {σ W : World D} (hg : GleichAuf (stabilS P S lok f Λ) σ W) :
    ∀ Ls : List D.Lock, (∀ L ∈ Ls, Res.held L ∈ Λ) →
      scopesInvH S Ls σ = scopesInvH S Ls W
  | [], _ => rfl
  | L :: Ls, hn => by
      change (S.inv L σ.speicher && scopesInvH S Ls σ) =
        (S.inv L W.speicher && scopesInvH S Ls W)
      rw [inv_gleich hS (hn L List.mem_cons_self) hg,
        scopesInvH_gleich hS hg Ls (fun K hK => hn K (List.mem_cons_of_mem _ hK))]

/-- The replay checks every released scope, including when a root returns. -/
theorem kopfS_scopedWert_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D F.f).erg)
    (R : RueckRessourcen D (vertragVon D F.f) Λ) (hret : r.scopedWert = some (e, R)) :
    scopesInvH S R.scopes (W.lese Λ e.orte) = true := by
  apply List.all_eq_true.mpr
  intro L hL
  change S.inv L W.speicher = true
  have hLΛ : Res.held L ∈ Λ :=
    R.genau.symm.mem_iff.mp (List.mem_append_right _ (List.mem_map.mpr ⟨L, hL, rfl⟩))
  apply kopfS_frei_inv hO hRL hQ hS hsp hK hG L hLΛ hr
  intro O' U calls σ hbad
  apply semH_scopedWert_falsch S O' U passes calls r e R hret σ ρ
  cases hc : scopesInvH S R.scopes (σ.lese Λ e.orte) with
  | false => rfl
  | true =>
      have hi := scopesInvH_mem hc hL
      change S.inv L σ.speicher = true at hi
      rw [hbad] at hi
      cases hi

/-- The reason channel has the same invariant obligations and no expression read. -/
theorem kopfS_scopedGrund_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (grund : Fin (vertragVon D F.f).gruende)
    (R : RueckRessourcen D (vertragVon D F.f) Λ) (hret : r.scopedGrund = some (grund, R)) :
    scopesInvH S R.scopes W = true := by
  apply List.all_eq_true.mpr
  intro L hL
  have hLΛ : Res.held L ∈ Λ :=
    R.genau.symm.mem_iff.mp (List.mem_append_right _ (List.mem_map.mpr ⟨L, hL, rfl⟩))
  apply kopfS_frei_inv hO hRL hQ hS hsp hK hG L hLΛ hr
  intro O' U calls σ hbad
  apply semH_scopedGrund_falsch S O' U passes calls r grund R hret σ ρ
  cases hc : scopesInvH S R.scopes σ with
  | false => rfl
  | true =>
      have hi := scopesInvH_mem hc hL
      rw [hbad] at hi
      cases hi

end Gabbro.Grammatik
