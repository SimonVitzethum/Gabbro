module
public import Bruecke.Kette.Simulation
public import Bruecke.Quelle
@[expose] public section

/-!
# Unit assembly

The `_M` theorems take the measure duties `MassPflichtU` and carry recursive and mutually
recursive units; the rank theorems are their instances under `MassU.rang`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem bruecke_koerperGutR_M {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (M : MassU) (hZ : MassPflichtU u C M) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c → KoerperGutR P passes c := by
  intro passes c hc O' _ _ R hRR hOV σ ρ _
  have hl := lauf_P_mass_G hlow S M hZ c hc O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  obtain ⟨d, σr, envA, hd, hD⟩ :=
    (lauf_P_mass_G hlow S M hZ c hc O' passes (torRuf P R)
      (torRuf_rahmen_teil hRR) σ ρ).1 _ h
  rw [torRuf_eq_teil (gesenkt_of_teil S.toGetragen hlow) R d hd σr envA] at hD
  exact hOV d σr envA _ hD g rfl

theorem bruecke_keineLogik_M {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (M : MassU) (hZ : MassPflichtU u C M) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), C c → KeineLogik P passes Q c := by
  intro passes Q c hc O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨d, σr, envA, _, hD⟩ := (lauf_P_mass_G hlow S M hZ c hc O' passes R hRR σ ρ).1 e h
  exact hOL d σr envA e hD

theorem bruecke_koerperGutS_M {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (M : MassU) (hZ : MassPflichtU u C M) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c →
      KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c := by
  intro passes c hc
  exact koerperGutS_leer
    ⟨koerperGutRQ_of_R _ (bruecke_koerperGutR_M hlow S M hZ passes c hc),
      bruecke_keineLogik_M hlow S M hZ passes _ c hc⟩

theorem bruecke_logik_M {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (M : MassU) (hZ : MassPflichtU u C M)
    (hOpen : OffenePflicht u C) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  logik_aus_teilpflichten S.toGetragen hOpen hlow (bruecke_koerperGutS_M hlow S M hZ)

/-- **Unit assembly under a measure**: carried Body duties, recursive ones included, and
    explicit open duties supply premise (b). -/
theorem bruecke_nutzer_M {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (M : MassU) (hZ : MassPflichtU u C M)
    (hOpen : OffenePflicht u C)
    (hn : nullB u = true) (hStart : OffeneStartPflicht u C P hn) :
    Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  ⟨bruecke_logik_M hlow S M hZ hOpen, startPflicht_teil hlow S.toGetragen hStart⟩

/-! ## The rank forms -/

theorem bruecke_koerperGutR_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c → KoerperGutR P passes c :=
  bruecke_koerperGutR_M hlow S _ (massPflichtU_of_rang hR hZ)

theorem bruecke_keineLogik_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), C c → KeineLogik P passes Q c :=
  bruecke_keineLogik_M hlow S _ (massPflichtU_of_rang hR hZ)

theorem bruecke_koerperGutS_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c →
      KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c :=
  bruecke_koerperGutS_M hlow S _ (massPflichtU_of_rang hR hZ)

theorem bruecke_logik_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) (hOpen : OffenePflicht u C) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  bruecke_logik_M hlow S _ (massPflichtU_of_rang hR hZ) hOpen

/-- Unit assembly: carried Body duties and explicit open duties supply premise (b). -/
theorem bruecke_nutzer_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) (hOpen : OffenePflicht u C)
    (hn : nullB u = true) (hStart : OffeneStartPflicht u C P hn) :
    Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  bruecke_nutzer_M hlow S _ (massPflichtU_of_rang hR hZ) hOpen hn hStart

/-! ## From the source text -/

/-- **The consolidated source bridge under a measure**, recursive units included. -/
theorem nutzer_aus_quelleM {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilM src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨_, hn, S, ⟨M, hZ⟩, hOpen⟩ := hp
  have hlow := lower_of_uebersetze h
  exact ⟨hn, bruecke_nutzer_M hlow S M hZ hOpen hn (hStart hn)⟩

/-- The consolidated source bridge, with the actual initial requirement of every open start. -/
theorem nutzer_aus_quelleG {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilG src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  nutzer_aus_quelleM (pflichtenTeilM_of_G hp) hStart h

/-- The same carried chain supplies the atomic-rely premise for units without atomics. -/
theorem nutzerA_aus_quelleM {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilM src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_quelleM hp hStart h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_scalar_kein_atomar u (nullB_statics hn)) hb⟩

theorem nutzerA_aus_quelleG {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilG src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) :=
  nutzerA_aus_quelleM (pflichtenTeilM_of_G hp) hStart h

end Gabbro.Bruecke

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- **Per-unit measure duties through the whole chain**, every function carried, recursion
    and mutual recursion included. -/
theorem nutzer_aus_quelleM_alle {src : String} (hp : PflichtenAlleM src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨u', hp'⟩ := pflichtenTeilM_of_alleM hp
  have hu' := hp'.1
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact nutzer_aus_quelleM hp' (fun _ _ _ hc => (hc True.intro).elim) h

/-- Per-unit branch duties pass through the same chain with every function carried. -/
theorem nutzer_aus_quelleG_alle {src : String} (hp : PflichtenAlle src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  nutzer_aus_quelleM_alle (pflichtenAlleM_of_alle hp) h

#print axioms nutzer_aus_quelleG
#print axioms nutzerA_aus_quelleG
#print axioms nutzer_aus_quelleG_alle
#print axioms nutzer_aus_quelleM
#print axioms nutzer_aus_quelleM_alle

end Gabbro.Bruecke
