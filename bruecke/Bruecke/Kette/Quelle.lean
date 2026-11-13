module
public import Bruecke.Kette.Simulation
public import Bruecke.Quelle
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem bruecke_koerperGutR_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c → KoerperGutR P passes c := by
  intro passes c hc O' _ _ R hRR hOV σ ρ _
  have hl := lauf_P_G hlow S rk hR hZ c hc O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  obtain ⟨d, σr, envA, hd, hD⟩ :=
    (lauf_P_G hlow S rk hR hZ c hc O' passes (torRuf P R)
      (torRuf_rahmen_teil hRR) σ ρ).1 _ h
  rw [torRuf_eq_teil (gesenkt_of_teil S.toGetragen hlow) R d hd σr envA] at hD
  exact hOV d σr envA _ hD g rfl

theorem bruecke_keineLogik_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), C c → KeineLogik P passes Q c := by
  intro passes Q c hc O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨d, σr, envA, _, hD⟩ := (lauf_P_G hlow S rk hR hZ c hc O' passes R hRR σ ρ).1 e h
  exact hOL d σr envA e hD

theorem bruecke_koerperGutS_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c →
      KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c := by
  intro passes c hc
  exact koerperGutS_leer
    ⟨koerperGutRQ_of_R _ (bruecke_koerperGutR_G hlow S rk hR hZ passes c hc),
      bruecke_keineLogik_G hlow S rk hR hZ passes _ c hc⟩

theorem bruecke_logik_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : SchnittstellenPflichtTeil u C) (hOpen : OffenePflicht u C) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  logik_aus_teilpflichten S.toGetragen hPtr hOpen hlow (bruecke_koerperGutS_G hlow S rk hR hZ)

/-- Unit assembly: carried Body duties and explicit open duties supply premise (b). -/
theorem bruecke_nutzer_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : SchnittstellenPflichtTeil u C) (hOpen : OffenePflicht u C)
    (hn : nullB u = true) (hStart : OffeneStartPflicht u C P hn) :
    Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  ⟨bruecke_logik_G hlow S rk hR hZ hPtr hOpen, startPflicht_teil hlow S.toGetragen hStart⟩

/-- The consolidated source bridge, with the actual initial requirement of every open start. -/
theorem nutzer_aus_quelleG {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilG src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨_, hn, S, hr, hPtr, hZ, hOpen⟩ := hp
  have hlow := lower_of_uebersetze h
  exact ⟨hn, bruecke_nutzer_G hlow S (rangAuto u) (rang_of hr) hZ hPtr hOpen hn (hStart hn)⟩

/-- The same carried chain supplies the atomic-rely premise for units without atomics. -/
theorem nutzerA_aus_quelleG {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilG src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_quelleG hp hStart h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_kein_atomar u (nullB_globs hn)) hb⟩

end Gabbro.Bruecke

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Per-unit branch duties pass through the same chain with every function carried. -/
theorem nutzer_aus_quelleG_alle {src : String} (hp : PflichtenAlle src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨u', hp'⟩ := pflichtenTeilG_of_alle hp
  have hu' := hp'.1
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact nutzer_aus_quelleG hp' (fun _ _ _ hc => (hc True.intro).elim) h

#print axioms nutzer_aus_quelleG
#print axioms nutzerA_aus_quelleG
#print axioms nutzer_aus_quelleG_alle

end Gabbro.Bruecke
