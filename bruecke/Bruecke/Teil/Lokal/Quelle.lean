module
public import Bruecke.Teil.Lokal.Simulation
@[expose] public section

/-!
# The partial source bridge with local bindings

Body simulation carries only the call-closed functions. Open bodies and interfaces remain user
duties; the additional open-start duty supplies precisely their initial requirements.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- The caller clause quantifies over every blame target `g`, including uncalled open targets.
    Run simulation with the gated handler gives an actual carried callee `d`. Its gate is
    trivial, and `OhneVorbedingung R` forbids blaming ANY `g` in that handler answer. -/
theorem bruecke_koerperGutR_teilB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenB u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c → KoerperGutR P passes c := by
  intro passes c hc O' _ _ R hRR hOV σ ρ _
  have hl := lauf_P_teilB hlow S rk hR hZ c hc O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  obtain ⟨d, σr, envA, hd, hD⟩ :=
    (lauf_P_teilB hlow S rk hR hZ c hc O' passes (torRuf P R)
      (torRuf_rahmen_teil hRR) σ ρ).1 _ h
  rw [torRuf_eq_teil (gesenkt_of_teil S.toGetragen hlow) R d hd σr envA] at hD
  exact hOV d σr envA _ hD g rfl

theorem bruecke_keineLogik_teilB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenB u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), C c → KeineLogik P passes Q c := by
  intro passes Q c hc O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨d, σr, envA, _, hD⟩ := (lauf_P_teilB hlow S rk hR hZ c hc O' passes R hRR σ ρ).1 e h
  exact hOL d σr envA e hD

/-- The carried component supplied to `logik_aus_teilpflichten`. -/
theorem bruecke_koerperGutS_teilB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenB u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), C c →
      KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c := by
  intro passes c hc
  exact koerperGutS_leer
    ⟨koerperGutRQ_of_R _ (bruecke_koerperGutR_teilB hlow S rk hR hZ passes c hc),
      bruecke_keineLogik_teilB hlow S rk hR hZ passes _ c hc⟩

theorem bruecke_logik_teilB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenB u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : SchnittstellenPflichtTeil u C) (hOpen : OffenePflicht u C) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  logik_aus_teilpflichten S.toGetragen hPtr hOpen hlow (bruecke_koerperGutS_teilB hlow S rk hR hZ)

/-- Unit-level assembly, with exactly the actual open-start duty. -/
theorem bruecke_nutzer_teilB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenB u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : SchnittstellenPflichtTeil u C) (hOpen : OffenePflicht u C)
    (hn : nullB u = true) (hStart : OffeneStartPflicht u C P hn) :
    Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  ⟨bruecke_logik_teilB hlow S rk hR hZ hPtr hOpen, startPflicht_teil hlow S.toGetragen hStart⟩

/-- The dependent `u` in `PflichtenTeilB` is the same `u` fixed by successful source lowering.
    Quantifying over its zero-memory proof avoids selecting a proof before the source duties
    have supplied it. Proof irrelevance makes this the same concrete initial memory. -/
theorem nutzer_aus_quelle_teilB {src : String} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (hp : PflichtenTeilB src C)
    (hStart : ∀ hn : nullB u = true, OffeneStartPflicht u C P hn)
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨_, hn, S, hr, hPtr, hZ, hOpen⟩ := hp
  have hlow := lower_of_uebersetze h
  exact ⟨hn, bruecke_nutzer_teilB hlow S (rangAuto u) (rang_of hr) hZ hPtr hOpen hn (hStart hn)⟩

end Gabbro.Bruecke
