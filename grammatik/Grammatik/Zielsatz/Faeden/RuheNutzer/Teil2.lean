module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Zielsatz.Faeden.RuheNutzer.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}

theorem gutO_mitRuhe {O : Orakel D} (h : GutO O) : GutO O.mitRuhe := by
  intro a σ ρ
  rw [wirkt_mitRuhe_welt O a σ ρ]
  obtain ⟨h1, h2, h3⟩ := h a (worldZ σ) (envZ ρ)
  have hh : (worldZ σ).haelt = σ.haelt := haelt_worldZ σ
  refine ⟨rahmen_worldR h1, ?_, fun ht hg => ?_⟩
  · show (worldR (O.wirkt a (worldZ σ) (envZ ρ)).1).haelt = σ.haelt
    rw [haelt_worldR, h2, hh]
  · obtain ⟨tabs, globs, Λe, e1, e2, e3, e4, e5, e6, e7⟩ :=
      h3 (fun t hta L hL => hh ▸ ht t hta L hL) (fun g hga L hL => hh ▸ hg g hga L hL)
    refine ⟨tabs, globs, Λe.map resR, e1, e2, fun t hta => darfR (e3 t hta),
      fun g hga => gdarfR (e4 g hga), fun m st hm => ?_, fun L hL => ?_, ?_⟩
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
      cases r with
      | held L => cases he
      | marke m' s' =>
          cases he
          exact e5 _ _ hr
    · rw [← hh]
      exact e6 L (held_mem_map.mp hL)
    · show (O.wirkt a (worldZ σ) (envZ ρ)).1.spur.map evR =
        axiomSpur (D := D.mitRuhe) tabs globs a (Λe.map resR) σ.haelt ++ σ.spur
      rw [e7, List.map_append, hh, axiomSpur_map]
      congr 1
      show (σ.spur.map evZ).map evR = σ.spur
      rw [List.map_map]
      conv => rhs; rw [← List.map_id σ.spur]
      exact List.map_congr_left fun e _ => evR_evZ e

theorem regLokal_mitRuhe {O : Orakel D} (h : RegLokal O) : RegLokal O.mitRuhe :=
  ⟨fun r _ _ hg => by
      rw [regLies_mitRuhe_welt, regLies_mitRuhe_welt]
      exact h.1 r _ _ (gleichAuf_worldZ hg),
    fun g _ _ hg => by
      rw [sichtbar_mitRuhe_welt, sichtbar_mitRuhe_welt]
      exact h.2 g _ _ (gleichAuf_worldZ hg)⟩

theorem axVertrag_mitRuhe {Q : AxEns D} {O : Orakel D} (h : AxVertragO Q O) :
    AxVertragO (axEnsRuhe Q) O.mitRuhe := by
  intro a σ ρ v hv
  rw [wirkt_mitRuhe_welt O a σ ρ] at hv ⊢
  change einpassenErg (D := D.mitRuhe) O.mitRuhe.zeiger ((D.aerg a).map tyR)
    (O.wirkt a (worldZ σ) (envZ ρ)).2 = some v at hv
  rw [einpassenErg_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)] at hv
  cases hx : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (worldZ σ) (envZ ρ)).2 with
  | none => rw [hx] at hv; cases hv
  | some v0 =>
      rw [hx] at hv
      cases hv
      show Q a (worldZ (worldR (O.wirkt a (worldZ σ) (envZ ρ)).1)) (ergZ _ (ergR _ v0)) = true
      rw [worldZ_worldR, ergZ_ergR]
      exact h a _ _ v0 hx

/-- Conditional membership transports to the idle-root oracle without
    requiring unconditional software summaries. -/
theorem axVertragOP_mitRuhe {P : Programm D} {Q : AxEns D} {O : Orakel D}
    (h : AxVertragOP (PreQ P) Q O) :
    AxVertragOP (PreQ P.mitRuhe) (axEnsRuhe Q) O.mitRuhe := by
  intro a σ ρ v hp hv
  have hp0 : PreQ P a ((worldZ σ).fragt (.inl a)) (envZ ρ) = true := by
    rw [← preQ_mitRuhe P a ((worldZ σ).fragt (.inl a)) (envZ ρ), ← worldZ_fragt, worldR_worldZ,
      envR_envZ]
    exact hp
  rw [wirkt_mitRuhe_welt] at hv
  change einpassenErg (D := D.mitRuhe) O.mitRuhe.zeiger ((D.aerg a).map tyR)
    (O.wirkt a ((worldZ σ).fragt (.inl a)) (envZ ρ)).2 = some v at hv
  rw [einpassenErg_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)] at hv
  cases hx : einpassenErg O.zeiger (D.aerg a) (O.wirkt a ((worldZ σ).fragt (.inl a)) (envZ ρ)).2 with
  | none => rw [hx] at hv; cases hv
  | some v0 =>
      rw [hx] at hv
      cases hv
      rw [wirkt_mitRuhe_welt]
      show Q a (worldZ (worldR (O.wirkt a ((worldZ σ).fragt (.inl a)) (envZ ρ)).1))
        (ergZ _ (ergR _ v0)) = true
      rw [worldZ_worldR, ergZ_ergR]
      exact h a (worldZ σ) (envZ ρ) v0 hp0 hx

/-- **The hardware assumptions on `O` are the ones on `O.mitRuhe`.** -/
theorem hardware_mitRuhe {O : Orakel D} {Q : AxEns D} (h : HardwareAnnahmen O Q) :
    HardwareAnnahmen O.mitRuhe (axEnsRuhe Q) :=
  ⟨gutO_mitRuhe h.1, regLokal_mitRuhe h.2.1, axVertrag_mitRuhe h.2.2.1, h.2.2.2⟩

#print axioms Gabbro.Grammatik.koerperGutS_mitRuhe
#print axioms Gabbro.Grammatik.invGutS_mitRuhe
#print axioms Gabbro.Grammatik.invGutGrund_mitRuhe
#print axioms Gabbro.Grammatik.logikPflicht_mitRuhe
#print axioms Gabbro.Grammatik.hardware_mitRuhe

end Gabbro.Grammatik
