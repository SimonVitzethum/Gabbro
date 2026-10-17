/- Part 3 of 4 of `Schlusssatz124` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz124.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T2

namespace Gabbro.Grammatik
namespace K124

open Zielsatz

section Arten

variable {passes : Nat}

/-- A carrier of the program is never an `atomic` global (there are none). -/
theorem nicht_atomar (tb : KTab) : ¬ AtomarAusgenommen (D := DR) (.inl tb) :=
  fun ⟨_, h, _⟩ => by cases h

/-- **A slot store as a block**: one G leaf step (`gBlatt`). -/
theorem k_store (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) (tb : KTab) (kk : Nat) (hkk : kk < 2) (v : Int)
    (hv : 0 ≤ v ∧ v ≤ 100) (wz : Zahl 0 100) (hwz : wz.n = v) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.store (cSlot (kTnr tb) kk) u32 (.lit v) :: k) ρ)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (hacc : (Sum.inl tb, true) ∈ zugriffe M M1 t)
    (hoff : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (hmem : M1.speicher.slots = ((M.speicher.welt []).storeSlot tb kk () wz).slots)
    (hrel : FadenRel (w t) (.an k ρ) (M1.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf (c124.tiefe + 1)
    (CallAt c124.L c124.orc keinXR c124.Pr c124.tiefe) keinXR tb kk hkk (.lit v) v ρ
    (fun _ => rfl) hv (M.speicher.welt []) K.st hR.1 [] wz hwz
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    refine ⟨seg1 M M1, 1, lauf1 s1, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · exact corrW_von hc1 (by show _ = M1.speicher.slots; rw [hmem]; rfl)
    · exact sperrRel_gleich t hR.2.1 rfl hoff (fun u hu => rufSchrittG_fremd s1 u hu)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fun u hu => rufSchrittG_fremd s1 u hu
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M1.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => ?_, fun b hb => ?_, fun k hk L hg => ?_, fun k hk L hn => ?_⟩
      · have hb' : b = .tab (kTnr tb) := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, c124] using hb
        exact ⟨.inl tb, hb'.symm, nicht_atomar tb, 0, Nat.zero_lt_one, Or.inl ⟨true, hacc⟩⟩
      · have hb' : b = .tab (kTnr tb) := by
          simpa [Etikett.fussW, fussW, CS.ziele0, CS.rufe, cSlot, CX.obj, c124] using hb
        exact ⟨.inl tb, hb'.symm, 0, Nat.zero_lt_one, Or.inl hacc⟩
      · match k, hk with
        | 0, _ => exact absurd hg (kein_wechsel hoff L).1
      · match k, hk with
        | 0, _ => exact absurd hn (kein_wechsel hoff L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

/-- A foreign call has no meaning inside a block. -/
theorem ext_kein_block {n : Nat} {st : CSt} {ρ : CLok} {o : COut} :
    ¬ c124.laeuft (.ext n [] none) st ρ o := by
  intro h
  cases h with
  | ext _ hxr _ => exact hxr.elim

/-- At `L_nimm();` the C lock is free, and so is G's. -/
theorem nimm_frei (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cNimm :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    K.halter 0 = none ∧ RufFreiG M t lL := by
  have h0 : K.halter 0 = none := by
    rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
      ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
      ⟨n, k', ρ', op, h', hK, ho, hl, -, -⟩
    · rw [hc] at hK; cases hK
    · rw [hc] at hK; cases hK
    · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
    · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
    · rw [hc] at hK
      cases hK
      cases ho
      exact hl.1
  refine ⟨h0, fun u hu hL => ?_⟩
  have := (hR.2.1 0 u).mpr ⟨rfl, hL⟩
  rw [h0] at this
  cases this

/-- **`L_nimm();`**: the acquire -- two G steps (`gNimm`). -/
theorem k_nimm (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cNimm :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h1 : (M1.faeden t).spur = (M.faeden t).spur) (h2 : offen (M2.faeden t).spur = [lL])
    (hm2 : M2.speicher = M.speicher) (h0 : offen (M.faeden t).spur = [])
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, ho, hl, hlab, hK'⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK
    cases hK
    cases ho
    obtain ⟨hh0, hh'⟩ := hl
    subst hlab; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) K.st
      rw [hm2]; exact hR.1
    · exact sperrRel_nimm t hR.2.1 hh0 hh' h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil,
        fun k hk L hg => ?_, fun _ _ _ _ => rfl⟩
      match k, hk with
      | 0, _ => exact absurd hg (kein_wechsel (by
          show offen (M1.faeden t).spur = offen (M.faeden t).spur; rw [h1]) L).1
      | 1, _ =>
          have := hg.1
          rw [show (seg2 M M1 M2 1) = M1 from rfl, h1, h0] at this
          exact absurd this List.not_mem_nil

/-- **`setze(n);`**: the call inside the lock -- five G steps (`gSetze`). -/
theorem k_setze (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) (n : Int) (hn : 0 ≤ n ∧ n ≤ 100) (wz : Zahl 0 100)
    (hwz : wz.n = n) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.call 0 [.lit n] none :: k) ρ)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 M3 M4 M5 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2) (s3 : RufSchrittG PR OR passes M2 t M3)
    (s4 : RufSchrittG PR OR passes M3 t M4) (s5 : RufSchrittG PR OR passes M4 t M5)
    (ho1 : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (ho2 : offen (M2.faeden t).spur = offen (M.faeden t).spur)
    (ho3 : offen (M3.faeden t).spur = offen (M.faeden t).spur)
    (ho4 : offen (M4.faeden t).spur = offen (M.faeden t).spur)
    (ho5 : offen (M5.faeden t).spur = offen (M.faeden t).spur)
    (hacc : (Sum.inl KTab.konto, true) ∈ zugriffe M1 M2 t)
    (hmem : M5.speicher.slots =
      (((M.speicher.welt []).storeSlot KTab.konto 0 () wz).storeSlot KTab.konto 1 () wz).slots)
    (hrel : FadenRel (w t) (.an k ρ) (M5.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  obtain ⟨st1, hx1, hc1⟩ := cSetze_lauf n hn (M.speicher.welt []) K.st hR.1 ρ [] [] wz hwz
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n', k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    have hl5 := lauf5 (passes := passes) s1 s2 s3 s4 s5
    refine ⟨seg5 M M1 M2 M3 M4 M5, 5, hl5, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · exact corrW_von hc1 (by show _ = M5.speicher.slots; rw [hmem]; rfl)
    · exact sperrRel_gleich t hR.2.1 rfl ho5 (fremd_ende hl5)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl5
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M5.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · have hoffs : ∀ j, j < 5 → offen ((seg5 M M1 M2 M3 M4 M5 (j + 1)).faeden t).spur =
          offen ((seg5 M M1 M2 M3 M4 M5 j).faeden t).spur := by
        intro j hj
        match j, hj with
        | 0, _ => exact ho1
        | 1, _ => exact ho2.trans ho1.symm
        | 2, _ => exact ho3.trans ho2.symm
        | 3, _ => exact ho4.trans ho3.symm
        | 4, _ => exact ho5.trans ho4.symm
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun j hj L hg => ?_, fun j hj L hn => ?_⟩
      · have hb' : b = .tab 0 := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, CX.objL, c124, c124Prog,
            cSetzeBody] using hb
        exact ⟨.inl KTab.konto, hb'.symm, nicht_atomar _, 1, by decide, Or.inl ⟨true, hacc⟩⟩
      · have hb' : b = .tab 0 := by
          simpa [Etikett.fussW, fussW, CS.ziele0, CS.rufe, cSlot, CX.obj, c124, c124Prog,
            cSetzeBody] using hb
        exact ⟨.inl KTab.konto, hb'.symm, 1, by decide, Or.inl hacc⟩
      · exact absurd hg (kein_wechsel (hoffs j hj) L).1
      · exact absurd hn (kein_wechsel (hoffs j hj) L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

/-- **`L_gib();`**: the release -- two G steps (`gGib`). -/
theorem k_gib (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (cGib :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h0 : offen (M.faeden t).spur = [lL]) (h1 : offen (M1.faeden t).spur = [])
    (h2 : offen (M2.faeden t).spur = []) (hm2 : M2.speicher = M.speicher)
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, ho, hl, hlab, hK'⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK; cases hK; exact (ext_kein_block hx).elim
  · rw [hc] at hK
    cases hK
    cases ho
    obtain ⟨hh0, hh'⟩ := hl
    subst hlab; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) K.st
      rw [hm2]; exact hR.1
    · exact sperrRel_gib t hR.2.1 hh0 hh' h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · refine ⟨fun b hb => absurd hb List.not_mem_nil, fun b hb => absurd hb List.not_mem_nil,
        fun _ _ _ _ => rfl, fun k hk L hn => ?_⟩
      match k, hk with
      | 0, _ =>
          have := hn.1
          rw [show (seg2 M M1 M2 0) = M from rfl, h0] at this
          exact (this (by cases L; exact List.mem_singleton_self _)).elim
      | 1, _ => exact absurd hn (kein_wechsel (by rw [show (seg2 M M1 M2 2) = M2 from rfl,
          show (seg2 M M1 M2 1) = M1 from rfl, h1, h2]) L).2

/-- **`(void)pruefeA();`**: call and return -- two G steps (`gPruefe`). -/
theorem k_pruefe (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.call 1 [] none :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    {M1 M2 : RufMaschineG DR} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2)
    (h1 : offen (M1.faeden t).spur = offen (M.faeden t).spur)
    (h2 : offen (M2.faeden t).spur = offen (M.faeden t).spur)
    (hacc : (Sum.inl KTab.privA, false) ∈ zugriffe M1 M2 t) (hm2 : M2.speicher = M.speicher)
    (hrel : FadenRel (w t) (.an k ρ) (M2.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hx1 := cPruefe_lauf (M.speicher.welt []) K.st hR.1 ρ
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, hl, hK'⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n', k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK
    cases hK
    have e := c124.laeuft_det hx hx1
    cases e
    subst hl; subst hK'
    have hl2 := lauf2 (passes := passes) s1 s2
    refine ⟨seg2 M M1 M2, 2, hl2, r124_neu w t hR ?_ ?_ ?_ ?_ ?_, ?_⟩
    · show corrW kEL (M2.speicher.welt []) _
      rw [hm2]; exact corrW_leave (corrW_enter hR.1 1 []) 1
    · exact sperrRel_gleich t hR.2.1 rfl h2 (fremd_ende hl2)
    · exact fun u hu => fadenSetze_ne _ _ _ _ hu
    · exact fremd_ende hl2
    · show FadenRel (w t) (fadenSetze K.faeden t _ t) (M2.faeden t)
      rw [fadenSetze_eq]; exact hrel
    · have hoffs : ∀ j, j < 2 → offen ((seg2 M M1 M2 (j + 1)).faeden t).spur =
          offen ((seg2 M M1 M2 j).faeden t).spur := by
        intro j hj
        match j, hj with
        | 0, _ => exact h1
        | 1, _ => exact h2.trans h1.symm
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun j hj L hg => ?_, fun j hj L hn => ?_⟩
      · have hb' : b = .tab 1 := by
          simpa [Etikett.fussR, fussR, CS.obj0, CS.rufe, cSlot, CX.obj, CX.objL, c124, c124Prog,
            cPruefeBody] using hb
        exact ⟨.inl KTab.privA, hb'.symm, nicht_atomar _, 1, by decide, Or.inl ⟨false, hacc⟩⟩
      · simp [Etikett.fussW, fussW, CS.ziele0, CS.rufe, c124, c124Prog, cPruefeBody] at hb
      · exact absurd hg (kein_wechsel (hoffs j hj) L).1
      · exact absurd hn (kein_wechsel (hoffs j hj) L).2
  · rw [hc] at hK
    cases hK
    cases (c124.laeuft_det hx hx1)
  · rw [hc] at hK; cases hK

end Arten
section Positionen

variable {passes : Nat}

/-- **Every C step of a `hauptA` thread is simulated.** -/
theorem schrittA (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hwt : w t = some 2) (hR : R124 w K M)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hA : ThreadA (K.faeden t) (M.faeden t) := by
    have := hR.2.2 t; rw [hwt] at this; exact this
  have mk : ∀ (j : Nat) (c : CFaden) (z : RufFadenG DR), j ≤ 12 → c = posA j →
      (∃ (sp' : List (Ereignis DR)) (log' : List (RufEreignisF DR)),
        z = ⟨[], frA (gOfA j), sp', log'⟩ ∧ offen sp' = heldGA (gOfA j)) →
      FadenRel (w t) c z := by
    intro j c z hj hcj ⟨sp', log', hz', ho'⟩
    rw [hwt]
    exact ⟨j, sp', log', hj, hcj, hz', ho'⟩
  obtain ⟨i, sp, log, hi, hc, hz, hoff⟩ := hA
  match i, hi, hc, hz, hoff with
  | 0, _, hc, hz, hoff =>
      exact k_teile w hR (a := cA0) (b := cRestA1) (k := []) hc hs
        (mk 1 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 1, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptA .nil
        KTab.privA kI0 k7 rfl (kDarfA _) (.cons kA1 (.cons kLocksA kRestA)) M t sp log
        (frA0_form M t sp log hz)
      exact k_store w hR KTab.privA 0 (by decide) 7 (by decide) ⟨7, by decide, by decide⟩ rfl
        (k := [cRestA1]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 2 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 2, _, hc, hz, hoff =>
      exact k_teile w hR (a := cA1) (b := cRestA2) (k := []) hc hs
        (mk 3 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 3, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptA .nil
        KTab.privA kI1 k7 rfl (kDarfA _) (.cons kLocksA kRestA) M t sp log hz
      exact k_store w hR KTab.privA 1 (by decide) 7 (by decide) ⟨7, by decide, by decide⟩ rfl
        (k := [cRestA2]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 4 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 4, _, hc, hz, hoff =>
      exact k_teile w hR (a := cNimm) (b := cRestA3) (k := []) hc hs
        (mk 5 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 5, _, hc, hz, hoff =>
      obtain ⟨_, hfrei⟩ := nimm_frei w hR (k := [cRestA3]) (ρ := ρ0) hc hs
      obtain ⟨M1, M2, s1, s2, hs1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gNimm (passes := passes) kHauptA
        .nil (.cons kRufA .nil) kRestA M t sp log hz hoff hfrei
      exact k_nimm w hR (k := [cRestA3]) (ρ := ρ0) hc hs s1 s2 (hs1.trans (by rw [hz]))
        (by rw [hz2]; exact ho2) hm2 (by rw [hz]; exact hoff)
        (mk 6 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 6, _, hc, hz, hoff =>
      exact k_teile w hR (a := cSetzeA) (b := cRestA4) (k := []) hc hs
        (mk 7 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 7, _, hc, hz, hoff =>
      obtain ⟨M1, M2, M3, M4, M5, s1, s2, s3, s4, s5, o1, o2, o3, o4, ⟨sp5, log5, hz5, ho5⟩,
        hacc, hmem⟩ := gSetze (passes := passes) kHauptA .nil kHpSetzeA k30
          (.dann .nil (.ende (ruEnd kRestA))) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [lL] := by rw [hz]; exact hoff
      exact k_setze w hR 30 (by decide) ⟨30, by decide, by decide⟩ rfl (k := [cRestA4]) (ρ := ρ0)
        hc hs s1 s2 s3 s4 s5 (o1.trans h0.symm) (o2.trans h0.symm) (o3.trans h0.symm)
        (o4.trans h0.symm) (by rw [hz5]; exact ho5.trans h0.symm) hacc (by rw [hmem]; rfl)
        (mk 8 _ _ (by omega) rfl ⟨sp5, log5, hz5, ho5⟩)
  | 8, _, hc, hz, hoff =>
      exact k_teile w hR (a := cGib) (b := cPruefe) (k := []) hc hs
        (mk 9 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 9, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gGib (passes := passes) kHauptA
        .nil kRestA M t sp log hz hoff
      exact k_gib w hR (k := [cPruefe]) (ρ := ρ0) hc hs s1 s2 (by rw [hz]; exact hoff) ho1
        (by rw [hz2]; exact ho2) hm2 (mk 10 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 10, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, log2, hz2, ho2⟩, hacc, _, hm2⟩ :=
        gPruefe (passes := passes) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [] := by rw [hz]; exact hoff
      exact k_pruefe w hR (k := []) (ρ := ρ0) hc hs s1 s2 (ho1.trans h0.symm)
        (by rw [hz2]; exact ho2.trans h0.symm) hacc hm2
        (mk 11 _ _ (by omega) rfl ⟨sp2, log2, hz2, ho2⟩)
  | 11, _, hc, hz, hoff =>
      exact k_ende w hR (ρ := ρ0) hc hs (mk 12 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 12, _, hc, _, _ => exact (schrittC_aus hs hc).elim

/-- **Every C step of a `hauptB` thread is simulated.** -/
theorem schrittB (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hwt : w t = some 3) (hR : R124 w K M)
    (hs : SchrittC c124 sperrAbstrakt K t ℓ K') :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  have hB : ThreadB (K.faeden t) (M.faeden t) := by
    have := hR.2.2 t; rw [hwt] at this; exact this
  have mk : ∀ (j : Nat) (c : CFaden) (z : RufFadenG DR), j ≤ 8 → c = posB j →
      (∃ (sp' : List (Ereignis DR)) (log' : List (RufEreignisF DR)),
        z = ⟨[], frB (gOfB j), sp', log'⟩ ∧ offen sp' = heldGB (gOfB j)) →
      FadenRel (w t) c z := by
    intro j c z hj hcj ⟨sp', log', hz', ho'⟩
    rw [hwt]
    exact ⟨j, sp', log', hj, hcj, hz', ho'⟩
  obtain ⟨i, sp, log, hi, hc, hz, hoff⟩ := hB
  match i, hi, hc, hz, hoff with
  | 0, _, hc, hz, hoff =>
      exact k_teile w hR (a := cB0) (b := cRestB1) (k := []) hc hs
        (mk 1 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 1, _, hc, hz, hoff =>
      obtain ⟨M1, s1, ⟨sp1, hz1, ho1⟩, hacc, hmem⟩ := gBlatt (passes := passes) kHauptB .nil
        KTab.privB kI0 k5 rfl (kDarfB _) (.cons kLocksB (.ret .empty List.Perm.nil)) M t sp log
        (frB0_form M t sp log hz)
      exact k_store w hR KTab.privB 0 (by decide) 5 (by decide) ⟨5, by decide, by decide⟩ rfl
        (k := [cRestB1]) (ρ := ρ0) hc hs s1 hacc (by rw [hz1, hz]; exact ho1)
        (by rw [hmem]; rfl) (mk 2 _ _ (by omega) rfl ⟨sp1, log, hz1, by rw [ho1, hoff]; rfl⟩)
  | 2, _, hc, hz, hoff =>
      exact k_teile w hR (a := cNimm) (b := cRestB2) (k := []) hc hs
        (mk 3 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 3, _, hc, hz, hoff =>
      obtain ⟨_, hfrei⟩ := nimm_frei w hR (k := [cRestB2]) (ρ := ρ0) hc hs
      obtain ⟨M1, M2, s1, s2, hs1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gNimm (passes := passes) kHauptB
        .nil (.cons kRufB .nil) (.ret .empty List.Perm.nil) M t sp log hz hoff hfrei
      exact k_nimm w hR (k := [cRestB2]) (ρ := ρ0) hc hs s1 s2 (hs1.trans (by rw [hz]))
        (by rw [hz2]; exact ho2) hm2 (by rw [hz]; exact hoff)
        (mk 4 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 4, _, hc, hz, hoff =>
      exact k_teile w hR (a := cSetzeB) (b := cGib) (k := []) hc hs
        (mk 5 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 5, _, hc, hz, hoff =>
      obtain ⟨M1, M2, M3, M4, M5, s1, s2, s3, s4, s5, o1, o2, o3, o4, ⟨sp5, log5, hz5, ho5⟩,
        hacc, hmem⟩ := gSetze (passes := passes) kHauptB .nil kHpSetzeB k70
          (.dann .nil (.ende (ruEnd (V := vertragVon kD kHauptB) (l := false) (Γ := []) (Λ := [])
            (.ret .empty List.Perm.nil)))) M t sp log hz hoff
      have h0 : offen (M.faeden t).spur = [lL] := by rw [hz]; exact hoff
      exact k_setze w hR 70 (by decide) ⟨70, by decide, by decide⟩ rfl (k := [cGib]) (ρ := ρ0)
        hc hs s1 s2 s3 s4 s5 (o1.trans h0.symm) (o2.trans h0.symm) (o3.trans h0.symm)
        (o4.trans h0.symm) (by rw [hz5]; exact ho5.trans h0.symm) hacc (by rw [hmem]; rfl)
        (mk 6 _ _ (by omega) rfl ⟨sp5, log5, hz5, ho5⟩)
  | 6, _, hc, hz, hoff =>
      obtain ⟨M1, M2, s1, s2, ho1, ⟨sp2, hz2, ho2⟩, _, hm2⟩ := gGib (passes := passes) kHauptB
        .nil (.ret .empty List.Perm.nil) M t sp log hz hoff
      exact k_gib w hR (k := []) (ρ := ρ0) hc hs s1 s2 (by rw [hz]; exact hoff) ho1
        (by rw [hz2]; exact ho2) hm2 (mk 7 _ _ (by omega) rfl ⟨sp2, log, hz2, ho2⟩)
  | 7, _, hc, hz, hoff =>
      exact k_ende w hR (ρ := ρ0) hc hs (mk 8 _ _ (by omega) rfl ⟨sp, log, hz, hoff⟩)
  | 8, _, hc, _, _ => exact (schrittC_aus hs hc).elim

end Positionen
/-! ## 6. The start, the certificate, the theorem -/


