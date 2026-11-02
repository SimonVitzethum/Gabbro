module
public import Grammatik.Logik.Terminierung.Rekursion.Teil1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 5. One step -/

section Schritt

variable {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (m : Mass D)
  (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

theorem schluessel_kopf {a b : RufFadenG D}
    (h : RufFadenSchluesselG a = RufFadenSchluesselG b) : RufSchluesselG a.kopf = RufSchluesselG b.kopf := by
  unfold RufFadenSchluesselG at h
  simp only [List.map_cons, List.cons.injEq] at h
  exact h.1

theorem gew_fst {r r' : RufRahmenG D} (hk : RufSchluesselG r' = RufSchluesselG r) :
    (gew pa m rk r').1 = (gew pa m rk r).1 := by
  unfold gew
  rw [hk]

theorem wlt_pot {a b : Gewicht} (h1 : a.1 = b.1) (h2 : a.2 < b.2) : wlt a b :=
  Or.inr ⟨congrArg (·.1) h1, Or.inr ⟨congrArg (·.2) h1, h2⟩⟩

/-- **An own step of a GX run lowers the thread's rank and keeps its static facts.** -/
theorem schritt_rang (hvoll : ∀ g, g ∈ fs)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    {M M' : RufMaschineG D} {t : Faden} (hP0 : RufMaschinePasstG M) (hP1 : RufMaschinePasstG M')
    (hs : RufSchrittGX P O pa Tg M t M')
    (hG : Glieder zyk rk fs (M.faeden t).kopf (M.faeden t).stapel) :
    slt (rangF pa m rk (M'.faeden t)) (rangF pa m rk (M.faeden t)) ∧
      Glieder zyk rk fs (M'.faeden t).kopf (M'.faeden t).stapel := by
  have hk := Zielsatz.schritt_schluesselX hP0 hP1 hs
  obtain ⟨σ, M'', hg, _, _, _, hfa, _, _⟩ := hs
  have hfa' : M'.faeden t = M''.faeden t := by rw [hfa]
  have hfm : (mitSpeicher M σ).faeden t = M.faeden t := rfl
  have hlen : ∀ z : RufFadenG D, (RufFadenSchluesselG z).length = z.stapel.length + 1 := by
    intro z; simp only [RufFadenSchluesselG, List.map_cons, List.length_cons, List.length_map, Nat.add_left_cancel_iff]
  rcases schrittArt hg (fun _ => 0) (tor zyk rk (M.faeden t).kopf.f) (torS zyk rk fs (M.faeden t).kopf.f) true with
    ⟨hst, hpot⟩ | ⟨g, caller', rho, s0, hst, hkopf, hpush⟩ | ⟨caller, rst, hst, hst', hpop⟩
  · -- the head steps: same stack, same key, lower potential
    rw [hfm, ← hfa'] at hst hpot
    obtain ⟨hok', hlt⟩ := hpot (glieder_kopf zyk rk fs hG)
    have hkey : RufSchluesselG (M'.faeden t).kopf = RufSchluesselG (M.faeden t).kopf := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exact schluessel_kopf he
      all_goals
        exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
    have hf : (M'.faeden t).kopf.f = (M.faeden t).kopf.f := congrArg Sigma.fst hkey
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst]
      simp only [List.map_cons, List.reverse_cons]
      apply slt_praefix
      exact Or.inl (wlt_pot (gew_fst m rk hkey) (by dsimp only [gew]; omega))
    · rw [hst]
      exact glieder_ersetze zyk rk fs hG hf hok'
  · -- a call: the caller's potential falls, the callee sits above it
    rw [hfm, ← hfa'] at hst
    rw [← hfa'] at hkopf
    rw [hfm] at hpush
    obtain ⟨hokc, hdir⟩ := hpush (glieder_kopf zyk rk fs hG)
    have hzg : tor zyk rk (M.faeden t).kopf.f g = true := by
      rcases hdir with ⟨hz, _⟩ | ⟨n, hn, hp, _⟩
      · exact hz
      · exact torS_tor zyk rk fs hvoll hn hp
    have hlt : potRest (fun _ => 0) pa caller'.rest.2.2.2.2 + 1 ≤
        potRest (fun _ => 0) pa (M.faeden t).kopf.rest.2.2.2.2 := by
      rcases hdir with ⟨_, h⟩ | ⟨_, _, _, h⟩
      · simp only [Nat.add_zero] at h; omega
      · exact h
    have hkey : RufSchluesselG caller' = RufSchluesselG (M.faeden t).kopf := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
      · unfold RufFadenSchluesselG at he
        rw [hst] at he
        simp only [List.map_cons, List.cons.injEq] at he
        exact he.2.1
      all_goals
        exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
    have hcf : caller'.f = (M.faeden t).kopf.f := congrArg Sigma.fst hkey
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      apply slt_praefix
      exact Or.inl (wlt_pot (gew_fst m rk hkey) (by dsimp only [gew]; omega))
    · rw [hst, hkopf]
      refine ⟨hR g, ?_, glieder_ersetze zyk rk fs hG hcf hokc⟩
      show tor zyk rk caller'.f g = true
      rw [hcf]; exact hzg
  · -- a return: the head goes, the caller stays at most where it was
    rw [hfm] at hst
    rw [← hfa'] at hst' hpop
    obtain ⟨hgate, hle⟩ := hpop (fun _ => 0) (tor zyk rk caller.f) (torS zyk rk fs caller.f) true
    have hkey : RufSchluesselG (M'.faeden t).kopf = RufSchluesselG caller := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst, hst'] at this
        omega
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst, hst'] at this
        omega
      all_goals
        unfold RufFadenSchluesselG at he
        rw [hst, hst'] at he
        simp only [List.map_cons, List.cons.injEq] at he
        exact he.2.1.symm
    have hf : (M'.faeden t).kopf.f = caller.f := congrArg Sigma.fst hkey
    rw [hst] at hG
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst, hst']
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      apply slt_praefix
      by_cases hp : potRest (fun _ => 0) pa (M'.faeden t).kopf.rest.2.2.2.2 <
          potRest (fun _ => 0) pa caller.rest.2.2.2.2
      · exact Or.inl (wlt_pot (gew_fst m rk hkey) hp)
      · refine Or.inr ⟨Prod.ext (gew_fst m rk hkey) (by dsimp only [gew]; omega), trivial⟩
    · rw [hst']
      exact glieder_ersetze zyk rk fs hG.2.2 hf (hgate (glieder_kopf zyk rk fs hG.2.2))

end Schritt

/-! ## 6. Runs -/

/-- The replay carries the measure's fall along every stack. -/
theorem stapelSA_massFaellt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (lok : D.Tab ⊕ D.Glob → Bool) (Tg : D.Tab ⊕ D.Glob → Prop) (m : Mass D) (zyk : D.Fn → D.Fn → Bool) :
    ∀ (G : Σ f : D.Fn, Env D (D.params f) × World D) (st : List (RufRahmenG D)),
      StapelSA P O passes Q S lok Tg m zyk G st → MassFaellt m zyk G st
  | _, [], _ => trivial
  | _, _ :: rest, ⟨hw, hr⟩ => by
      refine ⟨?_, stapelSA_massFaellt P O passes Q S lok Tg m zyk _ rest hr⟩
      obtain ⟨_, _, _, _, κ, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hz, _⟩ := hw
      exact ⟨κ, hz⟩

section Lauf

variable {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (m : Mass D)
  (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

/-- **T4 -- MEASURED RECURSION TERMINATES.** For a program whose every body calls only through the gate (a lower
    rank, or the caller's cycle at the same rank; no indirect call) and whose measures have one length along a
    cycle, on every infinite GX run from the start on which the goal's replay holds (with the measure), every
    thread takes only finitely many steps. -/
theorem rekursion_endlich (Q : AxEns D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool)
    (hvoll : ∀ g, g ∈ fs) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hInv : ∀ M, RufErreichbarGX P O pa Tg (RufStartG P sp init) M → ZielInvSA P O pa Q S lok Tg m zyk M)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t := by
  have hre := R.erreichbar h0
  have hP : ∀ j, RufMaschinePasstG (R.M j) := fun j => Zielsatz.gx_passt hTA sp init (hre j)
  have hGl : ∀ j, Glieder zyk rk fs ((R.M j).faeden t).kopf ((R.M j).faeden t).stapel := by
    intro j
    induction j with
    | zero =>
      rw [h0]
      rcases hi : init t with ⟨g, rho⟩
      unfold RufStartG
      dsimp only
      rw [hi]
      exact hR g
    | succ j ih =>
      cases h : R.akt j with
      | none => rw [R.stotter j h]; exact ih
      | some u =>
        by_cases htu : t = u
        · subst htu
          exact (schritt_rang m zyk rk fs hvoll hR (hP j) (hP (j + 1)) (R.schritt j t h) ih).2
        · rw [Zielsatz.gx_fremd (R.schritt j u h) t htu]; exact ih
  have hK : ∀ j, KetteW (rangF pa m rk ((R.M j).faeden t)) := fun j =>
    ketteT_reverse _ (kette_aus pa m zyk rk fs hL _ _ (hGl j)
      (stapelSA_massFaellt P O pa Q S lok Tg m zyk _ _ ((hInv _ (hre j)).1 t).2))
  obtain ⟨N, hN⟩ := endlich_aus_wf sltK (fun j => rangF pa m rk ((R.M j).faeden t))
    (fun j => R.akt j = some t) (fun j => acc_sltK _ (hK j))
    (fun j h => ⟨hK (j + 1), (schritt_rang m zyk rk fs hvoll hR (hP j) (hP (j + 1)) (R.schritt j t h) (hGl j)).1⟩)
    (fun j h => by
      cases ha : R.akt j with
      | none => show rangF pa m rk ((R.M (j + 1)).faeden t) = _; rw [R.stotter j ha]
      | some u =>
        have htu : t ≠ u := fun e => h (e ▸ ha)
        show rangF pa m rk ((R.M (j + 1)).faeden t) = _
        rw [Zielsatz.gx_fremd (R.schritt j u ha) t htu])
  exact ⟨N, hN⟩

end Lauf
end Gabbro.Grammatik
