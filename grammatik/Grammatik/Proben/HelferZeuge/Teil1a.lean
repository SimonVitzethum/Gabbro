module
public import Grammatik.Proben.HelferZeuge.Teil1
@[expose] public section

namespace Gabbro.Grammatik

/-! ## 4. The run: the helper under a lock and without one -/

theorem ntM0_faden0 : (RufStartG ntP ntSp ntInit).faeden 0 =
    ⟨[], ⟨ntSetze, .nil, ntSp.welt [], ⟨false, [], [], .nil, .ende ntRumpfSetze⟩⟩, [],
      [RufEreignisF.eintritt ntSetze .nil (ntSp.welt [])]⟩ := by rfl

theorem ntM0_faden1 : (RufStartG ntP ntSp ntInit).faeden 1 =
    ⟨[], ⟨ntFrei, .nil, ntSp.welt [], ⟨false, [], [], .nil, .ende ntRumpfFrei⟩⟩, [],
      [RufEreignisF.eintritt ntFrei .nil (ntSp.welt [])]⟩ := by rfl

theorem ntM0_offen (t : Faden) : offen ((RufStartG ntP ntSp ntInit).faeden t).spur = [] := by
  by_cases ht : t = 0
  · subst ht; rfl
  · show offen (match ntInit t with
      | ⟨g, _⟩ => startSpur g) = []
    rw [ntInit_sonst ht]; rfl

theorem ntHeld0 {s : List (Ereignis ntD)} : HeldIn ([] : List (Res ntD)) (offen s) :=
  fun _ h => nomatch h

/-- **`helfer_zeuge` -- one helper, two held sets, both contracts BY THE
    THEOREM.** On a reached machine: thread 0 (`setze`) took the lock `L`,
    called `helfer(5)` inside the `locks` block and returned; at that return
    `L` was held by thread 0 while `helfer`'s frame named no lock; thread 1
    (`frei`) called `helfer(3)` holding nothing and returned. Both logged
    returns meet `helfer`'s `ensures result == x` -- the values `5` and `3`
    -- by `ntP_zertifiziert`. -/
theorem helfer_zeuge : ∃ M : RufMaschineG ntD,
    RufErreichbarG ntP ntO 0 (RufStartG ntP ntSp ntInit) M ∧
    (∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (s0 s1 : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨5, by decide, by decide⟩ .nil) v s0 s1 ∈ (M.faeden 0).log ∧
      () ∈ offen s1.spur ∧
      EnsAmRueck ntP ntHelfer s0 s1 (.cons ⟨5, by decide, by decide⟩ .nil) v ∧ v.n = 5) ∧
    (∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (s0 s1 : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨3, by decide, by decide⟩ .nil) v s0 s1 ∈ (M.faeden 1).log ∧
      offen s1.spur = [] ∧
      EnsAmRueck ntP ntHelfer s0 s1 (.cons ⟨3, by decide, by decide⟩ .nil) v ∧ v.n = 3) := by
  -- thread 0: unfold `locks`, take `L`, call `helfer(5)`, return
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := ntP) (O := ntO) (passes := 0) ntM0_faden0 ntLocks
    ntSetzeRet .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := ntP) (O := ntO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl
    (fun L => by
      cases L
      constructor
      · intro h; exact nomatch h
      · intro h; exact absurd h List.not_mem_nil)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, ntM0_offen] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 0).spur) :: (M1.weltVon 0).spur) = [()]
    simp only [offen]
    show () :: offen (M1.faeden 0).spur = [()]
    rw [hZ1.spur]
    show () :: offen ((RufStartG ntP ntSp ntInit).faeden 0).spur = [()]
    rw [ntM0_offen]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := ntP) (O := ntO) (passes := 0) hZ2.1 ntHelfer
    (ntArg 5 (by decide) (by decide)) ntHpSetze rfl .nil _ .nil rfl
    (fun L _ => by
      cases L
      have h := hoff2
      rw [hZ2.1] at h
      rw [h]
      exact List.mem_cons_self)
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := ntP) (O := ntO) (passes := 0) hZ3.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl ntHeld0
  -- thread 1: call `helfer(3)` holding nothing, return
  have h41 : M4.faeden 1 = (RufStartG ntP ntSp ntInit).faeden 1 := by
    rw [rufSchrittG_fremd s4 1 (by decide), rufSchrittG_fremd s3 1 (by decide),
      rufSchrittG_fremd s2 1 (by decide), rufSchrittG_fremd s1 1 (by decide)]
  obtain ⟨M5, s5, hZ5⟩ := w_rufEnde (P := ntP) (O := ntO) (passes := 0) (h41.trans ntM0_faden1)
    ntHelfer (ntArg 3 (by decide) (by decide)) ntHpFrei rfl (.ret .empty List.Perm.nil) .nil rfl ntHeld0
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := ntP) (O := ntO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl ntHeld0
  have hr6 : RufErreichbarG ntP ntO 0 (RufStartG ntP ntSp ntInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6
  have hZ := ntP_zertifiziert M6 hr6
  have h60 : M6.faeden 0 = M4.faeden 0 := by
    rw [rufSchrittG_fremd s6 0 (by decide), rufSchrittG_fremd s5 0 (by decide)]
  obtain ⟨v0, a0, b0, hm0, hb0⟩ : ∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (a b : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨5, by decide, by decide⟩ .nil) v a b ∈ (M6.faeden 0).log ∧
      offen b.spur = [()] := by
    rw [h60, hG4.1]
    exact ⟨_, _, _, List.mem_cons_self, ((Erw.lese _ _ _).offen).trans hoff3⟩
  obtain ⟨v1, a1, b1, hm1, hb1⟩ : ∃ (v : ErgVal ntD (ntD.erg ntHelfer)) (a b : World ntD),
      RufEreignisF.rueck ntHelfer (.cons ⟨3, by decide, by decide⟩ .nil) v a b ∈ (M6.faeden 1).log ∧
      offen b.spur = [] := by
    rw [hG6.1]
    refine ⟨_, _, _, List.mem_cons_self, ?_⟩
    rw [(Erw.lese _ _ _).offen]
    show offen (M5.faeden 1).spur = []
    rw [hZ5.spur, (Erw.lese _ _ _).offen]
    show offen (M4.faeden 1).spur = []
    rw [h41, ntM0_offen]
  have hEns0 := (hZ.1 0 _ hm0).2 _ _ _ _ _ rfl
  have hEns1 := (hZ.1 1 _ hm1).2 _ _ _ _ _ rfl
  have hv0 : v0.n = 5 := of_decide_eq_true hEns0
  have hv1 : v1.n = 3 := of_decide_eq_true hEns1
  exact ⟨M6, hr6, ⟨v0, a0, b0, hm0, by rw [hb0]; exact List.mem_cons_self, hEns0, hv0⟩,
    ⟨v1, a1, b1, hm1, hb1, hEns1, hv1⟩⟩

end Gabbro.Grammatik
