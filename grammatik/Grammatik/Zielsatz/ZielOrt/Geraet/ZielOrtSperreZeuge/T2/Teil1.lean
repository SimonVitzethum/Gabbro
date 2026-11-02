module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T2.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T2.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1

@[expose] public section



namespace Gabbro.Grammatik
theorem shgL {s : List (Ereignis sD)} (h : offen s = [()]) : HeldGenau sL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem shg0 {s : List (Ereignis sD)} (h : offen s = []) :
    HeldGenau ([] : List (Res sD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem soff_z {M : RufMaschineG sD} {f : Faden} {stapel : List (RufRahmenG sD)} {fn : sD.Fn}
    {rho : Env sD (sD.params fn)} {s0 : World sD} {log : List (RufEreignisF sD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res sD)} {ρ : Env sD Γ} {r : GRest sD (vertragVon sD fn) l Γ Λ}
    {σ : World sD} {x : List sD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem soff_g {M : RufMaschineG sD} {f : Faden} {caller : RufRahmenG sD}
    {rst : List (RufRahmenG sD)} {fn : sD.Fn} {rho : Env sD (sD.params fn)} {s0 : World sD}
    {log : List (RufEreignisF sD)} {v : ErgVal sD (sD.erg fn)} {σ : World sD} {x : List sD.Lock}
    (h : GepopptG M f caller rst fn rho s0 log v σ) (ho : offen (M.faeden f).spur = x) :
    offen σ.spur = x := by
  rw [h.1] at ho; exact ho

/-- The `locks` statement of `haupt`. -/
def sLocks : Stmt sD (vertragVon sD sHaupt) false [.int 0 100] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons sRuf .nil)

def sHauptRet : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] := .ret .empty List.Perm.nil

/-- **One critical section of a thread `t` running `haupt(x)`**: eight
    steps from its start state -- take the lock, call `setze(x)`, both
    writes, return, release. Nothing else moves. -/
theorem sAbschnitt {M : RufMaschineG sD} (hr : RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M)
    (t : Faden) (x : Env sD [.int 0 100]) (hz : M.faeden t = sZ0 x)
    (hfrei : RufFreiG M t ()) :
    ∃ M' : RufMaschineG sD, RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M' ∧
      (∀ u, u ≠ t → M'.faeden u = M.faeden u) ∧ offen (M'.faeden t).spur = [] ∧
      (M'.speicher.slots () 0 ()).n = (x.get .here).n ∧
      (M'.speicher.slots () 1 ()).n = (x.get .here).n ∧
      (∃ s0 : World sD, RufEreignisF.eintritt sSetze (Env.cons (x.get .here) .nil) s0 ∈
          (M'.faeden t).log ∧ s0.speicher = M.speicher) ∧
      (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
          RufEreignisF.rueck sSetze (Env.cons (x.get .here) .nil) v s0 s1 ∈ (M'.faeden t).log ∧
          (s1.slots () 0 ()).n = (x.get .here).n) := by
  have hoff0 : offen (M.faeden t).spur = [] := by rw [hz]; rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := sP) (O := sO) (passes := 0) hz sLocks sHauptRet
    x rfl rfl
  have hfrei1 : RufFreiG M1 t () := by
    intro u hu
    rw [rufSchrittG_fremd s1 u hu]
    exact hfrei u hu
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := sP) (O := sO) (passes := 0) hZ1.1 ()
    _ _ _ _ x rfl (shg0 (by show offen (M.faeden t).spur = []; exact hoff0)) hfrei1
  have hoff2 : offen (M2.faeden t).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon t).spur) :: (M1.weltVon t).spur) = [()]
    simp only [offen]
    rw [sOffen_weltVon, hZ1.spur, sOffen_weltVon, hoff0]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := sP) (O := sO) (passes := 0) hZ2.1 sSetze
    (.cons (.var .here) .nil) sHp rfl .nil _ x rfl (shgL (soff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden t).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := sP) (O := sO) (passes := 0) hZ3.1
    _ _ _ rfl rfl (shgL (soff_z hZ3 hoff3)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden t).spur = [()] := by
    rw [hZ4.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := sP) (O := sO) (passes := 0) hZ4.1
    _ _ _ rfl rfl (shgL (soff_z hZ4 hoff4)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden t).spur = [()] := by
    rw [hZ5.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := sP) (O := sO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (shgL (soff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden t).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_dannLeer (P := sP) (O := sO) (passes := 0) hG6.1 _ _ rfl
  obtain ⟨M8, s8, hZ8⟩ := w_freiGib (P := sP) (O := sO) (passes := 0) hZ7.1 () _ _ rfl
  have hr8 : RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ hr s1) s2) s3) s4) s5) s6) s7) s8
  have hfremd : ∀ u, u ≠ t → M8.faeden u = M.faeden u := by
    intro u hu
    rw [rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu, rufSchrittG_fremd s6 u hu,
      rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu, rufSchrittG_fremd s3 u hu,
      rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu]
  have e8 : M8.speicher = M6.speicher := by
    rw [hZ8.2]
    show M7.speicher = M6.speicher
    rw [hZ7.2]
    rfl
  have e6 : M6.speicher = M5.speicher := by rw [hG6.2]; rfl
  have e3 : M3.speicher = M.speicher := by
    rw [hZ3.2]
    show M2.speicher = M.speicher
    rw [hZ2.2]
    show M1.speicher = M.speicher
    rw [hZ1.2]
    rfl
  refine ⟨M8, hr8, hfremd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hZ8.spur]
    show (offen (M7.weltVon t).spur).erase () = []
    show (offen (M7.faeden t).spur).erase () = []
    rw [hZ7.spur]
    show (offen (M6.faeden t).spur).erase () = []
    rw [hoff6]
    rfl
  · rw [e8, e6]
    have e54 : M5.speicher.slots () 0 () = M4.speicher.slots () 0 () := by rw [hZ5.2]; rfl
    rw [e54, hZ4.2]
    rfl
  · rw [e8, e6, hZ5.2]
    rfl
  · refine ⟨(M2.weltVon t).lese sL [], ?_, ?_⟩
    · rw [hZ8.1]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · show M2.speicher = M.speicher
      rw [hZ2.2]
      show M1.speicher = M.speicher
      rw [hZ1.2]
      rfl
  · refine ⟨(), (M2.weltVon t).lese sL [], (M5.weltVon t).lese sL [], ?_, ?_⟩
    · rw [hZ8.1]
      exact List.mem_cons_self
    · show (M5.speicher.slots () 0 ()).n = _
      have e54 : M5.speicher.slots () 0 () = M4.speicher.slots () 0 () := by rw [hZ5.2]; rfl
      rw [e54, hZ4.2]
      rfl

/-- **`ziel_ort_sperre_zeuge` -- TWO THREADS WRITE THE SAME TABLE UNDER ONE
    LOCK, and the contracts that depend on the lock invariant hold where
    they are claimed.** Every premise of `ziel_ort_sperre` holds on `sP`
    (`sP_zertifiziert`). On a reached run of sixteen steps thread 0
    (`haupt(30)`) takes the lock, `setze(30)` writes both slots, releases;
    then thread 1 (`haupt(70)`, the SAME routine) takes the lock and enters
    `setze(70)` at a world holding what thread 0 wrote (`30`, `30`) -- and
    `setze`'s `requires konto[0] == konto[1]` holds there, BY THE THEOREM
    (thread 1's own proof of it came from the invariant at the acquire);
    `setze(70)` returns with its `ensures` (`70`, `70`), BY THE THEOREM; at
    the end no thread holds the lock and its invariant holds in memory, BY
    THE THEOREM. -/
theorem ziel_ort_sperre_zeuge : ∃ M M' : RufMaschineG sD,
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M ∧
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M' ∧
    (sSp.slots () 0 ()).n = 0 ∧
    (M.speicher.slots () 0 ()).n = 30 ∧ (M.speicher.slots () 1 ()).n = 30 ∧
    (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
      RufEreignisF.rueck sSetze (sWert 30 (by decide) (by decide)) v s0 s1 ∈ (M'.faeden 0).log) ∧
    (∃ s0 : World sD,
      RufEreignisF.eintritt sSetze (sWert 70 (by decide) (by decide)) s0 ∈ (M'.faeden 1).log ∧
      (s0.slots () 0 ()).n = 30 ∧ (s0.slots () 1 ()).n = 30 ∧
      ReqAmEintritt sP sSetze s0 (sWert 70 (by decide) (by decide))) ∧
    (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
      RufEreignisF.rueck sSetze (sWert 70 (by decide) (by decide)) v s0 s1 ∈ (M'.faeden 1).log ∧
      EnsAmRueck sP sSetze s0 s1 (sWert 70 (by decide) (by decide)) v ∧ (s1.slots () 0 ()).n = 70) ∧
    (∀ t : Faden, (() : sD.Lock) ∉ offen (M'.faeden t).spur) ∧ sS.inv () M'.speicher = true := by
  have hfrei0 : RufFreiG (RufStartG sP sSp sInit) 0 () := fun u _ h => by
    rw [sM0_offen u] at h
    exact List.not_mem_nil h
  obtain ⟨M, hrM, hfremdM, hoffM, h0M, h1M, _, ⟨v0, a0, b0, hr0, _⟩⟩ :=
    sAbschnitt .start 0 _ sM0_faden0 hfrei0
  have hz1 : M.faeden 1 = sZ0 (sWert 70 (by decide) (by decide)) := by
    rw [hfremdM 1 (by decide)]
    exact sM0_faden 1 (by decide)
  have hfrei1 : RufFreiG M 1 () := by
    intro u hu h
    by_cases hu0 : u = 0
    · subst hu0
      rw [hoffM] at h
      exact List.not_mem_nil h
    · rw [hfremdM u hu0, sM0_offen u] at h
      exact List.not_mem_nil h
  obtain ⟨M', hrM', hfremdM', hoffM', _, _, ⟨s0, hent, hs0⟩, ⟨v1, c0, c1, hr1, hc1⟩⟩ :=
    sAbschnitt hrM 1 _ hz1 hfrei1
  have hZ := sP_zertifiziert M' hrM'
  have hreq := (hZ.1 1 _ hent).1 _ _ _ rfl
  have hens := (hZ.1 1 _ hr1).2 _ _ _ _ _ rfl
  have hfreiE : ∀ t : Faden, (() : sD.Lock) ∉ offen (M'.faeden t).spur := by
    intro t h
    by_cases ht1 : t = 1
    · subst ht1
      rw [hoffM'] at h
      exact List.not_mem_nil h
    · rw [hfremdM' t ht1] at h
      by_cases ht0 : t = 0
      · subst ht0
        rw [hoffM] at h
        exact List.not_mem_nil h
      · rw [hfremdM t ht0, sM0_offen t] at h
        exact List.not_mem_nil h
  refine ⟨M, M', hrM, hrM', rfl, h0M, h1M, ⟨v0, a0, b0, ?_⟩, ⟨s0, hent, ?_, ?_, hreq⟩,
    ⟨v1, c0, c1, hr1, hens, hc1⟩, hfreiE, hZ.2.1 () hfreiE⟩
  · rw [hfremdM' 0 (by decide)]
    exact hr0
  · show (s0.speicher.slots () 0 ()).n = 30
    rw [hs0]
    exact h0M
  · show (s0.speicher.slots () 1 ()).n = 30
    rw [hs0]
    exact h1M

/-! ## 5. Corpus 104 through the new theorem; probe A -/

end Gabbro.Grammatik
