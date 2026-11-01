module

public import Grammatik.Logik.Fortschritt.Lebendigkeit
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenLauf
public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge.Teil2

@[expose] public section

namespace Gabbro.Grammatik
set_option linter.unusedVariables false

theorem lZeuge : ∃ R : PlanLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧ R.akt = lAkt ∧
    LaufzeitAnnahme R 4 ∧ Haltezeit R (fun _ => 6) (fun _ => 0) ∧ Zielsatz.HardwareImAbschnitt R ∧
    Anwaerter R (fun _ => [0, 1]) ∧ (∀ n, KeinLogikHaltG mO 0 (R.M n)) ∧
    (∀ j, 5 ≤ j → j ≤ 15 → AnSperre (R.M j) 1 ()) ∧
    (∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((R.M j).faeden 0).spur) ∧
    () ∈ offen ((R.M 16).faeden 1).spur ∧
    (∀ j u, AnSperre (R.M j) u () ↔ (u = 0 ∧ lA0 j = true) ∨ (u = 1 ∧ lA1 j = true)) := by
  obtain ⟨Ms, h0, hS, hT, hB0, hB1, hI⟩ := lLauf
  have nb0 : ∀ j, 15 ≤ j → ¬ Bereit mP mO 0 (Ms j) 0 := fun j hj => by
    have hb := hB0 j
    have e : lF0 j = true := by simp only [lF0]; exact decide_eq_true hj
    rw [e] at hb
    exact befund_nicht_bereit hb
  have nb1 : ∀ j, 23 ≤ j → ¬ Bereit mP mO 0 (Ms j) 1 := fun j hj => by
    have hb := hB1 j
    have e : lF1 j = true := by simp only [lF1]; exact decide_eq_true hj
    rw [e] at hb
    exact befund_nicht_bereit hb
  have nbI : ∀ j u, 2 ≤ u → ¬ Bereit mP mO 0 (Ms j) u := fun j u hu =>
    befund_nicht_bereit (lRuhe_j hI j u hu)
  have an1 : ∀ j, 5 ≤ j → j ≤ 15 → AnSperre (Ms j) 1 () := fun j h1 h2 =>
    (befund_an (hB1 j) ()).2 (by simp only [lA1]; exact decide_eq_true ⟨h1, h2⟩)
  have halt0 : ∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((Ms j).faeden 0).spur := fun j h1 h2 => by
    rw [(hB0 j).off]
    unfold lO0
    rw [if_pos ⟨h1, h2⟩]
    exact List.mem_singleton_self _
  -- thread 1 cannot step while thread 0 holds the lock
  have nb1h : ∀ j, 6 ≤ j → j ≤ 11 → ¬ Bereit mP mO 0 (Ms j) 1 := fun j h1 h2 =>
    nicht_bereit_an_sperre (an1 j (by omega) (by omega)) (by decide) (halt0 j h1 h2)
  let R : PlanLauf mP mO 0 :=
    { M := Ms, akt := lAkt, schritt := hS,
      stotter := fun n hn => by
        have h23 := lAkt_none hn
        refine ⟨(hT (n + 1) (by omega)).trans (hT n h23).symm, fun u => ?_⟩
        by_cases hu0 : u = 0
        · subst hu0; exact nb0 n (by omega)
        · by_cases hu1 : u = 1
          · subst hu1; exact nb1 n h23
          · exact nbI n u (faden_ge2 hu0 hu1) }
  refine ⟨R, h0, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, an1, halt0, ?_, ?_⟩
  · -- FIFO
    intro t u L a n htu hW hakt hAu
    rcases lAkt_some hakt with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · -- thread 0 takes the lock: only at step 5
      rcases lAn hB0 hB1 hI hAu with ⟨_, h3, h5⟩ | ⟨h, _⟩
      · have hn5 : n = 5 := by omega
        subst hn5
        intro j hj1 hj2
        have ha : 5 ≤ a := by
          refine Classical.byContradiction fun ha => ?_
          rcases lAn hB0 hB1 hI (hW 4 (by omega) (by omega)) with ⟨ht, _, _⟩ | ⟨_, h5', _⟩
          · exact htu ht
          · omega
        have hj : j = 5 := by omega
        subst hj
        exact hAu
      · cases h
    · -- thread 1 takes the lock: only at step 15, when nobody else waits
      rcases lAn hB0 hB1 hI hAu with ⟨h, _⟩ | ⟨_, h5, h15⟩
      · cases h
      · have hn15 : n = 15 := by omega
        subst hn15
        intro j hj1 hj2
        exfalso
        rcases lAn hB0 hB1 hI (hW 15 (by omega) (Nat.le_refl 15)) with ⟨_, _, h⟩ | ⟨ht, _, _⟩
        · omega
        · exact htu ht
  · -- fairness, window 4
    intro t n hb
    have w := lAkt_wert
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hn : n ≤ 14
      · by_cases hn2 : n ≤ 2
        · exact ⟨n, Nat.le_refl n, by omega, (w n).1 hn2⟩
        · by_cases hn4 : n ≤ 4
          · exact ⟨5, by omega, by omega, (w 5).2.2.1 (by omega) (by omega)⟩
          · exact ⟨n, Nat.le_refl n, by omega, (w n).2.2.1 (by omega) hn⟩
      · exact absurd (hb n (Nat.le_refl n) (by omega)) (nb0 n (by omega))
    · by_cases ht1 : t = 1
      · subst ht1
        by_cases hn3 : n ≤ 3
        · exact ⟨3, by omega, by omega, (w 3).2.1 (by omega) (by omega)⟩
        · by_cases hn4 : n ≤ 4
          · exact ⟨4, by omega, by omega, (w 4).2.1 (by omega) (by omega)⟩
          · by_cases hn11 : n ≤ 11
            · have hm : 6 ≤ max n 6 ∧ max n 6 ≤ 11 := by omega
              exact absurd (hb (max n 6) (by omega) (by omega)) (nb1h _ hm.1 hm.2)
            · by_cases hn14 : n ≤ 14
              · exact ⟨15, by omega, by omega, (w 15).2.2.2 (by omega) (by omega)⟩
              · by_cases hn22 : n ≤ 22
                · exact ⟨n, Nat.le_refl n, by omega, (w n).2.2.2 (by omega) hn22⟩
                · exact absurd (hb n (Nat.le_refl n) (by omega)) (nb1 n (by omega))
      · exact absurd (hb n (Nat.le_refl n) (by omega)) (nbI n t (faden_ge2 ht0 ht1))
  · -- the hold time: 6 own steps, no nested acquisition
    intro u L a n hhold
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact ⟨Nat.zero_le _, Nat.le_refl _⟩
    · have hw : ∀ i, i < n → (u = 0 ∧ 6 ≤ a + i ∧ a + i ≤ 11) ∨
          (u = 1 ∧ 16 ≤ a + i ∧ a + i ≤ 21) :=
        fun i hi => lHaelt hB0 hB1 hI (hhold i hi)
      have hn6 : n ≤ 6 := by
        rcases hw 0 hn with ⟨hu, h1, _⟩ | ⟨hu, h1, _⟩
        · rcases hw (n - 1) (by omega) with ⟨_, _, h2⟩ | ⟨hu', _, _⟩
          · omega
          · rw [hu] at hu'; exact absurd hu' (by decide)
        · rcases hw (n - 1) (by omega) with ⟨hu', _, _⟩ | ⟨_, _, h2⟩
          · rw [hu] at hu'; exact absurd hu' (by decide)
          · omega
      refine ⟨Nat.le_trans (zaehl_le _ a n) hn6, Nat.le_of_eq (zaehl_null _ a n fun i hi hp => ?_)⟩
      obtain ⟨_, L', hA⟩ := hp
      rcases lAn hB0 hB1 hI hA with ⟨hu, _, h5⟩ | ⟨hu, _, h15⟩ <;>
        rcases hw i hi with ⟨hu', h6, _⟩ | ⟨hu', h16, _⟩
      · omega
      · rw [hu] at hu'; exact absurd hu' (by decide)
      · rw [hu] at hu'; exact absurd hu' (by decide)
      · omega
  · -- no hardware stop in a critical section
    intro n u L hL k hH
    have hk := halt_kopf hH
    rcases lHaelt hB0 hB1 hI hL with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have hne : lO0 n ≠ [] := by
        intro e; rw [(hB0 n).off, e] at hL; exact List.not_mem_nil hL
      exact (hB0 n).frei hne _ _ hk
    · have hne : lO1 n ≠ [] := by
        intro e; rw [(hB1 n).off, e] at hL; exact List.not_mem_nil hL
      exact (hB1 n).frei hne _ _ hk
  · -- the contenders
    intro n u L h
    rcases h with h | h
    · rcases lHaelt hB0 hB1 hI h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases lAn hB0 hB1 hI h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
  · -- no `logik` stop, from the flagship
    intro n
    have hr : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) (R.M n) :=
      R.erreichbar (by show RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) (Ms 0); rw [h0]
                       exact .start) n
    exact (mP_zertifiziert 0 (R.M n) hr).1.1.2.2.1
  · show () ∈ offen ((Ms 16).faeden 1).spur
    rw [(hB1 16).off]
    exact List.mem_singleton_self _
  · -- who stands at `locks`, as a table (the queue of the ticket-lock witness reads it)
    intro j u
    constructor
    · intro h
      rcases lAn hB0 hB1 hI h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
      · exact Or.inl ⟨rfl, by simp only [lA0]; exact decide_eq_true ⟨h1, h2⟩⟩
      · exact Or.inr ⟨rfl, by simp only [lA1]; exact decide_eq_true ⟨h1, h2⟩⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact (befund_an (hB0 j) ()).2 h
      · exact (befund_an (hB1 j) ()).2 h

/-- The bound on the witness: `(2 - 1) * (6 * 4 + 0 * 0 + 4) + 4 = 32`. -/
theorem lW_eq : wartezeit (D := mD) [()] (fun _ => [0, 1]) (fun _ => 6) (fun _ => 0) 4 () = 32 := by
  decide

/-- **THE WAITING BOUND ON THE WITNESS** (`wartezeit_schranke`, every premise
    discharged): thread 1, standing at `locks` at step 5 (while thread 0 is
    about to hold the lock for steps 6-11), takes the lock at a step
    `j < 5 + 32` and holds it after -- BY THE THEOREM. On the concrete run it
    takes it at step 15 (`lZeuge`: `akt 15 = some 1`, held at step 16). -/
theorem wartezeit_zeuge : ∃ R : PlanLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧ LaufzeitAnnahme R 4 ∧
    Haltezeit R (fun _ => 6) (fun _ => 0) ∧ Zielsatz.HardwareImAbschnitt R ∧
    Anwaerter R (fun _ => [0, 1]) ∧
    AnSperre (R.M 5) 1 () ∧
    (∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((R.M j).faeden 0).spur) ∧
    R.akt 15 = some 1 ∧ () ∈ offen ((R.M 16).faeden 1).spur ∧
    wartezeit (D := mD) [()] (fun _ => [0, 1]) (fun _ => 6) (fun _ => 0) 4 () = 32 ∧
    ∃ j, 5 ≤ j ∧ j < 5 + 32 ∧ R.akt j = some 1 ∧ () ∈ offen ((R.M (j + 1)).faeden 1).spur := by
  obtain ⟨R, h0, hakt, hLZ, hH, hHw, hAnw, hL, an1, halt0, h16, -⟩ := lZeuge
  have hA5 : AnSperre (R.M 5) 1 () := an1 5 (Nat.le_refl 5) (by decide)
  have hB : ∀ n t, BereichG (R.M n) t := fun n =>
    bereichG_mehrfaden mP mO 0 (axWahr mD) mSI mFs mSp mInit mK mO_gut mO_lokal
      (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
      (mP_koerper_alle 0) mP_start mSI_start mInit_exklusiv (R.M n)
      (R.erreichbar (by rw [h0]; exact .start) n)
  have hW := wartezeit_schranke R mO_gut mP_stufen mSp mInit mInit_leer
    (ls := [()]) (fun L => by cases L; exact List.mem_singleton_self _)
    (by rw [h0]; exact .start) hL hB
    (fun g x hx => absurd hx (by cases g <;> exact List.not_mem_nil)) hLZ hH hHw hAnw () 1 5 hA5
  rw [lW_eq] at hW
  exact ⟨R, h0, hLZ, hH, hHw, hAnw, hA5, halt0, by rw [hakt]; rfl, h16, lW_eq, hW⟩

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lLauf
#print axioms Gabbro.Grammatik.lZeuge
#print axioms Gabbro.Grammatik.wartezeit_zeuge
