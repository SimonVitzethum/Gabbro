module

public import Grammatik.Logik.Fortschritt.Lebendigkeit.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Kern

variable {P : Programm D} {O : Orakel D} {passes : Nat} (R : PlanLauf P O passes)

theorem PlanLauf.fremd (n : Nat) (u : Faden) (h : R.akt n ≠ some u) :
    (R.M (n + 1)).faeden u = (R.M n).faeden u := by
  cases ha : R.akt n with
  | none => rw [(R.stotter n ha).1]
  | some v =>
      have hvu : u ≠ v := fun e => h (by rw [ha, e])
      exact rufSchrittG_fremd (R.schritt n v ha) u hvu

theorem PlanLauf.stet {u : Faden} {m : Nat} :
    ∀ d, (∀ i, m ≤ i → i < m + d → R.akt i ≠ some u) →
      (R.M (m + d)).faeden u = (R.M m).faeden u
  | 0, _ => rfl
  | d + 1, h => by
      show (R.M (m + d + 1)).faeden u = _
      rw [R.fremd (m + d) u (h (m + d) (by omega) (by omega))]
      exact PlanLauf.stet d (fun i h1 h2 => h i h1 (by omega))

theorem PlanLauf.stet' {u : Faden} {m j : Nat} (hmj : m ≤ j)
    (h : ∀ i, m ≤ i → i < j → R.akt i ≠ some u) :
    (R.M j).faeden u = (R.M m).faeden u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmj
  exact R.stet d h

theorem PlanLauf.erreichbar {M0 : RufMaschineG D} (h0 : RufErreichbarG P O passes M0 (R.M 0)) :
    ∀ n, RufErreichbarG P O passes M0 (R.M n)
  | 0 => h0
  | n + 1 => by
      cases ha : R.akt n with
      | none => rw [(R.stotter n ha).1]; exact PlanLauf.erreichbar h0 n
      | some u => exact .schritt _ _ u (PlanLauf.erreichbar h0 n) (R.schritt n u ha)

variable {ls : List D.Lock} {Ts : D.Lock → List Faden} {h k : D.Lock → Nat} {F : Nat}

/-! ## 7. The core -/

section Beweis

variable (hO : GutO O) (hls : ∀ L : D.Lock, L ∈ ls)
  (hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t))
  (hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
    L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur)
  (hFifo : FifoSperre R) (hFair : FairF R F) (hH : Haltezeit R h k)
  (hAkt : AbschnittAktiv R) (hAnw : Anwaerter R Ts)

include hRang in
theorem an_sperre_frei {n : Nat} {t : Faden} {L : D.Lock} (hA : AnSperre (R.M n) t L) :
    L ∉ offen ((R.M n).faeden t).spur := by
  obtain ⟨w, hw⟩ := hRang n t
  exact (sperre_rang hw hA).1

include hRang in
theorem innen_hoeher {n : Nat} {t : Faden} {L L' : D.Lock}
    (hL : L ∈ offen ((R.M n).faeden t).spur) (hA : AnSperre (R.M n) t L') :
    D.rang L < D.rang L' := by
  obtain ⟨w, hw⟩ := hRang n t
  exact (sperre_rang hw hA).2 L hL

/-- The first own step of `u` in a window, with `u`'s state frozen up to it. -/
theorem erster_schritt {u : Faden} {m B : Nat}
    (h : ∃ j, m ≤ j ∧ j < m + B ∧ R.akt j = some u) :
    ∃ j, m ≤ j ∧ j < m + B ∧ R.akt j = some u ∧
      ∀ i, m ≤ i → i ≤ j → (R.M i).faeden u = (R.M m).faeden u := by
  obtain ⟨j, h1, h2, h3, h4⟩ := erster (fun j => R.akt j = some u) m B h
  exact ⟨j, h1, h2, h3, fun i hi1 hi2 =>
    R.stet' hi1 (fun i' h1' h2' => h4 i' h1' (by omega))⟩

include hRang hFair hAkt in
/-- **The gap before the holder's next own step.** A thread holding a lock
    takes its next step within `F` scheduler steps -- or, if it stands at a
    `locks L'` head (then `L'` ranks above every lock it holds), within the
    waiting bound `G` of the locks ranking above `L`. -/
theorem luecke {G : Nat} {L : D.Lock}
    (hV : ∀ L', D.rang L < D.rang L' → ∀ t n, AnSperre (R.M n) t L' →
      ∃ j, n ≤ j ∧ j < n + G ∧ R.akt j = some t)
    {u : Faden} {m : Nat} (hm : L ∈ offen ((R.M m).faeden u).spur) :
    ∃ j, m ≤ j ∧ R.akt j = some u ∧
      (∀ i, m ≤ i → i ≤ j → (R.M i).faeden u = (R.M m).faeden u) ∧
      ((∃ L', AnSperre (R.M m) u L') → j < m + G) ∧
      ((¬ ∃ L', AnSperre (R.M m) u L') → j < m + F) := by
  by_cases hA : ∃ L', AnSperre (R.M m) u L'
  · obtain ⟨L', hA'⟩ := hA
    have hr := innen_hoeher R hRang hm hA'
    obtain ⟨j, h1, h2, h3, h4⟩ := erster_schritt R (hV L' hr u m hA')
    exact ⟨j, h1, h3, h4, fun _ => h2, fun hn => absurd ⟨L', hA'⟩ hn⟩
  · have hex : ∃ j, m ≤ j ∧ j < m + F ∧ R.akt j = some u := by
      refine Classical.byContradiction fun hne => ?_
      have hst : ∀ j, m ≤ j → j < m + F → (R.M j).faeden u = (R.M m).faeden u :=
        fun j h1 h2 => R.stet' h1 (fun i hi1 hi2 he => hne ⟨i, hi1, by omega, he⟩)
      obtain ⟨j, h1, h2, h3⟩ := hFair u m fun j h1 h2 => by
        have e := hst j h1 h2
        have hmj : L ∈ offen ((R.M j).faeden u).spur := by rw [e]; exact hm
        rcases hAkt j u L hmj with hb | ⟨L', hA'⟩
        · exact hb
        · exact absurd ⟨L', anSperre_gleich e.symm hA'⟩ hA
      exact hne ⟨j, h1, h2, h3⟩
    obtain ⟨j, h1, h2, h3, h4⟩ := erster_schritt R hex
    exact ⟨j, h1, h3, h4, fun hn => absurd hn hA, fun _ => h2⟩

include hRang hFair hAkt in
/-- **The release.** A thread holding `L` at `m` with a remaining budget of
    `h'` own steps, `k'` of them nested acquisitions, releases `L` at a step
    `e < m + h' * F + k' * G`, holding it until then. -/
theorem freigabe {G : Nat} {L : D.Lock}
    (hV : ∀ L', D.rang L < D.rang L' → ∀ t n, AnSperre (R.M n) t L' →
      ∃ j, n ≤ j ∧ j < n + G ∧ R.akt j = some t)
    (u : Faden) :
    ∀ (h' k' m : Nat), L ∈ offen ((R.M m).faeden u).spur →
      (∀ n, (∀ i, i < n → L ∈ offen ((R.M (m + i)).faeden u).spur) →
        zaehl (fun j => R.akt j = some u) m n ≤ h' ∧
        zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') m n ≤ k') →
      ∃ e, m ≤ e ∧ e < m + (h' * F + k' * G) ∧ R.akt e = some u ∧
        (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
        L ∉ offen ((R.M (e + 1)).faeden u).spur := by
  intro h'
  induction h' with
  | zero =>
      intro k' m hm hB
      obtain ⟨j, h1, h2, h3, _, _⟩ := luecke R hRang hFair hAkt hV hm
      have hhold : ∀ i, i < j + 1 - m → L ∈ offen ((R.M (m + i)).faeden u).spur := by
        intro i hi
        rw [h3 (m + i) (by omega) (by omega)]; exact hm
      have hc := (hB (j + 1 - m) hhold).1
      have hp := zaehl_pos (fun j => R.akt j = some u) m (j + 1 - m) (j - m) (by omega)
        (by show R.akt (m + (j - m)) = some u; rw [show m + (j - m) = j by omega]; exact h2)
      omega
  | succ h' ih =>
      intro k' m hm hB
      obtain ⟨j, h1, h2, h3, hG, hFF⟩ := luecke R hRang hFair hAkt hV hm
      have hhold : ∀ i, i < j + 1 - m → L ∈ offen ((R.M (m + i)).faeden u).spur := by
        intro i hi
        rw [h3 (m + i) (by omega) (by omega)]; exact hm
      have hpj : ∀ i, m ≤ i → i ≤ j → L ∈ offen ((R.M i).faeden u).spur := by
        intro i hi1 hi2; rw [h3 i hi1 hi2]; exact hm
      have e1 : m + (j + 1 - m) = j + 1 := by omega
      -- the step `j` counts once, and once more as an acquisition if `u` stands at `locks`
      have hp1 : 1 ≤ zaehl (fun j => R.akt j = some u) m (j + 1 - m) :=
        zaehl_pos _ m (j + 1 - m) (j - m) (by omega)
          (by show R.akt (m + (j - m)) = some u; rw [show m + (j - m) = j by omega]; exact h2)
      have hmul : (h' + 1) * F = h' * F + F := Nat.succ_mul h' F
      by_cases hA : ∃ L', AnSperre (R.M m) u L'
      · have hjG := hG hA
        have hp2 : 1 ≤ zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') m
            (j + 1 - m) := by
          obtain ⟨L', hA'⟩ := hA
          refine zaehl_pos _ m (j + 1 - m) (j - m) (by omega) ?_
          show R.akt (m + (j - m)) = some u ∧ ∃ L', AnSperre (R.M (m + (j - m))) u L'
          rw [show m + (j - m) = j by omega]
          exact ⟨h2, L', anSperre_gleich (h3 j h1 (Nat.le_refl j)) hA'⟩
        have hk1 : 1 ≤ k' := Nat.le_trans hp2 (hB _ hhold).2
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        have hmulk : (k'' + 1) * G = k'' * G + G := Nat.succ_mul k'' G
        by_cases hrel : L ∈ offen ((R.M (j + 1)).faeden u).spur
        · have hB' : ∀ n, (∀ i, i < n → L ∈ offen ((R.M (j + 1 + i)).faeden u).spur) →
              zaehl (fun j => R.akt j = some u) (j + 1) n ≤ h' ∧
              zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') (j + 1) n ≤ k'' := by
            intro n hn
            have hall : ∀ i, i < (j + 1 - m) + n → L ∈ offen ((R.M (m + i)).faeden u).spur := by
              intro i hi
              by_cases hi' : i < j + 1 - m
              · exact hhold i hi'
              · have := hn (i - (j + 1 - m)) (by omega)
                rwa [show j + 1 + (i - (j + 1 - m)) = m + i by omega] at this
            have hb := hB _ hall
            rw [zaehl_add, zaehl_add, e1] at hb
            obtain ⟨hb1, hb2⟩ := hb
            exact ⟨by omega, by omega⟩
          obtain ⟨e, e1', e2, e3, e4, e5⟩ := ih k'' (j + 1) hrel hB'
          refine ⟨e, by omega, by omega, e3, fun i hi1 hi2 => ?_, e5⟩
          by_cases hij : i ≤ j
          · exact hpj i hi1 hij
          · exact e4 i (by omega) hi2
        · exact ⟨j, h1, by omega, h2, hpj, hrel⟩
      · have hjF := hFF hA
        by_cases hrel : L ∈ offen ((R.M (j + 1)).faeden u).spur
        · have hB' : ∀ n, (∀ i, i < n → L ∈ offen ((R.M (j + 1 + i)).faeden u).spur) →
              zaehl (fun j => R.akt j = some u) (j + 1) n ≤ h' ∧
              zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') (j + 1) n ≤ k' := by
            intro n hn
            have hall : ∀ i, i < (j + 1 - m) + n → L ∈ offen ((R.M (m + i)).faeden u).spur := by
              intro i hi
              by_cases hi' : i < j + 1 - m
              · exact hhold i hi'
              · have := hn (i - (j + 1 - m)) (by omega)
                rwa [show j + 1 + (i - (j + 1 - m)) = m + i by omega] at this
            have hb := hB _ hall
            rw [zaehl_add, zaehl_add, e1] at hb
            obtain ⟨hb1, hb2⟩ := hb
            exact ⟨by omega, by omega⟩
          obtain ⟨e, e1', e2, e3, e4, e5⟩ := ih k' (j + 1) hrel hB'
          refine ⟨e, by omega, by omega, e3, fun i hi1 hi2 => ?_, e5⟩
          by_cases hij : i ≤ j
          · exact hpj i hi1 hij
          · exact e4 i (by omega) hi2
        · exact ⟨j, h1, by omega, h2, hpj, hrel⟩
end Beweis
end Kern
end Gabbro.Grammatik
