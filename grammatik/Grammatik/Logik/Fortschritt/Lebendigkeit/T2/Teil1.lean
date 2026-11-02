module
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T2.Teil1Basis
import all Grammatik.Logik.Fortschritt.Lebendigkeit.T2.Teil1Basis

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


include hO hRang hFifo hFair in
/-- **The free gap.** If `L` is free at `m` and thread `t` has stood at
    `locks L` since `n0`, then within `F` scheduler steps `t` takes a step
    (and stands there until it), or another thread `v` takes `L` -- a thread
    that, by FIFO, has stood at `locks L` since `n0` as well. -/
theorem frei_luecke {L : D.Lock} {t : Faden} {n0 m : Nat} (hnm : n0 ≤ m)
    (hW : ∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) t L)
    (hfrei : ∀ v, L ∉ offen ((R.M m).faeden v).spur) :
    ∃ j, m ≤ j ∧ j < m + F ∧ (∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) t L) ∧
      (R.akt j = some t ∨
        ∃ v, v ≠ t ∧ R.akt j = some v ∧ L ∈ offen ((R.M (j + 1)).faeden v).spur ∧
          (∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) v L)) := by
  let Q : Nat → Prop := fun j => R.akt j = some t ∨ ∃ v, L ∈ offen ((R.M (j + 1)).faeden v).spur
  -- before the first `Q`: `L` stays free and `t` stays frozen
  have hvor : ∀ j, m ≤ j → (∀ i, m ≤ i → i < j → ¬ Q i) →
      (R.M j).faeden t = (R.M m).faeden t ∧ ∀ v, L ∉ offen ((R.M j).faeden v).spur := by
    intro j hj hQ
    refine ⟨R.stet' hj (fun i h1 h2 he => hQ i h1 h2 (Or.inl he)), fun v hv => ?_⟩
    rcases Nat.eq_zero_or_pos (j - m) with h0 | hpos
    · have : j = m := by omega
      subst this; exact hfrei v hv
    · exact hQ (j - 1) (by omega) (by omega) (Or.inr ⟨v, by rwa [show j - 1 + 1 = j by omega]⟩)
  have hex : ∃ j, m ≤ j ∧ j < m + F ∧ Q j := by
    refine Classical.byContradiction fun hne => ?_
    have hno : ∀ i, m ≤ i → i < m + F → ¬ Q i := fun i h1 h2 hq => hne ⟨i, h1, h2, hq⟩
    obtain ⟨j, h1, h2, h3⟩ := hFair t m fun j h1 h2 => by
      obtain ⟨e, hf⟩ := hvor j h1 (fun i hi1 hi2 => hno i hi1 (by omega))
      have hA : AnSperre (R.M j) t L := anSperre_gleich e (hW m hnm (Nat.le_refl m))
      obtain ⟨w, hw⟩ := hRang j t
      exact schritt_an_sperre hw hA (fun g _ => hf g)
    exact hno j h1 h2 (Or.inl h3)
  obtain ⟨j, h1, h2, hQ0, hfirst⟩ := erster Q m F hex
  have hQ : R.akt j = some t ∨ ∃ v, L ∈ offen ((R.M (j + 1)).faeden v).spur := hQ0
  obtain ⟨e, hf⟩ := hvor j h1 hfirst
  have hWj : ∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) t L := by
    intro i hi1 hi2
    by_cases him : i ≤ m
    · exact hW i hi1 him
    · have e' := R.stet' (u := t) (show m ≤ i by omega)
        (fun i' h1' h2' he => hfirst i' h1' (by omega) (Or.inl he))
      exact anSperre_gleich e' (hW m hnm (Nat.le_refl m))
  refine ⟨j, h1, h2, hWj, ?_⟩
  rcases hQ with ht | ⟨v, hv⟩
  · exact Or.inl ht
  · by_cases ht : R.akt j = some t
    · exact Or.inl ht
    · right
      have hvt : v ≠ t := by
        rintro rfl
        rw [R.fremd j v ht] at hv
        exact an_sperre_frei R hRang (hWj j (by omega) (Nat.le_refl j)) hv
      have hv0 : L ∉ offen ((R.M j).faeden v).spur := hf v
      have hakt : R.akt j = some v := by
        cases ha : R.akt j with
        | none => rw [(R.stotter j ha).1] at hv; exact absurd hv hv0
        | some w =>
            by_cases hwv : w = v
            · rw [hwv]
            · rw [rufSchrittG_fremd (R.schritt j w ha) v (Ne.symm hwv)] at hv
              exact absurd hv hv0
      have hAv := nimmt_an_sperre hO (R.schritt j v hakt) hv0 hv
      exact ⟨v, hvt, hakt, hv, hFifo t v L n0 j (Ne.symm hvt) hWj hakt hAv⟩

/-- The threads AHEAD of `t` at step `m` (`t` stands at `locks L` since `n0`):
    the holder of `L`, and every thread standing at `locks L` since `n0`. -/
abbrev Vor (t : Faden) (L : D.Lock) (n0 m : Nat) (u : Faden) : Prop :=
  u ≠ t ∧ (L ∈ offen ((R.M m).faeden u).spur ∨ ∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) u L)

include hO hRang hEx hFifo hFair hAnw in
/-- **Waiting while `L` is held**: with at most `q` threads ahead, `t` takes
    its step within `q * (S + F)` scheduler steps, where `S` bounds one
    critical section (`hRel`). Each round: the holder releases (`< S`), a
    free gap (`< F`) ends with `t`'s step or the next holder -- a thread
    ahead of `t` that leaves the set ahead for good. -/
theorem warte_gehalten {L : D.Lock} {t : Faden} {n0 S : Nat}
    (hRel : ∀ u m, L ∈ offen ((R.M m).faeden u).spur → ∃ e, m ≤ e ∧ e < m + S ∧
      R.akt e = some u ∧ (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
      L ∉ offen ((R.M (e + 1)).faeden u).spur) :
    ∀ q m, n0 ≤ m → (∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) t L) →
      (∃ u, L ∈ offen ((R.M m).faeden u).spur) →
      anz (Vor R t L n0 m) (Ts L) ≤ q →
      ∃ j, m ≤ j ∧ j < m + q * (S + F) ∧ R.akt j = some t
  | 0, m, hnm, hW, ⟨u, hu⟩, hc => by
      have hut : u ≠ t := fun e => an_sperre_frei R hRang (hW m hnm (Nat.le_refl m)) (e ▸ hu)
      have := anz_pos (Vor R t L n0 m) (Ts L) ⟨u, hAnw m u L (Or.inl hu), hut, Or.inl hu⟩
      omega
  | q + 1, m, hnm, hW, ⟨u, hu⟩, hc => by
      have hut : u ≠ t := fun e => an_sperre_frei R hRang (hW m hnm (Nat.le_refl m)) (e ▸ hu)
      have hmul : (q + 1) * (S + F) = q * (S + F) + (S + F) := Nat.succ_mul q (S + F)
      obtain ⟨e, he1, he2, he3, he4, he5⟩ := hRel u m hu
      by_cases hact : ∃ j, m ≤ j ∧ j < e + 1 ∧ R.akt j = some t
      · obtain ⟨j, j1, j2, j3⟩ := hact
        exact ⟨j, j1, by omega, j3⟩
      · have hno : ∀ i, m ≤ i → i < e + 1 → R.akt i ≠ some t :=
          fun i h1 h2 he => hact ⟨i, h1, h2, he⟩
        have hWe : ∀ j, n0 ≤ j → j ≤ e + 1 → AnSperre (R.M j) t L := by
          intro j hj1 hj2
          by_cases hjm : j ≤ m
          · exact hW j hj1 hjm
          · exact anSperre_gleich (R.stet' (show m ≤ j by omega)
              (fun i h1 h2 => hno i h1 (by omega))) (hW m hnm (Nat.le_refl m))
        have hfrei : ∀ v, L ∉ offen ((R.M (e + 1)).faeden v).spur := by
          intro v hv
          by_cases hvu : v = u
          · subst hvu; exact he5 hv
          · have hne : R.akt e ≠ some v := by
              rw [he3]; intro h; exact hvu (Option.some.inj h).symm
            rw [R.fremd e v hne] at hv
            exact hEx e u v (Ne.symm hvu) L (he4 e he1 (Nat.le_refl e)) hv
        obtain ⟨j, j1, j2, j3, j4⟩ := frei_luecke R hO hRang hFifo hFair (show n0 ≤ e + 1 by omega)
          hWe hfrei
        rcases j4 with ht | ⟨v, hvt, hv1, hv2, hv3⟩
        · exact ⟨j, by omega, by omega, ht⟩
        · have hW' : ∀ i, n0 ≤ i → i ≤ j + 1 → AnSperre (R.M i) t L := by
            intro i hi1 hi2
            by_cases hij : i ≤ j
            · exact j3 i hi1 hij
            · have e' : i = j + 1 := by omega
              subst e'
              have hne : R.akt j ≠ some t := by
                rw [hv1]; intro h; exact hvt (Option.some.inj h)
              exact anSperre_gleich (R.fremd j t hne) (j3 j (by omega) (Nat.le_refl j))
          -- the new holder `v` is the only holder, and it was ahead since `n0`
          have hnur : ∀ x, L ∈ offen ((R.M (j + 1)).faeden x).spur → x = v := by
            intro x hx
            refine Classical.byContradiction fun hxv => ?_
            exact hEx (j + 1) v x (Ne.symm hxv) L hv2 hx
          have hvu : v ≠ u := by
            rintro rfl
            exact an_sperre_frei R hRang (hv3 m hnm (by omega)) hu
          have himp : ∀ x ∈ Ts L, Vor R t L n0 (j + 1) x → Vor R t L n0 m x := by
            intro x _ ⟨hxt, hx⟩
            refine ⟨hxt, Or.inr ?_⟩
            rcases hx with hx | hx
            · have := hnur x hx
              subst this
              exact fun i hi1 hi2 => hv3 i hi1 (by omega)
            · exact fun i hi1 hi2 => hx i hi1 (by omega)
          have hunot : ¬ Vor R t L n0 (j + 1) u := by
            rintro ⟨_, hx | hx⟩
            · exact hvu (hnur u hx).symm
            · exact an_sperre_frei R hRang (hx m hnm (by omega)) hu
          have hlt := anz_lt (Vor R t L n0 (j + 1)) (Vor R t L n0 m) (Ts L) himp
            ⟨u, hAnw m u L (Or.inl hu), ⟨hut, Or.inl hu⟩, hunot⟩
          obtain ⟨j', j1', j2', j3'⟩ := warte_gehalten hRel q (j + 1) (by omega) hW' ⟨v, hv2⟩
            (by omega)
          exact ⟨j', by omega, by omega, j3'⟩

include hO hRang hEx hFifo hFair hAnw in
/-- **The waiting bound for one lock**, given the bound `S` of one critical
    section: `t` at `locks L` at `n0` takes its step before
    `n0 + (c L - 1) * (S + F) + F`. -/
theorem warte {L : D.Lock} {t : Faden} {n0 S : Nat}
    (hRel : ∀ u m, L ∈ offen ((R.M m).faeden u).spur → ∃ e, m ≤ e ∧ e < m + S ∧
      R.akt e = some u ∧ (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
      L ∉ offen ((R.M (e + 1)).faeden u).spur)
    (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + (((Ts L).length - 1) * (S + F) + F) ∧ R.akt j = some t := by
  have htT : t ∈ Ts L := hAnw n0 t L (Or.inr hA)
  have hc0 : anz (Vor R t L n0 n0) (Ts L) ≤ (Ts L).length - 1 := by
    have := anz_lt_len (Vor R t L n0 n0) (Ts L) ⟨t, htT, fun h => h.1 rfl⟩
    omega
  have hW0 : ∀ j, n0 ≤ j → j ≤ n0 → AnSperre (R.M j) t L := by
    intro j h1 h2
    rw [show j = n0 by omega]; exact hA
  by_cases hg : ∃ u, L ∈ offen ((R.M n0).faeden u).spur
  · obtain ⟨j, j1, j2, j3⟩ := warte_gehalten R hO hRang hEx hFifo hFair hAnw hRel _ n0
      (Nat.le_refl n0) hW0 hg hc0
    exact ⟨j, j1, by omega, j3⟩
  · have hfrei : ∀ v, L ∉ offen ((R.M n0).faeden v).spur := fun v hv => hg ⟨v, hv⟩
    obtain ⟨j, j1, j2, j3, j4⟩ := frei_luecke R hO hRang hFifo hFair (Nat.le_refl n0) hW0 hfrei
    rcases j4 with ht | ⟨v, hvt, hv1, hv2, hv3⟩
    · exact ⟨j, j1, by omega, ht⟩
    · have hW' : ∀ i, n0 ≤ i → i ≤ j + 1 → AnSperre (R.M i) t L := by
        intro i hi1 hi2
        by_cases hij : i ≤ j
        · exact j3 i hi1 hij
        · have e' : i = j + 1 := by omega
          subst e'
          have hne : R.akt j ≠ some t := by
            rw [hv1]; intro h; exact hvt (Option.some.inj h)
          exact anSperre_gleich (R.fremd j t hne) (j3 j (by omega) (Nat.le_refl j))
      have hnur : ∀ x, L ∈ offen ((R.M (j + 1)).faeden x).spur → x = v := by
        intro x hx
        refine Classical.byContradiction fun hxv => ?_
        exact hEx (j + 1) v x (Ne.symm hxv) L hv2 hx
      have himp : ∀ x ∈ Ts L, Vor R t L n0 (j + 1) x → Vor R t L n0 n0 x := by
        intro x _ ⟨hxt, hx⟩
        refine ⟨hxt, Or.inr ?_⟩
        rcases hx with hx | hx
        · have := hnur x hx
          subst this
          exact fun i hi1 hi2 => hv3 i hi1 (by omega)
        · exact fun i hi1 hi2 => hx i hi1 (by omega)
      have hle := anz_mono (Vor R t L n0 (j + 1)) (Vor R t L n0 n0) (Ts L) himp
      obtain ⟨j', j1', j2', j3'⟩ := warte_gehalten R hO hRang hEx hFifo hFair hAnw hRel _ (j + 1)
        (by omega) hW' ⟨v, hv2⟩ (Nat.le_trans hle hc0)
      exact ⟨j', by omega, by omega, j3'⟩

include hO hls hRang hEx hFifo hFair hH hAkt hAnw in
/-- **The bound is valid at every fuel level that covers the locks above `L`**
    -- induction over the rank levels. -/
theorem gueltig : ∀ (n : Nat) (L : D.Lock), hoeher ls L < n → ∀ (t : Faden) (m : Nat),
    AnSperre (R.M m) t L → ∃ j, m ≤ j ∧ j < m + wF ls Ts h k F n L ∧ R.akt j = some t
  | 0, _, hL, _, _, _ => absurd hL (Nat.not_lt_zero _)
  | n + 1, L, hL, t, m, hA => by
      have hV : ∀ L', D.rang L < D.rang L' → ∀ t' n', AnSperre (R.M n') t' L' →
          ∃ j, n' ≤ j ∧ j < n' + wMaxH L (wF ls Ts h k F n) ls ∧ R.akt j = some t' := by
        intro L' hr t' n' hA'
        have hlt := hoeher_lt ls (hls L') hr
        obtain ⟨j, j1, j2, j3⟩ := gueltig n L' (by omega) t' n' hA'
        exact ⟨j, j1, Nat.lt_of_lt_of_le j2
          (Nat.add_le_add_left (le_wMaxH L _ ls L' (hls L') hr) _), j3⟩
      have hRel : ∀ u m', L ∈ offen ((R.M m').faeden u).spur → ∃ e, m' ≤ e ∧
          e < m' + (h L * F + k L * wMaxH L (wF ls Ts h k F n) ls) ∧ R.akt e = some u ∧
          (∀ i, m' ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
          L ∉ offen ((R.M (e + 1)).faeden u).spur :=
        fun u m' hm' => freigabe R hRang hFair hAkt hV u (h L) (k L) m' hm'
          (fun n hn => hH u L m' n hn)
      obtain ⟨j, j1, j2, j3⟩ := warte R hO hRang hEx hFifo hFair hAnw hRel hA
      exact ⟨j, j1, j2, j3⟩

end Beweis
end Kern
end Gabbro.Grammatik
