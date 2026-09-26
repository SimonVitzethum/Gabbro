/-
  File:      Grammatik/Zielsatz/Faeden.lean -- the thread-machine legs of `ZielF` (Spec.lean),
             PROVED for every program of G (Opus agent A, 2026-09-26, OFFEN O21/O22).

  `ZielF` adds to `Ziel` (which holds on the G state of every thread-machine run, by the bridge
  `fadenErreichbar_G`) the legs that speak about spawns and joins. They are proved here from
  three facts about the program -- lock ranks (`StufenM`), roots without signature locks, a
  complete lock list -- and the invariant of the thread machine (`FadenInv`), generic in the
  declaration. `Zielsatz/Beweis.lean` instantiates them in `zielF_aus`.

  * `kein_warteZyklusF` -- no wait cycle through locks and joins. A joining starter holds no
    lock (`FadenInv.joinFrei`, from the `start` rule's side condition, `N461`), so a lock edge
    never ends at a joiner, and a thread that joins nothing has only lock edges: once a cycle
    has one non-joiner, every thread on it is one, and the cycle is a lock cycle -- refuted by
    the ranks (`Ziel.keinZyklus`). A cycle of joiners only climbs in the ghost rank of the
    spawn tree (`rangSteigt`) and cannot close.
  * `keine_verklemmungF` -- no global deadlock with join waits. If a live unfinished thread
    joins nothing, the waited-for lock of highest rank is held by a live, unfinished thread that
    joins nothing (a dormant slot and a joiner hold none, a finished thread holds none) and that
    waits for a HIGHER lock: contradiction (the `keine_verklemmungG` argument). Otherwise every
    live unfinished thread joins, and a join chain climbs in rank, which the spawn clock bounds.
  * `fortschrittF_aus` -- every stop is named: `FortschrittG` for a thread that joins nothing,
    the `join` step or a join wait for a starter, dormancy for a slot.
-/
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}

/-! ## 1. Facts about who holds a lock -/

/-- A thread that holds a lock joins nothing. -/
theorem wartet_leer_of_haelt {M0 : RufMaschineG D} {K : FadenMaschine D}
    (hI : FadenInv P O passes M0 K) {u : Faden} {L : D.Lock}
    (hL : L ∈ offen (K.m.faeden u).spur) : K.wartet u = [] := by
  refine Classical.byContradiction fun h => ?_
  rw [hI.joinFrei u h] at hL
  exact List.not_mem_nil hL

/-- A thread that holds a lock is live, when no root holds a lock by signature. -/
theorem lebt_of_haelt {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {K : FadenMaschine D} (hI : FadenInv P O passes (RufStartG P sp init) K)
    (hLeer : ∀ t, D.haelt (init t).1 = []) {u : Faden} {L : D.Lock}
    (hL : L ∈ offen (K.m.faeden u).spur) : K.lebt u = true := by
  cases h : K.lebt u with
  | true => rfl
  | false =>
      rw [faden_schlafend_frei rfl hI u h (hLeer u)] at hL
      exact absurd hL List.not_mem_nil

/-! ## 2. No wait cycle, join waits included -/

/-- **NO WAIT CYCLE THROUGH LOCKS AND JOINS.** -/
theorem kein_warteZyklusF {M0 : RufMaschineG D} {K : FadenMaschine D}
    (hI : FadenInv P O passes M0 K) (hZ : KeinWarteZyklus K.m) : KeinWarteZyklusF K := by
  intro n ts hW he
  -- a lock edge ends at a thread that joins nothing
  have ziel_leer : ∀ i, i ≤ n → K.wartet (ts i) = [] → K.wartet (ts (i + 1)) = [] ∧
      ∃ L, WartetAuf K.m (ts i) (ts (i + 1)) L := by
    intro i hi h0
    rcases hW i hi with ⟨_, L, hA⟩ | ⟨hu, _⟩
    · exact ⟨wartet_leer_of_haelt hI hA.2, L, hA⟩
    · rw [h0] at hu; exact absurd hu List.not_mem_nil
  -- from a thread that joins nothing, every later thread joins nothing
  have vorwaerts : ∀ j, K.wartet (ts j) = [] → ∀ k, j + k ≤ n + 1 → K.wartet (ts (j + k)) = [] := by
    intro j hj k
    induction k with
    | zero => intro _; exact hj
    | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have := (ziel_leer (j + k) (by omega) h1).1
        rwa [show j + (k + 1) = j + k + 1 by omega]
  by_cases h0 : K.wartet (ts 0) = []
  · -- every edge is a lock edge: a lock cycle
    have hleer : ∀ i, i ≤ n → K.wartet (ts i) = [] := fun i hi => by
      have := vorwaerts 0 h0 i (by omega)
      rwa [Nat.zero_add] at this
    have hlock : ∀ i, i ≤ n → ∃ L, WartetAuf K.m (ts i) (ts (i + 1)) L :=
      fun i hi => (ziel_leer i hi (hleer i hi)).2
    let Ls : Nat → D.Lock := fun i =>
      if h : i ≤ n then Classical.choose (hlock i h)
      else Classical.choose (hlock 0 (Nat.zero_le n))
    refine hZ n ts Ls (fun i hi => ?_) he
    show WartetAuf K.m (ts i) (ts (i + 1)) (if h : i ≤ n then _ else _)
    rw [dif_pos hi]
    exact Classical.choose_spec (hlock i hi)
  · -- every thread on the cycle joins: every edge is a join edge, and the rank climbs
    have hvoll : ∀ i, i ≤ n + 1 → K.wartet (ts i) ≠ [] := by
      intro i hi hi0
      have := vorwaerts i hi0 (n + 1 - i) (by omega)
      rw [show i + (n + 1 - i) = n + 1 by omega, he] at this
      exact h0 this
    have hsteigt : ∀ i, i ≤ n → K.rang (ts i) < K.rang (ts (i + 1)) := by
      intro i hi
      rcases hW i hi with ⟨hw0, _⟩ | ⟨hu, _⟩
      · exact absurd hw0 (hvoll i (by omega))
      · exact hI.rangSteigt _ _ hu
    have hkette : ∀ i, i ≤ n → K.rang (ts 0) + i < K.rang (ts (i + 1)) := by
      intro i
      induction i with
      | zero => intro hi; simpa using hsteigt 0 hi
      | succ i ih =>
          intro hi
          have h1 := ih (by omega)
          have h2 := hsteigt (i + 1) hi
          omega
    have := hkette n (Nat.le_refl n)
    rw [he] at this
    omega

/-! ## 3. No global deadlock, join waits included -/

/-- **NO DEADLOCK WITH JOIN WAITS.** If every live unfinished thread waits -- for a lock it does
    not hold, while it joins nothing, or for an unfinished root -- then every live thread is
    finished. -/
theorem keine_verklemmungF (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls) {K : FadenMaschine D}
    (hI : FadenInv P O passes (RufStartG P sp init) K)
    (hW : ∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) :
    ∀ t, K.lebt t = true → FertigG K.m t := by
  have hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup := fun t => by
    rw [startSpur, hLeer t]; exact List.nodup_nil
  have hR := rangInvG_erreichbar hO hSt sp init hND hI.lauf
  intro t0 ht0
  refine Classical.byContradiction fun hF0 => ?_
  by_cases hA : ∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧ K.wartet t = []
  · -- a lock wait: the highest waited-for lock
    obtain ⟨t1, hl1, hf1, hw1⟩ := hA
    let W := ls.filter fun L => @decide (∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧
      K.wartet t = [] ∧ AnSperre K.m t L) (Classical.propDecidable _)
    have hWmem : ∀ L, L ∈ W ↔ ∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧
        K.wartet t = [] ∧ AnSperre K.m t L := by
      intro L
      simp only [W, List.mem_filter, hls L, true_and]
      exact ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
        fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
    have hwarte : ∀ t, K.lebt t = true → ¬ FertigG K.m t → K.wartet t = [] → WartetG K.m t := by
      intro t hl hf hw
      rcases hW t hl hf with ⟨_, h⟩ | ⟨u, hu, _⟩
      · exact h
      · rw [hw] at hu; exact absurd hu List.not_mem_nil
    obtain ⟨L1, hL1⟩ := (hwarte t1 hl1 hf1 hw1).1
    have hne : W ≠ [] := fun he => by
      have := (hWmem L1).mpr ⟨t1, hl1, hf1, hw1, hL1⟩
      rw [he] at this
      exact List.not_mem_nil this
    obtain ⟨Lm, hLm, hmax⟩ := rang_max W hne
    obtain ⟨tm, hlm, hfm, hwm, hAm⟩ := (hWmem Lm).mp hLm
    obtain ⟨u, _, hLu⟩ := (hwarte tm hlm hfm hwm).2 Lm hAm
    have hlu := lebt_of_haelt hI hLeer hLu
    have hwu := wartet_leer_of_haelt hI hLu
    by_cases hFu : FertigG K.m u
    · rw [fertig_leer (hR u) (hLeer u) hFu] at hLu
      exact List.not_mem_nil hLu
    · obtain ⟨Lu, hAu⟩ := (hwarte u hlu hFu hwu).1
      have hlt := (sperre_rang (hR u) hAu).2 Lm hLu
      have hle := hmax Lu ((hWmem Lu).mpr ⟨u, hlu, hFu, hwu, hAu⟩)
      omega
  · -- every live unfinished thread joins: a join chain climbs in rank, bounded by the clock
    have hjoin : ∀ t, K.lebt t = true → ¬ FertigG K.m t →
        ∃ u, K.lebt u = true ∧ ¬ FertigG K.m u ∧ K.rang t < K.rang u := by
      intro t hl hf
      have hw : K.wartet t ≠ [] := fun hw => hA ⟨t, hl, hf, hw⟩
      rcases hW t hl hf with ⟨hw0, _⟩ | ⟨u, hu, hfu⟩
      · exact absurd hw0 hw
      · exact ⟨u, hI.kindLebt t u hu, hfu, hI.rangSteigt t u hu⟩
    have schranke : ∀ k t, K.lebt t = true → ¬ FertigG K.m t → K.uhr - K.rang t ≤ k → False := by
      intro k
      induction k with
      | zero =>
          intro t hl hf hk
          obtain ⟨u, _, _, hlt⟩ := hjoin t hl hf
          have := hI.rangUhr u
          omega
      | succ k ih =>
          intro t hl hf hk
          obtain ⟨u, hlu, hfu, hlt⟩ := hjoin t hl hf
          have := hI.rangUhr u
          exact ih u hlu hfu (by omega)
    exact schranke _ t0 ht0 hF0 (Nat.le_refl _)

/-! ## 4. Every stop is named -/

/-- **PROGRESS ON THE THREAD MACHINE**, from G's `FortschrittG` on the G state. -/
theorem fortschrittF_aus {K : FadenMaschine D}
    (hF : FortschrittG P O passes K.m) : FortschrittF P O passes K := by
  intro t
  cases hl : K.lebt t with
  | false => exact Or.inl rfl
  | true =>
      right
      by_cases hw : K.wartet t = []
      · right
        refine ⟨hw, ?_⟩
        rcases hF t with h | h | h | h | h | h | ⟨M', hs⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨M', hs, FadenSchritt.lauf K t M' hl hw hs⟩)))))
      · left
        refine ⟨hw, ?_⟩
        by_cases hj : JoinWartet K t
        · exact Or.inl hj
        · refine Or.inr ⟨_, FadenSchritt.join K t hl hw fun u hu =>
            Classical.byContradiction fun hfu => hj ⟨u, hu, hfu⟩, rfl, ?_⟩
          show (if t = t then [] else K.wartet t) = []
          simp

#print axioms Gabbro.Grammatik.Zielsatz.wartet_leer_of_haelt
#print axioms Gabbro.Grammatik.Zielsatz.lebt_of_haelt
#print axioms Gabbro.Grammatik.Zielsatz.kein_warteZyklusF
#print axioms Gabbro.Grammatik.Zielsatz.keine_verklemmungF
#print axioms Gabbro.Grammatik.Zielsatz.fortschrittF_aus

end Gabbro.Grammatik.Zielsatz
