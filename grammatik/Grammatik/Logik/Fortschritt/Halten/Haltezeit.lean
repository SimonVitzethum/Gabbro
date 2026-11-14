/-
  File:      Grammatik/Logik/Fortschritt/Halten/Haltezeit.lean
  Subject:   THE HOLD TIME AS A THEOREM (`haltezeit_aus`): on every scheduled run of a program whose hold
             bounds and declared costs the checker accepts (`haltPasst`), the hold-time premise of the
             waiting bound holds with `h = k = haltSchranke ls N`.

  * `sekInv_erreichbar` -- on every reachable machine, a thread holding `L` satisfies the section
    invariant at a measure at most `haltSchranke ls N L` (taken at `dannLocks`, `sekInv_nimmt`; kept by
    every step while `L` stays held, `sekInv_schritt`).
  * `zaehl_potential` -- on a stretch where `L` stays held, the own steps are at most the measure at its
    start: each own step lowers it by one, and a thread with measure `0` cannot step (`sekInv_pos`).
  * `haltezeit_aus` -- `Haltezeit R (haltSchranke ls N) (haltSchranke ls N)`; the steps at a `locks`
    head are counted among all own steps.

  Bridge 1 of Lebendigkeit.lean (checker operations to G steps) needs no new pricing: the model's check
  `haltE` prices a section in `kostenBlock`, the G-step cost of KostenG, in which every step the old
  operation count priced at `0` (branch choice, lock take and release, `leave`, empty-block close, loop
  resume) is paid by a constant; a call costs its callee's declared cost, which `kostenPasst` checks
  against the callee's body including its return predicates (C05). A value `return` inside the section is
  priced with the return predicates of the section's own function (`kostenBlock ep`, `ep = kostenEpilog P g`,
  carried per frame by `HaltInvG` and `SekInv`), so the epilogue is part of `N L`, not of the constant part.
  What `kostenBlock` does not contain is paid by the constant part of
  `haltSchranke`: the release of `L` (`1`) and the releases a scoped `return` performs before `L`
  (at most one per lock, `ls.length`).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.Nimmt
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Counting on a stretch -/

open Classical in
theorem zaehl_mono (p q : Nat → Prop) (a : Nat) (hpq : ∀ j, p j → q j) :
    ∀ n, zaehl p a n ≤ zaehl q a n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have ih := zaehl_mono p q a hpq n
      show zaehl p a n + (if p (a + n) then 1 else 0) ≤ zaehl q a n + (if q (a + n) then 1 else 0)
      by_cases hp : p (a + n)
      · rw [if_pos hp, if_pos (hpq _ hp)]; omega
      · rw [if_neg hp]; omega

/-- **A potential bounds the counted steps of a stretch**: if every counted step lowers a measure by
    one and a counted step needs a positive measure, a stretch has at most the measure at its start. -/
theorem zaehl_potential (p held : Nat → Prop) (Q : Nat → Nat → Prop)
    (hstep : ∀ a Φ, Q a Φ → held a → held (a + 1) → ∃ Φ', Q (a + 1) Φ' ∧ Φ' + zaehl p a 1 ≤ Φ)
    (hpos : ∀ a Φ, Q a Φ → 1 ≤ zaehl p a 1 → 1 ≤ Φ) :
    ∀ m a Φ, Q a Φ → (∀ i, i < m → held (a + i)) → zaehl p a m ≤ Φ := by
  intro m
  induction m with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro a Φ hQ hh
    have e : zaehl p a (m + 1) = zaehl p a 1 + zaehl p (a + 1) m := by
      rw [Nat.add_comm m 1]; exact zaehl_add p a 1 m
    rw [e]
    have h1 : zaehl p a 1 ≤ 1 := zaehl_le p a 1
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have e0 : zaehl p (a + 1) 0 = 0 := rfl
      rw [e0]
      rcases Nat.eq_zero_or_pos (zaehl p a 1) with hz | hz
      · omega
      · have := hpos a Φ hQ hz; omega
    · have h0 : held a := by simpa using hh 0 (by omega)
      obtain ⟨Φ', hQ', hle⟩ := hstep a Φ hQ h0 (hh 1 (by omega))
      have ih' := ih (a + 1) Φ' hQ' (fun i hi => by
        have h := hh (i + 1) (by omega)
        rwa [show a + (i + 1) = a + 1 + i by omega] at h)
      omega

/-! ## 2. The section invariant on every reachable machine -/

section Erreichbar

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  {P : Programm D} {O : Orakel D} {pa : Nat} (N : D.Lock → Nat) (ls : List D.Lock)

/-- **Every held lock has its section invariant, at most at the checked hold time.** -/
theorem sekInv_erreichbar (E : D.Fn → Nat) (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hls : ∀ K, K ∈ ls)
    (hS1 : ∀ i g, S i g = true → kostenEnd (kostenEpilog P g) (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    (i0 : ι) (hP : ∀ g, haltE (fun K => some (N K)) (E g) (T i0) (S i0) pa (P.rumpf g) = true)
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ u L, L ∈ offen (M.faeden u).spur →
      ∃ Φ, Φ ≤ haltSchranke ls N L ∧ SekInv T S pa L (M.faeden u) Φ := by
  have hND := startSpur_nodup_leer init hLeer
  induction hr with
  | start =>
    intro u L hL
    exfalso
    have e : ((RufStartG P sp init).faeden u).spur = startSpur (init u).1 := by
      show (match init u with
        | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
            Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
            [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = _
      cases init u
      rfl
    rw [e, offen_startSpur, hLeer u] at hL
    exact List.not_mem_nil hL
  | schritt M M' g hr' hs ih =>
    intro u L hL'
    have hrang := rangInvG_erreichbar hO hSt sp init hND hr' u
    have hbal := fadenScopeBalanceG_erreichbar hr' u
    by_cases hL : L ∈ offen (M.faeden u).spur
    · obtain ⟨Φ, hΦ, hI⟩ := ih u L hL
      obtain ⟨Φ', hI', hle⟩ := sekInv_schritt T S nx L hO hS1 hS2 hs hI hL hL' hrang.1 hbal _
        (hrang.2.2.1 _ List.mem_cons_self).2
      exact ⟨Φ', by omega, hI'⟩
    · by_cases hgu : g = u
      · subst hgu
        have hA := nimmt_an_sperre hO hs hL hL'
        have hH := haltInvG_erreichbar (fun K => some (N K)) E (T i0) (S i0) hP sp init hr' g
        have hha := rufG_haeltInv hO sp init hr' g
        obtain ⟨ep, hHk⟩ := hH _ List.mem_cons_self
        refine ⟨haltSchranke ls N L, Nat.le_refl _, ?_⟩
        exact sekInv_nimmt T S N ls i0 hA hs hHk hL
          (hha.alle _ List.mem_cons_self) hbal.1
          ((M.faeden g).kopf.rest.2.2.2.2.freis_nodup (hha.2.1 _ List.mem_cons_self)) hls
      · rw [rufSchrittG_passt_anders P O pa M M' g u (fun h => hgu h.symm) hs] at hL'
        exact absurd hL' hL

end Erreichbar

/-! ## 3. The hold time -/

/-- **THE HOLD TIME FROM THE CHECKER (`haltezeit_aus`).** Let the run start at a reachable machine of a
    program accepted by the hold-bound check `haltPasst P passes N decl fs ks` (every section of every
    function `g` of the complete list `fs` costs at most `N L` in `kostenBlock (kostenEpilog P g)` and calls
    only functions of
    `ks`, each of which fits its declared cost `decl`), under `GutO`, the rank stages `StufenM`, and
    starts without signature locks. Then on every stretch on which a thread holds `L` it takes at most
    `haltSchranke ls N L = N L + 1 + ls.length` own steps (and as many at a `locks` head):
    `Haltezeit R (haltSchranke ls N) (haltSchranke ls N)`. -/
theorem haltezeit_aus [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat}
    (R : PlanLauf P O pa) (hO : GutO O) (hSt : StufenM P)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hr0 : RufErreichbarG P O pa (RufStartG P sp init) (R.M 0))
    {ls : List D.Lock} (hls : ∀ K, K ∈ ls) {fs ks : List D.Fn} (hfs : ∀ g, g ∈ fs)
    {N : D.Lock → Nat} {decl : D.Fn → Nat} (hK : haltPasst P pa N decl fs ks = true) :
    Haltezeit R (haltSchranke ls N) (haltSchranke ls N) := by
  unfold haltPasst at hK
  rw [Bool.and_eq_true] at hK
  obtain ⟨hKP, hKH⟩ := hK
  have hfs' : ∀ h, h ∈ ks →
      kostenEnd (kostenEpilog P h) decl pa (P.rumpf h) ≤ decl h ∧
        rufeE (fun h => ks.contains h) (fun _ => false) true (P.rumpf h) = true := by
    intro h hh
    have := List.all_eq_true.mp hKP h hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hP : ∀ g, haltE (fun K => some (N K)) (kostenEpilog P g) decl (fun h => ks.contains h) pa
      (P.rumpf g) = true :=
    fun g => List.all_eq_true.mp hKH g (hfs g)
  have hS1 : ∀ (i : Unit) g, (fun (_ : Unit) h => ks.contains h) i g = true →
      kostenEnd (kostenEpilog P g) ((fun (_ : Unit) => decl) ((fun (_ : Unit) (_ : D.Fn) => ()) i g)) pa
        (P.rumpf g) ≤
        (fun (_ : Unit) => decl) i g :=
    fun _ h hS => (hfs' h (List.contains_iff_mem.mp hS)).1
  have hS2 : ∀ (i : Unit) g, (fun (_ : Unit) h => ks.contains h) i g = true →
      rufeE ((fun (_ : Unit) h => ks.contains h) ((fun (_ : Unit) (_ : D.Fn) => ()) i g))
        (fun _ => false) true (P.rumpf g) = true :=
    fun _ h hS => (hfs' h (List.contains_iff_mem.mp hS)).2
  have hND := startSpur_nodup_leer init hLeer
  intro u L a n hheld
  have hle : zaehl (fun j => R.akt j = some u) a n ≤ haltSchranke ls N L := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact Nat.zero_le _
    · obtain ⟨Φ, hΦ, hI⟩ := sekInv_erreichbar (fun (_ : Unit) => decl) (fun _ h => ks.contains h)
        (fun _ _ => ()) N ls (kostenEpilog P) hO hSt sp init hLeer hls hS1 hS2 () hP (R.erreichbar hr0 a)
        u L
        (by simpa using hheld 0 hn)
      have hz := zaehl_potential (fun j => R.akt j = some u)
        (fun j => L ∈ offen ((R.M j).faeden u).spur)
        (fun j Φ => SekInv (fun (_ : Unit) => decl) (fun _ h => ks.contains h) pa L ((R.M j).faeden u) Φ)
        (fun a' Φ hI hL hL' => by
          have hr := R.erreichbar hr0 a'
          have hrang := rangInvG_erreichbar hO hSt sp init hND hr u
          have hbal := fadenScopeBalanceG_erreichbar hr u
          have hz1 := zaehl_le (fun j => R.akt j = some u) a' 1
          cases ha : R.akt a' with
          | none =>
            have e := (R.stotter a' ha).1
            have hz : zaehl (fun j => R.akt j = some u) a' 1 = 0 :=
              zaehl_null _ a' 1 (fun i hi h => by
                have hi0 : i = 0 := by omega
                subst hi0
                have h' : R.akt a' = some u := h
                rw [ha] at h'
                cases h')
            refine ⟨Φ, ?_, by omega⟩
            show SekInv (fun (_ : Unit) => decl) (fun _ h => ks.contains h) pa L ((R.M (a' + 1)).faeden u) Φ
            rw [e]; exact hI
          | some g =>
            by_cases hgu : g = u
            · subst hgu
              obtain ⟨Φ', hI', hle⟩ := sekInv_eigen (fun (_ : Unit) => decl) (fun _ h => ks.contains h)
                (fun _ _ => ()) L hO hS1 hS2 (R.schritt a' g ha) hI hL hL' hrang.1 hbal _
                (hrang.2.2.1 _ List.mem_cons_self).2
              exact ⟨Φ', hI', by omega⟩
            · have hz : zaehl (fun j => R.akt j = some u) a' 1 = 0 :=
                zaehl_null _ a' 1 (fun i hi h => by
                  have hi0 : i = 0 := by omega
                  subst hi0
                  have h' : R.akt a' = some u := h
                  rw [ha] at h'
                  exact hgu (Option.some.inj h'))
              refine ⟨Φ, ?_, by omega⟩
              show SekInv (fun (_ : Unit) => decl) (fun _ h => ks.contains h) pa L
                ((R.M (a' + 1)).faeden u) Φ
              rw [rufSchrittG_fremd (R.schritt a' g ha) u (Ne.symm hgu)]
              exact hI)
        (fun a' Φ hI hz => by
          by_cases ha : R.akt a' = some u
          · exact sekInv_pos (fun (_ : Unit) => decl) (fun _ h => ks.contains h) L (R.schritt a' u ha) hI
          · have h0 : zaehl (fun j => R.akt j = some u) a' 1 = 0 :=
              zaehl_null _ a' 1 (fun i hi h => ha (by
                have hi0 : i = 0 := by omega
                subst hi0
                exact h))
            omega)
        n a Φ hI hheld
      omega
  exact ⟨hle, Nat.le_trans (zaehl_mono (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L')
    (fun j => R.akt j = some u) a (fun j h => h.1) n) hle⟩

end Gabbro.Grammatik
