/- Part 4 of 5 of `MaschinenKette` (split by instrumente/teile/lean-teilen.py; the umbrella `MaschinenKette.lean` imports all parts). -/
module
public import Grammatik.Kern.Semantik.MaschinenKette.T3
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **Witnessed lock step: the chain extends along a memory-framed step and the
    table link stays unconditional.** Same construction as
    `kette_aus_lauf_schritt_rahmen` (same read-only projection theorems, same
    single-thread arithmetic, same new-step frame transfer of `hFrame`); DELTA:
    no non-writer premise anywhere -- old steps inherit from the unconditional
    prefix link `hLinkOld`, the new step reuses the prefix witness `hwit_new`
    (lock events never carry one), the guard rides along from `hGuardOld`
    (same members, same code). Every premise is load-bearing. -/
theorem kette_bezeugt_schritt_sperre
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (Nb : Nebeneinander)
    (M M' : GenMaschine D) (f : Faden)
    (hReach : GenErreichbar P O passes (GenStart sp) M)
    (hReach' : GenErreichbar P O passes (GenStart sp) M')
    (neu : List (Ereignis D)) (nach : World D)
    (hM'l : M'.lauf = M.lauf ++ genEigen f neu)
    (hM'w : M'.welten = M.welten ++ [nach])
    (J : GemeinsamerLauf (D := D) Nb)
    (hJw : J.welten = M.welten)
    (hmem : f ∈ J.faeden)
    (hFrame : Rahmen (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (M.weltVon f) nach)
    (t₀ : D.Tab) (L : D.Lock)
    (hLinkOld : SerialLink Nb J M.lauf t₀)
    (hGuardOld : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → L ∈ D.haelt (J.code g))
    (hwit_new : TraegerSchreibt (J.code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (hsingle : ∀ s ∈ M.lauf, s.faden = f) :
    ∃ J' : GemeinsamerLauf (D := D) Nb,
      J'.welten = M'.welten ∧
      J'.l = M'.lauf ∧
      f ∈ J'.faeden ∧
      J'.faeden = J.faeden ∧
      J'.code = J.code ∧
      SerialLink Nb J' M'.lauf t₀ ∧
      (∀ (g : Faden), g ∈ J'.faeden → TraegerSchreibt (J'.code g) (.inl t₀) = true →
        L ∈ D.haelt (J'.code g)) := by
  have hlen : M.welten.length = J.schrittFaden.length + 1 := by
    rw [← hJw]
    exact J.hKette
  obtain ⟨f0, hlast⟩ := genWelten_letzte P O passes hO sp M hReach
  have hLastIdx : M.welten[J.schrittFaden.length]? =
      some (M.speicher.welt (M.spuren f0)) := by
    have hget : M.welten.getLast? = M.welten[M.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : M.welten.length - 1 = J.schrittFaden.length := by omega
    rw [hn] at hget
    rw [hlast] at hget
    exact hget.symm
  have hfaden : ∀ (i : Nat) (g : Faden) (ei : Ereignis D),
      M'.lauf[i]? = some (Schritt.mk g ei) → g = f := by
    intro i g ei hi
    rw [hM'l] at hi
    by_cases hlt : i < M.lauf.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hsingle _ (List.mem_of_getElem? hi)
    · have hle : M.lauf.length ≤ i := by omega
      rw [List.getElem?_append_right hle] at hi
      exact (gen_eigen_getElem f neu _ _ _ hi).1
  have hGes' : Gesittet M'.lauf := by
    refine ⟨gen_konsistent P O passes hO sp M' hReach',
            gen_gut_obs P O passes hO sp M' hReach',
            gen_ausschluss P O passes hO sp M' hReach', ?_, ?_⟩
    · intro i j g1 g2 m s s' e1 e2 hi hj _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
    · intro i j g1 g2 o e1 e2 hi hj _ _ _
      have h1 := hfaden i g1 e1 hi
      have h2 := hfaden j g2 e2 hj
      exact h1.trans h2.symm
  have hBeschr' : BeschraenkteVerschraenkung (D := D) Nb M'.lauf := by
    intro i j g1 g2 e1 e2 hi hj hne
    have h1 := hfaden i g1 e1 hi
    have h2 := hfaden j g2 e2 hj
    exact absurd (h1.trans h2.symm) hne
  have hKette' : M'.welten.length = (J.schrittFaden ++ [f]).length + 1 := by
    have h1 : (J.schrittFaden ++ [f]).length = J.schrittFaden.length + 1 := by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
    have h2 : M'.welten.length = M.welten.length + 1 := by rw [hM'w]; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_left_cancel_iff]
    omega
  have hSchritt' : ∀ (k : Nat) (g0 : Faden) (vor nach0 : World D),
      (J.schrittFaden ++ [f])[k]? = some g0 → M'.welten[k]? = some vor →
      M'.welten[k + 1]? = some nach0 →
      g0 ∈ J.faeden ∧
        Rahmen (D.schreibt (J.code g0)) (D.gschreibt (J.code g0)) vor nach0 := by
    intro k g0 vor nach0 hk hkv hkn
    rw [hM'w] at hkv hkn
    by_cases hlt : k < J.schrittFaden.length
    · have e1 : (J.schrittFaden ++ [f])[k]? = J.schrittFaden[k]? :=
        List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [nach])[k]? = M.welten[k]? :=
        List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [nach])[k + 1]? = M.welten[k + 1]? :=
        List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach0 := by rw [hJw]; exact hkn
      exact J.hSchritt k g0 vor nach0 hk hJkv hJkn
    · by_cases heq : k = J.schrittFaden.length
      · subst heq
        have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = f := (Option.some_inj.mp hk).symm
        have eW : (M.welten ++ [nach])[J.schrittFaden.length]? =
            M.welten[J.schrittFaden.length]? :=
          List.getElem?_append_left (by omega)
        rw [eW, hLastIdx] at hkv
        have hvor : vor = M.speicher.welt (M.spuren f0) :=
          Option.some_inj.mp hkv.symm
        have eW2 : (M.welten ++ [nach])[J.schrittFaden.length + 1]? = some nach := by
          have hle2 : M.welten.length ≤ J.schrittFaden.length + 1 := by omega
          rw [List.getElem?_append_right hle2]
          have hsub : J.schrittFaden.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach0 : nach = nach0 := Option.some_inj.mp hkn
        -- The new-step frame transfers `hFrame` across definitionally equal
        -- memories (successor worlds share memory by construction).
        rw [hg0, hvor, ← hnach0]
        refine ⟨hmem, ?_, ?_⟩
        · intro t ht k2 fld
          exact hFrame.1 t ht k2 fld
        · intro g hg
          exact hFrame.2 g hg
      · have hle : J.schrittFaden.length ≤ k := by omega
        have eNone : (J.schrittFaden ++ [f])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp only [reduceCtorEq] at hk
  -- DELTA: the extended chain keeps member, members, and code by construction;
  -- the link below is unconditional for `t₀` (old steps via `hLinkOld`, the new
  -- step via the prefix witness) and the guard rides along from `hGuardOld`.
  refine ⟨{ faeden := J.faeden, code := J.code, eintritt := J.eintritt,
            welten := M'.welten, schrittFaden := J.schrittFaden ++ [f], l := M'.lauf,
            hKette := hKette', hSchritt := hSchritt', hPaar := J.hPaar,
            hGesittet := hGes', hBeschraenkt := hBeschr',
            hEintritt := J.hEintritt, hSchuld := J.hSchuld, hInvSicht := J.hInvSicht },
          rfl, rfl, hmem, rfl, rfl, ?_, ?_⟩
  · intro k0 g0 hk0 hwr
    have hk0' : (J.schrittFaden ++ [f])[k0]? = some g0 := hk0
    have hwr0 : TraegerSchreibt (J.code g0) (.inl t₀) = true := hwr
    by_cases hlt : k0 < J.schrittFaden.length
    · have eOld : (J.schrittFaden ++ [f])[k0]? = J.schrittFaden[k0]? :=
        List.getElem?_append_left hlt
      rw [eOld] at hk0'
      -- DELTA: old steps inherit from the unconditional prefix link.
      obtain ⟨j, w, Λe, he, hw⟩ := hLinkOld k0 g0 hk0' hwr0
      have hjlt : j < M.lauf.length := by
        by_cases h : j < M.lauf.length
        · exact h
        · have hle : M.lauf.length ≤ j := by omega
          rw [List.getElem?_eq_none hle] at hw
          simp only [reduceCtorEq] at hw
      have hw' : M'.lauf[j]? = some (Schritt.mk g0 (.zugriff t₀ w Λe he)) := by
        rw [hM'l, List.getElem?_append_left hjlt]
        exact hw
      exact ⟨j, w, Λe, he, hw'⟩
    · by_cases heq : k0 = J.schrittFaden.length
      · subst heq
        have hg0 : g0 = f := by
          have eNew : (J.schrittFaden ++ [f])[J.schrittFaden.length]? = some f := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          rw [eNew] at hk0'
          exact (Option.some_inj.mp hk0').symm
        -- DELTA: the new lock step owns no fresh event, so it reuses the prefix
        -- witness, transported into the extended run -- no guard to hide under.
        rw [hg0] at hk0' hwr ⊢
        obtain ⟨j, w, Λe, he, hj⟩ := hwit_new hwr
        have hjlt : j < M.lauf.length := by
          by_cases h : j < M.lauf.length
          · exact h
          · have hle : M.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hj
            simp only [reduceCtorEq] at hj
        have hj' : M'.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
          rw [hM'l, List.getElem?_append_left hjlt]
          exact hj
        exact ⟨j, w, Λe, he, hj'⟩
      · have hle : J.schrittFaden.length ≤ k0 := by omega
        have eNone : (J.schrittFaden ++ [f])[k0]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk0'
        simp only [reduceCtorEq] at hk0'
  · intro g hg hw
    exact hGuardOld g hg hw

end Gabbro.Grammatik
