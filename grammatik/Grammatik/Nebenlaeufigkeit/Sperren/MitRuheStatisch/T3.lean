/- Part 3 of 3 of `MitRuheStatisch` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheStatisch.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheStatisch.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Graph

variable [DecidableEq D.Fn] (P : Programm D) {fs : List D.Fn}

theorem ruftB_mitRuhe (f g : D.Fn) : ruftB P.mitRuhe (some f) (some g) = ruftB P f g := by
  unfold ruftB
  rw [rumpf_mitRuhe_mE]
  apply congrArg (fun A => !(mE A (P.rumpf f)))
  apply merkmal_ext
  · funext h
    show (!decide (some h = some g)) = !decide (h = g)
    congr 1
    exact decide_eq_decide.mpr ⟨fun e => Option.some.inj e, fun e => e ▸ rfl⟩
  · funext n
    show (!decide (n + 1 = D.sig g + 1)) = !decide (n = D.sig g)
    congr 1
  · rfl

theorem ruftB_mitRuhe_ruhe_ziel (hT : ∀ f, mE (mVoll D) (P.rumpf f) = true) (f : D.Fn) :
    ruftB P.mitRuhe (some f) none = false := by
  unfold ruftB
  rw [rumpf_mitRuhe_mE]
  have e : ∀ A : Merkmal D, A = mVoll D → (!(mE A (P.rumpf f))) = false := by
    intro A hA; rw [hA, hT f]; rfl
  apply e
  apply merkmal_ext
  · funext h
    show (!decide ((some h : Option D.Fn) = none)) = true
    have : decide ((some h : Option D.Fn) = none) = false := decide_eq_false (by intro e; cases e)
    rw [this]; rfl
  · funext n
    show (!decide (n + 1 = 0)) = true
    have : decide (n + 1 = 0) = false := decide_eq_false (Nat.succ_ne_zero n)
    rw [this]; rfl
  · rfl

theorem ruftB_mitRuhe_ruhe (g : D.mitRuhe.Fn) : ruftB P.mitRuhe none g = false := rfl

/-- **Reach from `some w` is reach from `w`** in every round, and never the
    root. -/
theorem erreichB_mitRuhe (hT : ∀ f, mE (mVoll D) (P.rumpf f) = true) (w : D.Fn) :
    ∀ n, (∀ g, erreichB P.mitRuhe (fsRuhe fs) (some w) n (some g) = erreichB P fs w n g) ∧
      erreichB P.mitRuhe (fsRuhe fs) (some w) n none = false
  | 0 => ⟨fun g => by
        show decide ((some g : Option D.Fn) = some w) = decide (g = w)
        exact decide_eq_decide.mpr ⟨fun e => Option.some.inj e, fun e => e ▸ rfl⟩,
      by
        show decide ((none : Option D.Fn) = some w) = false
        exact decide_eq_false (by intro e; cases e)⟩
  | n + 1 => by
      obtain ⟨ih1, ih2⟩ := erreichB_mitRuhe hT w n
      refine ⟨fun g => ?_, ?_⟩
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) (some w) n)
          (some g) = erreichSchritt P fs (erreichB P fs w n) g
        unfold erreichSchritt
        rw [any_fsRuhe, ih1, ih2]
        simp only [Bool.false_and, Bool.false_or, ih1, ruftB_mitRuhe]
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) (some w) n)
          none = false
        unfold erreichSchritt
        rw [any_fsRuhe, ih2]
        simp only [Bool.false_and, Bool.false_or, ruftB_mitRuhe_ruhe_ziel P hT, Bool.and_false,
          List.any_eq_false]
        intro _ _ h
        cases h

/-- Reach from the root is the root alone. -/
theorem erreichB_mitRuhe_ruhe : ∀ n,
    erreichB P.mitRuhe (fsRuhe fs) none n none = true ∧
      ∀ g, erreichB P.mitRuhe (fsRuhe fs) none n (some g) = false
  | 0 => ⟨by
        show decide ((none : Option D.Fn) = none) = true
        exact decide_eq_true rfl,
      fun g => by
        show decide ((some g : Option D.Fn) = none) = false
        exact decide_eq_false (by intro e; cases e)⟩
  | n + 1 => by
      obtain ⟨ih1, ih2⟩ := erreichB_mitRuhe_ruhe n
      refine ⟨?_, fun g => ?_⟩
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) none n) none =
          true
        unfold erreichSchritt
        rw [ih1]
        rfl
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) none n)
          (some g) = false
        unfold erreichSchritt
        have h1 : ruftB P.mitRuhe none (some g) = false := rfl
        rw [any_fsRuhe]
        simp only [ih2, h1, Bool.and_false, Bool.false_or, Bool.false_and, List.any_eq_false]
        intro _ _ h
        cases h

theorem reachB_mitRuhe_ruhe_ruhe : reachB P.mitRuhe (fsRuhe fs) none none = true :=
  (erreichB_mitRuhe_ruhe P _).1

theorem reachB_mitRuhe_ruhe (g : D.Fn) : reachB P.mitRuhe (fsRuhe fs) none (some g) = false :=
  (erreichB_mitRuhe_ruhe P _).2 g

/-- A closed call graph is closed under `ruftB`. -/
theorem abgK_ruft (hvoll : ∀ g : D.Fn, g ∈ fs) {Z : D.Fn → Bool} (hA : AbgK P fs Z) {f g : D.Fn}
    (hf : Z f = true) (hr : ruftB P f g = true) : Z g = true := by
  cases hg : Z g
  · exfalso
    have hm := hA f hf
    have hle : MLe (rufM fs Z)
        ⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩ := by
      refine ⟨fun h hh => ?_, fun n hn => ?_, fun _ _ => rfl⟩
      · show (!decide (h = g)) = true
        have hh' : Z h = true := hh
        have : h ≠ g := fun e => by subst e; rw [hh'] at hg; cases hg
        simp [this]
      · show (!decide (n = D.sig g)) = true
        have h1 := (List.all_eq_true.mp hn) g (hvoll g)
        by_cases e : n = D.sig g
        · subst e; simp [hg] at h1
        · simp [e]
    have := mE_mono hle _ hm
    unfold ruftB at hr
    rw [this] at hr
    cases hr
  · rfl

/-- A closed graph is a fixed point of one more round. -/
theorem erreichSchritt_abg (hvoll : ∀ g : D.Fn, g ∈ fs) {Z : D.Fn → Bool} (hA : AbgK P fs Z) :
    erreichSchritt P fs Z = Z := by
  funext g
  unfold erreichSchritt
  cases hg : Z g
  · simp only [Bool.false_or, List.any_eq_false, Bool.and_eq_true, not_and]
    intro f _ hf hr
    rw [abgK_ruft P hvoll hA hf hr] at hg
    cases hg
  · rfl

/-- Every function's body passes the full feature set (from its own closed
    call graph). -/
theorem mVoll_of_abg (hA : ∀ w, AbgK P fs (reachB P fs w)) (f : D.Fn) :
    mE (mVoll D) (P.rumpf f) = true :=
  mE_mono ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ _ (hA f f (reachB_wurzel P fs f))

/-- **Reach in `P.mitRuhe` from `some w` IS reach in `P` from `w`**, given
    closed call graphs. -/
theorem reachB_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : ∀ w, AbgK P fs (reachB P fs w))
    (w g : D.Fn) : reachB P.mitRuhe (fsRuhe fs) (some w) (some g) = reachB P fs w g := by
  have h := (erreichB_mitRuhe (fs := fs) P (mVoll_of_abg P hA) w (fs.length + 1)).1 g
  unfold reachB
  have hl : (fsRuhe fs).length = fs.length + 1 := congrArg (· + 1) (List.length_map (as := fs) some)
  rw [hl, h]
  show erreichSchritt P fs (reachB P fs w) g = reachB P fs w g
  rw [erreichSchritt_abg P hvoll (hA w)]

theorem reachB_mitRuhe_nicht_ruhe (hA : ∀ w, AbgK P fs (reachB P fs w)) (w : D.Fn) :
    reachB P.mitRuhe (fsRuhe fs) (some w) none = false :=
  (erreichB_mitRuhe (fs := fs) P (mVoll_of_abg P hA) w _).2

end Graph

end Gabbro.Grammatik
