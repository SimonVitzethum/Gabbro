/-
  File:      Grammatik/Zielsatz/Eigenschaften/KernMaskeGleich.lean
  Subject:   The guarded machine of `KernMaske.lean` loses NO run that `KernPlan` admits, so
             `KernHaltM` and `KernHaltE` are the same statement.

  `kernPlan_aus_lauf` says a guarded run meets `KernPlan`. Here the converse: every run of
  machine G that meets `KernPlan` lifts to a guarded run through the same machines
  (`kernPlan_lift`), provided no thread of the start machine holds a lock declared `masks irqs`
  (every declared root holds nothing, `Akzeptiert.wurzeln`). So replacing the leg `KernHaltE`
  of `Ziel` by the leg over guarded runs is not a weakening: it quantifies over exactly the same
  runs, and the schedule becomes a property of the machine instead of a premise
  (`kernHaltE_iff_M`). The proposal for `Spec.lean` is dokumente/PLAN-DYNAMIC.md section 8a.4.
-/
import Grammatik.Zielsatz.Eigenschaften.KernMaske

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

theorem begLauf_iff (fs : Nat → Faden) :
    ∀ (k : Nat) (g : Faden), begLauf fs k g ↔ ∃ i, i < k ∧ fs i = g
  | 0, g => ⟨fun h => h.elim, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, g => by
      show (g = fs k ∨ begLauf fs k g) ↔ _
      rw [begLauf_iff fs k g]
      constructor
      · rintro (h | ⟨i, hi, hig⟩)
        · exact ⟨k, by omega, h.symm⟩
        · exact ⟨i, by omega, hig⟩
      · rintro ⟨i, hi, hig⟩
        by_cases hik : i = k
        · subst hik
          exact Or.inl hig.symm
        · exact Or.inr ⟨i, by omega, hig⟩

/-- The mask state of `maskLauf` stays consistent along a G run. -/
theorem maskLauf_ok {P : Programm D} {O : Orakel D} {passes : Nat} {kern : Faden → Nat}
    {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n)
    (h0 : ∀ (t : Faden) (L : D.Lock), L ∈ offen (M0.faeden t).spur → D.maskiert L = false) :
    ∀ k, k ≤ n → MaskeOk kern (ms k) (maskLauf kern ms fs (fun _ => []) k)
  | 0, _ => by
      show MaskeOk kern (ms 0) (fun _ => [])
      rw [hl.1]
      intro c f L
      constructor
      · intro hm
        exact absurd hm List.not_mem_nil
      · rintro ⟨_, hm, hL⟩
        rw [h0 f L hL] at hm
        exact Bool.noConfusion hm
  | k + 1, hk =>
      maskeOk_schritt (hl.2 k (by omega)) (maskLauf_ok hl h0 k (by omega))

/-- **EVERY RUN THAT `KernPlan` ADMITS IS A GUARDED RUN**: the guards of `KernSchritt` are the two
    clauses of `KernPlan`, read at the step they bind. -/
theorem kernPlan_lift {P : Programm D} {O : Orakel D} {passes : Nat} {kern : Faden → Nat}
    {H : Faden → Prop} {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : LaufG P O passes M0 ms fs n) (hp : KernPlan kern H ms fs n)
    (h0 : ∀ (t : Faden) (L : D.Lock), L ∈ offen (M0.faeden t).spur → D.maskiert L = false) :
    ∃ zs : Nat → KernZ D,
      KernStart kern M0 ⟨M0, fun _ => [], fun _ => False⟩ ∧
      KernLauf P O passes kern H ⟨M0, fun _ => [], fun _ => False⟩ zs fs n ∧
      ∀ k, k ≤ n → (zs k).m = ms k := by
  have hstart : KernStart kern M0 ⟨M0, fun _ => [], fun _ => False⟩ :=
    ⟨rfl, by
      have := maskLauf_ok (kern := kern) hl h0 0 (Nat.zero_le n)
      rw [hl.1] at this
      exact this, fun _ h => h⟩
  refine ⟨fun k => ⟨ms k, maskLauf kern ms fs (fun _ => []) k, begLauf fs k⟩, hstart,
    ⟨?_, fun k hk => ⟨hl.2 k hk, ?_, ?_, rfl, rfl⟩⟩, fun k _ => rfl⟩
  · show (⟨ms 0, fun _ => [], fun _ => False⟩ : KernZ D) = _
    rw [hl.1]
  · -- entry only when unmasked: clause 1 of the plan, and the mask state is consistent
    intro hH hnb
    have hmin : ∀ r, r < k → fs r ≠ fs k := fun r hr hrf => hnb ((begLauf_iff fs k _).2 ⟨r, hr, hrf⟩)
    have hok := maskLauf_ok (kern := kern) hl h0 k (Nat.le_of_lt hk)
    show maskLauf kern ms fs (fun _ => []) k (kern (fs k)) = []
    by_cases hnil : maskLauf kern ms fs (fun _ => []) k (kern (fs k)) = []
    · exact hnil
    · obtain ⟨f, L, hkf, hm, hL⟩ := (maske_nichtleer_iff hok _).1 hnil
      by_cases hf : f = fs k
      · rw [hf] at hL
        have hl' : LaufG P O passes M0 ms fs k := ⟨hl.1, fun j hj => hl.2 j (by omega)⟩
        have hconst := laufG_fremd hl' (fs k) (fun r hr => hmin r hr) k (Nat.le_refl k)
        rw [hconst] at hL
        rw [h0 (fs k) L hL] at hm
        exact Bool.noConfusion hm
      · have := hp.1 k hk hH hmin f L hf hkf hL
        rw [this] at hm
        exact Bool.noConfusion hm
  · -- run to completion: clause 2 of the plan at the step after
    intro g hHg hb hnf hkern
    have hb' := (begLauf_iff fs k g).1 hb
    obtain ⟨i, hi, hig, hmin⟩ := erster_index (fun i => fs i = g) k hb'
    by_cases hfg : fs k = g
    · exact hfg.symm
    · have hnf' : ¬ FertigG (ms (k + 1)) g := by
        intro hF
        apply hnf
        have e := rufSchrittG_fremd (hl.2 k hk) g (fun h => hfg h.symm)
        unfold FertigG at hF ⊢
        rw [e] at hF
        exact hF
      have := hp.2 g i (k + 1) k hHg hig hmin (Nat.le_of_lt hi) (Nat.lt_succ_self k) hk hnf'
        hkern.symm
      exact absurd this hfg

/-- **`KernHaltM` is `KernHaltE`**: the guarded machine and the plan quantify over the same runs
    (for a start machine in which no thread holds a masking lock). -/
theorem kernHaltE_iff_M {P : Programm D} {O : Orakel D} {passes : Nat} {M0 M : RufMaschineG D}
    (h0 : ∀ (t : Faden) (L : D.Lock), L ∈ offen (M0.faeden t).spur → D.maskiert L = false) :
    KernHaltE P O passes M0 M ↔ KernHaltM P O passes M0 M := by
  constructor
  · intro hE kern Z0 zs fs n hs hl hM g f L hH hfg hk hA
    exact hE kern (fun k => (zs k).m) fs n (kernLauf_laufG hs hl) hM (kernPlan_aus_lauf hs hl)
      g f L hH hfg hk hA
  · intro hM kern ms fs n hl hMn hp g f L hH hfg hk hA
    obtain ⟨zs, hs, hz, hm⟩ := kernPlan_lift hl hp h0
    exact hM kern _ zs fs n hs hz (by rw [hm n (Nat.le_refl n)]; exact hMn) g f L hH hfg hk hA

#print axioms Gabbro.Grammatik.Zielsatz.begLauf_iff
#print axioms Gabbro.Grammatik.Zielsatz.maskLauf_ok
#print axioms Gabbro.Grammatik.Zielsatz.kernPlan_lift
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltE_iff_M

end Gabbro.Grammatik.Zielsatz
