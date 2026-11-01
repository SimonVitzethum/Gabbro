module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem invU_nil (S : SperrInv D) : InvU S ([] : List (UEintrag D)) :=
  fun _ _ _ h => absurd h List.not_mem_nil

theorem kurzU_nil (N : Nat) : KurzU N ([] : List (UEintrag D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzU_mono {N N' : Nat} {HU : List (UEintrag D)} (h : KurzU N HU) (hN : N ≤ N') :
    KurzU N' HU :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

theorem passtU_append {S : SperrInv D} {U : Umwelt D} {HU : List (UEintrag D)} {e : UEintrag D}
    (h : PasstU S U (HU ++ [e])) : PasstU S U HU :=
  fun L σ s hmem => h L σ s (List.mem_append_left _ hmem)

theorem funkU_append {HU : List (UEintrag D)} (hf : FunkU HU) {N : Nat} (hk : KurzU N HU)
    (e : UEintrag D) (he : N ≤ e.2.1.spur.length) : FunkU (HU ++ [e]) := by
  intro L σ s s' h1 h2
  rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
  · exact hf L σ s s' h1 h2
  · have := hk _ h1
    rw [List.mem_singleton] at h2
    subst h2
    exact absurd he (Nat.not_le.mpr this)
  · have := hk _ h2
    rw [List.mem_singleton] at h1
    subst h1
    exact absurd he (Nat.not_le.mpr this)
  · rw [List.mem_singleton] at h1 h2
    rw [← h1] at h2
    simp only [Prod.mk.injEq] at h2
    exact h2.2.2.symm

theorem invU_append {S : SperrInv D} {HU : List (UEintrag D)} (hi : InvU S HU) (L : D.Lock)
    (σ : World D) (s : Speicher D) (hs : S.inv L s = true) : InvU S (HU ++ [(L, σ, s)]) := by
  intro L' σ' s' hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi L' σ' s' hm
  · rw [List.mem_singleton] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact hs

#print axioms Gabbro.Grammatik.fussSperreB_ok
#print axioms Gabbro.Grammatik.fussSperreB_of_G
#print axioms Gabbro.Grammatik.vertrag_stabil
#print axioms Gabbro.Grammatik.koerperGutS_leer
#print axioms Gabbro.Grammatik.umweltAus_ok

end Gabbro.Grammatik
