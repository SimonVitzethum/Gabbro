/-
  File:      Grammatik/Zielsatz/AtomarMasken.lean
  Subject:   THE SAME-CORE INTERRUPT LEG OVER GA RUNS (Opus lane O25b, 2026-09-26). Standalone.

  `KernHaltG` (fix lane F11) speaks about G runs. With shared atomics the machine's runs are W
  runs, whose G-parts are GX runs, which are GA runs (`gx_ga`). `KernHaltGA` is `KernHaltG` with
  `LaufGA` in place of `LaufG`; `kernHaltGA_gilt` proves it for every program, as
  `kernHaltG_gilt` does: the argument reads only the threads' own states, which a GA step moves
  exactly as its inner G step does.
-/
import Grammatik.Zielsatz.Masken
import Grammatik.Speichermodell.Atomar

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-- **No same-core interrupt deadlock, on GA runs** (`KernHaltG` with `LaufGA`). -/
def KernHaltGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (H : Faden → Prop) (Z : Faden → D.Fn → Prop)
    (A : Faden → D.Fn → Merkmal D),
    (∀ t, H t → MerkAbg P (Z t) (A t)) →
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t)) →
    (∀ t, H t → ∀ (f : D.Fn) (L : D.Lock), Z t f → (A t f).sperre L = true →
      D.maskiert L = true) →
    (∀ (t : Faden) (L : D.Lock), ¬ AnSperre M0 t L) →
    ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufGA P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ (g f : Faden) (L : D.Lock), H g → f ≠ g → kern f = kern g →
        AnSperre M g L → L ∉ offen ((M.faeden f).spur)

section Lauf

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem merkInvG_laufA {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : LaufGA P O passes M0 ms fs n) {Z : D.Fn → Prop} {A : D.Fn → Merkmal D}
    (hA : MerkAbg P Z A) (t : Faden) (h0 : MerkInvG Z A (M0.faeden t)) :
    ∀ k, k ≤ n → MerkInvG Z A ((ms k).faeden t)
  | 0, _ => by rw [hl.1]; exact h0
  | k + 1, hk => by
      have hs := hl.2 k (by omega)
      have ih := merkInvG_laufA hl hA t h0 k (by omega)
      by_cases htu : t = fs k
      · subst htu
        obtain ⟨σ, M'', hs', _, _, _, hfa, _, _⟩ := hs
        rw [hfa]
        exact merkInvG_schritt hA hs' ih
      · rw [ga_fremd hs t htu]
        exact ih

theorem laufGA_fremd {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : LaufGA P O passes M0 ms fs n) (g : Faden) (hg : ∀ k, k < n → fs k ≠ g) :
    ∀ k, k ≤ n → (ms k).faeden g = M0.faeden g
  | 0, _ => by rw [hl.1]
  | k + 1, hk => by
      rw [ga_fremd (hl.2 k (by omega)) g (Ne.symm (hg k (by omega)))]
      exact laufGA_fremd hl g hg k (by omega)

/-- **THE LEG over GA runs, for every program.** -/
theorem kernHaltGA_gilt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : KernHaltGA P O passes M0 M := by
  intro kern H Z A hAbg hInv0 hMask hM0 ms fs n hl hMn hKP g f L hHg hfg hkern hA hL
  subst hMn
  have hnf : ¬ FertigG (ms n) g := anSperre_nicht_fertig hA
  by_cases hstep : ∃ i, i < n ∧ fs i = g
  · obtain ⟨i, hin, hig, hmin⟩ := erster_index (fun i => fs i = g) n hstep
    have hmaskL : D.maskiert L = true := by
      have hI := merkInvG_laufA hl (hAbg g hHg) g (hInv0 g hHg) n (Nat.le_refl n)
      have h := sperre_merkmal hI hA
      exact hMask g hHg _ L h.1 h.2
    have hfn : ∀ k, i ≤ k → k < n → fs k ≠ f := by
      intro k hik hkn hk
      have h2 := hKP.2 g i n k hHg hig hmin hik hkn (Nat.le_refl n) hnf
        (by rw [hk]; exact hkern)
      rw [hk] at h2
      exact hfg h2
    have hsub : LaufGA P O passes (ms i) (fun k => ms (i + k)) (fun k => fs (i + k)) (n - i) :=
      ⟨rfl, fun k hk => by
        have h3 := hl.2 (i + k) (by omega)
        rw [Nat.add_assoc] at h3
        exact h3⟩
    have hconst := laufGA_fremd hsub f (fun k hk => hfn (i + k) (by omega) (by omega))
      (n - i) (Nat.le_refl _)
    have e : i + (n - i) = n := by omega
    rw [e] at hconst
    have hLi : L ∈ offen ((ms i).faeden f).spur := by rw [← hconst]; exact hL
    have hne : f ≠ fs i := by rw [hig]; exact hfg
    have := hKP.1 i hin (by rw [hig]; exact hHg) (by rw [hig]; exact hmin) f L hne
      (by rw [hig]; exact hkern) hLi
    rw [hmaskL] at this
    exact Bool.noConfusion this
  · have hnie : ∀ k, k < n → fs k ≠ g := fun k hk hq => hstep ⟨k, hk, hq⟩
    have he := laufGA_fremd hl g hnie n (Nat.le_refl n)
    exact hM0 g L (anSperre_gleich he.symm hA)

/-- **Every G run is a GA run**, so `KernHaltGA` contains `KernHaltG`. -/
theorem kernHaltG_of_GA {M0 M : RufMaschineG D} (h : KernHaltGA P O passes M0 M) :
    KernHaltG P O passes M0 M := by
  intro kern H Z A hAbg hInv0 hMask hM0 ms fs n hl hMn hKP
  exact h kern H Z A hAbg hInv0 hMask hM0 ms fs n ⟨hl.1, fun k hk => schrittGA_of_g (hl.2 k hk)⟩
    hMn hKP

end Lauf

#print axioms Gabbro.Grammatik.Zielsatz.kernHaltGA_gilt

end Gabbro.Grammatik.Zielsatz
