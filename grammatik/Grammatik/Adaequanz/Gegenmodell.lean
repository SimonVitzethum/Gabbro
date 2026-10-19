/-
  File:      Grammatik/Adaequanz/Gegenmodell.lean
  Subject:   THE PLANTED COUNTER-MODELS: why the hypotheses of Theorem 1 are needed.

    * `zaehlerModell` -- a program-neutral implementation (a tree automaton) that counts the height of the
      tree up to `h + 1` and answers wrongly above `h`. It agrees with the spec on every tree of height at
      most `h` (`zaehler_sem`). With `h` the largest height in a finite test set it PASSES that set and is
      WRONG on a taller tree (`kein_endlicher_test`): no finite test set is sufficient for program-neutral
      implementations without a bound on their states. It has `n * (h + 2)` states, so it does not
      contradict Theorem 1: against a set sufficient for `m` it must have more than `m` states
      (`zaehler_ueber_m`). This is the "dependence on program size" counter-example.
    * `sonderfall` -- an implementation that special-cases ONE program `t*` (a program-specific branch) passes
      every test set without `t*` and is wrong at `t*`; a set sufficient for `m` therefore admits no
      automaton with at most `m` states that computes it (`sonderfall_nicht_neutral`).

  Both need a signature with infinitely many trees: a constructor of arity 0 and one of arity at least 1.
-/
import Grammatik.Adaequanz.Minimal

namespace Gabbro.Grammatik.Adaequanz

set_option linter.unusedSectionVars false

variable {σ : Sig} {Q O : Type}

/-- The height as an automaton: `1 + max` of the children's heights. -/
def hoeheA (σ : Sig) : Automat σ Nat Nat where
  δ _ p := 1 + Finset.univ.sup p
  aus n := n

/-- The height of a tree. -/
def hoehe (t : Baum σ) : Nat := (hoeheA σ).lauf t

theorem hoehe_knoten (k : σ.K) (ch : Fin (σ.ar k) → Baum σ) :
    hoehe (.knoten k ch) = 1 + Finset.univ.sup fun i => hoehe (ch i) := rfl

/-- **The counter model**: the spec state and the height saturated at `h + 1`; above `h` the output is
    changed by `kipp`. -/
def zaehlerModell (S : Automat σ Q O) (kipp : O → O) (h : Nat) : Automat σ (Q × Fin (h + 2)) O where
  δ k p := (S.δ k fun i => (p i).1,
    ⟨min (h + 1) (1 + Finset.univ.sup fun i => ((p i).2 : Nat)), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩)
  aus x := if (x.2 : Nat) = h + 1 then kipp (S.aus x.1) else S.aus x.1

section Zaehler

variable (S : Automat σ Q O) (kipp : O → O) (h : Nat)

theorem zaehler_δ (k : σ.K) (p : Fin (σ.ar k) → Q × Fin (h + 2)) :
    (zaehlerModell S kipp h).δ k p = (S.δ k fun i => (p i).1,
      ⟨min (h + 1) (1 + Finset.univ.sup fun i => ((p i).2 : Nat)), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩) := rfl

theorem zaehler_aus (x : Q × Fin (h + 2)) :
    (zaehlerModell S kipp h).aus x = if (x.2 : Nat) = h + 1 then kipp (S.aus x.1) else S.aus x.1 := rfl

theorem zaehler_fst (t : Baum σ) : ((zaehlerModell S kipp h).lauf t).1 = S.lauf t := by
  induction t with
  | knoten k ch ih =>
      rw [Automat.lauf_knoten (zaehlerModell S kipp h), zaehler_δ, Automat.lauf_knoten S]
      show (S.δ k fun i => ((zaehlerModell S kipp h).lauf (ch i)).1) = _
      rw [funext ih]

theorem zaehler_snd (t : Baum σ) : (((zaehlerModell S kipp h).lauf t).2 : Nat) = min (h + 1) (hoehe t) := by
  induction t with
  | knoten k ch ih =>
      rw [Automat.lauf_knoten (zaehlerModell S kipp h), zaehler_δ, hoehe_knoten]
      show min (h + 1) (1 + Finset.univ.sup fun i => (((zaehlerModell S kipp h).lauf (ch i)).2 : Nat)) = _
      rw [funext ih]
      have hd : (Finset.univ.sup fun i => min (h + 1) (hoehe (ch i))) =
          min (h + 1) (Finset.univ.sup fun i => hoehe (ch i)) := by
        have := Finset.sup_inf_distrib_left Finset.univ (fun i => hoehe (ch i)) (h + 1)
        exact this.symm
      rw [hd]
      omega

/-- **The counter model is wrong exactly on the trees taller than `h`.** -/
theorem zaehler_sem (t : Baum σ) :
    (zaehlerModell S kipp h).sem t = if h + 1 ≤ hoehe t then kipp (S.sem t) else S.sem t := by
  have h1 := zaehler_fst S kipp h t
  have h2 := zaehler_snd S kipp h t
  unfold Automat.sem
  rw [zaehler_aus, h2, h1]
  by_cases hh : h + 1 ≤ hoehe t
  · rw [if_pos (by omega), if_pos hh]
  · rw [if_neg (by omega), if_neg hh]

theorem zaehler_zustaende [Fintype Q] : Fintype.card (Q × Fin (h + 2)) = Fintype.card Q * (h + 2) := by
  simp [Fintype.card_prod, Fintype.card_fin]

end Zaehler

/-! ## A tower of every height -/

/-- The tree of height `j + 1`: `k1` over `k1` over ... over the leaf `k0`. -/
def turm {k0 : σ.K} (h0 : σ.ar k0 = 0) (k1 : σ.K) : Nat → Baum σ
  | 0 => .knoten k0 fun i => absurd i.isLt (by omega)
  | j + 1 => .knoten k1 fun _ => turm h0 k1 j

theorem hoehe_turm {k0 k1 : σ.K} (h0 : σ.ar k0 = 0) (h1 : 0 < σ.ar k1) (j : Nat) :
    hoehe (turm h0 k1 j) = j + 1 := by
  induction j with
  | zero =>
      simp only [turm, hoehe_knoten]
      have : (Finset.univ.sup fun i : Fin (σ.ar k0) => hoehe (absurd i.isLt (by omega) : Baum σ)) = 0 :=
        Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => absurd i.isLt (by omega))
      rw [this]
  | succ j ih =>
      simp only [turm, hoehe_knoten, ih]
      have hne : (Finset.univ : Finset (Fin (σ.ar k1))).Nonempty := ⟨⟨0, h1⟩, Finset.mem_univ _⟩
      rw [Finset.sup_const hne]
      omega

/-- A member's height is at most the sum of the heights. -/
theorem hoehe_le_summe {M : List (Baum σ)} {p : Baum σ} (hp : p ∈ M) : hoehe p ≤ (M.map hoehe).sum := by
  induction M with
  | nil => simp at hp
  | cons a M ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have := ih hp; omega

/-- **No finite test set without a bound on the states.** For every finite list of trees there is a
    program-neutral implementation (the counter model) that passes it and is wrong on some tree. -/
theorem kein_endlicher_test (S : Automat σ Q O) {kipp : O → O} (hkipp : ∀ o, kipp o ≠ o)
    {k0 k1 : σ.K} (h0 : σ.ar k0 = 0) (h1 : 0 < σ.ar k1) (M : List (Baum σ)) :
    let h := (M.map hoehe).sum
    (∀ p ∈ M, (zaehlerModell S kipp h).sem p = S.sem p) ∧
      (zaehlerModell S kipp h).sem (turm h0 k1 h) ≠ S.sem (turm h0 k1 h) := by
  intro h
  refine ⟨fun p hp => ?_, ?_⟩
  · have : hoehe p ≤ h := hoehe_le_summe hp
    rw [zaehler_sem, if_neg (by omega)]
  · rw [zaehler_sem, if_pos (hoehe_turm h0 h1 h).symm.le]
    exact hkipp _

/-- **The counter model needs more than `m` states** against a test set sufficient for `m`: the bound on the
    implementation's states is a hypothesis that cannot be dropped. -/
theorem zaehler_ueber_m [Fintype Q] (S : Automat σ Q O) {kipp : O → O} (hkipp : ∀ o, kipp o ≠ o)
    {k0 k1 : σ.K} (h0 : σ.ar k0 = 0) (h1 : 0 < σ.ar k1) {M : List (Baum σ)} {m : Nat} (hM : Hinreichend S M m) :
    m < Fintype.card Q * ((M.map hoehe).sum + 2) := by
  obtain ⟨hpass, hfalsch⟩ := kein_endlicher_test S hkipp h0 h1 M
  by_contra hle
  push Not at hle
  exact hfalsch (hM _ (zaehlerModell S kipp _) (by rw [zaehler_zustaende]; exact hle) hpass _)

/-! ## A program-specific branch -/

open Classical in
/-- An implementation that special-cases the one program `ts`. -/
noncomputable def sonderfall (S : Automat σ Q O) (kipp : O → O) (ts : Baum σ) (t : Baum σ) : O :=
  if t = ts then kipp (S.sem t) else S.sem t

/-- **A program-specific branch is no neutral implementation with at most `m` states** when a sufficient set
    for `m` does not contain the special program. -/
theorem sonderfall_nicht_neutral (S : Automat σ Q O) {kipp : O → O} (hkipp : ∀ o, kipp o ≠ o) {ts : Baum σ}
    {M : List (Baum σ)} {m : Nat} (hM : Hinreichend S M m) (hts : ts ∉ M) :
    ∀ (Q' : Type) [Fintype Q'] (I : Automat σ Q' O), Fintype.card Q' ≤ m → I.sem ≠ sonderfall S kipp ts := by
  intro Q' _ I hm hI
  have hpass : ∀ p ∈ M, I.sem p = S.sem p := fun p hp => by
    rw [hI, sonderfall, if_neg (fun he : p = ts => hts (he ▸ hp))]
  have := hM Q' I hm hpass ts
  rw [hI, sonderfall, if_pos rfl] at this
  exact hkipp _ this

end Gabbro.Grammatik.Adaequanz
