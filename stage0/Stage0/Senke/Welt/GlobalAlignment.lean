module
public import Stage0.Senke.Welt.AnordnungLayouta
/-! Absolute alignment of canonical global addresses.

    The relative layout (`globStarts` on the common `wordAlign` grid) preserves
    declared alignment; adding an image base that lies on the combined
    `Nat.lcm 8 N` grid keeps every placed global's absolute address divisible
    by its declared alignment and by eight. The base-grid premise is the
    loader/runner base-placement duty (THEOREM-MAP 127): relative geometry alone
    does not discharge it. -/
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Every enumerated relative start lies on the common grid of its own alignment. -/
theorem globStarts_wordAlign_dvd {G : Type} (gs : List G) (o : Nat)
    (sz alignment : G → Nat) (g : G) (start : Nat)
    (hm : (g, start) ∈ globStarts gs o sz (fun g => wordAlign (alignment g)))
    (hpos : 0 < alignment g) : wordAlign (alignment g) ∣ start := by
  induction gs generalizing o with
  | nil => simp [globStarts] at hm
  | cons a gs ih =>
    simp only [globStarts, List.mem_cons] at hm
    rcases hm with hm | hm
    · simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact alignUp_dvd o (wordAlign (alignment a)) (Nat.lcm_pos (by decide) hpos)
    · exact ih _ hm

/-- **The placement lemma**: with a base on the combined grid, the absolute
    address of a placed global is a multiple of that grid. -/
theorem layU_ga_lcm_dvd (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat)
    (g : Fin u.globs.length) (hpos : 0 < globAlign u g)
    (hbase : Nat.lcm 8 (globAlign u g) ∣ b) :
    Nat.lcm 8 (globAlign u g) ∣ (layU u tor b).ga g := by
  have hmem : (g, globStartOf (List.finRange u.globs.length) 0 (globSz u)
      (fun g => wordAlign (globAlign u g)) g) ∈
      globStarts (List.finRange u.globs.length) 0 (globSz u)
        (fun g => wordAlign (globAlign u g)) :=
    globStartOf_mem _ _ _ _ g (by simp)
  have hrel : Nat.lcm 8 (globAlign u g) ∣ globStartOf (List.finRange u.globs.length) 0
      (globSz u) (fun g => wordAlign (globAlign u g)) g :=
    globStarts_wordAlign_dvd _ _ _ _ _ _ hmem hpos
  show Nat.lcm 8 (globAlign u g) ∣ b + globStartOf (List.finRange u.globs.length) 0
    (globSz u) (fun g => wordAlign (globAlign u g)) g
  exact Nat.dvd_add hbase hrel

/-- **Every aligned global's absolute address is divisible by its alignment.** -/
theorem layU_ga_aligned (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat)
    (g : Fin u.globs.length) (hpos : 0 < globAlign u g)
    (hbase : Nat.lcm 8 (globAlign u g) ∣ b) :
    globAlign u g ∣ (layU u tor b).ga g :=
  Nat.dvd_trans (Nat.dvd_lcm_right 8 (globAlign u g)) (layU_ga_lcm_dvd u tor b g hpos hbase)

/-- **Absolute addresses keep eight-byte storage alignment.** -/
theorem layU_ga_word_aligned (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat)
    (g : Fin u.globs.length) (hpos : 0 < globAlign u g)
    (hbase : Nat.lcm 8 (globAlign u g) ∣ b) :
    8 ∣ (layU u tor b).ga g :=
  Nat.dvd_trans (Nat.dvd_lcm_left 8 (globAlign u g)) (layU_ga_lcm_dvd u tor b g hpos hbase)

/-- One step of the required base alignment: skip globals without a positive alignment. -/
def bodenSchritt (u : UProg) (acc : Nat) (g : Fin u.globs.length) : Nat :=
  if 0 < globAlign u g then Nat.lcm acc (Nat.lcm 8 (globAlign u g)) else acc

/-- The required base alignment of an image: the finite least common multiple of eight
    and every positively declared static alignment. The image builder aligns the world base
    up to this grid (`alignUp`), so every placed global is absolutely aligned; the loader
    maps the file byte-exact at `IMG`, hence honours the builder-chosen offset exactly
    (page granularity constrains only `IMG` itself, which is `2 ^ 28`). -/
def bodenAusrichtung (u : UProg) : Nat :=
  (List.finRange u.globs.length).foldl (bodenSchritt u) 8

/-- The accumulator divides every fold it starts: skipped globals keep it. -/
theorem bodenSchritt_dvd (u : UProg) (acc : Nat) (g : Fin u.globs.length) :
    acc ∣ bodenSchritt u acc g := by
  unfold bodenSchritt
  split
  · exact Nat.dvd_lcm_left _ _
  · exact Nat.dvd_refl _

/-- The accumulator divides the whole fold it starts. -/
theorem bodenFold_dvd (u : UProg) : ∀ (l : List (Fin u.globs.length)) (acc : Nat),
    acc ∣ l.foldl (bodenSchritt u) acc := by
  intro l acc
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.dvd_trans (bodenSchritt_dvd u acc hd) (ih _)

/-- The required base alignment is positive: eight is, and every step keeps it. -/
theorem boden_pos (u : UProg) : 0 < bodenAusrichtung u := by
  unfold bodenAusrichtung
  have h : ∀ (l : List (Fin u.globs.length)) (acc : Nat), 0 < acc →
      0 < l.foldl (bodenSchritt u) acc := by
    intro l acc ha
    induction l generalizing acc with
    | nil => simpa using ha
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold bodenSchritt
      split
      · next hc => exact Nat.lcm_pos ha (Nat.lcm_pos (by decide) hc)
      · exact ha
  exact h _ _ (by decide)

/-- Every positively declared alignment's combined grid divides the required base alignment. -/
theorem boden_teilt (u : UProg) (g : Fin u.globs.length) (hpos : 0 < globAlign u g) :
    Nat.lcm 8 (globAlign u g) ∣ bodenAusrichtung u := by
  unfold bodenAusrichtung
  have hmem : g ∈ List.finRange u.globs.length := by simp
  have h : ∀ (l : List (Fin u.globs.length)) (acc : Nat), g ∈ l →
      Nat.lcm 8 (globAlign u g) ∣ l.foldl (bodenSchritt u) acc := by
    intro l acc hm
    induction l generalizing acc with
    | nil => simp at hm
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · unfold bodenSchritt
        rw [if_pos hpos]
        exact Nat.dvd_trans (Nat.dvd_lcm_right _ _) (bodenFold_dvd u tl _)
      · by_cases hc : 0 < globAlign u hd
        · unfold bodenSchritt
          rw [if_pos hc]
          exact ih _ hm
        · unfold bodenSchritt
          rw [if_neg hc]
          exact ih _ hm
  exact h _ _ hmem

/-- An aligned builder base meets every positively declared alignment's combined grid. -/
theorem boden_basis (u : UProg) (g : Fin u.globs.length) (hpos : 0 < globAlign u g)
    (b : Nat) (hb : bodenAusrichtung u ∣ b) :
    Nat.lcm 8 (globAlign u g) ∣ b :=
  Nat.dvd_trans (boden_teilt u g hpos) hb

end Gabbro.Stage0.Senke
