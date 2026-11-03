/-! Absolute alignment of canonical global addresses.

    The relative layout (`globStarts` on the common `wordAlign` grid) preserves
    declared alignment; adding an image base that lies on the combined
    `Nat.lcm 8 N` grid keeps every placed global's absolute address divisible
    by its declared alignment and by eight. The base-grid premise is the
    loader/runner base-placement duty (THEOREM-MAP 127): relative geometry alone
    does not discharge it. -/
module
public import Stage0.Senke.Welt.AnordnungLayouta
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

end Gabbro.Stage0.Senke
