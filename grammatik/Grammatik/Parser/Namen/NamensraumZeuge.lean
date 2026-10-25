import Grammatik.Parser.Namen.Namensraum

/-!
  File:      Grammatik/Parser/Namen/NamensraumZeuge.lean
  Subject:   Witnesses of the name-space rule, for every project: a project with one dependency,
             placed as the program and as a copy, its dependency under two different copies.
             An own name and a public name of the dependency are reached, and every path means
             the same on both places. Nothing here names a particular program.
-/

namespace Gabbro.Grammatik.Parser.Namensraum

/-- The project as the program, its dependency `d` (public names `pub`) under the copy `k₁`. -/
def platzA (d k₁ : String) (pub : List Pfad) : Platz := ⟨none, [(d, k₁, pub)]⟩

/-- The project as the copy `n`, its dependency under the copy `k₂`. -/
def platzB (n d k₂ : String) (pub : List Pfad) : Platz := ⟨some n, [(d, k₂, pub)]⟩

theorem platzA_gut (d k₁ : String) (pub : List Pfad) : (platzA d k₁ pub).Gut := by
  unfold Platz.Gut platzA; simp

theorem platzB_gut {n d k₂ : String} (pub : List Pfad) (h : n ≠ k₂) : (platzB n d k₂ pub).Gut := by
  unfold Platz.Gut platzB; simp [h]

/-- The first candidate of a path written at the root is the path itself. -/
theorem kandidaten_wurzel (Q : Quelle) (p : Pfad) : ∃ r, kandidaten Q [] p = p :: r := by
  exact ⟨(Q.verwendet.filter fun z => decide (z.1 = []) && decide (z.2.getLast? = p.getLast?)).map Prod.snd,
    by simp [kandidaten, umgebend]⟩

theorem aufloese_erster {Q : Quelle} {L : Platz} {p : Pfad} (h : qualifiziere L p ∈ sichtbar Q L) :
    aufloese Q L [] p = some (qualifiziere L p) := by
  obtain ⟨r, hr⟩ := kandidaten_wurzel Q p
  simp [aufloese, aufloeseK, hr, h]

/-- **An own name is reached**, in the project's own copy. -/
theorem eigen_erreicht {Q : Quelle} {n d k : String} {pub : List Pfad} {x : String} {xs : Pfad}
    (hx : x :: xs ∈ Q.namen) (hxd : x ≠ d) :
    aufloese Q (platzB n d k pub) [] (x :: xs) = some (some n, x :: xs) := by
  have hq : qualifiziere (platzB n d k pub) (x :: xs) = (some n, x :: xs) := by
    simp [qualifiziere, platzB, ziel, Ne.symm hxd]
  rw [aufloese_erster (by rw [hq]; simp [sichtbar, platzB, hx]), hq]

/-- **A public name of the dependency is reached**, in the dependency's copy. -/
theorem abh_erreicht (Q : Quelle) {n d k : String} {pub : List Pfad} {y : Pfad} (hy : y ∈ pub) :
    aufloese Q (platzB n d k pub) [] (d :: y) = some (some k, y) := by
  have hq : qualifiziere (platzB n d k pub) (d :: y) = (some k, y) := by
    simp [qualifiziere, platzB, ziel]
  rw [aufloese_erster (by rw [hq]; simp [sichtbar, platzB, hy]), hq]

/-- **The witness of `aufloeseK_platz`**: on the two places -- the project as the program with its
    dependency under `k₁`, and as the copy `n` with its dependency under `k₂ ≠ k₁` -- every path
    means the same candidate, while an own name and a public name of the dependency are reached in
    different copies. -/
theorem namensraum_zeuge (Q : Quelle) {n d k₁ k₂ : String} (pub : List Pfad) (hn : n ≠ k₂) :
    (∀ von p, aufloeseK Q (platzA d k₁ pub) von p = aufloeseK Q (platzB n d k₂ pub) von p) ∧
      (platzA d k₁ pub).ns ≠ (platzB n d k₂ pub).ns :=
  ⟨aufloeseK_platz Q (platzA_gut d k₁ pub) (platzB_gut pub hn) rfl, by simp [platzA, platzB]⟩

#print axioms namensraum_zeuge
#print axioms eigen_erreicht
#print axioms abh_erreicht

end Gabbro.Grammatik.Parser.Namensraum
