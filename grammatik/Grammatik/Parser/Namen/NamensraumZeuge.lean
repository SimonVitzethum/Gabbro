import Mathlib.Data.List.Nodup
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
  unfold Platz.Gut platzA; simp only [List.mem_cons, List.not_mem_nil, or_false, ne_eq, reduceCtorEq, not_false_eq_true, implies_true,
  List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil, and_self]

theorem platzB_gut {n d k₂ : String} (pub : List Pfad) (h : n ≠ k₂) : (platzB n d k₂ pub).Gut := by
  unfold Platz.Gut platzB; simp only [List.mem_cons, List.not_mem_nil, or_false, ne_eq, Option.some.injEq, forall_eq, h,
  not_false_eq_true, List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil, and_self]

/-- The first candidate of a path written at the root is the path itself. -/
theorem kandidaten_wurzel (Q : Quelle) (p : Pfad) : ∃ r, kandidaten Q [] p = p :: r := by
  exact ⟨(Q.verwendet.filter fun z => decide (z.1 = []) && decide (z.2.getLast? = p.getLast?)).map Prod.snd,
    by simp only [kandidaten, umgebend, List.take_nil, List.length_nil, Nat.zero_add, List.range_one,
  List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, List.flatMap_cons,
  List.flatMap_nil, List.append_nil, List.cons_append]⟩

theorem aufloese_erster {Q : Quelle} {L : Platz} {p : Pfad} (h : qualifiziere L p ∈ sichtbar Q L) :
    aufloese Q L [] p = some (qualifiziere L p) := by
  obtain ⟨r, hr⟩ := kandidaten_wurzel Q p
  simp only [aufloese, aufloeseK, hr, h, decide_true, List.find?_cons_of_pos, Option.map_some]

/-- **An own name is reached**, in the project's own copy. -/
theorem eigen_erreicht {Q : Quelle} {n d k : String} {pub : List Pfad} {x : String} {xs : Pfad}
    (hx : x :: xs ∈ Q.namen) (hxd : x ≠ d) :
    aufloese Q (platzB n d k pub) [] (x :: xs) = some (some n, x :: xs) := by
  have hq : qualifiziere (platzB n d k pub) (x :: xs) = (some n, x :: xs) := by
    simp only [qualifiziere, platzB, ziel, Ne.symm hxd, ↓reduceIte]
  rw [aufloese_erster (by rw [hq]; simp only [sichtbar, platzB, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
  List.mem_map, Prod.mk.injEq, true_and, exists_eq_right, hx, Option.some.injEq, exists_eq_right_right, true_or]), hq]

/-- **A public name of the dependency is reached**, in the dependency's copy. -/
theorem abh_erreicht (Q : Quelle) {n d k : String} {pub : List Pfad} {y : Pfad} (hy : y ∈ pub) :
    aufloese Q (platzB n d k pub) [] (d :: y) = some (some k, y) := by
  have hq : qualifiziere (platzB n d k pub) (d :: y) = (some k, y) := by
    simp only [qualifiziere, platzB, ziel, ↓reduceIte]
  rw [aufloese_erster (by rw [hq]; simp only [sichtbar, platzB, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
  List.mem_map, Prod.mk.injEq, Option.some.injEq, exists_eq_right_right, true_and, exists_eq_right, hy, or_true]), hq]

/-- **The witness of `aufloeseK_platz`**: on the two places -- the project as the program with its
    dependency under `k₁`, and as the copy `n` with its dependency under `k₂ ≠ k₁` -- every path
    means the same candidate, while an own name and a public name of the dependency are reached in
    different copies. -/
theorem namensraum_zeuge (Q : Quelle) {n d k₁ k₂ : String} (pub : List Pfad) (hn : n ≠ k₂) :
    (∀ von p, aufloeseK Q (platzA d k₁ pub) von p = aufloeseK Q (platzB n d k₂ pub) von p) ∧
      (platzA d k₁ pub).ns ≠ (platzB n d k₂ pub).ns :=
  ⟨aufloeseK_platz Q (platzA_gut d k₁ pub) (platzB_gut pub hn) rfl, by simp only [platzA, platzB, ne_eq, reduceCtorEq, not_false_eq_true]⟩

#print axioms namensraum_zeuge
#print axioms eigen_erreicht
#print axioms abh_erreicht

end Gabbro.Grammatik.Parser.Namensraum
