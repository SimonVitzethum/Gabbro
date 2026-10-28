/-
  File:      Grammatik/Gen/Fein/Tafel.lean
  Subject:   THE FINE TABLE FROM DATA: a list of witnesses with their cells, a list of impossible cells with their
             theorems, and an assignment of a witness to every cell of the universe that the kernel checks in one
             pass (`feinTafel_aus`); and the witnessed fine cells of the tests of N (`nFein_aus`).
-/
import Grammatik.Gen.Fein.Neutral

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- Every element of a list has a partner in a zipped list of the same length that the test accepts. -/
theorem zip_all_mem {α β : Type} {P : α × β → Bool} :
    ∀ {xs : List α} {ys : List β}, ys.length = xs.length → (xs.zip ys).all P = true → ∀ x ∈ xs, ∃ y, P (x, y) = true
  | [], _, _, _, x, hx => absurd hx (List.not_mem_nil)
  | _ :: _, [], hl, _, _, _ => by simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
  one_ne_zero, and_false] at hl
  | a :: as, b :: bs, hl, h, x, hx => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, h.1⟩
    · exact zip_all_mem (by simpa using hl) h.2 x hx

/-- A cell in the `j`-th list of the witnesses' cells is a cell of the `j`-th witness. -/
theorem mem_getD_map {paare : List (Einsatz × List FZelle)}
    (hp : ∀ p ∈ paare, p.1.gueltig = true ∧ ∀ c ∈ p.2, p.1.HatF c) {j : Nat} {c : FZelle}
    (h : ((paare.map (·.2)).getD j []).contains c = true) : ∃ m ∈ paare.map (·.1), m.HatF c := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hj : (paare.map (·.2))[j]? with
  | none => simp only [hj, Option.getD_none, List.contains_eq_mem, List.not_mem_nil, decide_false,
  Bool.false_eq_true] at h
  | some zs =>
    rw [hj] at h
    obtain ⟨hjl, hjz⟩ := List.getElem?_eq_some_iff.1 hj
    have hjl' : j < paare.length := by simpa using hjl
    refine ⟨(paare[j]'hjl').1, List.mem_map.2 ⟨_, List.getElem_mem hjl', rfl⟩, ?_⟩
    have hz : zs = (paare[j]'hjl').2 := by rw [← hjz]; simp only [List.getElem_map]
    exact (hp _ (List.getElem_mem hjl')).2 c (hz ▸ List.contains_iff_mem.1 h)

/-- **The fine table from data.** -/
theorem feinTafel_aus (paare : List (Einsatz × List FZelle))
    (hp : ∀ p ∈ paare, p.1.gueltig = true ∧ ∀ c ∈ p.2, p.1.HatF c) (unm : List FZelle)
    (hu : ∀ c ∈ unm, ∀ e : Einsatz, e.HatF c → e.gueltig = false) (zu : List Nat) (hl : zu.length = uF.length)
    (hz : (uF.zip zu).all (fun x => ((paare.map (·.2)).getD x.2 []).contains x.1 || unm.contains x.1) = true) :
    FeinTafel (paare.map (·.1)) where
  gut m hm := by
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hm
    exact (hp p hp').1
  deckt c hc := by
    obtain ⟨j, hj⟩ := zip_all_mem hl hz c hc
    rcases Bool.or_eq_true_iff.1 hj with h | h
    · exact Or.inl (mem_getD_map hp h)
    · exact Or.inr (hu c (List.contains_iff_mem.1 h))

/-- **The fine cells of the tests of N are witnessed**, when the kernel finds each in a witness's list. -/
theorem nFein_aus (paare : List (Einsatz × List FZelle))
    (hp : ∀ p ∈ paare, p.1.gueltig = true ∧ ∀ c ∈ p.2, p.1.HatF c) (N : List Einsatz)
    (h : N.all (fun n => n.feinZellen.all fun c => (paare.map (·.2)).any (·.contains c)) = true) :
    ∀ n ∈ N, ∀ c, n.HatF c → ∃ m ∈ paare.map (·.1), m.HatF c := by
  intro n hn c hc
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h n hn) c hc
  obtain ⟨zs, hzs, hzc⟩ := List.any_eq_true.1 h1
  obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hzs
  exact ⟨p.1, List.mem_map.2 ⟨p, hp', rfl⟩, (hp p hp').2 c (List.contains_iff_mem.1 hzc)⟩

end Gabbro.Grammatik.Gen.Fein
