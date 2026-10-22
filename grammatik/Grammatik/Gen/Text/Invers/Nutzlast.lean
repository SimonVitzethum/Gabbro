/-
  File:      Grammatik/Gen/Text/Invers/Nutzlast.lean
  Subject:   A PRINTED PAYLOAD IS READ BACK AS ITS NAMES: the statement reader keeps `publishes { g0, g1 }` and
             `awaits { .. }` as raw text (`uNutzNamen`, split at blanks and commas); on the delaborator's text of a
             list of statics it gives exactly their names.
-/
import Grammatik.Gen.Text.Invers.Namen

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A word: no blank, no comma. -/
def WortOk (w : List Char) : Prop := ∀ c ∈ w, c ≠ ' ' ∧ c ≠ ','

theorem woerter_wort : ∀ (w : List Char) (acc rest : List Char) (c : Char), WortOk w → (c = ' ' ∨ c = ',') →
    acc ++ w ≠ [] → uWoerter (w ++ c :: rest) acc = (acc.reverse ++ w) :: uWoerter rest []
  | [], acc, rest, c, _, hc, hne => by
    have : (c == ' ' || c == ',') = true := by rcases hc with rfl | rfl <;> rfl
    have ha : acc.isEmpty = false := by simpa using hne
    simp [uWoerter, this, ha]
  | d :: w, acc, rest, c, hw, hc, _ => by
    have hd := hw d List.mem_cons_self
    have : (d == ' ' || d == ',') = false := by simp [hd.1, hd.2]
    simp only [List.cons_append, uWoerter, this, Bool.false_eq_true, ite_false]
    rw [woerter_wort w (d :: acc) rest c (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hc (by simp)]
    simp

theorem spell_nameTok (n : String) : spell (nameTok n) = n.toList := by
  unfold nameTok; split <;> rfl

/-- **The payload text**: the words of a comma-separated list of names are the names. -/
theorem woerter_namen : ∀ (ws : List String), (∀ w ∈ ws, WortOk w.toList ∧ w.toList ≠ []) →
    uWoerter (render ((ws.map fun n => [nameTok n]).intersperse [.zeichen ","] |>.flatten)) [] = ws.map String.toList
  | [], _ => by simp [render, uWoerter]
  | [a], h => by
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.map_nil, List.intersperse_singleton, List.flatten_cons, List.flatten_nil,
      List.append_nil, render, spell_nameTok]
    rw [woerter_wort a.toList [] [] ' ' ha.1 (Or.inl rfl) (by simpa using ha.2)]
    simp [uWoerter]
  | a :: b :: rest, h => by
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.intersperse_cons_cons, List.flatten_cons, List.singleton_append, render,
      spell_nameTok, List.cons_append, List.nil_append]
    rw [woerter_wort a.toList [] _ ' ' ha.1 (Or.inl rfl) (by simpa using ha.2)]
    have hk : spell (Token.zeichen ",") = [','] := rfl
    simp only [hk, List.cons_append, List.nil_append, uWoerter, List.reverse_nil, List.nil_append]
    have ih := woerter_namen (b :: rest) (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons] at ih
    simp [ih]

theorem nGlob_wort (k : Nat) : WortOk (nGlob k).toList ∧ (nGlob k).toList ≠ [] := by
  rw [nGlob_toList]
  refine ⟨?_, by simp⟩
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with rfl | hc
  · decide
  · have hd := toDigits_ziffern k
    have : (toString k).toList = Nat.toDigits 10 k := by
      rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    rw [this] at hc
    have := (List.all_eq_true.1 hd) c hc
    constructor <;> intro e <;> subst e <;> simp [istZiffer] at this

end Gabbro.Grammatik.Gen.Text
