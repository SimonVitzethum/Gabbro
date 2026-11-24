module

public import Core.Ast.Semantik.Regeln
import Mathlib.Data.List.Nodup

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

inductive Rufpfad (table : List Funktion) : Identifier → Identifier → Prop where
  | direkt : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table source call.name
  | weiter : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table call.name target → Rufpfad table source target

/-- The trace records the source of each edge, excluding the final vertex. -/
private inductive Rufspur (table : List Funktion) (target : Identifier) :
    Identifier → List Identifier → Prop where
  | ende : Rufspur table target target []
  | schritt : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufspur table target call.name rest → Rufspur table target source (source :: rest)

private theorem Rufspur.suffix (path : Rufspur table target source names)
    (member : atName ∈ names) :
    ∃ rest, rest <:+ names ∧ Rufspur table target atName rest := by
  induction path with
  | ende => exact (List.not_mem_nil member).elim
  | schritt found call tail ih =>
    rcases List.mem_cons.mp member with h | h
    · subst atName
      exact ⟨_, List.suffix_refl _, .schritt found call tail⟩
    · obtain ⟨rest, suffix, walk⟩ := ih h
      exact ⟨rest, suffix.trans (List.suffix_cons _ _), walk⟩

private theorem Rufspur.einfach (path : Rufspur table target source names) :
    ∃ rest, Rufspur table target source rest ∧ rest.Nodup := by
  induction path with
  | ende => exact ⟨[], .ende, List.nodup_nil⟩
  | @schritt source function call rest found member _ ih =>
    obtain ⟨short, path, simple⟩ := ih
    by_cases repeated : source ∈ short
    · obtain ⟨suffix, part, walk⟩ := path.suffix repeated
      exact ⟨suffix, walk, simple.sublist part.sublist⟩
    · exact ⟨source :: short, .schritt found member path, List.nodup_cons.mpr ⟨repeated, simple⟩⟩

private theorem Rufspur.registriert (path : Rufspur table target source names) :
    names ⊆ table.map Funktion.name := by
  intro name member
  induction path with
  | ende => exact (List.not_mem_nil member).elim
  | @schritt source function call rest found _ _ ih =>
    rcases List.mem_cons.mp member with rfl | h
    · have named : function.name.val = source.val :=
        beq_iff_eq.mp (List.find?_some found)
      have present : function ∈ table :=
        List.mem_of_find?_eq_some found
      exact List.mem_map.mpr ⟨function, present, Subtype.ext named⟩
    · exact ih h

private theorem Rufspur.erreichbar (path : Rufspur table target source names)
    (enough : names.length ≤ fuel) : Funktion.erreichbar table target fuel source = true := by
  induction path generalizing fuel with
  | ende => cases fuel <;> simp only [Funktion.erreichbar, beq_self_eq_true, Bool.true_or]
  | schritt found member _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [Funktion.erreichbar, found, Option.map_some, Option.getD_some, Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨_, member, ih (Nat.le_of_succ_le_succ enough)⟩)

private theorem Rufpfad.spur (path : Rufpfad table source target) :
    ∃ names, Rufspur table target source names := by
  induction path with
  | direkt found member => exact ⟨_, .schritt found member .ende⟩
  | weiter found member _ ih =>
    obtain ⟨_, tail⟩ := ih
    exact ⟨_, .schritt found member tail⟩

private theorem funktion_reachable_path (found : Funktion.erreichbar table target fuel source = true) :
    source = target ∨ Rufpfad table source target := by
  induction fuel generalizing source with
  | zero =>
    exact Or.inl (Subtype.ext (beq_iff_eq.mp found))
  | succ fuel ih =>
    rcases Bool.or_eq_true_iff.mp found with same | via
    · exact Or.inl (Subtype.ext (beq_iff_eq.mp same))
    cases lookup : Funktion.finde table source with
    | none => simp only [lookup, Option.map_none, Option.getD_none, Bool.false_eq_true] at via
    | some f =>
      simp only [lookup, Option.map_some, Option.getD_some, List.any_eq_true] at via
      obtain ⟨call, member, tail⟩ := via
      rcases ih tail with rfl | path
      · exact Or.inr (.direkt lookup member)
      · exact Or.inr (.weiter lookup member path)

private theorem Rufpfad.erste (path : Rufpfad table source target) :
    ∃ function call, Funktion.finde table source = some function ∧ call ∈ function.ruft ∧
      (call.name = target ∨ Rufpfad table call.name target) := by
  cases path with
  | direkt found member => exact ⟨_, _, found, member, Or.inl rfl⟩
  | weiter found member tail => exact ⟨_, _, found, member, Or.inr tail⟩

private theorem funktion_find_member (unique : (table.map (fun f => f.name.val)).Nodup)
    (member : function ∈ table) : Funktion.finde table function.name = some function := by
  induction table with
  | nil => exact (List.not_mem_nil member).elim
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.find?_cons_of_pos (p := fun f => f.name.val == function.name.val)
        (beq_self_eq_true _)
    · have properties := List.nodup_cons.mp unique
      have different : first.name.val ≠ function.name.val := by
        intro same
        exact properties.1 (List.mem_map.mpr ⟨function, member, same.symm⟩)
      rw [Funktion.finde, List.find?_cons_of_neg (by simpa only [beq_iff_eq] using different)]
      exact ih properties.2 member

theorem function_rekursiv_korrekt (table : List Funktion) (function : Funktion)
    (unique : (table.map (fun f => f.name.val)).Nodup)
    (member : function ∈ table) :
    Funktion.rekursiv table function = true ↔ Rufpfad table function.name function.name := by
  have found := funktion_find_member unique member
  rw [Funktion.rekursiv, List.any_eq_true]
  constructor
  · rintro ⟨call, hcall, search⟩
    rcases funktion_reachable_path search with same | path
    · have edge : Rufpfad table function.name call.name := .direkt found hcall
      exact same ▸ edge
    · exact .weiter found hcall path
  · intro path
    obtain ⟨f, call, lookup, hcall, tail⟩ := path.erste
    have same := Option.some.inj (found.symm.trans lookup)
    subst f
    rcases tail with eq | tail
    · refine ⟨call, hcall, ?_⟩
      rw [eq]
      exact Rufspur.ende.erreichbar (Nat.zero_le _)
    · obtain ⟨_, trace⟩ := tail.spur
      obtain ⟨_, simple, distinct⟩ := trace.einfach
      have size := distinct.length_le_of_subset simple.registriert
      rw [List.length_map] at size
      exact ⟨_, hcall, simple.erreichbar size⟩

end Gabbro.Core.Ast.Semantik
