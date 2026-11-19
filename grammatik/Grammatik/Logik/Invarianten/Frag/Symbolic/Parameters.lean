module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Product
public import Grammatik.Logik.Invarianten.VC.Domain

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open VC Elim Elim.Korrekt

/-- Cases distinguish finite non-integer choices only. Coverage extends any
    existing valuation and supplies the actual, fully typed parameter Env. -/
structure Parameters (D : Deklaration) (start : Nat) (Γ : Ctx) where
  next : Nat
  ordered : start ≤ next
  templates : List (SymEnv D Nat Γ)
  bounded : ∀ symbols ∈ templates, symbols.Bounded next
  cover : ∀ world (actual : Env D Γ) (incoming : Assignment Nat),
    ∃ symbols ∈ templates, ∃ valuation, symbols.Realizes valuation world actual ∧
      ∀ key, key < start → valuation key = incoming key

def parameters (budget start : Nat) : (Γ : Ctx) → Except Refusal (Parameters D start Γ)
  | [] => .ok {
      next := start
      ordered := Nat.le_refl start
      templates := [.nil]
      bounded := fun symbols member => by
        have same := List.mem_singleton.mp member
        subst symbols
        trivial
      cover := fun _ actual incoming => by
        cases actual
        exact ⟨.nil, List.mem_cons_self, incoming, trivial, fun _ _ => rfl⟩ }
  | .int lo hi :: Γ => do
      let rest ← parameters budget (start + 1) Γ
      return {
        next := rest.next
        ordered := Nat.le_trans (Nat.le_succ start) rest.ordered
        templates := rest.templates.map (fun symbols => .cons (.integer (.var start)) symbols)
        bounded := fun symbols member => by
          obtain ⟨tail, inside, same⟩ := List.mem_map.mp member
          subst symbols
          refine ⟨?_, rest.bounded tail inside⟩
          intro key selected
          have same := List.mem_singleton.mp selected
          subst key
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self start) rest.ordered
        cover := fun world actual incoming => by
          cases actual with
          | cons value actual =>
              let seed := incoming.bind start value.n
              obtain ⟨tail, inside, valuation, realized, agrees⟩ := rest.cover world actual seed
              refine ⟨.cons (.integer (.var start)) tail,
                List.mem_map.mpr ⟨tail, inside, rfl⟩, valuation, ⟨?_, realized⟩, ?_⟩
              · exact (agrees start (Nat.lt_succ_self start)).trans (bind_same incoming start value.n)
              · intro key before
                have different : key ≠ start := Nat.ne_of_lt before
                exact (agrees key (Nat.lt_trans before (Nat.lt_succ_self start))).trans (by
                  simp only [seed, Assignment.bind, different, ↓reduceIte]) }
  | .prod name fields :: Γ => do
      let flat ← parameters budget start (fields ++ Γ)
      return {
        next := flat.next
        ordered := flat.ordered
        templates := flat.templates.map (fun symbols => symbols.packProduct name fields)
        bounded := fun symbols member => by
          obtain ⟨source, inside, same⟩ := List.mem_map.mp member
          subst symbols
          exact source.bounded_packProduct name fields (flat.bounded source inside)
        cover := fun world actual incoming => by
          cases actual with
          | cons value tail =>
              obtain ⟨symbols, member, valuation, realized, agrees⟩ :=
                flat.cover world (flattenProduct fields value tail) incoming
              exact ⟨symbols.packProduct name fields, List.mem_map.mpr ⟨symbols, member, rfl⟩,
                valuation, symbols.realizes_packProduct name fields value tail valuation world realized, agrees⟩ }
  | kind :: Γ => do
      let rest ← parameters budget (start + 1) Γ
      -- Without a complete domain within the budget the parameter is unobserved: one template that every
      -- value realizes.
      let unobserved : Parameters D start (kind :: Γ) := {
          next := rest.next
          ordered := Nat.le_trans (Nat.le_succ start) rest.ordered
          templates := rest.templates.map (fun symbols => .cons .unobserved symbols)
          bounded := fun symbols member => by
            obtain ⟨tail, inside, same⟩ := List.mem_map.mp member
            subst symbols
            exact ⟨trivial, rest.bounded tail inside⟩
          cover := fun world actual incoming => by
            cases actual with
            | cons value actual =>
                obtain ⟨tail, inside, valuation, realized, agrees⟩ := rest.cover world actual incoming
                exact ⟨.cons .unobserved tail, List.mem_map.mpr ⟨tail, inside, rfl⟩, valuation,
                  ⟨trivial, realized⟩, fun key before => agrees key (Nat.lt_trans before (Nat.lt_succ_self start))⟩ }
      match localDomain (D := D) budget kind with
      | .error _ => return unobserved
      | .ok head =>
        if head.values.length * rest.templates.length ≤ budget then
          return {
            next := rest.next
            ordered := Nat.le_trans (Nat.le_succ start) rest.ordered
            templates := head.values.flatMap (fun value => rest.templates.map (fun symbols => .cons (.known value) symbols))
            bounded := fun symbols member => by
              obtain ⟨value, _, inside⟩ := List.mem_flatMap.mp member
              obtain ⟨tail, inRest, same⟩ := List.mem_map.mp inside
              subst symbols
              exact ⟨trivial, rest.bounded tail inRest⟩
            cover := fun world actual incoming => by
              cases actual with
              | cons value actual =>
                  obtain ⟨tail, inside, valuation, realized, agrees⟩ := rest.cover world actual incoming
                  exact ⟨.cons (.known value) tail,
                    List.mem_flatMap.mpr ⟨value, head.complete value, List.mem_map.mpr ⟨tail, inside, rfl⟩⟩,
                    valuation, ⟨rfl, realized⟩,
                    fun key before => agrees key (Nat.lt_trans before (Nat.lt_succ_self start))⟩ }
        else return unobserved

termination_by Γ => sizeOf Γ
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | (have bound := context_size_append fields Γ; simp_wf; omega)

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
