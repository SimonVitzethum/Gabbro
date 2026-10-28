import Grammatik.Bausteine.Arena.Ownership.Source.Arguments

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

/-- Function entry instantiates provenance from its selected parameter.
All other numeric parameters remain ordinary numbers, never implicit rights. -/
def Context.parameter {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (mode : PassingMode) : Context :=
  ⟨(List.range Γ.length).map (fun j => if j = x.unten then some 0 else none),
    fun i => if i = 0 then some mode else none, 1⟩

theorem Context.parameter_reference {Γ : Ctx} {τ υ : Ty} (x : Var Γ τ) (y : Var Γ υ)
    (mode : PassingMode) : (Context.parameter x mode).reference y =
      if y.unten = x.unten then some 0 else none := by
  simp only [reference, parameter, List.length_map, List.length_range, Var.unten_lt y, getElem?_pos,
  List.getElem_map, List.getElem_range, Option.getD_some]

theorem Context.parameter_bounded {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (mode : PassingMode) :
    (Context.parameter x mode).bounded := by
  constructor
  · intro i hi
    have hn : i ≠ 0 := by change 1 ≤ i at hi; omega
    simp only [parameter, hn, ↓reduceIte]
  · intro ref hm i he
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hm
    by_cases hz : j = x.unten
    · simp only [hz, ite_true] at hj
      have hi : i = 0 := (Option.some.inj (hj.trans he)).symm
      subst i
      change 0 < 1
      decide
    · have hf : ref = none := by simpa only [hz, ite_false] using hj.symm
      rw [hf] at he
      cases he

theorem parameter_realizes (A : FreiForm D) {Γ : Ctx}
    (x : Var Γ (Ty.index (D.count A.tab))) (mode : PassingMode)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D Γ)
    (ha : s.agrees A σ) (hf : A.FreiOk σ) (h : Handle)
    (ho : mode.permits s frame h) (hx : h.slot = (ρ.get x).n) :
    Realizes (Context.parameter x mode) (fun i => if i = 0 then some h else none) A frame s σ ρ := by
  refine ⟨ha, hf, Context.parameter_bounded x mode, ⟨?_, ?_⟩, ?_⟩
  · simp only [Context.parameter, List.length_map, List.length_range]
  · intro υ y i hi
    rw [Context.parameter_reference] at hi
    split at hi
    · rename_i hpos
      cases hi
      refine ⟨h, rfl, ?_⟩
      rw [← Env.unten_get, hpos, Env.unten_get]
      exact congrArg some hx.symm
    · cases hi
  · constructor
    · intro i m hi
      by_cases hz : i = 0
      · subst i
        have he : m = mode := by simpa [Context.parameter] using hi.symm
        subst m
        exact ⟨h, rfl, ho⟩
      · simp only [Context.parameter, hz, ↓reduceIte, reduceCtorEq] at hi
    · intro i j p q hi hj hne _ _ _ _ _
      have hiz : i = 0 := by
        by_cases hn : i = 0
        · exact hn
        · simp only [Context.parameter, hn, ↓reduceIte, reduceCtorEq] at hi
      have hjz : j = 0 := by
        by_cases hn : j = 0
        · exact hn
        · simp only [Context.parameter, hn, ↓reduceIte, reduceCtorEq] at hj
      exact False.elim (hne (hiz.trans hjz.symm))

#print axioms parameter_realizes

end Gabbro.Grammatik.ArenaOwnership.Source
