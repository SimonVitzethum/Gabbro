module
public import Bruecke.Teil.Senkung
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem mem_insertS_of_mem_teil (x y : String) : ∀ l : List String,
    y = x ∨ y ∈ l → y ∈ insertS x l
  | [], h => by
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · cases h
  | z :: zs, h => by
      unfold insertS
      split
      · rcases h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ h
      · split
        · rename_i he
          rcases h with rfl | h
          · rw [he]; exact List.mem_cons_self ..
          · exact h
        · rcases h with rfl | h
          · exact List.mem_cons_of_mem _ (mem_insertS_of_mem_teil _ _ zs (.inl rfl))
          · rcases List.mem_cons.mp h with rfl | h
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (mem_insertS_of_mem_teil x y zs (.inr h))

theorem mem_sortDedup_of_mem_teil {y : String} : ∀ {l : List String},
    y ∈ l → y ∈ sortDedup l
  | [], h => by cases h
  | x :: xs, h => by
      apply mem_insertS_of_mem_teil
      rcases List.mem_cons.mp h with rfl | h
      · exact .inl rfl
      · exact .inr (mem_sortDedup_of_mem_teil h)

/-- Closure can be used at each actual direct call, including a suffix of the body. -/
theorem call_mem_calleesOf_teil {f : UFn} {n : String} {args : List UArg}
    (hm : UStmt.call n args ∈ f.body) : n ∈ calleesOf f := by
  apply mem_sortDedup_of_mem_teil
  exact List.mem_filterMap.mpr ⟨.call n args, hm, rfl⟩

theorem callsIn_mem_calleesOf {f : UFn} {n : String} {args : List UArg}
    (h : CallsIn f.body n args) : n ∈ calleesOf f := by
  obtain ⟨st, hm, hs⟩ := h
  apply mem_sortDedup_of_mem_teil
  exact List.mem_filterMap.mpr ⟨st, hm, by rw [hs] <;> rfl⟩

theorem callee_getragen_calls (S : Getragen u C) {c d : Fin u.fns.length}
    (hc : C c) {n : String} {args : List UArg}
    (hm : CallsIn (fnAt u c).body n args)
    (hd : fnSuch u n = some (fnAt u d)) : C d :=
  S.geschlossen c hc n (callsIn_mem_calleesOf hm) d hd

theorem callee_getragen_teil (S : Getragen u C) {c d : Fin u.fns.length}
    (hc : C c) {n : String} {args : List UArg}
    (hm : UStmt.call n args ∈ (fnAt u c).body)
    (hd : fnSuch u n = some (fnAt u d)) : C d :=
  S.geschlossen c hc n (call_mem_calleesOf_teil hm) d hd

/-- For an actually carried callee the gate is the original handler. No global equality. -/
theorem torRuf_eq_teil {P : Programm (declOf u)} (G : GesenktC u C P)
    (R : ∀ f : (declOf u).Fn, World (declOf u) →
      Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (g : (declOf u).Fn) (hg : C g) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params g)) : torRuf P R g σ ρ = R g σ ρ := by
  unfold torRuf
  rw [G.req g hg] <;> rfl

/-- Gating preserves normal contracts and frames even for open functions: rejection is logical. -/
theorem torRuf_rahmen_teil {D : Deklaration} {P : Programm D}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : RespektiertRahmen P R) : RespektiertRahmen P (torRuf P R) := by
  constructor
  · intro g σ ρ hreq σ' v h
    have heq : torRuf P R g σ ρ = R g σ ρ := by
      unfold torRuf
      exact if_pos hreq
    rw [heq] at h
    exact hR.1 g σ ρ hreq σ' v h
  · intro g σ ρ σ' v h
    unfold torRuf at h
    split at h
    · exact hR.2 g σ ρ σ' v h
    · cases h

end Gabbro.Bruecke
