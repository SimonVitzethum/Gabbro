module
public import Bruecke.Anweisung.Ruf.Simulation
public import Bruecke.Teil.Abschluss
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem lowRufKopf_writes (S : Getragen u C) {c : Fin u.fns.length} (hc : C c)
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {g : String} {args : List UArg}
    {k : RufKopf u c Γ Λ} (hk : lowRufKopf u c Γ fn Λ g args = .ok k)
    (hm : CallsIn (fnAt u c).body g args) :
    ∀ w ∈ writesU (fnAt u k.callee), w ∈ writesU (fnAt u c) := by
  obtain ⟨hi, _, hw⟩ := lowRufKopf_ok hk
  have hf : fnSuch u g = some (fnAt u k.callee) := fnIdx_find _ _ _ hi
  have hd := callee_getragen_calls S hc hm hf
  intro w hmem
  rcases List.mem_append.mp hmem with ht | hg
  · obtain ⟨t, rfl⟩ := S.schreibt k.callee hd w ht
    apply writesU_table
    apply any_mem
    exact hw t (List.any_eq_true.mpr ⟨_, ht, beq_self_eq_true _⟩)
  · rcases List.mem_append.mp hg with hg | hclock
    · obtain ⟨i, rfl⟩ := S.gschreibt k.callee hd w hg
      apply writesU_global
      apply any_mem
      exact lowRufKopf_gwrites hk i (List.any_eq_true.mpr ⟨_, hg, beq_self_eq_true _⟩)
    · exact List.mem_append_right _ (List.mem_append_right _ hclock)

end Gabbro.Bruecke
