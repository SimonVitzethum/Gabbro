/- The index (or reference) child of a complete cell read runs before the address is known;
   its own precondition is a prefix of the whole read's. -/
import Stage0.Senke.Welt.Spans.CellStore

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem slotValueC_index_pre {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {d K reserved top : Nat}
    {index : List II × Nat} {code : List II} {m : Runner.Mem} {pc fp : Runner.W} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (made : slotValueC L t f d index = some (code, top))
    (pre : Pre L m pc fp K d code ρ W reserved) :
    Pre L m pc fp K (d + valueWords (D.typ t f)) index.1 ρ W reserved := by
  have tops := slotValueC_top made
  unfold slotValueC at made
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨ca, ta⟩, hca, rfl, rfl⟩ := made
  unfold cellAddressC at hca
  split at hca
  · simp only [Option.some.injEq, Prod.mk.injEq] at hca
    obtain ⟨rfl, rfl⟩ := hca
    exact pre.left.left.raise (by omega)
  · cases hca

end Gabbro.Stage0.Senke
