/- The shared exact span footprint specialized to world writes. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Footprint
public import Stage0.Senke.Welt.WeltAt
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
theorem SpanEffect.agreeW {D : Deklaration} {L : Lay D}
    {fp : Runner.W} {tmp address count K : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (ht : tmp < K)
    (lo : L.lo ≤ address) (hi : address + 8 * count ≤ L.hi) : AgreeW L fp tmp K m m' := by
  refine AgreeW.stark h.rd h.wr fun x hx hw => h.b x ?_ ?_
  · intro ⟨a, b⟩; exact hx ⟨a, by omega⟩
  · intro ⟨a, b⟩; exact hw ⟨by omega, by omega⟩

end Gabbro.Stage0.Senke
