module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
@[expose] public section

namespace Gabbro.Stage0.NarrowRequiredWitness

open Gabbro.Grammatik Gabbro.Stage0.Senke.ControlProbe

/-- Required narrowing exercises the successful continuation and the generated stop. -/
def body (n : Int) : Endblock D (vertragVon D entry) false [] [] :=
  .narrowRequired (.lit n) 3 7
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl []))

def block (n : Int) : Block D (vertragVon D entry) false [] [] [] :=
  .narrowRequired (.lit n) 3 7
    (.cons (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl [])) .nil)

theorem accepted_end_zeuge :
    [2, 3, 7, 8].all (fun n => (imageOf (body n)).isOk) = true := by
  decide +kernel

theorem accepted_block_zeuge :
    [2, 3, 7, 8].all (fun n => (blockImageOf (block n)).isOk) = true := by
  decide +kernel

end Gabbro.Stage0.NarrowRequiredWitness
