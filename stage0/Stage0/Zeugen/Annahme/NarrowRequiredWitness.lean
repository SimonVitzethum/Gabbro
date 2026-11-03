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

/-- The continuation reads the narrowed high limbs before returning a scalar.
    The target has an unsigned high limb and needs two complete words. -/
def wideEnd (required : Bool) (n : Int) : Endblock D (vertragVon D entry) false [] [] :=
  let rest : Endblock D (vertragVon D entry) false [.int (2^80) (2^80+3)] [] :=
    .ite (.eq (.var .here) (.lit (2^80+2)))
      (retN 7 (by decide) (by decide)) (retN 8 (by decide) (by decide))
  if required then .narrowRequired (.lit n) (2^80) (2^80+3) rest
  else .narrow (.lit n) (2^80) (2^80+3) (retN 41 (by decide) (by decide)) rest

def wideBlock (required : Bool) (n : Int) : Block D (vertragVon D entry) false [] [] [] :=
  let rest : Block D (vertragVon D entry) false [.int (2^80) (2^80+3)] [] [] :=
    .cons (.ite (.eq (.var .here) (.lit (2^80+2)))
      (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 7))) (.refl [])) .nil)
      (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 8))) (.refl [])) .nil)) .nil
  if required then .narrowRequired (.lit n) (2^80) (2^80+3) rest
  else .narrow (.lit n) (2^80) (2^80+3) (retN 41 (by decide) (by decide)) rest

/-- Both control forms and both required-capacity outcomes reach image emission,
    including values below, on, inside and above the target bounds. -/
theorem wide_images_zeuge :
    [false, true].all (fun required =>
      [2^80-1, 2^80, 2^80+2, 2^80+3, 2^80+4].all (fun n =>
        (imageOf (wideEnd required n)).isOk &&
        (blockImageOf (wideBlock required n)).isOk)) = true := by
  decide +kernel

/-- Inverted bounds are a failed range check, not a compiler limitation. -/
theorem empty_target_zeuge :
    (imageOf (.narrow (.lit (2^80)) (2^80) (-(2^80))
      (retN 41 (by decide) (by decide)) (retN 7 (by decide) (by decide)))).isOk = true ∧
    (blockImageOf (.narrowRequired (.lit (2^80)) (2^80) (-(2^80)) .nil)).isOk = true := by
  decide +kernel

end Gabbro.Stage0.NarrowRequiredWitness
