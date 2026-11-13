/-
  File:      Grammatik/Niedrig/Maske/MaskeZeuge.lean
  Subject:   WITNESS FOR INTERRUPT MASKING AS A PER-CORE STATE (L7a): two
    cores; core 0 masks, a handler attempt on core 0 is refused, a handler
    enters and leaves on core 1, core 0 unmasks; the end state by `rfl`.
-/
module

public import Grammatik.Niedrig.Maske.Maske

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Maske

/-- The fixture start: two unmasked cores, nothing running. -/
def m0 : CoreMask :=
  { zustand := fun _ =>
    { maskiert := false
      tiefe := 0
      stapel := [] } }

/-- Core 0 masks. -/
def m1 : CoreMask :=
  maskiereNach m0 0

/-- Step one: core 0 masks. -/
theorem wMaskiere : MaskStep (MaskEvent.maskiere 0) m0 m1 :=
  MaskStep.maskiere m0 0

/-- Core 0 reads back masked. -/
theorem wMaskiert : (m1.zustand 0).maskiert = true :=
  rfl

/-- Core 1 stays unmasked. -/
theorem wUnmaskiert1 : (m1.zustand 1).maskiert = false :=
  rfl

/-- Refused: no handler enters on masked core 0. -/
theorem wVerweigert (s' : CoreMask) :
    ¬ MaskStep (MaskEvent.betreteHandler 0 7) m1 s' :=
  fun h => keinBetreteMaskiert m1 s' 0 7 wMaskiert h

/-- A handler enters on core 1. -/
def m2 : CoreMask :=
  betreteNach m1 1

/-- Step two: the handler enters on core 1. -/
theorem wBetrete : MaskStep (MaskEvent.betreteHandler 1 7) m1 m2 :=
  MaskStep.betrete m1 1 7 wUnmaskiert1

/-- Entering masks core 1 and grows its depth. -/
theorem wTiefe : (m2.zustand 1).tiefe = 1 :=
  rfl

/-- The entry pushes the saved bit. -/
theorem wStapel1 : (m2.zustand 1).stapel = [false] :=
  rfl

/-- The handler leaves core 1, restoring the saved bit. -/
def m3 : CoreMask :=
  verlasseNach m2 1 false []

/-- Step three: the handler leaves core 1. -/
theorem wVerlasse : MaskStep (MaskEvent.verlasseHandler 1) m2 m3 :=
  MaskStep.verlasse m2 1 false [] wStapel1

/-- Core 0 unmasks. -/
def m4 : CoreMask :=
  entmaskiereNach m3 0

/-- Step four: core 0 unmasks. -/
theorem wEntmaskiere : MaskStep (MaskEvent.entmaskiere 0) m3 m4 :=
  MaskStep.entmaskiere m3 0

/-- The end state: core 0 unmasked, core 1 restored unmasked at depth zero
    with an empty stack. -/
theorem wEnde :
    (m4.zustand 0).maskiert = false ∧ (m4.zustand 1).maskiert = false ∧
      (m4.zustand 1).tiefe = 0 ∧ (m4.zustand 1).stapel = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms Gabbro.Grammatik.Niedrig.Maske.wMaskiere
#print axioms Gabbro.Grammatik.Niedrig.Maske.wVerweigert
#print axioms Gabbro.Grammatik.Niedrig.Maske.wEnde

end Gabbro.Grammatik.Niedrig.Maske
