module
public import Bruecke.Kette.Einheit
public import Stage0.Compiler
@[expose] public section

/-!
# The duties of the unit Stage 0 compiles

Stage 0 elaborates with its own front end (scopes, constants, expansion); its result
`Compiled text` carries the unit and the fact that the generic lowering accepts it
(`Compiled.lowered`). That fact is all the bridge needs: the duties of the unit, given as data,
supply premise (b) of the goal theorem for the program the lowering builds from it. The
restoration of `old(global)` postconditions that follows the lowering in Stage 0 replaces only
`ensures`; the statement here is over the lowered program, the one the bridge simulates.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- **Premise (b) for the unit Stage 0 compiles from `text`**, from the duties of that unit
    given as data. The link between the text and `u` is `hu`, checked by running Stage 0. -/
theorem nutzer_aus_stage0 {u : UProg} (hp : PflichtenEinheit u) {text : String}
    {options : Gabbro.Stage0.Profil.Options} (c : Gabbro.Stage0.Compiled text options) (hu : c.unit = u) :
    ∃ (P : Programm (declOf u)) (fs : List (declOf u).Fn) (hn : nullB u = true),
      lowerAllg u = .ok (P, fs) ∧ Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  subst hu
  obtain ⟨P, fs, hlow, -⟩ := c.lowered
  obtain ⟨hn, hb⟩ := nutzer_aus_senkung hp hlow
  exact ⟨P, fs, hn, hlow, hb⟩

#print axioms nutzer_aus_stage0

end Gabbro.Bruecke
