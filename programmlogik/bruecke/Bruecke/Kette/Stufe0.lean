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

open Gabbro.Stage0 Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Cover.Differenz in
/-- **The unit Stage 0 compiles, without the checks after it.** Exactly the steps of
    `Gabbro.Stage0.compile` up to its `unit`: the source, the constant and metadata gate, the
    expansion choice, the scoped elaboration with the profile's selection, and the export gate.
    `compile` then lowers and runs the checker, which costs far more on large units; `gabbrov`
    needs only the unit. That it is `compile`'s unit is read off the two definitions; a proof
    (`stufe0Einheit_compile`) is owed. The theorems never use it: their premise is `c.unit = u`. -/
def stufe0Einheit (text : String) (options : Profil.Options := {}) : Except String UProg := do
  let source ← Frontend.source text options
  let declarations := pre108 source.prepared.elaborierbar
  let members := uMembers declarations
  Konst.checkSourceConstants members
  let (expanded, _) ← Modules.prepare declarations
  let gateMembers ←
    if members.any Frontend.expansionHeader then
      match Konst.checkSourceMetadata (uMembers expanded) with
      | .ok () => pure (uMembers expanded)
      | .error expandedError =>
        match Konst.checkSourceMetadata members with
        | .ok () => pure members
        | .error _ => throw expandedError
    else
      match Konst.checkSourceMetadata members with
      | .ok () => pure members
      | .error originalError =>
        match Konst.checkSourceMetadata (uMembers expanded) with
        | .ok () => pure (uMembers expanded)
        | .error _ => throw originalError
  let candidate ← (Frontend.elabWithScopes declarations
      source.scopes.values source.scopes.types source.scopes.functions
      (Frontend.tableWithEmpty source.scopes.values source.scopes.types)
      (widths := source.scopes.widths)).bind (Profil.selectUnit options)
  pure {candidate with exportGate := Konst.checkSourceMetadata gateMembers}

end Gabbro.Bruecke
