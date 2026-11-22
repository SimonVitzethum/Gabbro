module
public import Stage0.Compiler
public import Stage0.Senke.Ausdruck.Old.JudgedUnit
@[expose] public section

/-!
# The facts of Stage 0's run that GabbroV uses

`stufe0Einheit` is the unit Stage 0 compiles (the steps of `compile` up to its unit);
`ohneAltGlobalB` decides that no postcondition reads `old` of a static, and `restore_ohneAlt` proves
that Stage 0's restoration is then the identity on the lowered program. Stage 0's run is the one
boundary between a source text and the program the theorems speak about (owner, 2026-11-22).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

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

/-- No postcondition of the items reads `old` of a static (`OldSource.hasEntry`). -/
def ohneAltGlobalB (items : List SItemTief) : Bool :=
  items.all fun it => match it with
    | .fnT sig _ => sig.klauseln.all fun k => match k with
        | .gives e => !Gabbro.Stage0.OldSource.hasEntry e
        | _ => true
    | _ => true

theorem collect_ok : ∀ (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i))
    (vals : (i : Fin n) → T i), (∀ i, get i = .ok (vals i)) →
      Gabbro.Stage0.OldSource.collect n T get = .ok vals
  | 0, _, _, vals, _ => by
    simp only [Gabbro.Stage0.OldSource.collect, pure, Except.pure]
    congr
    funext i
    exact i.elim0
  | n + 1, T, get, vals, h => by
    simp only [Gabbro.Stage0.OldSource.collect, h 0,
      collect_ok n (fun i => T i.succ) (fun i => get i.succ) (fun i => vals i.succ) (fun i => h i.succ),
      bind, Except.bind, pure, Except.pure]
    congr
    funext i
    cases i using Fin.cases <;> rfl

/-- **Without `old(global)` the restoration is the identity.** -/
theorem restore_ohneAlt (items : List SItemTief) (u : UProg) (P : Programm (declOf u))
    {expanded : List SItemTief} {requirements : List (STyp × String)}
    (hx : Modules.prepare items = .ok (expanded, requirements))
    (hb : ohneAltGlobalB expanded = true) :
    Gabbro.Stage0.OldSource.restore items u P = .ok P := by
  unfold Gabbro.Stage0.OldSource.restore
  have hx' : expandU items = .ok (expanded, requirements) := hx
  simp only [hx', bind, Except.bind]
  rw [collect_ok _ _ _ P.ensures (fun f => ?_)]
  · rfl
  unfold Gabbro.Stage0.OldSource.atFunction
  have hsrc : (Gabbro.Stage0.OldSource.clauses (Gabbro.Stage0.OldSource.koepfeVon expanded)
      (fnAt u f).name).any Gabbro.Stage0.OldSource.hasEntry = false := by
    unfold Gabbro.Stage0.OldSource.clauses
    split
    · rename_i sig hsig
      have hmem := List.mem_of_find?_eq_some hsig
      obtain ⟨it, hit, hsome⟩ := List.mem_filterMap.mp hmem
      have hall := List.all_eq_true.mp hb it hit
      cases it with
      | fnT s body =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        simp only at hall
        rw [List.any_eq_false]
        intro e he
        obtain ⟨k, hk, hke⟩ := List.mem_filterMap.mp he
        have hkall := List.all_eq_true.mp hall k hk
        cases k <;> simp_all
      | _ => simp at hsome
    · rfl
  simp only [hsrc, Bool.not_false, if_true]
  rfl

open Gabbro.Stage0 in
/-- The run fact `hold` of `nutzerA_aus_compiled`, computed as Stage 0 computes its expanded
    items (the steps of `compile` up to `Modules.prepare`); checked in the generated
    `Pruefung` module by running it. -/
def stufe0AltFreiB (text : String) (options : Profil.Options := {}) : Bool :=
  match Frontend.source text options with
  | .error _ => false
  | .ok source =>
    match Modules.prepare (pre108 source.prepared.elaborierbar) with
    | .ok (expanded, _) => ohneAltGlobalB expanded
    | .error _ => false


#print axioms restore_ohneAlt

end Gabbro.Bruecke
