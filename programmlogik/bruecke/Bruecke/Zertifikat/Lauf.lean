module
public import Stage0.Compiler
public import Stage0.Senke.Ausdruck.Old.JudgedUnit
@[expose] public section

/-!
# The facts of Stage 0's run that GabbroV uses

`stufe0Einheit` is the unit Stage 0 compiles (the steps of `compile` up to its unit);
`restored` is the program Stage 0's restoration of `old(global)` postconditions builds from the
lowered one (`restore_restored`), from the restored functions' source clauses given as data. Stage 0's run is the one
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

/-! ## `old(global)` in postconditions: the program Stage 0 restores

Stage 0 lowers a postcondition that reads `old` of a static through `OldSource.restore`: only the
postcondition family changes, each function's from its own source clauses. `altVon` keeps exactly the
clauses the restoration reads (those of the functions with an entry read, `[]` for all others), `restored`
is the restored program as a total function of them, and `restore_restored` proves that it is what
Stage 0 compiles. The duties are stated over `restored alt u P` for clauses `alt` given as data; that
they are Stage 0's is the run fact `altVon c.expanded = alt` on the unit's functions. -/

open Gabbro.Stage0.OldSource (hasEntry clauses koepfeVon predicates) in
/-- The source postconditions of the function `name` that read `old` of a static, as the restoration
    reads them; `[]` when none does. -/
def altVon (items : List SItemTief) (name : String) : List SExpr :=
  let src := clauses (koepfeVon items) name
  if src.any hasEntry then src else []

open Gabbro.Stage0.OldSource (hasEntry predicates) in
/-- `OldSource.atFunction` over the clauses `cl` and the lowered postcondition `e0` of `f`. -/
def atFunctionMit (cl : String → List SExpr) (u : UProg) (f : Fin u.fns.length) (e0 : EnsTy u f) :
    Except String (EnsTy u f) := do
  let src := cl (fnAt u f).name
  if !src.any hasEntry then return e0
  let e ← predicates u (ErgCtx (ctxOf u f) ((verOf u f).erg)) (verOf u f).ende
    (fnAt u f) (fnAt u f).ergTy src (fnAt u f).gives
  pure (by
    unfold EnsTy
    rw [← ensCtx_eq u f]
    exact e)

/-- The restored postcondition of `f` (the lowered one where the restoration refuses; Stage 0 then
    compiles nothing). -/
def ensAltAt (alt : String → List SExpr) (u : UProg) (f : Fin u.fns.length) (e0 : EnsTy u f) : EnsTy u f :=
  match atFunctionMit alt u f e0 with
  | .ok e => e
  | .error _ => e0

/-- **The program with the postconditions restored from the clauses `alt`.** -/
def restored (alt : String → List SExpr) (u : UProg) (P : Programm (declOf u)) : Programm (declOf u) :=
  { P with ensures := fun f => ensAltAt alt u f (P.ensures f) }

theorem atFunction_mit (K : Tafel FnSig (·.name)) (u : UProg) (P : Programm (declOf u)) (f : Fin u.fns.length) :
    Gabbro.Stage0.OldSource.atFunction K u P f =
      atFunctionMit (Gabbro.Stage0.OldSource.clauses K) u f (P.ensures f) := rfl

theorem atFunctionMit_altVon (items : List SItemTief) (u : UProg) (f : Fin u.fns.length) (e0 : EnsTy u f) :
    atFunctionMit (Gabbro.Stage0.OldSource.clauses (Gabbro.Stage0.OldSource.koepfeVon items)) u f e0 =
      atFunctionMit (altVon items) u f e0 := by
  unfold atFunctionMit altVon
  by_cases h : (Gabbro.Stage0.OldSource.clauses (Gabbro.Stage0.OldSource.koepfeVon items)
      (fnAt u f).name).any Gabbro.Stage0.OldSource.hasEntry = true
  · simp only [h, if_true]
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, if_false, List.any_nil, Bool.not_false, if_true]

/-- **What Stage 0 compiles is the restored program.** -/
theorem restore_restored {items expanded : List SItemTief} {requirements : List (STyp × String)}
    {u : UProg} {P P' : Programm (declOf u)}
    (hx : Modules.prepare items = .ok (expanded, requirements))
    (h : Gabbro.Stage0.OldSource.restore items u P = .ok P') :
    P' = restored (altVon expanded) u P := by
  obtain ⟨hP', xs, rs, hexp, hat⟩ := Gabbro.Stage0.OldSource.restore_fields items u P P' h
  have hx' : expandU items = .ok (expanded, requirements) := hx
  rw [hx'] at hexp
  injection hexp with hexp
  injection hexp with hxs
  subst hxs
  rw [hP']
  unfold restored
  congr
  funext f
  have hf : atFunctionMit (altVon expanded) u f (P.ensures f) = .ok (P'.ensures f) := by
    exact (atFunctionMit_altVon expanded u f (P.ensures f)).symm.trans (hat f)
  unfold ensAltAt
  rw [hf]

theorem ensAltAt_kongruent {alt alt' : String → List SExpr} {u : UProg} {f : Fin u.fns.length}
    {e0 : EnsTy u f} (h : alt (fnAt u f).name = alt' (fnAt u f).name) :
    ensAltAt alt u f e0 = ensAltAt alt' u f e0 := by
  unfold ensAltAt atFunctionMit
  rw [h]

/-- Clauses that agree on the unit's functions restore the same program. -/
theorem restored_kongruent {alt alt' : String → List SExpr} {u : UProg} (P : Programm (declOf u))
    (h : ∀ f : Fin u.fns.length, alt (fnAt u f).name = alt' (fnAt u f).name) :
    restored alt u P = restored alt' u P := by
  unfold restored
  congr
  funext f
  exact ensAltAt_kongruent (h f)

/-- A function without an entry read keeps its lowered postcondition. -/
theorem ensAltAt_ohne {alt : String → List SExpr} {u : UProg} {f : Fin u.fns.length} {e0 : EnsTy u f}
    (h : (alt (fnAt u f).name).any Gabbro.Stage0.OldSource.hasEntry = false) : ensAltAt alt u f e0 = e0 := by
  unfold ensAltAt atFunctionMit
  simp only [h, Bool.not_false, if_true]
  rfl

/-- A function with an entry read has the restored postcondition. -/
theorem ensAltAt_mit {alt : String → List SExpr} {u : UProg} {f : Fin u.fns.length} {e0 e : EnsTy u f}
    (h : atFunctionMit alt u f e0 = .ok e) : ensAltAt alt u f e0 = e := by
  unfold ensAltAt
  rw [h]

/-- The clauses `alt` as data: a list of the functions with an entry read. -/
def altAus (l : List (String × List SExpr)) (name : String) : List SExpr := (l.lookup name).getD []

open Gabbro.Stage0 in
/-- The run fact of `nutzerBild` about `alt`, computed as Stage 0 computes its expanded items (the
    steps of `compile` up to `Modules.prepare`); checked in the generated `Pruefung` module. -/
def stufe0AltB (text : String) (u : UProg) (alt : String → List SExpr) (options : Profil.Options := {}) : Bool :=
  match Frontend.source text options with
  | .error _ => false
  | .ok source =>
    match Modules.prepare (pre108 source.prepared.elaborierbar) with
    | .ok (expanded, _) => u.fns.all fun fn => beqSExprList (altVon expanded fn.name) (alt fn.name)
    | .error _ => false

open Gabbro.Stage0 in
/-- The clauses of the unit of `text` as data for the generator. -/
def stufe0Alt (text : String) (u : UProg) (options : Profil.Options := {}) : List (String × List SExpr) :=
  match Frontend.source text options with
  | .error _ => []
  | .ok source =>
    match Modules.prepare (pre108 source.prepared.elaborierbar) with
    | .ok (expanded, _) => u.fns.filterMap fun fn =>
        let s := altVon expanded fn.name
        if s.isEmpty then none else some (fn.name, s)
    | .error _ => []

#print axioms restore_restored

end Gabbro.Bruecke
