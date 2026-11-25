module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean Meta

namespace Gabbro.Core.Waechter

/-- A statement may be wrong in ways its proof never meets, because the false part is never used: a binder the
    body ignores (so the claim is the same for every value, or false for all of them), a free function parameter
    nothing ties to the model (a degenerate choice proves it), a pinned statement with no non-triviality lemma.
    These checks read the elaborated statement only; they decide nothing about its meaning and report what a
    reviewer should look at. A finding in the namespace of the correctness statements is an error; elsewhere it is
    reported as information, so the existing statements are measured before the rule is made strict. -/
public meta structure BinderFindings where
  errors : Array String
  infos : Array String

private meta def userNamed (n : Name) : Bool :=
  !n.isAnonymous && !n.hasMacroScopes && !(n.toString.startsWith "_")

/-- Names of data binders the author wrote and the scope never uses. A binder whose type is a proposition is a
    hypothesis and may be unused; an instance binder is resolved by the elaborator. -/
private meta def unusedBinders : Nat → Expr → MetaM (Array Name)
  | 0, _ => pure #[]
  | fuel + 1, e => do
    match e with
    | .forallE n t b bi | .lam n t b bi =>
      let inner ← withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        let rest ← unusedBinders fuel body
        if userNamed n && bi != .instImplicit && !(← isProp t) && !body.containsFVar x.fvarId! then
          return rest.push n
        return rest
      return (← unusedBinders fuel t) ++ inner
    | .app f a => return (← unusedBinders fuel f) ++ (← unusedBinders fuel a)
    | .mdata _ b => unusedBinders fuel b
    | .proj _ _ b => unusedBinders fuel b
    | _ => return #[]

/-- Parameters of a statement that are functions: data supplied by the caller that no premise binds to the
    model. A statement quantified over such a parameter is proved by a degenerate choice unless a premise or the
    unit itself determines it. -/
private meta def functionParameters (type : Expr) : MetaM (Array Name) :=
  forallTelescope type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if userNamed decl.userName && decl.binderInfo != .instImplicit && !(← isProp decl.type) then
        if (← whnfR decl.type).isForall then
          out := out.push decl.userName
    return out

public meta def endsWithAussage (name : Name) : Bool :=
  match name with
  | .str _ s => s.endsWith "Aussage"
  | _ => false

public meta def isStatement (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ result => pure result.isProp

/-- The Core module that declares `name`, for reports that list name, file and reason. -/
public meta def modulName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.modules[idx.toNat]!.module).toString
  | none => "unknown module"

/-- Scan one statement (`…Aussage` or an unnamed proposition used as one): unused data binders and
    free function parameters. `force` scans even deep values; every scan runs on its own heartbeat
    budget and reports instead of failing when the budget runs out. -/
public meta def statementScan (env : Environment) (name : Name) (info : DefinitionVal)
    (force : Bool) : MetaM (Array String) := do
  tryCatchRuntimeEx
    (Core.withCurrHeartbeats do
        let mut found : Array String := #[]
        let depth := info.value.approxDepth.toNat
        let modul := modulName env name
        if force || depth ≤ 60 then
          for n in (← unusedBinders (depth + 2) info.value) do
            found := found.push s!"statement {name} in module {modul} has the unused data binder {n}"
          for n in (← functionParameters info.type) do
            found := found.push
              s!"statement {name} in module {modul} takes the free function parameter {n} that nothing binds to the model"
        -- A binder unused in both the type and the value position (or shadowed) would print
        -- byte-identical lines; report each finding once.
        return found.toList.eraseDups.toArray)
    fun _ => return #[s!"statement {name} in module {modulName env name} could not be scanned within the heartbeat budget"]

private meta def correctnessNamespace : Name := `Gabbro.Core.Ziel.Korrektheit

/-- Scan every statement (`…Aussage` returning a proposition, parameters included). Reports unused data binders
    and function parameters, and, for the correctness statements, a missing pin and the missing companions
    `X.erfuellbar` and `X.nichtTrivial`. The companions are open entries (information) until the closing guard
    (`closing`) turns them into errors, as the registry's open entries are. -/
public meta def binderFindings (env : Environment) (pinned : Name → Bool) (closing : Bool) :
    MetaM BinderFindings := do
  let mut errors : Array String := #[]
  let mut infos : Array String := #[]
  for name in coreDeclarations env do
    unless endsWithAussage name do continue
    let some (.defnInfo info) := env.find? name | continue
    unless (← isStatement info.type) do continue
    let strict := correctnessNamespace.isPrefixOf name
    let mut here : Array String := #[]
    here := here ++ (← statementScan env name info strict)
    unless pinned name do
      if strict then
        here := here.push s!"statement {name} is not pinned (parameterised statements are not covered by the pin check)"
    if strict then
      for companion in #[`erfuellbar, `nichtTrivial] do
        unless env.contains (name ++ companion) do
          let message := s!"statement {name} has no companion {name ++ companion}"
          if closing then here := here.push message else infos := infos.push message
    if strict then errors := errors ++ here else infos := infos ++ here
  return ⟨errors, infos⟩

end Gabbro.Core.Waechter
