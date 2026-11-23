/-
  File:      Grammatik/Zielsatz/Waechter/Grundlagen.lean
  Subject:   The shared meta code of the build guards of the goal's foundations (B24 step 0, `dokumente/PERFECT-MODEL.md` §6): constant closures, definition hashes, the semantic notion of a STATE TYPE, the wildcard
             alternatives of a matcher, and the comparison of a measured list with its ratchet list.

  Nothing here is a check; the guards are the modules beside this one. Every guard is a RATCHET: it compares what it
  measures with a pinned list of today's known cases; a new case fails the build, and a pinned case that disappeared
  fails it too until it is removed from the list, so the list only shrinks.
-/
module
public import Lean
meta import Lean
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter

open Lean Meta

/-- Packages that are NOT the project: the Lean core, its libraries and Mathlib. -/
def bibliotheken : List Name := [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible,
  `ProofWidgets, `ImportGraph, `LeanSearchClient]

/-- The module that defines a constant (`none`: the current module). -/
def modulVon (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Is the constant defined in the project (and not in the core, its libraries or Mathlib)? -/
def imProjekt (env : Environment) (n : Name) : Bool :=
  match modulVon env n with
  | none => true
  | some m => !bibliotheken.contains m.getRoot

/-- The constants a constant's MEANING depends on: its type, the value of a definition, the constructors of an
    inductive type, the type of a constructor. Proofs of theorems are not followed (proof irrelevance). -/
def direkt (ci : ConstantInfo) : List Name :=
  let t := ci.type.getUsedConstants.toList
  match ci with
  | .defnInfo d => t ++ d.value.getUsedConstants.toList
  | .opaqueInfo d => t ++ d.value.getUsedConstants.toList
  | .inductInfo i => t ++ i.ctors
  | .ctorInfo c => t ++ [c.induct]
  | _ => t

/-- The project constants the meaning of `starts` depends on, transitively, `starts` included. -/
partial def huelle (env : Environment) (starts : List Name) : Std.HashSet Name := Id.run do
  let mut gesehen : Std.HashSet Name := {}
  let mut offen := starts
  while !offen.isEmpty do
    match offen with
    | [] => pure ()
    | n :: rest =>
      offen := rest
      if gesehen.contains n || !imProjekt env n then continue
      gesehen := gesehen.insert n
      if let some ci := env.find? n then
        offen := (direkt ci).filter (!gesehen.contains ·) ++ offen
  return gesehen

/-- Names sorted by their text (deterministic reports and hashes). -/
def sortiert (s : Std.HashSet Name) : Array Name :=
  s.toList.toArray.qsort (fun a b => a.toString < b.toString)

/-- The hash of ONE constant: its kind, type and value, or the types of its constructors. `Expr.hash` is structural
    and ignores binder names; it can move with the Lean toolchain (then the pins are renewed the same way).
    `ZellenPruefung.huelleHash` hashes definition bodies only and therefore cannot pin a structure or an inductive
    relation; this hash covers both. -/
def konstHash (env : Environment) (n : Name) : UInt64 :=
  match env.find? n with
  | none => 0
  | some ci =>
    let h := mixHash (hash n) ci.type.hash
    match ci with
    | .defnInfo d => mixHash (mixHash h 1) d.value.hash
    | .opaqueInfo d => mixHash (mixHash h 2) d.value.hash
    | .inductInfo i => i.ctors.foldl (fun h c => match env.find? c with
        | some cc => mixHash h (mixHash (hash c) cc.type.hash)
        | none => h) (mixHash h 3)
    | .thmInfo _ => mixHash h 4
    | .axiomInfo _ => mixHash h 5
    | _ => mixHash h 6

/-- The hash of a set of constants (sorted, each with `konstHash`). -/
def mengenHash (env : Environment) (s : Std.HashSet Name) : UInt64 :=
  (sortiert s).foldl (fun h n => mixHash h (konstHash env n)) 7

/-- The codomain of a type, after all its binders. -/
def kodomain : Lean.Expr → Lean.Expr
  | .forallE _ _ b _ => kodomain b
  | e => e

/-- The head constant of a type. -/
def kopf (e : Lean.Expr) : Option Name := e.getAppFn.constName?

/-- **State types, semantically.** The seeds are the store of a body (`World`, `Speicher`, passed by the guard).
    A project inductive type is a state type when the codomain of one of its fields mentions a state type: every
    machine (G's call machine, the thread machine, W, the generic machine, a renamed copy of any of them) holds a
    store and is therefore a state type, without being named here. Computed as a fixpoint over all project
    inductive types of the environment. -/
def zustandsTypen (env : Environment) (seeds : List Name) : Std.HashSet Name := Id.run do
  let mut ind : Array (Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    if let .inductInfo i := ci then
      if imProjekt env n then
        let mut cs : List Name := []
        for c in i.ctors do
          if let some (.ctorInfo cc) := env.find? c then
            let mut t := cc.type
            for _ in [0:cc.numParams] do
              t := match t with | .forallE _ _ b _ => b | t => t
            while t.isForall do
              cs := (kodomain t.bindingDomain!).getUsedConstants.toList ++ cs
              t := t.bindingBody!
        ind := ind.push (n, cs)
  let mut st : Std.HashSet Name := seeds.foldl (·.insert ·) {}
  let mut weiter := true
  while weiter do
    weiter := false
    for (n, cs) in ind do
      if !st.contains n && cs.any st.contains then
        st := st.insert n; weiter := true
  return st

/-- A pattern of a matcher alternative is OPEN against another when it is one of the alternative's own variables
    where the other alternative has a constructor or a literal (recursively below equal constructors). -/
partial def offenGegen (env : Environment) (vars : Array Lean.Expr) (p q : Lean.Expr) : Bool :=
  if vars.contains p then
    q.isLit || (match q.getAppFn.constName? with
      | some c => (env.find? c matches some (.ctorInfo _)) || c == ``OfNat.ofNat
      | none => false)
  else
    match p.getAppFn.constName?, q.getAppFn.constName? with
    | some a, some b =>
      if a == b then
        match env.find? a with
        | some (.ctorInfo c) =>
          let ps := p.getAppArgs.extract c.numParams p.getAppNumArgs
          let qs := q.getAppArgs.extract c.numParams q.getAppNumArgs
          (ps.zip qs).any fun (x, y) => offenGegen env vars x y
        | _ => false
      else false
    | _, _ => false

/-- The number of WILDCARD alternatives of a matcher: alternatives that leave open a position (at any depth) that
    another alternative splits by a constructor or a literal -- the elaborated form of `_ =>` and of a variable
    pattern catching the remaining constructors. A position no alternative splits is not counted. -/
def wildcardAlts (m : Name) : MetaM Nat := do
  let some info ← getMatcherInfo? m | return 0
  let ci ← getConstInfo m
  forallTelescope ci.type fun xs _ => do
    let erst := info.numParams + 1 + info.numDiscrs
    let alts := xs.extract erst (erst + info.numAlts)
    let mut pats : Array (Array Lean.Expr × Array Lean.Expr) := #[]
    for a in alts do
      let t ← inferType a
      let r ← forallTelescope t fun vs body => do
        let args := body.getAppArgs
        return (vs, args.extract (args.size - info.numDiscrs) args.size)
      pats := pats.push r
    let env ← getEnv
    let mut k := 0
    for i in [0:pats.size] do
      let (vs, ps) := pats[i]!
      let mut wild := false
      for j in [0:pats.size] do
        if i != j && !wild then
          if (ps.zip pats[j]!.2).any fun (p, q) => offenGegen env vs p q then wild := true
      if wild then k := k + 1
    return k

/-- The user-facing name of a compiler-generated auxiliary (`f._f`, `f._unary`, `f.match_1`, ...): `f`. -/
partial def basisName (n : Name) : Name :=
  match n with
  | .str p s => if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" then basisName p else n
  | _ => n

/-- Compare a measurement with its ratchet list. Both are lists of (key, count); the result names every new key,
    every raised count, every key that disappeared and every count that fell (the list must then shrink). -/
def ratsche (gemessen gepinnt : List (String × Nat)) : List String := Id.run do
  let mut out : List String := []
  for (k, n) in gemessen do
    match gepinnt.lookup k with
    | none => out := out ++ [s!"NEW: {k} ({n})"]
    | some p =>
      if n > p then out := out ++ [s!"MORE: {k} ({n}, pinned {p})"]
      else if n < p then out := out ++ [s!"FEWER (shrink the list): {k} ({n}, pinned {p})"]
  for (k, p) in gepinnt do
    if (gemessen.lookup k).isNone then out := out ++ [s!"GONE (remove it from the list): {k} (pinned {p})"]
  return out

/-- A ratchet over a plain set of keys (each counted once). -/
def ratscheMenge (gemessen gepinnt : List String) : List String :=
  ratsche (gemessen.map (·, 1)) (gepinnt.map (·, 1))

/-- A measurement as the Lean text of its ratchet list (printed by a failing guard, for review and re-pinning). -/
def alsListe (xs : List (String × Nat)) : String :=
  "[" ++ String.intercalate ",\n " (xs.map fun (k, n) => s!"(\"{k}\", {n})") ++ "]"

/-- Names as the Lean text of a ratchet list of strings. -/
def alsNamen (xs : List String) : String :=
  "[" ++ String.intercalate ",\n " (xs.map fun k => s!"\"{k}\"") ++ "]"

/-- Does a term bind a RUN: a binder (∀, λ) whose type is `Nat → ... → T` with `T` headed by a state type? -/
def bindetLauf (st : Std.HashSet Name) (e : Lean.Expr) : Bool :=
  let lauf (d : Lean.Expr) : Bool :=
    d.isForall && d.bindingDomain!.isConstOf ``Nat &&
      (match kopf (kodomain d) with | some k => st.contains k | none => false)
  (e.find? fun s => match s with
    | .forallE _ d _ _ => lauf d
    | .lam _ d _ _ => lauf d
    | _ => false).isSome

/-- Fail with a headline and the findings, if there are any. -/
def melde (titel : String) (befunde : List String) (hinweis : String) : MetaM Unit := do
  unless befunde.isEmpty do
    throwError "{titel}:\n{String.intercalate "\n" befunde}\n{hinweis}"

end Gabbro.Grammatik.Zielsatz.Waechter
