/-
  File:      Grammatik/Zielsatz/Waechter/Abhaengigkeit.lean
  Subject:   GUARD 1 (B24 step 0, `dokumente/PERFECT-MODEL.md` §6.1): ACCEPTANCE IS NOT CIRCULAR. The acceptance of the goal may use the
             syntax, the ideal meaning `I` and the catalogue rows; it may NOT use a step relation, a run or a
             reachability notion of G/GX/W (or any machine), the image, or the error notion.

  `A` is the meaning closure (`Grundlagen.huelle`: types, definition bodies, constructors; proofs are not
  followed) of the acceptance predicates: the decided checker `AkzeptiertX`/`AkzeptiertXVoll`, its soundness target
  `AkzeptiertSpecX` with `BesitzStart` and `Kernzelle.AkkuStart`, and `PrueferX`, the checker interface of the goal.

  WHITELIST. Every constant of `A` must be one of:
  * STATE-FREE (syntax, checker, decision procedures): its type and body mention no state type. State types are
    found semantically (`Grundlagen.zustandsTypen`): the store seeds `World`, `Speicher`, and every inductive type
    with a field whose codomain mentions a state type -- so every machine, and every renamed copy of one, is a state
    type without being named;
  * in the INTERIM `I`: `I` does not exist yet; its interim stand-in is the per-thread big-step semantics that the
    truth of written clauses needs: the clause duties `ContractDuties`/`InvariantDuties` with the body semantics
    `execEndHA` they range over, and the five
    two-place store relations of the clauses (`Rahmen`, `GleichAuf`, `EnsAmRueck`, `CallContract.postHolds`,
    `TraegerGleich`), with their whole closure. The closure is HASH-PINNED (`iHash`): any change of the interim `I`
    stops the build for review;
  * on the RATCHET list `zustandErlaubt`: today's state-mentioning acceptance constants outside `I`, counted per
    module. They are the contract/invariant VC checker, whose decision procedures return certificates stating
    their soundness over the semantics (`{formula // ∀ world, ... ↔ holds ...}`), and the checked environment
    replay. The list may only shrink: a new module or a higher count fails.
  Independently of the whitelist, over ALL of `A` (the interim `I` included):
  * no RUN: no binder (∀ or λ, anywhere in a type or a definition body) of type `Nat → ... → T` with `T` headed by
    a state type;
  * no STEP RELATION: no Prop-valued constant or constructor with two arguments of the same state type, except the
    five clause relations above;
  * no ERROR NOTION: `HaltArt` is not in `A`;
  * no hidden body: a project definition whose body the module system does not export (an `axiomInfo` of non-Prop
    type) cannot be inspected; today's are the opaque native-float primitives, pinned in `versteckt`.
  REVERSE GUARD: `I` must not depend on acceptance. Today: the interim `I` contains none of the acceptance roots.
  Once `I` exists as its own definition, `iWurzeln` becomes `I` and the same check applies to it.
-/
module
public import Grammatik.Zielsatz.Waechter.Grundlagen
public import Grammatik.Zielsatz.Atomar.AkzeptiertSchnell
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Bausteine.Kernzelle.Start
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1Basis
meta import Lean
meta import Grammatik.Zielsatz.Waechter.Grundlagen
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter.Abhaengigkeit

open Lean Meta

/-- The acceptance roots. -/
def aWurzeln : List Name := [``AkzeptiertX, ``AkzeptiertXVoll, ``AkzeptiertSpecX, ``BesitzStart,
  ``Kernzelle.AkkuStart, ``PrueferX]

/-- The roots of the interim `I`. -/
def iWurzeln : List Name := [``execEndHA, ``Invarianten.Pruefer.InvariantDuties,
  ``Vertraege.Pruefer.ContractDuties, ``Rahmen, ``GleichAuf, ``EnsAmRueck, ``CallContract.postHolds,
  ``TraegerGleich]

/-- The two-place store relations of the clauses (allowed step-shaped relations). -/
def klauselRelationen : List Name := [``Rahmen, ``GleichAuf, ``EnsAmRueck, ``CallContract.postHolds,
  ``TraegerGleich]

/-- The error notion: never part of acceptance. -/
def fehlerBegriff : List Name := [``HaltArt]

/-- The pinned hash of the interim `I` (its whole closure). -/
def iHash : UInt64 := 1859952517140106798

/-- RATCHET: today's state-mentioning acceptance constants outside the interim `I`, counted per module. -/
def zustandErlaubt : List (String × Nat) :=
  [("Grammatik.Bausteine.Arena.ArenaZucker.Teil1Basis", 1),
   ("Grammatik.Bausteine.Arena.Ownership.Machine.Reach", 1),
   ("Grammatik.Bausteine.Arena.Struktur.ArenaFrei.Teil1Basis", 1),
   ("Grammatik.Bausteine.Kernzelle.Start", 1),
   ("Grammatik.Kern.Semantik.Maschine.T1.Teil1", 1),
   ("Grammatik.Kern.Semantik.Semantik.T1.Teil1", 5),
   ("Grammatik.Kern.Semantik.Semantik.T1.Teil2", 1),
   ("Grammatik.Logik.Invarianten.Frag.Bounded", 8),
   ("Grammatik.Logik.Invarianten.Frag.Constant", 8),
   ("Grammatik.Logik.Invarianten.Frag.Observation", 16),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Current", 56),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Encoding", 13),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Environment", 12),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters", 7),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Projection", 3),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Relation", 4),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Scope", 12),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Base", 3),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Encoding", 19),
   ("Grammatik.Logik.Invarianten.Frag.Symbolic.Translation", 22),
   ("Grammatik.Logik.Invarianten.Frag.Translation", 30),
   ("Grammatik.Logik.Invarianten.Pruefer.Locks", 2),
   ("Grammatik.Logik.Invarianten.Pruefer.Program", 1),
   ("Grammatik.Logik.Invarianten.Pruefer.Writer", 9),
   ("Grammatik.Logik.Invarianten.VC.Calls", 6),
   ("Grammatik.Logik.Invarianten.VC.Compiler", 14),
   ("Grammatik.Logik.Invarianten.VC.Continuation", 10),
   ("Grammatik.Logik.Invarianten.VC.Control", 23),
   ("Grammatik.Logik.Invarianten.VC.Domain", 22),
   ("Grammatik.Logik.Invarianten.VC.Extended", 1),
   ("Grammatik.Logik.Invarianten.VC.Induction", 5),
   ("Grammatik.Logik.Invarianten.VC.Leaves", 13),
   ("Grammatik.Logik.Invarianten.VC.Locks", 6),
   ("Grammatik.Logik.Invarianten.VC.Loops", 11),
   ("Grammatik.Logik.Invarianten.VC.Scalar", 19),
   ("Grammatik.Logik.Invarianten.VC.Writer", 2),
   ("Grammatik.Logik.Ruf.FremdRuf.T4", 1),
   ("Grammatik.Logik.Ruf.Schnittstellen.Vertrag", 2),
   ("Grammatik.Logik.Vertraege.Pruefer.Auxiliary", 2),
   ("Grammatik.Logik.Vertraege.Pruefer.Basic", 47),
   ("Grammatik.Logik.Vertraege.Pruefer.Calls", 7),
   ("Grammatik.Logik.Vertraege.Pruefer.Compiler", 21),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Arguments", 14),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Binding", 2),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.CallBinding", 12),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Composition", 35),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Entry", 4),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Flow", 5),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Join", 3),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Memory", 8),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Narrowing", 2),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Block", 12),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.End", 12),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Goals", 1),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Result", 4),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Tail", 4),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Policy", 14),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Quantified", 3),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Refinement", 8),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Results", 14),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Selection", 22),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Snapshots", 2),
   ("Grammatik.Logik.Vertraege.Pruefer.Control.Symbolic", 29),
   ("Grammatik.Logik.Vertraege.Pruefer.Decision", 12),
   ("Grammatik.Logik.Vertraege.Pruefer.Indirect.Basic", 8),
   ("Grammatik.Logik.Vertraege.Pruefer.Indirect.Binding", 7),
   ("Grammatik.Logik.Vertraege.Pruefer.Indirect.Fallible", 10),
   ("Grammatik.Logik.Vertraege.Pruefer.Leaves", 24),
   ("Grammatik.Logik.Vertraege.Pruefer.Locks", 7),
   ("Grammatik.Logik.Vertraege.Pruefer.Loops", 24),
   ("Grammatik.Logik.Vertraege.Pruefer.Program", 1),
   ("Grammatik.Logik.Vertraege.Pruefer.Sources", 1),
   ("Grammatik.Nebenlaeufigkeit.Sperren.Sources", 1),
   ("Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1", 21),
   ("Grammatik.Speichermodell.Atomar.AtomarSem.Teil1", 2),
   ("Grammatik.Zielsatz.Kern.Spec.Teil1Basis", 9),
   ("Grammatik.Zielsatz.Kern.Spec.Teil2", 3)]

/-- RATCHET: today's project definitions in `A` without an exported body. -/
def versteckt : List String :=
  ["Float.hwAdd",
   "Float.hwDiv",
   "Float.hwIsFinite",
   "Float.hwIsNaN",
   "Float.hwLe",
   "Float.hwLt",
   "Float.hwMul",
   "Float.hwNeg",
   "Float.hwOfBits",
   "Float.hwOfInt",
   "Float.hwSub",
   "Float.hwToBits",
   "Float.hwToInt64",
   "Float.hwToUInt64",
   "Float32.hwAdd",
   "Float32.hwDiv",
   "Float32.hwIsFinite",
   "Float32.hwIsNaN",
   "Float32.hwLt",
   "Float32.hwMul",
   "Float32.hwNeg",
   "Float32.hwOfBits",
   "Float32.hwSub",
   "Float32.hwToBits",
   "Float32.hwToInt64",
   "Float32.hwToUInt64",
   "Int64.hwToFloat",
   "Int64.hwToFloat32",
   "RootNativeFloat.Contracts.Format.Rounded",
   "RootNativeFloat.Contracts.Format.binary32",
   "RootNativeFloat.Contracts.Format.binary64",
   "RootNativeFloat.canonLiteral",
   "UInt64.hwToFloat",
   "UInt64.hwToFloat32"]

/-- What a constant's meaning mentions (type, and body of a definition). -/
def erwaehnt (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo d => ci.type.getUsedConstants ++ d.value.getUsedConstants
  | .opaqueInfo d => ci.type.getUsedConstants ++ d.value.getUsedConstants
  | _ => ci.type.getUsedConstants

def pruefe : MetaM Unit := do
  let env ← getEnv
  let st := zustandsTypen env [``World, ``Speicher]
  let a := huelle env aWurzeln
  let i := huelle env iWurzeln
  let mut befunde : List String := []
  -- the pin of the interim `I`
  let h := mengenHash env i
  if h != iHash then
    befunde := befunde ++ [s!"the interim I changed ({i.size} constants, hash {h}, pinned {iHash})"]
  -- the reverse guard
  for r in aWurzeln do
    if i.contains r then befunde := befunde ++ [s!"the interim I depends on acceptance: {r}"]
  for f in fehlerBegriff do
    if a.contains f then befunde := befunde ++ [s!"acceptance depends on the error notion: {f}"]
  let mut zustand : Std.HashMap String Nat := {}
  let mut verborgen : List String := []
  for n in sortiert a do
    let some ci := env.find? n | continue
    -- runs and step relations, over all of `A`
    let fund ← forallTelescopeReducing ci.type fun xs body => do
      let mut out : List String := []
      let mut koepfe : Array Name := #[]
      for x in xs do
        let t ← inferType x
        if let some k := kopf t then
          if st.contains k then koepfe := koepfe.push k
      if body.isProp && !klauselRelationen.contains n then
        let mut zwei := false
        for x in [0:koepfe.size] do
          for y in [x+1:koepfe.size] do
            if koepfe[x]! == koepfe[y]! then zwei := true
        if zwei then out := out ++ [s!"a step-shaped relation over a state type: {n}"]
      return out
    befunde := befunde ++ fund
    let wert := match ci with
      | .defnInfo d => some d.value | .opaqueInfo d => some d.value | _ => none
    if bindetLauf st ci.type || (wert.map (bindetLauf st)).getD false then
      befunde := befunde ++ [s!"a run (a binder Nat → state) in {n}"]
    -- the whitelist
    if !i.contains n && (erwaehnt ci).any st.contains then
      let m := ((modulVon env n).getD `this).toString
      zustand := zustand.insert m (zustand.getD m 0 + 1)
    if let .axiomInfo ax := ci then
      if !(← isProp ax.type) then verborgen := verborgen ++ [n.toString]
  let zustandL := (zustand.toList.toArray.qsort (fun a b => a.1 < b.1)).toList
  let r1 := ratsche zustandL zustandErlaubt
  let r2 := ratscheMenge verborgen versteckt
  befunde := befunde ++ r1.map ("outside the whitelist: " ++ ·) ++ r2.map ("hidden body: " ++ ·)
  melde s!"acceptance depends on more than syntax, the interim I and the catalogue ({a.size} constants)" befunde
    ("review with the owner; a step relation, a run or the error notion in acceptance is never pinned. " ++
     "Re-pin only after review: `iHash`, `zustandErlaubt` and `versteckt` in Waechter/Abhaengigkeit.lean. " ++
     s!"Measured lists:\nzustandErlaubt := {alsListe zustandL}\nversteckt := {alsNamen verborgen}")

run_meta pruefe

end Gabbro.Grammatik.Zielsatz.Waechter.Abhaengigkeit
