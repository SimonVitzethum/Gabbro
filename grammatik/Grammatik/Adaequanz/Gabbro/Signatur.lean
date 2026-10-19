/-
  File:      Grammatik/Adaequanz/Gabbro/Signatur.lean
  Subject:   THE ABSTRACT SIGNATURE OF GABBRO, read off the model: for every constructor of the term families of
             `Kern/Syntax/Syntax.lean` (`Expr`, `NutzlastExpr`, `Args`, `ErgExpr`, `Stmt`, `Block`, `Endblock`, `Arms`,
             `GrundArms`) its CHILDREN (the arguments whose type is one of the families: the arity in the sense of
             `Adaequanz/Baum.lean`), its PREMISES (the `Prop`-typed arguments: each is a typing rule the checker must
             refuse when it fails, i.e. one local refusal cell of Theorem 4) and its DATA (the remaining explicit
             arguments: declared names, numbers, types; they form the constructor's label).

  The table `tabelle` is written here and COMPARED with the environment when this file is elaborated
  (`pruefeTabelle`): a new constructor, a new child or a new premise in the model stops the build here until
  the table and `PRUEFER.md` §16.6 are updated (the register moves with the model, as `Gen/Abdeckung/Mitglieder`).
-/
import Lean
import Grammatik.Kern.Syntax.Syntax

namespace Gabbro.Grammatik.Adaequanz.GabbroSig

open Lean Meta

/-- The families, in this order. -/
def familien : List Name := [``Gabbro.Grammatik.Expr, ``Gabbro.Grammatik.NutzlastExpr, ``Gabbro.Grammatik.Args,
  ``Gabbro.Grammatik.ErgExpr, ``Gabbro.Grammatik.Stmt, ``Gabbro.Grammatik.Block, ``Gabbro.Grammatik.Endblock,
  ``Gabbro.Grammatik.Arms, ``Gabbro.Grammatik.GrundArms]

/-- One constructor: family, name, the families of its children, the number of premises, the number of data. -/
structure Konstr where
  familie : String
  name : String
  kinder : List String
  praemissen : Nat
  daten : Nat
  deriving Repr, BEq

/-- Read one constructor off the environment. -/
def lies (c : Name) : MetaM Konstr := do
  let info ← getConstInfoCtor c
  forallTelescope info.type fun args _ => do
    let mut kinder : List String := []
    let mut pr := 0
    let mut da := 0
    for a in args do
      let ty ← inferType a
      let ld ← a.fvarId!.getDecl
      match ty.getAppFn.constName? with
      | some n =>
          if familien.contains n then kinder := kinder ++ [n.getString!]
          else if ← isProp ty then pr := pr + 1
          else if ld.binderInfo.isExplicit then da := da + 1
      | none =>
          if ← isProp ty then pr := pr + 1
          else if ld.binderInfo.isExplicit then da := da + 1
    return ⟨info.induct.getString!, c.getString!, kinder, pr, da⟩

/-- The whole table, read off the environment. -/
def leseAlle : MetaM (List Konstr) := do
  let mut out := []
  for f in familien do
    let iv ← getConstInfoInduct f
    for c in iv.ctors do
      out := out ++ [← lies c]
  return out

/-- **The table**, one row per constructor: family, name, children, premises, data. -/
def tabelle : List Konstr := [
  ⟨"Expr", "lit", [], 0, 1⟩,
  ⟨"Expr", "tru", [], 0, 0⟩,
  ⟨"Expr", "fls", [], 0, 0⟩,
  ⟨"Expr", "var", [], 0, 1⟩,
  ⟨"Expr", "glob", [], 1, 1⟩,
  ⟨"Expr", "slot", ["Expr"], 1, 2⟩,
  ⟨"Expr", "thru", ["Expr", "Expr"], 2, 2⟩,
  ⟨"Expr", "ptrOf", [], 1, 3⟩,
  ⟨"Expr", "fnref", [], 1, 2⟩,
  ⟨"Expr", "oldG", [], 1, 1⟩,
  ⟨"Expr", "oldS", ["Expr"], 1, 2⟩,
  ⟨"Expr", "widen", ["Expr"], 2, 0⟩,
  ⟨"Expr", "add", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "sub", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "neg", ["Expr"], 0, 0⟩,
  ⟨"Expr", "mul", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "div", ["Expr", "Expr"], 2, 0⟩,
  ⟨"Expr", "rem", ["Expr", "Expr"], 2, 0⟩,
  ⟨"Expr", "sdiv", ["Expr", "Expr"], 1, 0⟩,
  ⟨"Expr", "srem", ["Expr", "Expr"], 1, 0⟩,
  ⟨"Expr", "getBytes", ["Expr"], 4, 3⟩,
  ⟨"Expr", "band", ["Expr", "Expr"], 2, 0⟩,
  ⟨"Expr", "bor", ["Expr", "Expr"], 4, 1⟩,
  ⟨"Expr", "bxor", ["Expr", "Expr"], 4, 1⟩,
  ⟨"Expr", "shl", ["Expr", "Expr"], 4, 1⟩,
  ⟨"Expr", "shr", ["Expr", "Expr"], 4, 1⟩,
  ⟨"Expr", "lt", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "le", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "eq", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "fllt", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "flle", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "and", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "or", ["Expr", "Expr"], 0, 0⟩,
  ⟨"Expr", "not", ["Expr"], 0, 0⟩,
  ⟨"Expr", "none", [], 0, 1⟩,
  ⟨"Expr", "some", ["Expr"], 0, 0⟩,
  ⟨"Expr", "istSome", ["Expr"], 0, 0⟩,
  ⟨"Expr", "case", ["NutzlastExpr"], 0, 2⟩,
  ⟨"Expr", "why", [], 0, 2⟩,
  ⟨"Expr", "forallSlots", ["Expr"], 1, 1⟩,
  ⟨"Expr", "existsSlots", ["Expr"], 1, 1⟩,
  ⟨"Expr", "reaches", ["Expr", "Expr"], 2, 2⟩,
  ⟨"NutzlastExpr", "empty", [], 0, 0⟩,
  ⟨"NutzlastExpr", "num", ["Expr"], 0, 0⟩,
  ⟨"Args", "nil", [], 0, 0⟩,
  ⟨"Args", "cons", ["Expr", "Args"], 0, 0⟩,
  ⟨"ErgExpr", "empty", [], 0, 0⟩,
  ⟨"ErgExpr", "val", ["Expr"], 0, 0⟩,
  ⟨"Stmt", "assignSlot", ["Expr", "Expr"], 2, 2⟩,
  ⟨"Stmt", "assignThru", ["Expr", "Expr", "Expr"], 3, 2⟩,
  ⟨"Stmt", "assignGlob", ["Expr"], 2, 1⟩,
  ⟨"Stmt", "putBytes", ["Expr", "Expr"], 5, 3⟩,
  ⟨"Stmt", "assignVar", ["Expr"], 0, 1⟩,
  ⟨"Stmt", "shift", ["Expr"], 5, 4⟩,
  ⟨"Stmt", "ite", ["Expr", "Block", "Block"], 0, 0⟩,
  ⟨"Stmt", "onOption", ["Expr", "Block", "Block"], 0, 0⟩,
  ⟨"Stmt", "onTag", ["Expr", "Arms"], 0, 0⟩,
  ⟨"Stmt", "onWhy", ["Expr", "GrundArms"], 0, 0⟩,
  ⟨"Stmt", "call", ["Args"], 2, 1⟩,
  ⟨"Stmt", "callInd", ["Expr", "Args"], 2, 0⟩,
  ⟨"Stmt", "locks", ["Block"], 1, 1⟩,
  ⟨"Stmt", "breaking", ["Block"], 0, 1⟩,
  ⟨"Stmt", "traverse", ["Expr", "Block"], 0, 1⟩,
  ⟨"Stmt", "retry", ["Expr", "Block", "Block"], 0, 1⟩,
  ⟨"Stmt", "forever", ["Expr", "Block"], 0, 1⟩,
  ⟨"Stmt", "axiomCall", ["Args"], 5, 1⟩,
  ⟨"Stmt", "regWrite", ["Expr"], 1, 1⟩,
  ⟨"Stmt", "transition", [], 3, 4⟩,
  ⟨"Stmt", "publish", ["Expr"], 3, 2⟩,
  ⟨"Stmt", "advances", [], 2, 2⟩,
  ⟨"Stmt", "retires", [], 1, 3⟩,
  ⟨"Stmt", "ret", ["ErgExpr"], 1, 0⟩,
  ⟨"Stmt", "retWhy", [], 1, 1⟩,
  ⟨"Stmt", "leave", [], 1, 0⟩,
  ⟨"Stmt", "next", [], 1, 0⟩,
  ⟨"Block", "nil", [], 0, 0⟩,
  ⟨"Block", "cons", ["Stmt", "Block"], 0, 0⟩,
  ⟨"Block", "bind", ["Expr", "Block"], 0, 0⟩,
  ⟨"Block", "bindCall", ["Args", "Block"], 3, 1⟩,
  ⟨"Block", "bindCallInd", ["Expr", "Args", "Block"], 3, 0⟩,
  ⟨"Block", "bindCallElse", ["Args", "Endblock", "Block"], 3, 1⟩,
  ⟨"Block", "bindAxiom", ["Args", "Block"], 5, 1⟩,
  ⟨"Block", "bindAxiomElse", ["Args", "Endblock", "Block"], 6, 1⟩,
  ⟨"Block", "regRead", ["Block"], 1, 1⟩,
  ⟨"Block", "regReadElse", ["Expr", "Endblock", "Block"], 1, 1⟩,
  ⟨"Block", "awaits", ["Block"], 2, 2⟩,
  ⟨"Block", "exchange", ["Expr", "Block"], 2, 1⟩,
  ⟨"Block", "narrow", ["Expr", "Endblock", "Block"], 0, 2⟩,
  ⟨"Block", "check", ["Expr", "Endblock", "Block"], 0, 0⟩,
  ⟨"Block", "float", ["Expr", "Expr", "Block"], 0, 3⟩,
  ⟨"Block", "floatLit", ["Block"], 0, 3⟩,
  ⟨"Block", "floatOf", ["Expr", "Block"], 0, 2⟩,
  ⟨"Block", "floatNarrow", ["Expr", "Endblock", "Block"], 0, 2⟩,
  ⟨"Endblock", "ret", ["ErgExpr"], 1, 0⟩,
  ⟨"Endblock", "retWhy", [], 1, 1⟩,
  ⟨"Endblock", "leave", [], 1, 0⟩,
  ⟨"Endblock", "next", [], 1, 0⟩,
  ⟨"Endblock", "cons", ["Stmt", "Endblock"], 0, 0⟩,
  ⟨"Endblock", "bind", ["Expr", "Endblock"], 0, 0⟩,
  ⟨"Endblock", "bindCall", ["Args", "Endblock"], 3, 1⟩,
  ⟨"Endblock", "bindCallElse", ["Args", "Endblock", "Endblock"], 3, 1⟩,
  ⟨"Endblock", "bindAxiom", ["Args", "Endblock"], 5, 1⟩,
  ⟨"Endblock", "bindAxiomElse", ["Args", "Endblock", "Endblock"], 6, 1⟩,
  ⟨"Arms", "nil", [], 0, 0⟩,
  ⟨"Arms", "cons", ["Block", "Arms"], 0, 0⟩,
  ⟨"GrundArms", "nil", [], 0, 0⟩,
  ⟨"GrundArms", "cons", ["Block", "GrundArms"], 0, 0⟩]

/-- Compare the written table with the model. -/
def pruefeTabelle : MetaM Unit := do
  let ist ← leseAlle
  if ist != tabelle then
    let zeilen := ist.map fun k => s!"  ⟨\"{k.familie}\", \"{k.name}\", {repr k.kinder}, {k.praemissen}, {k.daten}⟩"
    throwError m!"Adaequanz/Gabbro/Signatur.lean: the constructor table is out of date; the model reads\n{String.intercalate ",\n" zeilen}"

run_meta pruefeTabelle

/-- The rows of a family. -/
def zeilen (f : String) : List Konstr := tabelle.filter (·.familie == f)

/-- 107 constructors: `Expr` 42, `NutzlastExpr` 2, `Args` 2, `ErgExpr` 2, `Stmt` 27, `Block` 18, `Endblock` 10,
    `Arms` 2, `GrundArms` 2. -/
theorem anzahl_konstruktoren : tabelle.length = 107 ∧
    ["Expr", "NutzlastExpr", "Args", "ErgExpr", "Stmt", "Block", "Endblock", "Arms", "GrundArms"].map
      (fun f => (zeilen f).length) = [42, 2, 2, 2, 27, 18, 10, 2, 2] := by decide

/-- The arity histogram: how many constructors have 0, 1, 2, 3 children. -/
theorem stelligkeiten : [0, 1, 2, 3].map (fun a => (tabelle.filter (·.kinder.length == a)).length) = [25, 27, 41, 14] := by
  decide

/-- The premises (each one local refusal cell of Theorem 4) and the child positions (each one "child of the wrong
    sort or index" refusal cell). -/
theorem praemissen_und_kinder : (tabelle.map (·.praemissen)).sum = 130 ∧
    (tabelle.map (·.kinder.length)).sum = 151 := by decide

end Gabbro.Grammatik.Adaequanz.GabbroSig
