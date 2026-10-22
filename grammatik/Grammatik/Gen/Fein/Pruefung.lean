/-
  File:      Grammatik/Gen/Fein/Pruefung.lean
  Subject:   THE CONSTRUCTOR TABLE `kTab` IS READ OFF THE MODEL when this file is elaborated (`pruefeKTab`): for every
             constructor the type class of its result, whether it needs the loop context (a premise `l = true`),
             whether it is a foreign body, and per child its family, the type class an expression child must have and
             the loop context of a statement child. A changed constructor stops the build here until `kTab` follows.
-/
import Lean
import Grammatik.Gen.Fein.Universum

namespace Gabbro.Grammatik.Gen.Fein

open Lean Meta

/-- The families, numbered as in `Gen/Fein/Zellen.lean`. -/
def familienF : List Name := [``Gabbro.Grammatik.Expr, ``Gabbro.Grammatik.NutzlastExpr, ``Gabbro.Grammatik.Args,
  ``Gabbro.Grammatik.ErgExpr, ``Gabbro.Grammatik.Stmt, ``Gabbro.Grammatik.Block, ``Gabbro.Grammatik.Endblock,
  ``Gabbro.Grammatik.Arms, ``Gabbro.Grammatik.GrundArms]

/-- The constructors of `Ty` in the order of `Ty.kopf`. -/
def koepfeF : List Name := [``Ty.int, ``Ty.bool, ``Ty.opt, ``Ty.sum, ``Ty.why, ``Ty.never, ``Ty.fl, ``Ty.fnptr,
  ``Ty.ptr]

/-- The type class of a type expression (`none`: not a constructor application, any class). -/
def kopfVon (t : Lean.Expr) : MetaM (Option Nat) := do
  let t ← whnfD (← whnfR t)
  match t.getAppFn.constName? with
  | some n => return if koepfeF.contains n then some (koepfeF.idxOf n) else none
  | none => return none

/-- The fixed loop context of a statement-family type (`none`: a variable). -/
def lVon (t : Lean.Expr) : MetaM (Option Bool) := do
  let a := t.getAppArgs
  if a.size > 2 then
    let x ← whnfR a[2]!
    if x.isConstOf ``Bool.true then return some true
    if x.isConstOf ``Bool.false then return some false
  return none

/-- One row, read off the environment. -/
def zeileVon (fam : Nat) (c : Name) : MetaM Zeile := do
  let info ← getConstInfoCtor c
  forallTelescope info.type fun args res => do
    let erg ← if fam = 0 then kopfVon res.getAppArgs.back! else pure none
    let mut kinder : List (Nat × Option Nat × Option Bool) := []
    let mut lnoetig := false
    for a in args do
      let ty ← inferType a
      match ty.getAppFn.constName? with
      | some n =>
        if familienF.contains n then
          let i := familienF.idxOf n
          if i = 0 then kinder := kinder ++ [(0, ← kopfVon ty.getAppArgs.back!, none)]
          else if i ≥ 4 then kinder := kinder ++ [(i, none, ← lVon ty)]
          else kinder := kinder ++ [(i, none, none)]
        else if n == ``Eq then
          let ea := ty.getAppArgs
          let ra := res.getAppArgs
          if ea.size == 3 && ra.size > 2 && (← whnfR ea[2]!).isConstOf ``Bool.true && ea[1]! == ra[2]! then
            lnoetig := true
      | none => pure ()
    let fremd ← args.anyM fun a => do return (← inferType a).getAppFn.constName? == some ``Deklaration.Ax
    return ⟨erg, lnoetig, fremd, kinder⟩

/-- Compare `kTab` with the model. -/
def pruefeKTab : MetaM Unit := do
  let mut ist : List (List Zeile) := []
  for (f, i) in familienF.zipIdx do
    let iv ← getConstInfoInduct f
    let mut zs : List Zeile := []
    for c in iv.ctors do
      zs := zs ++ [← zeileVon i c]
    ist := ist ++ [zs]
  if ist != kTab then
    throwError m!"Gen/Fein/Universum.lean: kTab is out of date; the model reads\n{repr ist}"

run_meta pruefeKTab

end Gabbro.Grammatik.Gen.Fein
