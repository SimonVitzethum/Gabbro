module
public import Bruecke.Kette.Pflichten
@[expose] public section

/-!
# Named refusals of the generated duty file

The template generator (`Bruecke/Vorlage.lean`) states every duty over the computed readers.
When a reader or a unit check refuses, the generated file says WHICH statement forms or WHICH
checks are outside the bridge, so that the refusal is a named one. These functions only produce
diagnostics: they occur in no statement and in no proof.
-/

namespace Gabbro.Bruecke.Vorlage

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The source name of a statement form (its constructor). -/
def formName : UStmt → String
  | .assign .. => "assign"
  | .assignTab .. => "assignTab"
  | .assignB .. => "assignB"
  | .assignTabB .. => "assignTabB"
  | .assignGlob .. => "assignGlob"
  | .assignGlobB .. => "assignGlobB"
  | .storeAtom .. => "storeAtom"
  | .storeAtomB .. => "storeAtomB"
  | .call .. => "call"
  | .lockBeg .. => "lockBeg"
  | .blkEnd .. => "blkEnd"
  | .bind .. => "bind"
  | .bindB .. => "bindB"
  | .bindMut .. => "bindMut"
  | .setVar .. => "setVar"
  | .bindOpt .. => "bindOpt"
  | .assignOpt .. => "assignOpt"
  | .assignTabOpt .. => "assignTabOpt"
  | .matchBeg .. => "matchBeg"
  | .startS .. => "startS"
  | .allocBeg .. => "allocBeg"
  | .allocReqBeg .. => "allocReqBeg"
  | .bindSum .. => "bindSum"
  | .matchTagBeg .. => "matchTagBeg"
  | .bindElse .. => "bindElse"
  | .matchWhyBeg .. => "matchWhyBeg"
  | .bindAxElse .. => "bindAxElse"
  | .bindCall .. => "bindCall"
  | .axCall .. => "axCall"
  | .bindAx .. => "bindAx"
  | .retryBeg .. => "retryBeg"
  | .foreverBeg .. => "foreverBeg"
  | .narrowBeg .. => "narrowBeg"
  | .setVarB .. => "setVarB"
  | .ifBeg .. => "ifBeg"
  | .ifElse .. => "ifElse"
  | .loopBeg .. => "loopBeg"
  | .ret .. => "ret"
  | .leave .. => "leave"
  | .next .. => "next"
  | .regRead .. => "regRead"
  | .regReadElse .. => "regReadElse"
  | .regWrite .. => "regWrite"
  | .regWriteB .. => "regWriteB"
  | .shiftTab .. => "shiftTab"
  | .bindFnref .. => "bindFnref"
  | .callInd .. => "callInd"
  | .bindCallInd .. => "bindCallInd"
  | .awaitBind .. => "awaitBind"
  | .assignRef .. => "assignRef"
  | .bindW .. => "bindW"
  | .assignGlobO .. => "assignGlobO"
  | .tausch .. => "tausch"
  | .ifEnde .. => "ifEnde"
  | .arrayLoopBeg .. => "arrayLoopBeg"
  | .resetRange .. => "resetRange"
  | .bindOptBeg .. => "bindOptBeg"
  | .bindOptElseBeg .. => "bindOptElseBeg"
  | .floatLit .. => "floatLit"
  | .float .. => "float"
  | .narrowReqBeg .. => "narrowReqBeg"
  | .axCallElseBeg .. => "axCallElseBeg"
  | .retires .. => "retires"
  | .callIndElseBeg .. => "callIndElseBeg"
  | .retireMark .. => "retireMark"
  | .breakingBeg .. => "breakingBeg"
  | .consumeLoopBeg .. => "consumeLoopBeg"
  | .floatOf .. => "floatOf"
  | .advances .. => "advances"
  | .bindCallIndElse .. => "bindCallIndElse"
  | .setVarOpt .. => "setVarOpt"
  | .setVarSum .. => "setVarSum"

/-- The statement forms the body readers (`seqZ`, `stmtsBodyZ`, `schrittB`, `stmtBody`) read
    at all. A form in this list can still be refused for its arguments. -/
def getragenB : UStmt → Bool
  | .assign .. => true
  | .assignTab .. => true
  | .assignOpt .. => true
  | .assignTabOpt .. => true
  | .assignGlob .. => true
  | .assignGlobB .. => true
  | .call .. => true
  | .bind .. => true
  | .bindMut .. => true
  | .bindB .. => true
  | .bindOpt .. => true
  | .setVarOpt .. => true
  | .bindCall .. => true
  | .setVarB .. => true
  | .setVar .. => true
  | .ifBeg .. => true
  | .ifEnde .. => true
  | .ifElse .. => true
  | .blkEnd .. => true
  | .matchTagBeg .. => true
  | .matchWhyBeg .. => true
  | .matchBeg .. => true
  | .loopBeg .. => true
  | .narrowBeg .. => true
  | .leave .. => true
  | .next .. => true
  | .ret .. => true
  | .bindW .. => true
  | _ => false

/-- The statement forms of a body that no body reader reads, each named once. -/
def fremdeFormen (f : UFn) : List String :=
  ((f.body.filter (fun s => !getragenB s)).map formName).eraseDups

/-- Why the body of `f` has no Body reading: the forms outside the bridge, or an argument
    (expression, loop invariant, return kind) of a read form. -/
def koerperAblehnung (f : UFn) : String :=
  match fremdeFormen f with
  | [] => "a read statement form has an argument outside the fragment " ++
      "(an expression, a loop invariant other than `true`, or a return kind)"
  | fs => "statement forms outside the bridge: " ++ String.intercalate ", " fs

/-- The largest traversal the generator reads: the Body model lists a traversal's indices explicitly
    (`forEach`), so a traversal over a huge table would be materialised. -/
def schleifenGrenze : Int := 65536

/-- A traversal of `f` over a table with more slots than `schleifenGrenze`, named. -/
def grosseSchleife (u : UProg) (f : UFn) : Option String :=
  f.body.findSome? fun s =>
    match s with
    | .loopBeg _ tab _ =>
      match u.tabs.find? (·.name == tab) with
      | some t => if t.count > schleifenGrenze then
          some ("traversal over table `" ++ tab ++ "` with " ++ toString t.count ++
            " slots: the Body model lists a traversal's indices explicitly; more than " ++
            toString schleifenGrenze ++ " are not read")
        else none
      | none => none
    | _ => none

/-- The function conditions of `stimmigB` that fail for `f`, by name. -/
def fnAblehnungen (u : UProg) (f : UFn) : List String :=
  [("parameter kinds (artB)", artB f), ("parameter names unique (namenB)", namenB f),
   ("parameter names free (freiB)", freiB f), ("at most nine old values (oldsB)", oldsB u f),
   ("postconditions in the fragment (postB)", postB u f),
   ("written places declared (schreibtB)", schreibtB u f),
   ("no requires beside Held", f.needs.isEmpty),
   ("result type represented", resultTypeB f && f.resSum.isNone && f.resWhy.isNone)].filterMap
    fun p => if p.2 then none else some p.1

/-- The unit conditions of `stimmigB` that fail, by name, with the failing functions. -/
def stimmigAblehnungen (u : UProg) : List String :=
  ([("no bool or record table fields", u.tabs.all (fun t => t.bools.isEmpty && t.werte.isEmpty)),
    ("tables (tabB)", tabB u), ("no declared invariants", u.invs.isEmpty),
    ("only integer and bool statics, none atomic (staticsB)", staticsB u)].filterMap
    fun p => if p.2 then none else some p.1) ++
  u.fns.filterMap fun f =>
    match fnAblehnungen u f with
    | [] => none
    | xs => some (f.name ++ ": " ++ String.intercalate ", " xs)

end Gabbro.Bruecke.Vorlage
