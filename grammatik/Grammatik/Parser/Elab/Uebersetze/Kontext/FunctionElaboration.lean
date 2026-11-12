module
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Profil.Eintritt
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
public import Grammatik.Parser.Elab.Uebersetze.Folds.SpecArguments
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Initializers
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000
/-- The contract clauses with every `spec fn` inlined: `refines g` is `ensures g(params)` (`M131`/`M132`),
    `maintains` documents (the owed invariants are derived from `effects`), `by induction over` names a scheme
    and carries no term. Without `spec fn`s the clauses stay as they are. -/
def uSpecKlauseln (ctx : UCtx) (params : List String) (ks : List SKlausel) : Except String (List SKlausel) :=
  let ein := uSpecEin ctx.specs 1000
  ks.foldr (fun k acc => match acc with
    | .error e => .error e
    | .ok r =>
      match k with
      | .needs e => do
        uSpecArgs 1000 ctx e
        pure (.needs (ein e) :: r)
      | .gives e => do
        uSpecArgs 1000 ctx e
        pure (.gives (ein e) :: r)
      | .refs [g] =>
        match ctx.specs.find? (fun p => strEq p.1 g) with
        | some (_, ps, _) =>
          if ps.length == params.length then do
            let call := SExpr.call g (params.map .variable)
            uSpecArgs 1000 ctx call
            pure (.gives (ein call) :: r)
          else .error "refines a spec fn of another arity"
        | none => .error ("refines unknown spec fn " ++ g)
      | .refs _ => .error "refines without one spec fn"
      | .keeps _ | .induc _ => .ok r
      | k => .ok (k :: r)) (.ok [])
/-- The contracts of one head: `gives` (with `refines` inlined) and `needs`
    beside `Held(..)` (which rides `kopf.held`, never a predicate). Shared by
    functions (`elabFn`) and pointer types (`elabZeigerTyp`, C06): the two
    lists are the normalised predicate lists the conformance check compares. -/
def elabKlauseln (ctx : UCtx) (klauseln0 : List SKlausel) :
    Except String (List UEns × List UEns) :=
  match (if ctx.specs.isEmpty then .ok klauseln0 else uSpecKlauseln ctx ctx.names klauseln0) with
  | .error e => .error e
  | .ok klauseln =>
  match uSeq ((klauseln.filterMap (fun
    | .gives e => some (uSichert ctx e)
    | _ => none))) with
  | .error e => .error e
  | .ok gives =>
    match uSeq ((klauseln.filterMap (fun
      | .needs (.call "Held" _) => none
      | .needs e => some (uBool ctx e)
      | _ => none))) with
    | .error e => .error e
    | .ok needs => .ok (gives, needs)
/-- Pass two: contracts and body of one function. -/
def elabFn (ctx : UCtx) (koepfe : List UFnKopf) (klauseln0 : List SKlausel)
    (koerper : SAnw) : Except String (List UEns × List UEns × List UStmt × URet) :=
  match elabKlauseln ctx klauseln0 with
  | .error e => .error e
  | .ok (gives, needs) =>
    match koerper with
    | .block ss ende =>
      match uAnwReihe ctx.tabs koepfe 1000000 ctx ss with
      | .error e => .error e
      | .ok (body, ctxE) =>
        match expandFoldEnd ctxE ende with
        | .error e => .error e
        | .ok (beforeEnd, ctxEnd, ending) =>
        match expandReturnCall ctxEnd koepfe ending with
        | .error e => .error e
        | .ok (beforeCall, ctxReturn, returning) =>
        match uEnde ctxReturn returning with
        | .error e =>
          if returning.isNone && (match ss.getLast? with | some s => uEndetTief 64 s | none => false) then
            .ok (gives, needs, body, .keins)
          else .error e
        | .ok r => .ok (gives, needs, body ++ beforeEnd ++ beforeCall, r)
    | _ => .error "fn body without G form"
/-- The context of a function from its head. -/
def uCtxVon (alias : List (String × (Int × Int))) (lits : List (String × Int))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (kopf : UFnKopf)
    (fname : String) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (regs : List UReg := []) (zustaende : List UZustand := [])
    (specs : List (String × List String × SExpr) := []) (arrKonst : List (String × USide) := [])
    (specTypen : List (String × List STyp) := []) : UCtx :=
  { names := kopf.names, kinds := kopf.kinds, types := kopf.types, tabs := tabs, locks := locks, held := kopf.held, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, fname, bits := kopf.bits, alias, lits, globs, annahmen, whys, kanal := kopf.kanal, sums, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, regs, griffe := kopf.griffe.map (·.2), zustaende, specs, arrKonst, specTypen }
/-- One whole function: head (pass one) plus contracts and
    body (pass two). -/
def elabUFunktion (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (devs : List String := []) (regs : List UReg := []) (zustaende : List UZustand := [])
    (zeiger : List String := []) (zb : Nat := 0) (specs : List (String × List String × SExpr) := [])
    (arrKonst : List (String × USide) := []) (spaces : List String := []) (valueScope : UTypeScope := { types := [] }) (eigner : List String := [])
    (specTypen : List (String × List STyp) := []) :
    Except String UFn :=
  match elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb spaces valueScope.types eigner with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx := { uCtxVon alias consts tabs locks globs kopf sig.name annahmen whys sums regs zustaende specs arrKonst specTypen with zeiger := zeiger, zeigerBasis := zb, spaces := spaces, records := valueScope.records, namedTypes := valueScope.types, eigner := eigner }
    match elabFn ctx koepfe sig.klauseln koerper with
    | .error e => .error e
    | .ok (gives, needs, body, r) =>
      match uMeasureClause alias sig.klauseln with
      | .error e => .error e
      | .ok decreases =>
        .ok { name := sig.name, params := kopf.names.zip kopf.types, kinds := kopf.kinds, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, gruende := (kopf.kanal.map (·.2)).getD 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, nimmt := kopf.nimmt, gibt := kopf.gibt, leiht := kopf.leiht, bewegt := kopf.bewegt, praegt := kopf.praegt, gives, needs, body, ret := r, decreases, measureConstants := if decreases.isSome then consts else [], measureTypes := if decreases.isSome then alias else [] }

/-- The payload of an `atomic` item: statics named bare (a table payload, `T.slots`, has no form: `D.nutzlast`
    lists statics). -/
def uNutzItem : List SExpr → Except String (List String)
  | [] => .ok []
  | .variable g :: rest =>
    match uNutzItem rest with
    | .error e => .error e
    | .ok gs => .ok (g :: gs)
  | _ :: _ => .error "payload of a table without G form"
/-- The statics of a tagged type with their type, read once the `tagged type`s are known. -/
def uSumGlobs (consts : List (String × Int)) (sums : List USum) (ms : List SItemTief) :
    List UGlob → Except String (List UGlob)
  | [] => .ok []
  | g :: rest =>
    match uSumGlobs consts sums ms rest, g.sumName with
    | .error e, _ => .error e
    | .ok gs, none => .ok (g :: gs)
    | .ok gs, some a =>
      match sums.findIdx? (fun sm => strEq sm.name a), sums.find? (fun sm => strEq sm.name a) with
      | some k, some sm =>
        match ms.findSome? (fun m => match m with | .globT _ n _ v .. => if strEq n g.name then some v else none | _ => none) with
        | some v =>
          match uSumKonst consts sums sm v with
          | .ok kv => .ok ({ g with ty := .wert (.sum sm.spec), initK := kv, sumNum := some k } :: gs)
          | .error e => .error e
        | none => .error ("static unknown: " ++ g.name)
      | _, _ => .error ("type unknown: " ++ a)
/-- The tables with their fields of a tagged type typed (`werte`) and numbered (`sumFelder`). -/
def uSumTabs (sums : List USum) : List UTab → Except String (List UTab)
  | [] => .ok []
  | t :: rest =>
    match uSumTabs sums rest,
        uSeq (t.sumNamen.map fun (f, a) =>
          match sums.findIdx? (fun sm => strEq sm.name a), sums.find? (fun sm => strEq sm.name a) with
          | some k, some sm => .ok (f, k, sm.spec)
          | _, _ => .error ("type unknown: " ++ a)) with
    | .ok ts, .ok fs =>
      .ok ({ t with werte := t.werte ++ fs.map (fun (f, _, sp) => (f, Ty.sum sp)), sumFelder := fs.map (fun (f, k, _) => (f, k)) } :: ts)
    | .error e, _ | _, .error e => .error e
/-- The range of a column: an `index into T` field reads `0 .. count T - 1`. -/
def uIdxSpalte (tabs : List UTab) (t : UTab) (c : String × (Int × Int)) : String × (Int × Int) :=
  match t.idxNamen.find? (fun p => strEq p.1 c.1) with
  | some (_, tn) =>
    match tabs.find? (fun x => strEq x.name tn) with
    | some x => (c.1, (0, x.count - 1))
    | none => c
  | none => c
/-- The `index into T` fields with their range `0 .. count T - 1`. -/
def uIdxTabs (tabs : List UTab) : List UTab :=
  tabs.map fun t => { t with cols := t.cols.map (uIdxSpalte tabs t) }
/-- The option statics with the number and count of their table. -/
def uOptGlobs (tabs : List UTab) : List UGlob → Except String (List UGlob)
  | [] => .ok []
  | g :: rest =>
    match uOptGlobs tabs rest, g.optName with
    | .error e, _ => .error e
    | .ok gs, none => .ok (g :: gs)
    | .ok gs, some tn =>
      match uTabNr tabs tn with
      | .ok (num, c) => .ok ({ g with ty := .wert (.opt c), optNum := some num } :: gs)
      | .error e => .error e
/-- Scalar initializers keep their declared range at every constant-evaluator intermediate.
    Existing literal/constant encodings retain their canonical admission; new expressions are checked. -/
def uInitialNumber (consts : List (String × Int)) (lo hi : Int) : SKonstWert → Except String Int
  | .one (.lit k) => .ok (Int.ofNat k)
  | .one (.un "-" (.lit k)) => .ok (-(Int.ofNat k))
  | .one (.variable name) => uSuch "const" consts name
  | .one expression =>
      match uKonstWert lo hi [] consts 64 expression with
      | some value => .ok value
      | none => .error "source export: scalar initializer is outside its canonical constant domain"
  | .rows _ => .error "static initialiser without G form"

end Gabbro.Grammatik.Parser.Uebersetze
