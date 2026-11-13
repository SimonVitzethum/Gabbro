module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.FunctionElaboration
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- Install the unit's shared head table and the function's initial local stacks. -/
def elabFnMemo (memo : Merk UHeadMemo) (ctx : UCtx) (heads : List UFnKopf)
    (clauses : List SKlausel) (body : SAnw) :
    Except String (List UEns × List UEns × List UStmt × URet) :=
  elabFn {ctx with lookupMemo := ULookupMemo.von ctx.names ctx.kinds ctx.types memo} heads clauses body

theorem elabFnMemo_eq (memo : Merk UHeadMemo) (ctx : UCtx) (heads : List UFnKopf)
    (clauses : List SKlausel) (body : SAnw) :
    elabFnMemo memo ctx heads clauses body = elabFn ctx heads clauses body := by
  rw [elabFnMemo, UCtx.memo_eq]

def elabUFunktionMemo (memo : Merk UHeadMemo) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (devs : List String := []) (regs : List UReg := []) (zustaende : List UZustand := [])
    (zeiger : List String := []) (zb : Nat := 0) (specs : List (String × List String × SExpr) := [])
    (arrKonst : List (String × USide) := []) (spaces : List String := []) (valueScope : UTypeScope := { types := [] }) (eigner : List String := [])
    (specTypen : List (String × List STyp) := []) (narrow : Bool := false) :
    Except String UFn :=
  match elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb spaces valueScope.types eigner with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx : UCtx :=
      { uCtxVon alias consts tabs locks globs kopf sig.name annahmen whys sums regs zustaende specs arrKonst specTypen with
        zeiger := zeiger
        zeigerBasis := zb
        spaces := spaces
        records := valueScope.records
        namedTypes := valueScope.types
        eigner := eigner
        narrow := narrow }
    match elabFnMemo memo ctx koepfe sig.klauseln koerper with
    | .error e => .error e
    | .ok (gives, needs, body, r) =>
      match uMeasureClause alias sig.klauseln with
      | .error e => .error e
      | .ok decreases =>
        .ok
          { name := sig.name
            params := kopf.names.zip kopf.types
            kinds := kopf.kinds
            res := kopf.res
            resBool := kopf.resBool
            resOpt := kopf.resOpt
            resSum := kopf.resSum
            resWhy := kopf.resWhy
            resTy := kopf.resTy
            gruende := (kopf.kanal.map (·.2)).getD 0
            held := kopf.held
            puts := schreibt
            gputs := kopf.gputs
            nimmt := kopf.nimmt
            gibt := kopf.gibt
            leiht := kopf.leiht
            bewegt := kopf.bewegt
            praegt := kopf.praegt
            gives := gives
            needs := needs
            body := body
            ret := r
            decreases := decreases
            measureConstants := if decreases.isSome then consts else []
            measureTypes := if decreases.isSome then alias else [] }

theorem elabUFunktionMemo_eq (memo : Merk UHeadMemo) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String) (whys : List UWhy) (sums : List USum)
    (devs : List String) (regs : List UReg) (zustaende : List UZustand)
    (zeiger : List String) (zb : Nat) (specs : List (String × List String × SExpr))
    (arrKonst : List (String × USide)) (spaces : List String) (valueScope : UTypeScope) (eigner : List String)
    (specTypen : List (String × List STyp)) (narrow : Bool) :
    elabUFunktionMemo memo consts alias tabs locks globs koepfe sig koerper annahmen whys sums devs regs zustaende zeiger zb specs arrKonst spaces valueScope eigner specTypen narrow = elabUFunktion consts alias tabs locks globs koepfe sig koerper annahmen whys sums devs regs zustaende zeiger zb specs arrKonst spaces valueScope eigner specTypen narrow := by
  unfold elabUFunktionMemo elabUFunktion
  simp only [elabFnMemo_eq] <;> rfl

end Gabbro.Grammatik.Parser.Uebersetze
