module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil10

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
      | .needs e => .ok (.needs (ein e) :: r)
      | .gives e => .ok (.gives (ein e) :: r)
      | .refs [g] =>
        match ctx.specs.find? (fun p => strEq p.1 g) with
        | some (_, ps, _) =>
          if ps.length == params.length then .ok (.gives (ein (.call g (params.map .variable))) :: r)
          else .error "refines a spec fn of another arity"
        | none => .error ("refines unknown spec fn " ++ g)
      | .refs _ => .error "refines without one spec fn"
      | .keeps _ | .induc _ => .ok r
      | k => .ok (k :: r)) (.ok [])

/-- Pass two: contracts and body of one function. -/
def elabFn (ctx : UCtx) (koepfe : List UFnKopf) (klauseln0 : List SKlausel)
    (koerper : SAnw) : Except String (List UEns × List UEns × List UStmt × URet) :=
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
    | .ok needs =>
    match koerper with
    | .block ss ende =>
      match uAnwReihe ctx.tabs koepfe 1000000 ctx ss with
      | .error e => .error e
      | .ok (body, ctxE) =>
        match uEnde ctxE ende with
        | .error e =>
          if ende.isNone && (match ss.getLast? with | some s => uEndetTief 64 s | none => false) then
            .ok (gives, needs, body, .keins)
          else .error e
        | .ok r => .ok (gives, needs, body, r)
    | _ => .error "fn body without G form"

/-- The context of a function from its head. -/
def uCtxVon (alias : List (String × (Int × Int))) (lits : List (String × Int))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (kopf : UFnKopf)
    (fname : String) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (regs : List UReg := []) (zustaende : List UZustand := [])
    (specs : List (String × List String × SExpr) := []) (arrKonst : List (String × USide) := []) : UCtx :=
  { names := kopf.names, kinds := kopf.kinds, types := kopf.types, tabs := tabs, locks := locks, held := kopf.held, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt,
    fname, bits := kopf.bits, alias, lits, globs, annahmen, whys, kanal := kopf.kanal, sums,
    resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, regs, griffe := kopf.griffe.map (·.2),
    zustaende, specs, arrKonst }

/-- One whole function: head (pass one) plus contracts and
    body (pass two). -/
def elabUFunktion (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (devs : List String := []) (regs : List UReg := []) (zustaende : List UZustand := [])
    (zeiger : List String := []) (zb : Nat := 0) (specs : List (String × List String × SExpr) := [])
    (arrKonst : List (String × USide) := []) :
    Except String UFn :=
  match elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx := { uCtxVon alias consts tabs locks globs kopf sig.name annahmen whys sums regs zustaende specs arrKonst with
                 zeiger := zeiger, zeigerBasis := zb }
    match elabFn ctx koepfe sig.klauseln koerper with
    | .error e => .error e
    | .ok (gives, needs, body, r) =>
      match uMeasureClause sig.klauseln with
      | .error e => .error e
      | .ok decreases =>
        .ok { name := sig.name, params := kopf.names.zip kopf.types, kinds := kopf.kinds, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, gruende := (kopf.kanal.map (·.2)).getD 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, gives, needs, body, ret := r,
              decreases, measureConstants := if decreases.isSome then consts else [] }

/-- The payload of an `atomic` item: statics named bare (a table payload, `T.slots`, has no form: `D.nutzlast`
    lists statics). -/
def uNutzItem : List SExpr → Except String (List String)
  | [] => .ok []
  | .variable g :: rest =>
    match uNutzItem rest with
    | .error e => .error e
    | .ok gs => .ok (g :: gs)
  | _ :: _ => .error "payload of a table without G form"

mutual
/-- The initial value of a static of a tagged type: a payload-free case, or a case with a numeral payload. -/
def uSumKonst (consts : List (String × Int)) (sm : USum) : SKonstWert → Except String UKonst
  | .one (.variable c) =>
    match sm.cases.findIdx? (fun x => strEq x.1 c) with
    | some i => .ok (.fall i .null)
    | none => .error ("case unknown: " ++ c)
  | .one (.call c [e]) =>
    match sm.cases.findIdx? (fun x => strEq x.1 c), (sm.cases.find? (fun x => strEq x.1 c)).bind (·.2) with
    | some i, some (lo, hi) =>
      match uKonstWert lo hi [] consts 64 e with
      | some z => .ok (.fall i (.zahl z))
      | none => .error "static initialiser without G form"
    | _, _ => .error "static initialiser without G form"
  | _ => .error "static initialiser without G form"

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
          match uSumKonst consts sm v with
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

/-- The initial value of an aggregate static: `0` is zero memory, a numeral or constant a number, a string literal
    its bytes, a row literal its elements. -/
def uKonst (consts : List (String × Int)) : SKonstWert → Except String UKonst
  | .one (.lit 0) => .ok .null
  | .one (.call "None" []) => .ok .null
  | .one (.lit k) => .ok (.zahl (Int.ofNat k))
  | .one (.un "-" (.lit k)) => .ok (.zahl (-(Int.ofNat k)))
  | .one .tru => .ok (.wahr true)
  | .one .fls => .ok (.wahr false)
  | .one (.variable c) =>
    match uSuch "const" consts c with
    | .error e => .error e
    | .ok z => .ok (.zahl z)
  | .one (.ext .text [t] []) => .ok (.text (t.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
  | .one _ => .error "static initialiser without G form"
  | .rows ks => uKonstReihe consts ks
def uKonstReihe (consts : List (String × Int)) : List SKonstWert → Except String UKonst
  | [] => .ok .nil
  | k :: ks =>
    match uKonst consts k, uKonstReihe consts ks with
    | .ok a, .ok r => .ok (.cons a r)
    | .error e, _ | _, .error e => .error e
end

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

/-- The statics of the unit: ONE value each, an integer range or `bool`, with a numeral (or `true`/`false`)
    as the initial value; a placement, an alignment or a `shared` word has no `Glob` form. -/
def uGlobs (consts : List (String × Int)) (alias : List (String × (Int × Int))) :
    List SItemTief → Except String (List UGlob)
  | [] => .ok []
  | .globT m n t v al sec sh :: rest =>
    if al.isSome || sec.isSome then .error "static placement without G form"
    else
      match (match t with
          | .atom "bool" =>
            match v with
            | .one .tru => .ok (GTy.bool, (1 : Int))
            | .one .fls => .ok (GTy.bool, (0 : Int))
            | _ => .error "static initialiser without G form"
          | .array _ _ | .str _ =>
            match uTyp alias [] t with
            | .error e => .error e
            | .ok τ => .ok (GTy.wert τ, (0 : Int))
          -- the count of `T` is read with the tables (`uOptGlobs`)
          | .index true _ => .ok (GTy.wert (.opt 0), (0 : Int))
          -- a name that is no integer type may be a tagged type, read with the types (`uSumGlobs`)
          | .atom a =>
            match uErgBereich alias (.atom a) with
            | .error _ => .ok (GTy.wert (.sum []), (0 : Int))
            | .ok (lo, hi) =>
              match uInitialNumber consts lo hi v with
              | .error e => .error e
              | .ok z =>
                if lo ≤ z ∧ z ≤ hi then .ok (GTy.int lo hi, z)
                else .error "static initialiser outside its range"
          | _ =>
            match uErgBereich alias t with
            | .error e => .error e
            | .ok (lo, hi) =>
              match uInitialNumber consts lo hi v with
              | .error e => .error e
              | .ok z =>
                if lo ≤ z ∧ z ≤ hi then .ok (GTy.int lo hi, z)
                else .error "static initialiser outside its range" : Except String (GTy × Int)) with
      | .error e => .error e
      | .ok (ty, z) =>
        match (match ty, t with
            | .wert (.sum _), _ => .ok .null
            | .wert _, _ => uKonst consts v
            | _, _ => .ok .null : Except String UKonst) with
        | .error e => .error e
        | .ok k =>
        match uGlobs consts alias rest with
        | .error e => .error e
        | .ok gs => .ok ({ name := n, ty, init := z, initK := k, var := m, shared := sh, optName := match t with | .index true tn => some tn | _ => none, sumName := match ty, t with | .wert (.sum _), .atom a => some a | _, _ => none, breite := match ty with | .int _ _ => uSpeicherBreite alias t | _ => 0 } :: gs)
  | .atomT n t pub _ obs :: rest =>
    if obs.isSome then .error "atomic observed by a device without G form"
    else
      match uNutzItem (pub.getD []) with
      | .error e => .error e
      | .ok nl =>
        match (match t with
            | .atom "bool" => .ok GTy.bool
            | _ =>
              match uErgBereich alias t with
              | .error e => .error e
              | .ok (lo, hi) =>
                if lo ≤ 0 ∧ 0 ≤ hi then .ok (GTy.int lo hi)
                else .error "atomic starts at zero outside its range" : Except String GTy) with
        | .error e => .error e
        | .ok ty =>
          match uGlobs consts alias rest with
          | .error e => .error e
          | .ok gs => .ok ({ name := n, ty, init := 0, var := true, atomic := true, shared := true, nutzlast := nl, breite := match ty with | .int _ _ => uSpeicherBreite alias t | _ => 0 } :: gs)
  | _ :: rest => uGlobs consts alias rest

/-- The arenas of a unit as the PAIR the specification names (`ArenaZucker`): a table of `hi` slots with the one
    field `wert`, and the counter static `A#used` over `0 .. hi` starting at zero. A dynamic ceiling and a
    placement have no form here. -/
def uArenen (consts : List (String × Int)) (alias : List (String × (Int × Int))) :
    List SItemTief → Except String (List UTab × List UGlob)
  | [] => .ok ([], [])
  | .arenaT n _ hi mx t pb :: rest =>
    match mx, pb with
    | .some _, _ => .error "arena with a dynamic ceiling without G form"
    | _, .some _ => .error "arena placement without G form"
    | .none, .none =>
      match uAnzahl consts hi with
      | .error e => .error e
      | .ok h =>
        match uFeldTyp alias t with
        | .error e => .error e
        | .ok r =>
          match uArenen consts alias rest with
          | .error e => .error e
          | .ok (ts, gs) =>
            if 0 < h then
              .ok ({ name := n, count := h, cols := [("wert", r)], arena := true, breiten := (let w := uSpeicherBreite alias t; if 0 < w then [("wert", w)] else []) } :: ts,
                   { name := n ++ "#used", ty := GTy.int 0 h, init := 0, var := true } :: gs)
            else .error "arena of no slots"
  | _ :: rest => uArenen consts alias rest

/-- Items outside the fragment: everything but constants,
    type aliases, statics, tables, locks and functions is an explicit
    error (the refused rows of `collect`). -/
def uRestFehler : List SItemTief → Except String Unit
  | [] => .ok ()
  | .constT _ _ _ :: rest => uRestFehler rest
  | .typeT _ _ _ _ _ :: rest => uRestFehler rest
  | .tableT _ _ _ _ _ _ _ :: rest => uRestFehler rest
  | .lockT _ _ _ _ _ _ _ :: rest => uRestFehler rest
  | .globT .. :: rest => uRestFehler rest
  | .atomT .. :: rest => uRestFehler rest
  | .arenaT .. :: rest => uRestFehler rest
  | .protoT .. :: rest => uRestFehler rest
  | .assumT .. :: rest => uRestFehler rest
  | .whyT .. :: rest => uRestFehler rest
  | .callT .. :: rest => uRestFehler rest
  | .varT .. :: rest => uRestFehler rest
  | .goalT .. :: rest => uRestFehler rest
  | .fnT _ _ :: rest => uRestFehler rest
  | .entryT _ :: rest => uRestFehler rest
  | .concT _ :: rest => uRestFehler rest
  | .devT .. :: rest => uRestFehler rest
  | .groupT .. :: rest => uRestFehler rest
  | .stateT .. :: rest => uRestFehler rest
  | .specT .. :: rest => uRestFehler rest
  | .asmT .. :: rest => uRestFehler rest
  -- `axiom f(..) effects { .. } falsifier p;`: a foreign body under a named hardware assumption; a `requires` has no
  -- G form yet (the model's foreign bodies carry no caller duty)
  | .axiomT _ _ _ .none _ _ :: rest => uRestFehler rest
  | _ :: _ => .error "item without G form"

/-- A start names one parameterless function of the unit (`check_starts` of `lean_g.rs`). -/
def uStart (fns : List UFn) (quelle d : String) : Except String String :=
  match fns.find? (fun f => strEq f.name d) with
  | .some f =>
    if f.params.isEmpty then .ok d
    else .error (quelle ++ " names a function with parameters: no start-argument form: " ++ d)
  | .none => .error (quelle ++ " names an unknown function: " ++ d)

/-- A start argument is a value of its parameter's type: a literal in the range, `true`/`false`, `None`. -/
def uStartArg (tabs : List UTab) : Ty → SExpr → Bool
  | .int lo hi, .lit n => decide (lo ≤ (n : Int) ∧ (n : Int) ≤ hi)
  | .int lo hi, .un "-" (.lit n) => decide (lo ≤ -(n : Int) ∧ -(n : Int) ≤ hi)
  | .bool, .tru => true
  | .bool, .fls => true
  | .opt _, .call "None" [] => true
  -- `&T` for a `ptr<…> T` parameter (`Expr.ptrOf`): the one pointer to the carrier the type names
  | .ptr n _, .fnref t => match tabs[n]? with
    | .some tb => strEq tb.name t
    | .none => false
  | _, _ => false

/-- A `concurrent` member: a function of the unit, started with one value per parameter
    (`concurrent { m::f(a, b) }`, the model's start with its arguments). -/
def uStartMit (tabs : List UTab) (fns : List UFn) (d : String) (args : List SExpr) : Except String String :=
  match fns.find? (fun f => strEq f.name d) with
  | .some f =>
    if f.params.length != args.length then
      .error ("concurrent member with " ++ toString args.length ++ " arguments for " ++
        toString f.params.length ++ " parameters: " ++ d)
    else if (f.params.zip args).all (fun (p, a) => uStartArg tabs p.2 a) then .ok d
    else .error ("concurrent member with an argument outside its parameter's type: " ++ d)
  | .none => .error ("concurrent member names an unknown function: " ++ d)

/-- The roots of the `concurrent` items, in order (their members come first, as in `check_starts`). -/
def uNebenWurzeln (tabs : List UTab) (fns : List UFn) : List SItemTief → Except String (List String)
  | [] => .ok []
  | .concT ps :: rest => do
    let here ← uSeq (ps.map fun (p, args) => match p.getLast? with
      | .some d => uStartMit tabs fns d args
      | .none => .error "empty path in concurrent")
    let more ← uNebenWurzeln tabs fns rest
    pure (here ++ more)
  | _ :: rest => uNebenWurzeln tabs fns rest

/-- The dispatch roots of the `entry` items: ONE dispatch target that names a parameterless function of
    the unit. Everything else about the entry (vector, registers, stack) is the
    hardware side and stays with the checker. -/
def uEingangsWurzeln (fns : List UFn) : List SItemTief → Except String (List String)
  | [] => .ok []
  | .entryT e :: rest =>
    match e.dispatch.getLast? with
    | .some d => do
      let w ← uStart fns "dispatch" d
      let ws ← uEingangsWurzeln fns rest
      pure (w :: ws)
    | .none => .error "entry without a dispatch: no G form"
  | _ :: rest => uEingangsWurzeln fns rest

/-- The handlers: the dispatch targets of the entries that carry a `via` word. -/
def uHandler : List SItemTief → List String
  | [] => []
  | .entryT e :: rest =>
    match e.via, e.dispatch.getLast? with
    | .some _, .some d => d :: uHandler rest
    | _, _ => uHandler rest
  | _ :: rest => uHandler rest

/-- The thread roots: `concurrent` members, then entry dispatch roots. -/
def uWurzeln (tabs : List UTab) (fns : List UFn) (ms : List SItemTief) : Except String (List String) := do
  let a ← uNebenWurzeln tabs fns ms
  let b ← uEingangsWurzeln fns ms
  pure (a ++ b)

/-- The clauses an `extern fn` may carry: `effects { pure | diverges | reads .. }` and `costs`; a `requires`,
    an `ensures` or a write has no form (`D.Ax` carries no contract here). -/
def uAxKlauseln (kopf : UFnKopf) (tabs : List UTab) (globs : List UGlob) :
    List SKlausel → Except String UFnKopf
  | [] => .ok kopf
  | .effs es :: rest =>
    if es.all (fun e => match e with | .pure => true | .loops => true | .reads _ => true | .writes _ => true | _ => false) then
      match uEffekteAux kopf tabs [] globs es with
      | .error e => .error e
      | .ok eff =>
        uAxKlauseln { kopf with puts := uEindeutig (kopf.puts ++ eff.puts), gputs := uEindeutig (kopf.gputs ++ eff.gputs) } tabs globs rest
    else .error "foreign fn effect without G form"
  | .cost _ :: rest => uAxKlauseln kopf tabs globs rest
  | .arch _ :: rest => uAxKlauseln kopf tabs globs rest
  -- `deadline <= n ops arch X falsifier p`: a named hardware outcome outside the goal (`Spec.lean`, NOT CLAIMED:
  -- time bounds), the same as at an implemented function
  | .limit _ :: rest => uAxKlauseln kopf tabs globs rest
  | _ :: _ => .error "foreign fn clause without G form"

end Gabbro.Grammatik.Parser.Uebersetze
