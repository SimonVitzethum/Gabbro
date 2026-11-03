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
public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
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
        | .ok (prefix, ctxE, ende) =>
        match uEnde ctxE ende with
        | .error e =>
          if ende.isNone && (match ss.getLast? with | some s => uEndetTief 64 s | none => false) then
            .ok (gives, needs, body, .keins)
          else .error e
        | .ok r => .ok (gives, needs, body ++ prefix, r)
    | _ => .error "fn body without G form"
/-- The context of a function from its head. -/
def uCtxVon (alias : List (String × (Int × Int))) (lits : List (String × Int))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (kopf : UFnKopf)
    (fname : String) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (regs : List UReg := []) (zustaende : List UZustand := [])
    (specs : List (String × List String × SExpr) := []) (arrKonst : List (String × USide) := []) : UCtx :=
  { names := kopf.names, kinds := kopf.kinds, types := kopf.types, tabs := tabs, locks := locks, held := kopf.held, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, fname, bits := kopf.bits, alias, lits, globs, annahmen, whys, kanal := kopf.kanal, sums, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, regs, griffe := kopf.griffe.map (·.2), zustaende, specs, arrKonst }
/-- One whole function: head (pass one) plus contracts and
    body (pass two). -/
def elabUFunktion (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) (annahmen : List String := []) (whys : List UWhy := []) (sums : List USum := [])
    (devs : List String := []) (regs : List UReg := []) (zustaende : List UZustand := [])
    (zeiger : List String := []) (zb : Nat := 0) (specs : List (String × List String × SExpr) := [])
    (arrKonst : List (String × USide) := []) (spaces : List String := []) (valueScope : UTypeScope := { types := [] }) (eigner : List String := []) :
    Except String UFn :=
  match elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb spaces valueScope.types eigner with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx := { uCtxVon alias consts tabs locks globs kopf sig.name annahmen whys sums regs zustaende specs arrKonst with zeiger := zeiger, zeigerBasis := zb, spaces := spaces, records := valueScope.records, namedTypes := valueScope.types, eigner := eigner }
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
mutual
/-- A tagged initializer checks payload presence, then uses the canonical typed
    constant reader for the complete selected value. -/
def uSumKonst (consts : List (String × Int)) (sums : List USum) (sm : USum) :
    SKonstWert → Except String UKonst
  | .one (.variable name) =>
    match sm.cases.findIdx? (fun c => strEq c.1 name), sm.cases.find? (fun c => strEq c.1 name) with
    | some i, some (_, none) => .ok (.fall i .null)
    | some _, some (_, some _) => .error "missing tagged payload in static initializer"
    | _, _ => .error ("case unknown: " ++ name)
  | .one (.call name [value]) =>
    match sm.cases.findIdx? (fun c => strEq c.1 name), (sm.cases.find? (fun c => strEq c.1 name)).bind (·.2) with
    | some i, some τ => (uKonst consts sums (some τ) (.one value)).map (.fall i)
    | _, _ => .error "missing or extra tagged payload in static initializer"
  | _ => .error "static initialiser without G form"
termination_by value => 2 * sizeOf value
decreasing_by all_goals simp_wf; omega
/-- Constants use their declared type throughout nested tagged and array values.
    The later value decoder still checks exact shape, ranges and string bounds. -/
def uKonst (consts : List (String × Int)) (sums : List USum) (expected : Option Ty) :
    SKonstWert → Except String UKonst
  | value =>
    match expected, value with
    | some (.sum cs), _ =>
      match sums.find? (fun sm => sm.spec = cs) with
      | some sm => uSumKonst consts sums sm value
      | none => .error "unknown tagged type in static initializer"
    | some (.int lo hi), .one e =>
      match uKonstWert lo hi [] consts 64 e with
      | some z => .ok (.zahl z)
      | none => .error "static initialiser outside its declared range"
    | _, .one (.lit 0) => .ok .null
    | _, .one (.call "None" []) => .ok .null
    | _, .one (.lit k) => .ok (.zahl (Int.ofNat k))
    | _, .one (.un "-" (.lit k)) => .ok (.zahl (-(Int.ofNat k)))
    | _, .one .tru => .ok (.wahr true)
    | _, .one .fls => .ok (.wahr false)
    | _, .one (.variable c) => (uSuch "const" consts c).map .zahl
    | _, .one (.ext .text [text] []) =>
      .ok (.text (text.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
    | some (.arr element _), .rows ks => uKonstReihe consts sums (some element) ks
    | _, .rows ks => uKonstReihe consts sums none ks
    | _, .one _ => .error "static initialiser without G form"
termination_by value => 2 * sizeOf value + 1
decreasing_by all_goals simp_wf; omega
/-- Read all array elements under their declared element type. -/
def uKonstReihe (consts : List (String × Int)) (sums : List USum) (element : Option Ty) :
    List SKonstWert → Except String UKonst
  | [] => .ok .nil
  | k :: ks =>
    match uKonst consts sums element k, uKonstReihe consts sums element ks with
    | .ok a, .ok r => .ok (.cons a r)
    | .error e, _ | _, .error e => .error e
termination_by values => 2 * sizeOf values
decreasing_by all_goals simp_wf; omega
end
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
/-- The statics of the unit: ONE value each, an integer range or `bool`, with a numeral (or `true`/`false`)
    as the initial value; explicit placement is retained for the image-layout gate. -/
def uGlobs (consts : List (String × Int)) (alias : List (String × (Int × Int))) :
    List SItemTief → Except String (List UGlob)
  | [] => .ok []
  | .globT m n t v al sec sh :: rest =>
    let alignment := match al with
      | none => some 1
      | some e => ProfilBindung.ausrichtungWert (consts.map (fun (n, z) => (n, z.toNat))) e
    if !alignment.any ausrichtungB then .error ("global " ++ n ++ ": invalid alignment")
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
            | .wert τ, _ => uKonst consts [] (some τ) v
            | _, _ => .ok .null : Except String UKonst) with
        | .error e => .error e
        | .ok k =>
        match uGlobs consts alias rest with
        | .error e => .error e
        | .ok gs => .ok ({ name := n, ty, init := z, initK := k, placement := if al.isSome || sec.isSome then some ⟨[n], alignment.getD 1, sec, m⟩ else none, var := m, shared := sh, optName := match t with | .index true tn => some tn | _ => none, sumName := match ty, t with | .wert (.sum _), .atom a => some a | _, _ => none, breite := match ty with | .int _ _ => uSpeicherBreite alias t | _ => 0 } :: gs)
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
/-- The closed merge operators of `accumulates` (SYNTAX.md §11.4, C15):
    `max`, `min`, `add` and the bitwise `or`/`and`. Any other operator is refused. -/
def akkuOperatorOk (m : String) : Bool :=
  strEq m "max" || strEq m "min" || strEq m "add" || strEq m "or" || strEq m "and"
/-- An `accumulates` item in admitted surface form (C15 storage slice): a closed
    operator and a `per cpu` count. The count's value (positive constant), the
    value type (integer range) and the operator's neutral (width-indexed for
    `and`) are checked at expansion (`UebersetzeAkku`); updates, reads and the
    core query stay refused there (they need C08). -/
def akkuFormZulaessig : SItemTief → Bool
  | .accT _ _ m (some _) _ => akkuOperatorOk m
  | _ => false
/-- Items outside the fragment: everything but constants,
    type aliases, statics, tables, locks and functions is an explicit
    error (the refused rows of `collect`). Translators (`transT`) are consumed by the certified
    expansion (`exportLibraryUnit` runs before this check): they are certificate input, never
    runtime items, so they step past here. -/
def uRestFehler : List SItemTief → Except String Unit
  | [] => .ok ()
  | .transT .. :: rest => uRestFehler rest
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
  -- `check` items elaborate into `UProg.checks` (C16); their codegen refusal lives in `elabU`.
  | .checkT _ :: rest => uRestFehler rest
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
  -- `accumulates` (C15 storage slice): admitted surface forms expand to guarded
  -- cells (`UebersetzeAkku`); anything else is refused by name (the core query
  -- and updates/reads need C08, task 4; `and` needs the stored width).
  | ((.accT _ _ m p _) as it) :: rest =>
    if akkuFormZulaessig it then uRestFehler rest
    else if !akkuOperatorOk m then .error "accumulator operator without G form"
    else .error "accumulator without per cpu count without G form"
  | .walkT walk :: _ => .error ("source export: walk requires a proved safe child binding, va scale and traversal correspondence: " ++ walk.name)
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
  | .ptr ⟨0, ⟨_, _, none⟩, .table n⟩, .fnref t => match tabs[n]? with
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
/-- Foreign effects are checked here; retained pre/postconditions lower through the shared contract gate. -/
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
  | .needs (.call "Held" _) :: _ => .error "foreign fn precondition cannot borrow a held lock"
  | .needs _ :: rest | .gives _ :: rest => uAxKlauseln kopf tabs globs rest
  | .cost _ :: rest => uAxKlauseln kopf tabs globs rest
  | .arch _ :: rest => uAxKlauseln kopf tabs globs rest
  -- `deadline <= n ops arch X falsifier p`: a named hardware outcome outside the goal (`Spec.lean`, NOT CLAIMED:
  -- time bounds), the same as at an implemented function
  | .limit _ :: rest => uAxKlauseln kopf tabs globs rest
  | _ :: _ => .error "foreign fn clause without G form"
end Gabbro.Grammatik.Parser.Uebersetze
