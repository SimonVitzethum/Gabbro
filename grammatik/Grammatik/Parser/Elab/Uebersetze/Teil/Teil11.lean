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
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Initializers
public import Grammatik.Parser.Elab.Uebersetze.Kontext.FunctionElaboration
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000
/-- The statics of the unit: ONE value each, an integer range or `bool`, with a numeral (or `true`/`false`)
    as the initial value; explicit placement is retained for the image-layout gate. -/
def uGlobs (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (items : List SItemTief) (widths : List (String × (Int × Int)) := []) : Except String (List UGlob) :=
  match items with
  | [] => .ok []
  | .globT m n t v al sec sh :: rest =>
    let alignment := match al with
      | none => some 1
      | some e => ProfilBindung.ausrichtungWert
          (consts.map (fun (n, z) => (n, Int.toNat z))) e
    if !alignment.any ausrichtungB then .error ("global " ++ n ++ ": invalid alignment")
    else
      match (match t with
          | .atom "bool" =>
            match v with
            | .one .tru => .ok (GTy.bool, (1 : Int))
            | .one .fls => .ok (GTy.bool, (0 : Int))
            | _ => .error "static initialiser without G form"
          | .array _ _ | .str _ =>
            match uTyp alias [] [] [] t with
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
        match uGlobs consts alias rest widths with
        | .error e => .error e
        | .ok gs => .ok ({ name := n, ty, init := z, initK := k, placement := if al.isSome || sec.isSome then some ⟨[n], alignment.getD 1, sec, m⟩ else none, var := m, shared := sh, optName := match t with | .index true tn => some tn | _ => none, sumName := match ty, t with | .wert (.sum _), .atom a => some a | _, _ => none, breite := match ty with | .int _ _ => uSpeicherBreite widths t | _ => 0 } :: gs)
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
          match uGlobs consts alias rest widths with
          | .error e => .error e
          | .ok gs => .ok ({ name := n, ty, init := 0, var := true, atomic := true, shared := true, nutzlast := nl, breite := match ty with | .int _ _ => uSpeicherBreite widths t | _ => 0 } :: gs)
  | _ :: rest => uGlobs consts alias rest widths
/-- The arenas of a unit as the PAIR the specification names (`ArenaZucker`): a table of `hi` slots with the one
    field `wert`, and the counter static `A#used` over `0 .. hi` starting at zero. A dynamic ceiling and a
    placement have no form here. -/
def uArenen (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (items : List SItemTief) (widths : List (String × (Int × Int)) := []) : Except String (List UTab × List UGlob) :=
  match items with
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
          match uArenen consts alias rest widths with
          | .error e => .error e
          | .ok (ts, gs) =>
            if 0 < h then
              .ok ({ name := n, count := h, cols := [("wert", r)], arena := true, breiten := (let w := uSpeicherBreite widths t; if 0 < w then [("wert", w)] else []) } :: ts,
                   { name := n ++ "#used", ty := GTy.int 0 h, init := 0, var := true } :: gs)
            else .error "arena of no slots"
  | _ :: rest => uArenen consts alias rest widths
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
  | .tableT _ _ _ _ _ _ _ _ :: rest => uRestFehler rest
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
  | it@(.accT _ _ m _ _) :: rest =>
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
/-- Closed start values: bounded literals, booleans, `None`, or a table capability in its registered space. -/
def uStartArg (spaces : List String) (tabs : List UTab) : Ty → SExpr → Bool
  | .int lo hi, .lit n => decide (lo ≤ (n : Int) ∧ (n : Int) ≤ hi)
  | .int lo hi, .un "-" (.lit n) => decide (lo ≤ -(n : Int) ∧ -(n : Int) ≤ hi)
  | .bool, .tru => true
  | .bool, .fls => true
  | .opt _, .call "None" [] => true
  -- `&T` for a `ptr<…> T` parameter (`Expr.ptrOf`): the one pointer to the carrier the type names
  | .ptr ⟨space, ⟨_, _, none⟩, .table n⟩, .fnref t => match tabs[n]? with
    | .some tb => strEq tb.name t && decide (tb.space = space ∧ space < spaces.length)
    | .none => false
  | _, _ => false
/-- A `concurrent` member: a function of the unit, started with one value per parameter
    (`concurrent { m::f(a, b) }`, the model's start with its arguments). -/
def uStartMit (spaces : List String) (tabs : List UTab) (fns : List UFn) (d : String) (args : List SExpr) : Except String String :=
  match fns.find? (fun f => strEq f.name d) with
  | .some f =>
    if f.params.length != args.length then
      .error ("concurrent member with " ++ toString args.length ++ " arguments for " ++
        toString f.params.length ++ " parameters: " ++ d)
    else if (f.params.zip args).all (fun (p, a) => uStartArg spaces tabs p.2 a) then .ok d
    else .error ("concurrent member with an argument outside its parameter's type: " ++ d)
  | .none => .error ("concurrent member names an unknown function: " ++ d)
/-- The roots of the `concurrent` items, in order (their members come first, as in `check_starts`). -/
def uNebenWurzeln (spaces : List String) (tabs : List UTab) (fns : List UFn) : List SItemTief → Except String (List String)
  | [] => .ok []
  | .concT ps :: rest => do
    let here ← uSeq (ps.map fun (p, args) => match p.getLast? with
      | .some d => uStartMit spaces tabs fns d args
      | .none => .error "empty path in concurrent")
    let more ← uNebenWurzeln spaces tabs fns rest
    pure (here ++ more)
  | _ :: rest => uNebenWurzeln spaces tabs fns rest
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
def uWurzeln (spaces : List String) (tabs : List UTab) (fns : List UFn) (ms : List SItemTief) : Except String (List String) := do
  let a ← uNebenWurzeln spaces tabs fns ms
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
