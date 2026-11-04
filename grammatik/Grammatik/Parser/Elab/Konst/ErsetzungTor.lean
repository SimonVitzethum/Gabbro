module

public import Grammatik.Parser.Elab.Konst.Ersetzung
public import Grammatik.Parser.Elab.Konst.Scope
public import Grammatik.Parser.Elab.Export.ExportMetadata

@[expose] public section

namespace Gabbro.Grammatik.Parser.Konst

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.ExportMetadata

mutual
/-- Source constant payloads recurse element-wise, including nested rows. -/
def ersetzeKonstWert (fns : List UKonstFn) : SKonstWert → Except String SKonstWert
  | .one source => (ersetzeSExpr fns source).map SKonstWert.one
  | .rows rows => (ersetzeKonstWerte fns rows).map SKonstWert.rows
def ersetzeKonstWerte (fns : List UKonstFn) : List SKonstWert → Except String (List SKonstWert)
  | [] => .ok []
  | value :: rest => do return (← ersetzeKonstWert fns value) :: (← ersetzeKonstWerte fns rest)
end

/-- Replace value calls in function bodies, contracts and constant initializers. -/
def ersetzeSItem (fns : List UKonstFn) : SItemTief → Except String SItemTief
  | .fnT sig body => do
    if strEq sig.art "const" then return .fnT sig body
    let body' ← ersetzeSAnwIn (sig.params.map Prod.fst) fns body
    let clauses ← sig.klauseln.mapM fun
      | .needs source => (ersetzeSExprIn (sig.params.map Prod.fst) fns source).map SKlausel.needs
      | .gives source => (ersetzeSExprIn ("result" :: sig.params.map Prod.fst) fns source).map SKlausel.gives
      | .cost source => (ersetzeSExprIn (sig.params.map Prod.fst) fns source).map SKlausel.cost
      | .drops source => (ersetzeSExprIn (sig.params.map Prod.fst) fns source).map SKlausel.drops
      | clause => pure clause
    return .fnT {sig with klauseln := clauses} body'
  | .constT name ty value => do return .constT name ty (← ersetzeKonstWert fns value)
  | .globT mutable name ty value bound proof shared => do
    return .globT mutable name ty (← ersetzeKonstWert fns value) bound proof shared
  | item => .ok item

/-- The whole pass over a unit: every function body substituted. -/
def ersetzeItems (fns : List UKonstFn) : List SItemTief → Except String (List SItemTief)
  | [] => .ok []
  | m :: rest =>
    match ersetzeSItem fns m, ersetzeItems fns rest with
    | .ok m', .ok rest' => .ok (m' :: rest')
    | .error e, _ | _, .error e => .error e

/-- Const calls are certified on original source arguments. Global names close
    only inside their proof-producing typed expression reader; runtime expressions
    keep their canonical source spelling and ordinary name resolution. -/
def konstErsetzePipeline (items : List SItemTief) : Except String (List SItemTief) := do
  let functions ← collectFunctions items
  ersetzeItems functions items

mutual
/-- A surface call still names a dropped const function. -/
def hatKonstRufSExpr (namen : List String) : SExpr → Bool
  | .lit _ => false
  | .float _ => false
  | .tru => false
  | .fls => false
  | .variable _ => false
  | .field e _ => hatKonstRufSExpr namen e
  | .index a i => hatKonstRufSExpr namen a || hatKonstRufSExpr namen i
  | .arrow e _ => hatKonstRufSExpr namen e
  | .un _ e => hatKonstRufSExpr namen e
  | .bin _ a b => hatKonstRufSExpr namen a || hatKonstRufSExpr namen b
  | .call g args => namen.any (strEq · g) || hatKonstRufSExprList namen args
  | .fnref _ => false
  | .built _ args => hatKonstRufSExprList namen args
  | .old e => hatKonstRufSExpr namen e
  | .res => false
  | .why _ _ => false
  | .ext _ _ subs => hatKonstRufSExprList namen subs
def hatKonstRufSExprList (namen : List String) : List SExpr → Bool
  | [] => false
  | e :: rest => hatKonstRufSExpr namen e || hatKonstRufSExprList namen rest
end

mutual
/-- A body still calls a dropped const function (statement calls count:
    they are never substituted, so they stay visible here). -/
def hatKonstRufSAnw (namen : List String) : SAnw → Bool
  | .bind _ _ _ v => hatKonstRufSExpr namen v
  | .bindElse _ _ v _ b => hatKonstRufSExpr namen v || hatKonstRufSAnw namen b
  | .bindQ _ _ _ v | .bindAxiomOpt _ _ v => hatKonstRufSExpr namen v
  | .bindAxiomOptElse _ _ v _ b => hatKonstRufSExpr namen v || hatKonstRufSAnw namen b
  | .bindLib _ _ _ _ => false
  | .set z _ x => hatKonstRufSExpr namen z || hatKonstRufSExpr namen x
  | .shift z _ _ => hatKonstRufSExpr namen z
  | .callIndElse p args _ body => hatKonstRufSExpr namen p || hatKonstRufSExprList namen args || hatKonstRufSAnw namen body
  | .callElse g args _ body => namen.any (strEq · g) || hatKonstRufSExprList namen args || hatKonstRufSAnw namen body
  | .callQ g args | .genericCall g _ args => namen.any (strEq · g) || hatKonstRufSExprList namen args
  | .call g args => namen.any (strEq · g) || hatKonstRufSExprList namen args
  | .lcall _ => false
  | .cond c t eis fb =>
    hatKonstRufSExpr namen c || hatKonstRufSAnw namen t ||
    hatKonstRufSAnwList namen eis ||
      match fb with | none => false | some f => hatKonstRufSAnw namen f
  | .elsif c b => hatKonstRufSExpr namen c || hatKonstRufSAnw namen b
  | .cases g arms => hatKonstRufSExpr namen g || hatKonstRufSAnwList namen arms
  | .arm _ _ t => hatKonstRufSAnw namen t
  | .each _ o _ s _ _ i d =>
    (match o with | none => false | some v => hatKonstRufSExpr namen v) ||
    hatKonstRufSExpr namen s ||
    (match i with | none => false | some v => hatKonstRufSExpr namen v) ||
    hatKonstRufSAnw namen d
  | .retry _ b => hatKonstRufSAnw namen b
  | .loop _ b => hatKonstRufSAnw namen b
  | .waive _ b => hatKonstRufSAnw namen b
  | .trim o _ s => hatKonstRufSExpr namen o || hatKonstRufSAnw namen s
  | .trimReq o _ => hatKonstRufSExpr namen o
  | .locks _ o b => hatKonstRufSExpr namen o || hatKonstRufSAnw namen b
  | .watch _ b => hatKonstRufSAnw namen b
  | .leave _ => false
  | .next _ => false
  | .emit z w _ => hatKonstRufSExpr namen z || hatKonstRufSExpr namen w
  | .await _ _ q _ => hatKonstRufSExpr namen q
  | .swap _ _ o _ => hatKonstRufSExpr namen o
  | .retires _ => false
  | .step _ _ => false
  | .ret x => match x with | none => false | some e => hatKonstRufSExpr namen e
  | .alloc _ _ _ _ v s =>
    hatKonstRufSExpr namen v ||
      match s with | none => false | some b => hatKonstRufSAnw namen b
  | .reset _ r =>
    match r with | none => false | some (x, y) => hatKonstRufSExpr namen x || hatKonstRufSExpr namen y
  | .grow _ e b => hatKonstRufSExpr namen e || hatKonstRufSAnw namen b
  | .free e => hatKonstRufSExpr namen e
  | .child b => hatKonstRufSAnw namen b
  | .start _ => false
  | .other _ => false
  | .block ss e =>
    hatKonstRufSAnwList namen ss ||
      match e with
      | none => false
      | some (.ret x) => match x with | none => false | some v => hatKonstRufSExpr namen v
      | some _ => false
  | .allocVon _ _ _ _ => false
def hatKonstRufSAnwList (namen : List String) : List SAnw → Bool
  | [] => false
  | a :: rest => hatKonstRufSAnw namen a || hatKonstRufSAnwList namen rest
def hatKonstRufOptAnw (namen : List String) : Option SAnw → Bool
  | none => false
  | some a => hatKonstRufSAnw namen a
end

/-- No remaining reference in a substituted unit. -/
def hatKonstRufItems (namen : List String) : List SItemTief → Bool
  | [] => false
  | .fnT _ body :: rest => hatKonstRufSAnw namen body || hatKonstRufItems namen rest
  | _ :: rest => hatKonstRufItems namen rest

/-- Const declarations travel dropped, like `fnItems`: the gate below
    checks the runtime unit only. -/
def ohneKonst : List SItemTief → List SItemTief
  | [] => []
  | .fnT sig body :: rest =>
    if strEq sig.art "const" then ohneKonst rest else .fnT sig body :: ohneKonst rest
  | m :: rest => m :: ohneKonst rest

/-- The metadata gate opens exactly for successful certificates: no
    remaining call to a dropped const function, and no other metadata
    duty in the runtime unit. Failing substitutions keep their refusal
    upstream (`ersetzeSExpr` errors); anything else keeps the exact
    `ExportMetadata.check` refusal. -/
def checkErsetzt (ms msErs : List SItemTief) : Except String Unit :=
  let namen := ms.filterMap (fun | .fnT sig _ => if strEq sig.art "const" then some sig.name else none | _ => none)
  if hatKonstRufItems namen msErs then
    .error "const call without certified value: refusing runtime export"
  else ExportMetadata.check (ohneKonst msErs)

/-- Dropping const declarations cannot introduce a metadata duty: a unit
    whose non-const items are clean stays clean. -/
theorem ohneKonst_sauber (ms : List SItemTief)
    (h : (ohneKonst ms).any itemMetadata = false) :
    check (ohneKonst ms) = .ok () :=
  check_clear (ohneKonst ms) h

/-- Exact literals never name a const function. -/
theorem literalVonInt_ohne (namen : List String) (v : Int) :
    hatKonstRufSExpr namen (literalVonInt v) = false := by
  simp only [literalVonInt]
  split
  · rfl
  · rfl

/-- Boolean literals never name a const function. -/
theorem literalVonBool_ohne (namen : List String) (b : Bool) :
    hatKonstRufSExpr namen (literalVonBool b) = false := by
  cases b <;> rfl

/-! ### Witnesses: nested calls, parameters, negative value, refused open case. -/

/-- An expression-bodied const function with parameters. -/
def zeugeFnAdd : UKonstFn :=
  { name := "add"
    params := [("x", .int 0 10), ("y", .int 0 10)]
    erg := .int 0 20
    rumpf := .block [] (some (.ret (some (.bin "+" (.variable "x") (.variable "y")))))
    signature :=
      { art := "const"
        name := "add"
        params := [("x", .atom "u8"), ("y", .atom "u8")]
        res := some (.atom "u8")
        fehler := none
        klauseln := [] } }

/-- Nested const calls substitute inside out. -/
theorem zeugeVerschachtelt :
    ersetzeSExpr [zeugeFnAdd] (.call "add" [.call "add" [.lit 1, .lit 2], .lit 3]) =
      .ok (literalVonInt 6) := by
  cbv

/-- Parameters bind positionally: `add(4, 5)` is `9`. -/
theorem zeugeParameter :
    ersetzeSExpr [zeugeFnAdd] (.call "add" [.lit 4, .lit 5]) = .ok (.lit 9) := by
  cbv

/-- A negative certified value travels via the negative form. -/
theorem zeugeNegativ : literalVonInt (-5) = .un "-" (.lit 5) := by
  rfl

/-- An open argument keeps the program refused, naming the callee. -/
theorem zeugeOffenVerweigert :
    ersetzeSExpr [zeugeFnAdd] (.call "add" [.variable "x", .lit 1]) =
      .error "const open argument at `add`: certified substitution needs closed arguments" := by
  rfl

/-- A substituted call leaves no reference to the dropped function. -/
theorem zeugeOhneRest :
    hatKonstRufSExpr ["add"] (literalVonInt 6) = false := by
  rfl

/-- Original runtime annotations are checked before rewriting, as well as afterwards.
    Only const declarations may leave this domain, through the certified call pass. -/
def checkSourceMetadata (items : List SItemTief) : Except String Unit := do
  let rewritten ← konstErsetzePipeline items
  ExportMetadata.check (ohneKonst items)
  checkErsetzt items rewritten

/-- The original runtime metadata check is retained without any rewrite assumption. -/
theorem checkSourceMetadata_runtime_sound (items : List SItemTief)
    (accepted : checkSourceMetadata items = .ok ()) :
    (ohneKonst items).any ExportMetadata.itemMetadata = false := by
  cases hr : konstErsetzePipeline items with
  | error error =>
    simp [checkSourceMetadata, hr, bind, Except.bind, pure, Except.pure] at accepted
  | ok rewritten =>
    cases hm : ExportMetadata.check (ohneKonst items) with
    | error error =>
      simp [checkSourceMetadata, hr, hm, bind, Except.bind, pure, Except.pure] at accepted
    | ok value => cases value; exact ExportMetadata.check_sound _ hm

/-- The compiler gate retains an actual successful substitution and the metadata
    check of its remaining runtime declarations. -/
theorem checkSourceMetadata_sound (items : List SItemTief)
    (accepted : checkSourceMetadata items = .ok ()) :
    ∃ rewritten, konstErsetzePipeline items = .ok rewritten ∧
      checkErsetzt items rewritten = .ok () ∧
      (ohneKonst rewritten).any ExportMetadata.itemMetadata = false := by
  cases hr : konstErsetzePipeline items with
  | error error =>
    simp [checkSourceMetadata, hr, bind, Except.bind, pure, Except.pure] at accepted
  | ok rewritten =>
    have original := ExportMetadata.check_clear (ohneKonst items)
      (checkSourceMetadata_runtime_sound items accepted)
    have gate : checkErsetzt items rewritten = .ok () := by
      simpa only [checkSourceMetadata, hr, original, bind, Except.bind,
        pure, Except.pure] using accepted
    refine ⟨rewritten, rfl, gate, ?_⟩
    unfold checkErsetzt at gate
    dsimp only at gate
    split at gate
    · contradiction
    · exact ExportMetadata.check_sound _ gate

/-- New compile-time header positions use the same original-source certificate. -/
def checkSourceConstants (items : List SItemTief) : Except String Unit :=
  if items.any ExportMetadata.constantExpansion then checkSourceMetadata items else .ok ()

theorem checkSourceConstants_sound (items : List SItemTief)
    (used : items.any ExportMetadata.constantExpansion = true)
    (accepted : checkSourceConstants items = .ok ()) :
    ∃ rewritten, konstErsetzePipeline items = .ok rewritten ∧
      checkErsetzt items rewritten = .ok () ∧
      (ohneKonst rewritten).any ExportMetadata.itemMetadata = false :=
  checkSourceMetadata_sound items (by simpa [checkSourceConstants, used] using accepted)

end Gabbro.Grammatik.Parser.Konst
