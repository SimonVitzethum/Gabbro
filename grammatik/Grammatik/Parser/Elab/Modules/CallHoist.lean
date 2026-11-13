module
public import Grammatik.Parser.Elab.Modules.CallHoist.Expressions
public import Grammatik.Parser.Elab.Modules.CallHoist.Collect
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

/-- The first `else if` whose condition satisfies `p`: the arms in front, the condition, its body, the
    arms behind. -/
def elsifSpalte (p : SExpr → Bool) : List SAnw → Option (List SAnw × SExpr × SAnw × List SAnw)
  | [] => none
  | .elsif c b :: rest =>
    if p c then some ([], c, b, rest)
    else (elsifSpalte p rest).map fun (vor, c2, b2, nach) => (.elsif c b :: vor, c2, b2, nach)
  | arm :: rest => (elsifSpalte p rest).map fun (vor, c2, b2, nach) => (arm :: vor, c2, b2, nach)

/-- The declared type of an option or tagged static read by its name, outside any local of that name. -/
def statikTypVon (k : Kontext) : SExpr → Option STyp
  | .variable v =>
    if k.lokal.contains v then none else (k.statikTyp.find? fun entry => strEq entry.1 v).map (·.2)
  | _ => none

/-- Most variables are not statics. Read the immutable declaration table first,
    avoiding a live-scope membership scan when no static can match. -/
def statikTypVonFast (k : Kontext) : SExpr → Option STyp
  | .variable v =>
    match k.statikTyp.find? (fun entry => strEq entry.1 v) with
    | none => none
    | some entry => if k.lokal.contains v then none else some entry.2
  | _ => none

@[csimp] theorem statikTypVon_eq_fast : @statikTypVon = @statikTypVonFast := by
  funext k e
  cases e <;> first
    | rfl
    | rename_i name
      cases hl : k.lokal.contains name <;>
        cases ht : k.statikTyp.find? (fun entry => strEq entry.1 name) <;>
          simp only [statikTypVon, statikTypVonFast, hl, ht] <;> rfl

/-- Read a tagged place exactly once through the existing match reader. The fresh local starts
    with a declared payload-free case; every arm replaces it with the observed value. The written
    result type, when present, is retained for the ordinary elaborator to check. -/
def leseFaelle (nr : Nat) (mu : Bool) (x : String) (ty : Option STyp) (e : SExpr)
    (typ : STyp) (faelle : List (String × Bool)) : Option (List SAnw × Nat) :=
  match faelle.find? (fun fall => !fall.2) with
  | none => none
  | some (start, _) =>
    let r := "#r" ++ toString nr
    let p := "#r" ++ toString (nr + 1)
    some ([.bind true r (some typ) (.variable start),
      .cases e (faelle.map fun (fall, nutzlast) =>
        if nutzlast then .arm fall (some p) (.block [.set (.variable r) "=" (.call fall [.variable p])] none)
        else .arm fall none (.block [.set (.variable r) "=" (.variable fall)] none)),
      .bind mu x (ty.orElse fun _ => some typ) (.variable r)], nr + 2)

/-- A tagged static uses the common match expansion, outside any local of the same name. -/
def leseStatik (k : Kontext) (nr : Nat) (mu : Bool) (x : String) (ty : Option STyp) : SExpr → Option (List SAnw × Nat)
  | .variable v =>
    if k.lokal.contains v then none else
    match k.statikFaelle.find? (fun entry => strEq entry.1 v), k.statikTyp.find? (fun entry => strEq entry.1 v) with
    | some (_, faelle), some (_, typ) => leseFaelle nr mu x ty (.variable v) typ faelle
    | _, _ => none
  | _ => none

/-- A missing tagged static likewise needs no scan of lexical locals. Successful
    static lookup still applies exactly the original shadowing check. -/
def leseStatikFast (k : Kontext) (nr : Nat) (mu : Bool) (x : String) (ty : Option STyp) :
    SExpr → Option (List SAnw × Nat)
  | .variable v =>
    match k.statikFaelle.find? (fun entry => strEq entry.1 v),
        k.statikTyp.find? (fun entry => strEq entry.1 v) with
    | some (_, faelle), some (_, typ) =>
      if k.lokal.contains v then none else leseFaelle nr mu x ty (.variable v) typ faelle
    | _, _ => none
  | _ => none

@[csimp] theorem leseStatik_eq_fast : @leseStatik = @leseStatikFast := by
  funext k nr mu x ty e
  cases e <;> first
    | rfl
    | rename_i name
      cases hl : k.lokal.contains name <;>
        cases hf : k.statikFaelle.find? (fun entry => strEq entry.1 name) <;>
          cases ht : k.statikTyp.find? (fun entry => strEq entry.1 name) <;>
            simp only [leseStatik, leseStatikFast, hl, hf, ht] <;> rfl

/-- A tagged slot is read where its binding stood. Only its index is rewritten: a named table
    has no evaluation before the index. Hoisted index calls run first, and the remaining index
    occurs once, in the match's scrutinee. No payload-free case means no rewrite. -/
def leseFeld (k : Kontext) (n nr : Nat) (mu : Bool) (x : String) (ty : Option STyp) :
    SExpr → Option (List SAnw × Nat)
  | e@(.field (.index (.field (.variable table) "slots") index) field) => do
    if k.lokal.contains table then none else do
      let .atom name ← feldTyp k e | none
      let (_, faelle) ← k.typFaelle.find? (fun entry => strEq entry.1 name)
      let ri := hebeE k n nr true e
      let source := ri.2.1
      let (statements, next) ← leseFaelle ri.2.2.1 mu x ty source (.atom name) faelle
      pure (ri.1 ++ statements, next)
  | _ => none

/-- Rewrite one statement into the statements that replace it, with the next fresh number. -/
def hebeS (k : Kontext) : Nat → Nat → SAnw → List SAnw × Nat
  | 0, nr, s => ([s], nr)
  | n + 1, nr, s =>
    -- A body: every statement in order, each seeing the names bound before it, then the calls of a
    -- closing `return`. `zus` are names the body itself opens (a loop binder, a payload, a reason).
    let koerper : List String → Nat → SAnw → SAnw × Nat := fun zus nr b =>
      match b with
      | .block ss ende =>
        let r := collectSteps (fun (state : Nat × List String) t =>
          let x := hebeS { k with lokal := state.2, oben := false } n state.1 t
          (x.1, x.2, ExportMetadata.binders t ++ state.2)) ss (nr, zus ++ k.lokal)
        match ende with
        | some (.ret (some e)) =>
          let x := hebeRet { k with lokal := r.2.2 } n r.2.1 e
          (.block (r.1 ++ x.1) (some (.ret (some x.2.1))), x.2.2)
        | _ => (.block r.1 ende, r.2.1)
      | t =>
        let x := hebeS { k with lokal := zus ++ k.lokal, oben := false } n nr t
        match x.1 with
        | [one] => (one, x.2)
        | many => (.block many none, x.2)
    let koerperL : Nat → List SAnw → List SAnw × Nat := fun nr bs =>
      collectSteps (fun current b =>
        let x := koerper [] current b
        ([x.1], x.2)) bs nr
    match s with
    | .bind mu x ty e =>
      match (leseStatik k nr mu x ty e).orElse (fun _ => leseFeld k n nr mu x ty e) with
      | some gelesen => gelesen
      | none =>
        let r := if mu then (let y := hebeE k n nr true e; (y.1, y.2.1, y.2.2.1)) else hebeOben k n nr e
        (r.1 ++ [.bind mu x (ty.orElse fun _ => (feldTyp k r.2.1).orElse fun _ => statikTypVon k r.2.1) r.2.1], r.2.2)
    | .bindElse x ty e g b =>
      let r := hebeOben k n nr e
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.bindElse x ty r.2.1 g y.1], y.2)
    | .set target op value =>
      match target with
      | .variable x =>
        -- `x = Case(v);` is read as it stands for a local; for a static the value is bound first, as
        -- is any other call in the value. A compound assignment `x op= v` is `x = x op v`: the target
        -- is read first, so a call in `v` moves only when that read is no read of mutable state.
        let plain := strEq op "="
        let lokal := k.lokal.contains x || !(k.statics.finde x).isSome
        let r := match value with
          | .call c _ =>
            if plain && (k.faelle.finde c).isSome && lokal then hebeOben k n nr value
            else (let y := hebeE k n nr (plain || lokal) value; (y.1, y.2.1, y.2.2.1))
          | _ =>
            -- `S = End;` for a static `S`: the case without a payload is bound first as well.
            match (if !plain || lokal then none else bindeFall k true nr true value) with
            | some y => (y.1, y.2.1, y.2.2.1)
            | none => let y := hebeE k n nr (plain || lokal) value; (y.1, y.2.1, y.2.2.1)
        (r.1 ++ [.set target op r.2.1], r.2.2)
      | .field (.index base i) name =>
        -- A compound assignment reads the slot before the value: nothing in the value moves then.
        let ri := hebeE k n nr true i
        -- A case without a payload reads nothing: it is bound first wherever the index was read.
        let rv : Schritt := ((if strEq op "=" then bindeFall k true ri.2.2.1 true value else none).getD
          (hebeE k n ri.2.2.1 (ri.2.2.2 && strEq op "=") value))
        -- Like an explicit `let v = a[j]`, retain the element's inferred range at the store.
        -- The target index's calls are already in ri.1. Its remaining expression must read no
        -- mutable state, and a compound assignment must keep its target read before the value.
        let rv : Schritt := match rv.2.1 with
          | .index _ _ =>
            if ri.2.2.2 && strEq op "=" then
              let name := "#r" ++ toString rv.2.2.1
              (rv.1 ++ [.bind false name none rv.2.1], .variable name, rv.2.2.1 + 1, rv.2.2.2)
            else rv
          | _ => rv
        (ri.1 ++ rv.1 ++ [.set (.field (.index base ri.2.1) name) op rv.2.1], rv.2.2.1)
      | _ => ([s], nr)
    | .call f args =>
      let r := hebeArgs k n nr args
      (r.1 ++ [.call f r.2.1], r.2.2)
    | .callElse f args g b =>
      let r := hebeArgs k n nr args
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.callElse f r.2.1 g y.1], y.2)
    | .callIndElse p args g b =>
      let r := hebeArgs k n nr args
      let y := koerper [g] r.2.2 b
      (r.1 ++ [.callIndElse p r.2.1 g y.1], y.2)
    | .ret (some e) =>
      let r := hebeRet k n nr e
      (r.1 ++ [.ret (some r.2.1)], r.2.2)
    | .cond c t eis sonst =>
      match elsifSpalte (fun bed => !(hebeE k n 0 true bed).1.isEmpty) eis with
      | some (vor, c2, b2, nach) =>
        hebeS k n nr (.cond c t vor (some (.block [.cond c2 b2 nach sonst] none)))
      | none =>
        let r := hebeE k n nr true c
        let yt := koerper [] r.2.2.1 t
        let ye := koerperL yt.2 eis
        match sonst with
        | some b =>
          let ys := koerper [] ye.2 b
          (r.1 ++ [.cond r.2.1 yt.1 ye.1 (some ys.1)], ys.2)
        | none => (r.1 ++ [.cond r.2.1 yt.1 ye.1 none], ye.2)
    | .elsif c b =>
      let y := koerper [] nr b
      ([.elsif c y.1], y.2)
    | .cases scrutinee arms =>
      let r := hebeE k n nr true scrutinee
      let y := koerperL r.2.2.1 arms
      (r.1 ++ [.cases r.2.1 y.1], y.2)
    | .arm v binder b =>
      let y := koerper binder.toList nr b
      ([.arm v binder y.1], y.2)
    | .emit z w p =>
      let r := hebeE k n nr true w
      (r.1 ++ [.emit z r.2.1 p], r.2.2.1)
    | .each a b c d m raw inv body =>
      let y := koerper [a] nr body
      ([.each a b c d m raw inv y.1], y.2)
    | .boundedLoop h b =>
      let y := koerper ((boundedLoopLocals h).map Prod.fst) nr b
      ([.boundedLoop h y.1], y.2)
    | .retry h b => let y := koerper [] nr b; ([.retry h y.1], y.2)
    | .loop h b => let y := koerper [] nr b; ([.loop h y.1], y.2)
    | .waive ns b => let y := koerper [] nr b; ([.waive ns y.1], y.2)
    | .trim o t b => let y := koerper [] nr b; ([.trim o t y.1], y.2)
    | .locks g o b => let y := koerper [] nr b; ([.locks g o y.1], y.2)
    | .watch d b => let y := koerper [] nr b; ([.watch d y.1], y.2)
    | .block _ _ => let y := koerper [] nr s; ([y.1], y.2)
    | _ => ([s], nr)

/-- Rewrite the body of a function. -/
def hebeKoerper (k : Kontext) (b : SAnw) : SAnw :=
  match (hebeS { k with oben := true } 100000 0 b).1 with
  | [one] => one
  | many => .block many none

/-- Rewrite the ordinary functions of an item; a `const fn` is evaluated at compile time and stays. -/
def hebeItem (k : Kontext) : SItemTief → SItemTief
  | .fnT s b => if strEq s.art "const" then .fnT s b
    else .fnT s (hebeKoerper { k with lokal := s.params.map (·.1) } b)
  | .gateT item => .gateT (hebeItem k item)
  | item => item

/-- The names a `let` can bind a call of: functions, foreign prototypes and gates. -/
def fnNamen (items : List SItemTief) : List String :=
  items.filterMap fun
    | .fnT s _ => if strEq s.art "const" then none else some s.name
    | .protoT s => some s.name
    | .callT s => some s.name
    | .gateT (.fnT s _) => some s.name
    | _ => none

/-- The statics of a unit. -/
def statikNamen (items : List SItemTief) : List String :=
  items.filterMap fun
    | .globT _ n _ _ _ _ _ => some n
    | .atomT n _ _ _ _ => some n
    | _ => none

/-- The case names of the unit's tagged types. -/
def fallNamen (items : List SItemTief) : List String :=
  match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
  | .ok schemas => schemas.flatMap fun schema => schema.cases.map (·.1)
  | .error _ => []

/-- The fields of the unit's tables whose declared type is a string, array, record or tagged type. -/
def feldNamen (items : List SItemTief) : List (String × String × STyp) :=
  let records : List String := items.filterMap fun
    | .typeT _ name _ _ (some (.raw _)) => some name
    | .taggedByT (.typeT _ name _ _ (some (.raw _))) _ => some name
    | _ => none
  items.flatMap fun
    | .tableT name _ _ _ _ _ parts _ => parts.flatMap fun
      | .tSlot fields => fields.filterMap fun field =>
          match field.ftyp with
          | .array .. | .str _ => some (name, field.fname, field.ftyp)
          | .atom a => if records.contains a then some (name, field.fname, field.ftyp) else none
          | _ => none
      | _ => []
    | _ => []

/-- The statics of option or tagged type, with their declared type. -/
def statikTypen (items : List SItemTief) : List (String × STyp) :=
  let tagged : List String := match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
    | .ok schemas => schemas.map fun schema => schema.name
    | .error _ => []
  items.filterMap fun
    | .globT _ n t _ _ _ _ =>
      match t with
      | .index true _ => some (n, t)
      | .atom a => if tagged.contains a then some (n, t) else none
      | _ => none
    | _ => none

/-- The declared tagged types with the payload-presence bit of every case. -/
def typFaelleVon (items : List SItemTief) : List (String × List (String × Bool)) :=
  match Uebersetze.uSumSchemas (items.map fun | .taggedByT declaration _ => declaration | item => item) with
  | .error _ => []
  | .ok schemas => schemas.map fun schema =>
      (schema.name, schema.cases.map fun fall => (fall.1, fall.2.isSome))

/-- The tagged statics with the cases of their type. -/
def statikFaelleVon (items : List SItemTief) : List (String × List (String × Bool)) :=
  let schemas := typFaelleVon items
  items.filterMap fun
    | .globT _ n (.atom a) _ _ _ _ =>
      (schemas.find? fun schema => strEq schema.1 a).map fun schema => (n, schema.2)
    | _ => none

/-- **Calls inside expressions become bindings**, in every ordinary function of the unit. -/
def hebe (items : List SItemTief) : List SItemTief :=
  let k : Kontext :=
    { fns := Tafel.von _ (fnNamen items), statics := Tafel.von _ (statikNamen items),
      faelle := Tafel.von _ (fallNamen items), felder := feldNamen items, statikTyp := statikTypen items,
      statikFaelle := statikFaelleVon items, typFaelle := typFaelleVon items }
  items.map (hebeItem k)


end Gabbro.Grammatik.Parser.CallHoist
