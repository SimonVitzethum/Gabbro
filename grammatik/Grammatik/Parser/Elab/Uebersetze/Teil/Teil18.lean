/-
  File:      Grammatik/Parser/Elab/Uebersetze/Teil/Teil18.lean
  Subject:   Phase 1 desugaring (`ABSTRACTION-SYNTAX-PLAN.md` §4, steps 1a/1b): reason
             propagation `?` and adapters `fn … from f` to EXISTING surface forms.

  `entzuckere` runs after module/generic/spec/literal expansion inside `elabU`,\n  so machine G never sees the new syntax:

  * `let x = f(args) ?;` (resp. `f(args) ?;`) becomes the explicit `else` form of §4.3:
    `let x = f(args) else (e) { match e { C => { return R::C; } … } };` with one arm
    per ground of the SHARED reason channel `R`. A different channel, a missing channel
    or a non-call under `?` is refused; the writer then keeps the written `else`.
  * `fn g(adaptparams) … from f …` becomes an ordinary `fnT` whose body calls `f` with
    the mapped arguments (§4.1): the prelude, the call (plain, `?`, or the explicit
    `else`), then the user body — or the short `;` body returning the call answer.
    The source must be an ordinary function of the unit (no `divergent`, no spec,
    not the adapter itself, not called in its own prelude); `..` stands at most once;
    `-x` names a parameter the source has; no name stands twice after expansion; the
    prelude binds every dropped parameter; the short body keeps the source result type.

  Every refusal is a named `Except` error at desugar time; elaboration never sees a new
  constructor. The identity of the desugaring with the explicit form is definitional
   (`entfalteFrage_beispiel`, `frageZuElse_ist_else`); end-to-end witnesses elaborate
   the desugared programs (`Parser/Elab/Proben/Spaet/UebersetzeProben42`).
-/
module

public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Namen.Gebunden
public import Grammatik.Parser.Spec.Resolve

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-! ### Reason propagation `?`: the explicit `else` form -/

/-- Re-raise each ground through an exhaustive match. Every arm returns its own reason.
    The unreachable trailing return gives the existing Endblock lowerer a closed continuation;
    its reason is declared, and an empty channel remains refused by ordinary elaboration. -/
def frageSonst (r : String) (e : String) (cs : List String) : SAnw :=
  .block [.cases (.variable e)
    (cs.map fun c => .arm c none (.block [] (some (.ret (some (.why r c))))))]
    (cs.head?.map (fun c => .ret (some (.why r c))))

/-- `let x = f(args) ?;` as the explicit `else` form (§4.3). -/
def frageZuElse (x : String) (ty : Option STyp) (f : String) (args : List SExpr)
    (r : String) (cs : List String) : SAnw :=
  .bindElse x ty (.call f args) "#frage" (frageSonst r "#frage" cs)

/-- `?` unfolds to the explicit `else` form it abbreviates (definitional). -/
theorem frageZuElse_ist_else (x : String) (ty : Option STyp) (f : String) (args : List SExpr)
    (r : String) (cs : List String) :
    frageZuElse x ty f args r cs =
      .bindElse x ty (.call f args) "#frage" (frageSonst r "#frage" cs) := rfl

/-- What `?` needs: the enclosing `or R`, every function of the unit with its `or R`,
    and every reason with its grounds. -/
structure FrageKontext where
  eigen : Option String
  ruf : List (String × Option String)
  gruende : List (String × List String)

/-- Expand `?` in one statement (no recursion into blocks): `bindQ`/`callQ` over a call whose
    channel equals the enclosing one become the explicit `else` form; everything else stays. -/
def entfalteFrageSchritt (k : FrageKontext) : SAnw → Except String SAnw
  | .bindQ _ x ty (.call f args) =>
    match k.ruf.find? (fun p => strEq p.1 f) with
    | none => .error ("call unknown: " ++ f)
    | some (_, kanal) => match kanal, k.eigen with
      | none, _ => .error "? without a reason channel"
      | some r, some e =>
        if strEq r e then
          match k.gruende.find? (fun p => strEq p.1 r) with
          | none => .error ("reason unknown: " ++ r)
          | some (_, cs) => .ok (frageZuElse x ty f args r cs)
        else .error "? needs the same reason channel; write else"
      | some _, none => .error "? needs the same reason channel; write else"
  | .bindQ .. => .error "? needs a call"
  | .callQ f args =>
    match k.ruf.find? (fun p => strEq p.1 f) with
    | none => .error ("call unknown: " ++ f)
    | some (_, kanal) => match kanal, k.eigen with
      | none, _ => .error "? without a reason channel"
      | some r, some e =>
        if strEq r e then
          match k.gruende.find? (fun p => strEq p.1 r) with
          | none => .error ("reason unknown: " ++ r)
          | some (_, cs) => .ok (frageZuElse "#frage" none f args r cs)
        else .error "? needs the same reason channel; write else"
      | some _, none => .error "? needs the same reason channel; write else"
  | s => .ok s

mutual
/-- Expand `?` in a statement, recursing into every block. -/
def entfalteFrage (k : FrageKontext) : SAnw → Except String SAnw
  | s@(.bindQ _ _ _ _) => entfalteFrageSchritt k s
  | s@(.callQ _ _) => entfalteFrageSchritt k s
  | .callElse name args reason body => (entfalteFrage k body).map (.callElse name args reason)
  | .cond c t eis s => match entfalteFrage k t with
    | .error e => .error e
    | .ok t' => match entfalteFrageL k eis with
      | .error e => .error e
      | .ok eis' => match s with
        | none => .ok (.cond c t' eis' none)
        | some b => match entfalteFrage k b with
          | .error e => .error e
          | .ok b' => .ok (.cond c t' eis' (some b'))
  | .elsif c b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.elsif c b')
  | .cases g arms => match entfalteFrageL k arms with
    | .error e => .error e
    | .ok arms' => .ok (.cases g arms')
  | .arm v bi b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.arm v bi b')
  | .each b o kk s m r i body => match entfalteFrage k body with
    | .error e => .error e
    | .ok body' => .ok (.each b o kk s m r i body')
  | .retry h b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.retry h b')
  | .loop h b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.loop h b')
  | .waive ns b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.waive ns b')
  | .trim o t b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.trim o t b')
  | .locks g o b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.locks g o b')
  | .watch d b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.watch d b')
  | .child b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.child b')
  | .grow a e b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.grow a e b')
  | .alloc m x t a w s => match s with
    | none => .ok (.alloc m x t a w none)
    | some b => match entfalteFrage k b with
      | .error e => .error e
      | .ok b' => .ok (.alloc m x t a w (some b'))
  | .bindElse x t e g b => match entfalteFrage k b with
    | .error e => .error e
    | .ok b' => .ok (.bindElse x t e g b')
  | .block ss e => match entfalteFrageL k ss with
    | .error e => .error e
    | .ok ss' => .ok (.block ss' e)
  | s => .ok s
/-- Expand `?` in a statement list. -/
def entfalteFrageL (k : FrageKontext) : List SAnw → Except String (List SAnw)
  | [] => .ok []
  | s :: ss => match entfalteFrage k s with
    | .error e => .error e
    | .ok s' => match entfalteFrageL k ss with
      | .error e => .error e
      | .ok ss' => .ok (s' :: ss')
end

/-- `?` over a shared channel unfolds to the explicit `else` form (definitional: the
    desugarer builds exactly the written-else node the plan demands). -/
theorem entfalteFrage_beispiel :
    entfalteFrageSchritt { eigen := some "R", ruf := [("g", some "R")], gruende := [("R", ["A", "B"])] }
      (.bindQ false "x" none (.call "g" [])) =
    .ok (.bindElse "x" none (.call "g" []) "#frage"
      (.block [.cases (.variable "#frage")
        [.arm "A" none (.block [] (some (.ret (some (.why "R" "A"))))),
         .arm "B" none (.block [] (some (.ret (some (.why "R" "B")))))]]
        (some (.ret (some (.why "R" "A")))))) := rfl

/-! ### Adapters: the ordinary function -/

/-- The dropped parameters of an adapter list. -/
def adaptEntfernt : List SAdaptParam → List String
  | [] => []
  | .ohne x :: rest => x :: adaptEntfernt rest
  | _ :: rest => adaptEntfernt rest

/-- Expand `..`/`-x`/new parameters against the source signature: `..` splices the kept
    source parameters in order, at most once; `-x` drops a parameter the source has; a new
    parameter stands nowhere else after expansion. -/
def erweitereParamsAux (q : List (String × STyp)) (entf : List String) :
    List SAdaptParam → List (String × STyp) → Except String (List (String × STyp))
  | [], acc => .ok acc
  | .alle :: rest, acc =>
    let kept := q.filter (fun p => !entf.any (strEq · p.1))
    match kept.find? (fun p => acc.any (fun a => strEq a.1 p.1)) with
    | some (n, _) => .error ("adapter parameter twice: " ++ n)
    | none => erweitereParamsAux q entf rest (acc ++ kept)
  | .ohne _ :: rest, acc => erweitereParamsAux q entf rest acc
  | .neu n t :: rest, acc =>
    if acc.any (fun p => strEq p.1 n) || q.any (fun p => strEq p.1 n) then
      .error ("adapter parameter twice: " ++ n)
    else erweitereParamsAux q entf rest (acc ++ [(n, t)])

def erweitereParams (q : List (String × STyp)) (ps : List SAdaptParam) :
    Except String (List (String × STyp)) :=
  let entf := adaptEntfernt ps
  match entf.find? (fun x => !(q.any (fun p => strEq p.1 x))) with
  | some x => .error ("adapter drops no parameter: " ++ x)
  | none =>
    if (ps.filter (fun | .alle => true | _ => false)).length > 1 then
      .error "adapter takes .. twice"
    else erweitereParamsAux q entf ps []

/-- The call of the source with every source parameter as a variable (dropped ones are
    prelude-bound). -/
def adaptRuf (q : FnSig) : SExpr :=
  .call q.name (q.params.map fun (n, _) => .variable n)

def adaptRufAnw (q : FnSig) : SAnw :=
  .call q.name (q.params.map fun (n, _) => .variable n)

/-- The statement binding the source answer: a plain call, `?`, or the explicit `else`. -/
def adaptBindung (q : FnSig) (sig : FnSig) (a : SAdapt) (binder : Option String) :
    Except String SAnw :=
  match q.fehler, sig.fehler with
  | none, _ => match binder with
    | none => .ok (adaptRufAnw q)
    | some b => .ok (.bind false b none (adaptRuf q))
  | some r, some e =>
    if strEq r e then match binder with
      | none => .ok (.callQ q.name (q.params.map fun (n, _) => .variable n))
      | some b => .ok (.bindQ false b none (adaptRuf q))
    else match a.sonst with
      | none => .error "adapter changes the reason channel without else"
      | some (g, blk) => .ok (.bindElse (binder.getD "#erg") none (adaptRuf q) g blk)
  | some _, none => match a.sonst with
    | none => .error "adapter drops the reason channel without else"
    | some (g, blk) => .ok (.bindElse (binder.getD "#erg") none (adaptRuf q) g blk)

mutual
/-- The call names of an expression. -/
def rufNamenE : SExpr → List String
  | .field a _ => rufNamenE a
  | .index a i => rufNamenE a ++ rufNamenE i
  | .arrow a _ => rufNamenE a
  | .un _ a => rufNamenE a
  | .bin _ a b => rufNamenE a ++ rufNamenE b
  | .call f args => f :: rufNamenEL args
  | .built _ args => rufNamenEL args
  | .old a => rufNamenE a
  | .ext _ _ xs => rufNamenEL xs
  | _ => []
/-- The call names of an expression list. -/
def rufNamenEL : List SExpr → List String
  | [] => []
  | e :: es => rufNamenE e ++ rufNamenEL es
end

mutual
/-- The call names of a statement, recursing into every block. -/
def rufNamenS : SAnw → List String
  | .bind _ _ _ e => rufNamenE e
  | .bindElse _ _ e _ b => rufNamenE e ++ rufNamenS b
  | .bindQ _ _ _ e => rufNamenE e
  | .set l _ r => rufNamenE l ++ rufNamenE r
  | .shift z _ _ => rufNamenE z
  | .call f args => f :: rufNamenEL args
  | .callQ f args => f :: rufNamenEL args
  | .cond c t eis s => rufNamenE c ++ rufNamenS t ++ rufNamenL eis ++
    (match s with | none => [] | some b => rufNamenS b)
  | .elsif c b => rufNamenE c ++ rufNamenS b
  | .cases g arms => rufNamenE g ++ rufNamenL arms
  | .arm _ _ b => rufNamenS b
  | .each _ _ _ s _ _ _ b => rufNamenE s ++ rufNamenS b
  | .retry _ b => rufNamenS b
  | .loop _ b => rufNamenS b
  | .waive _ b => rufNamenS b
  | .trim o _ b => rufNamenE o ++ rufNamenS b
  | .trimReq o _ => rufNamenE o
  | .locks _ o b => rufNamenE o ++ rufNamenS b
  | .watch _ b => rufNamenS b
  | .emit z w _ => rufNamenE z ++ rufNamenE w
  | .await _ _ q _ => rufNamenE q
  | .swap _ _ o _ => rufNamenE o
  | .ret e => match e with | none => [] | some v => rufNamenE v
  | .alloc _ _ _ _ w s => rufNamenE w ++ (match s with | none => [] | some b => rufNamenS b)
  | .reset _ rg => match rg with | none => [] | some (i, n) => rufNamenE i ++ rufNamenE n
  | .grow _ e b => rufNamenE e ++ rufNamenS b
  | .free a => rufNamenE a
  | .child b => rufNamenS b
  | .block ss _ => rufNamenL ss
  | _ => []
/-- The call names of a statement list. -/
def rufNamenL : List SAnw → List String
  | [] => []
  | s :: ss => rufNamenS s ++ rufNamenL ss
end

mutual
/-- The names a prelude binds, recursing into every block (leaves follow `gebunden`). -/
def bindNamenS : SAnw → List String
  | .block ss _ => bindNamenL ss
  | .cond _ t eis s => bindNamenS t ++ bindNamenL eis ++
    (match s with | none => [] | some b => bindNamenS b)
  | .elsif _ b => bindNamenS b
  | .cases _ arms => bindNamenL arms
  | .arm _ bi b => bi.toList ++ bindNamenS b
  | .each b _ _ _ _ _ _ body => b :: bindNamenS body
  | .retry _ b => bindNamenS b
  | .loop _ b => bindNamenS b
  | .waive _ b => bindNamenS b
  | .trim _ _ b => bindNamenS b
  | .trimReq _ _ => []
  | .locks _ _ b => bindNamenS b
  | .watch _ b => bindNamenS b
  | .child b => bindNamenS b
  | .grow _ _ b => bindNamenS b
  | .alloc _ x _ _ _ s => x :: (match s with | none => [] | some b => bindNamenS b)
  | .bindElse x _ _ g b => x :: g :: bindNamenS b
  | s => Gabbro.Grammatik.Parser.Aufloesung.gebunden s
/-- The names a prelude binds, list form. -/
def bindNamenL : List SAnw → List String
  | [] => []
  | s :: ss => bindNamenS s ++ bindNamenL ss
end

/-- Expand one adapter to the ordinary function and body (§4.1). -/
def entfalteAdapt (sigs : List FnSig) (sig : FnSig) (ps : List SAdaptParam) (a : SAdapt)
    (body : Option SAnw) : Except String (FnSig × SAnw) :=
  if !(strEq sig.art "" || strEq sig.art "impl") then .error "adapter modifier without G form"
  else match sigs.find? (fun q => strEq q.name a.quelle) with
  | none => .error ("adapter source unknown: " ++ a.quelle)
  | some q =>
    if strEq q.name sig.name then .error ("adapter calls itself: " ++ sig.name)
    else if strEq q.art "divergent" then .error ("adapter source is divergent: " ++ q.name)
    else
      let rufe := rufNamenL a.vorspiel
      if rufe.any (strEq · sig.name) then .error ("adapter called in its own prelude: " ++ sig.name)
      else if rufe.any (strEq · q.name) then
        .error ("adapter source called in its own prelude: " ++ q.name)
      else match erweitereParams q.params ps with
      | .error e => .error e
      | .ok params =>
        let geb := bindNamenL a.vorspiel
        match (adaptEntfernt ps).find? (fun x => !geb.any (strEq · x)) with
        | some x => .error ("adapter prelude must bind: " ++ x)
        | none =>
          let sig' : FnSig := { sig with params }
          match body with
          | none =>
            if !beqSTypOpt sig.res q.res then
              .error "short adapter body needs the source result type"
            else match adaptBindung q sig a (some "#erg") with
            | .error e => .error e
            | .ok stmt =>
              let ende : Option SEnde := match sig.res with
                | none => some (.ret none)
                | some _ => some (.ret (some (.variable "#erg")))
              .ok (sig', .block (a.vorspiel ++ [stmt]) ende)
          | some b => match b with
            | .block ss ende => match adaptBindung q sig a a.gebunden with
              | .error e => .error e
              | .ok stmt => .ok (sig', .block (a.vorspiel ++ [stmt] ++ ss) ende)
            | _ => .error "adapter body without G form"

/-- The function signatures of an item list (the desugarer runs on the flattened unit). -/
def sigsVon : List SItemTief → List FnSig
  | [] => []
  | .fnT s _ :: rest => s :: sigsVon rest
  | _ :: rest => sigsVon rest

/-- The reasons of an item list with their grounds. -/
def gruendeVon : List SItemTief → List (String × List String)
  | [] => []
  | .whyT n cs _ :: rest => (n, cs.map (·.1)) :: gruendeVon rest
  | _ :: rest => gruendeVon rest

/-- Resolve adapter signatures before collecting the reason-call environment. Otherwise a
    later `adapted(args) ?;` sees only the original functions and reports an unknown call. -/
def entfalteAdapterItem (sigs : List FnSig) : SItemTief → Except String SItemTief
  | .adaptT s ps a body => do
    let (signature, expanded) ← entfalteAdapt sigs s ps a body
    pure (.fnT signature expanded)
  | .gateT item => (entfalteAdapterItem sigs item).map SItemTief.gateT
  | item => pure item

/-- Expand reason propagation in ordinary and newly generated adapter functions. -/
def entfalteItem (ks : FrageKontext) : SItemTief → Except String SItemTief
  | .fnT s b => (entfalteFrage { ks with eigen := s.fehler } b).map (.fnT s)
  | .gateT item => (entfalteItem ks item).map SItemTief.gateT
  | .implGroupT name types effects bodies => do
    pure (.implGroupT name types effects (← bodies.mapM (entfalteItem ks)))
  | item => pure item

/-- The single Phase-1 expansion: adapters first, then `?` with their complete signatures.
    Adapter targets keep the existing ordinary-function admission rule. -/
def entzuckere (items : List SItemTief) : Except String (List SItemTief) := do
  let expanded ← items.mapM (entfalteAdapterItem (sigsVon items))
  let sigs := sigsVon (Spec.materialize expanded)
  let ks : FrageKontext :=
    { eigen := none, ruf := sigs.map (fun s => (s.name, s.fehler)), gruende := gruendeVon expanded }
  expanded.mapM (entfalteItem ks)

end Gabbro.Grammatik.Parser.Uebersetze
