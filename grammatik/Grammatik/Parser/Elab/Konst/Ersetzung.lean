module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section

namespace Gabbro.Grammatik.Parser.Konst

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.ExportMetadata

/-! ## Source call-site substitution for `const` functions.

  Position: after name resolution and the checked const/type views
  (`uMembers`, `uConstsRech`, `uAliase`), BEFORE `fnItems`/`elabUFunktion`
  and the export metadata gate. The exporter (`elabU`) and Stage 0
  (`elabWithScopes`) drop `const` declarations; programs that CALL them are
  refused unless this pass replaces every such call by the literal of its
  certified value. `uKonstWert` is only the candidate generator: the
  justification is `ConstAdmissible` (`constAdmissibleB_iff`), the checked
  certificate (`ConstCallCertificate`, `evalConstCall`), its generic meaning
  (`const_call_sound`), the source derivation (`ConstElaborates`) and its
  source meaning (`const_source_call_sound`).

  A const call contributes no runtime trace/call-log entry and no budget:
  closed arguments and exact literals read no places, so `World.lese` is the
  identity, and the work bound is checked at compile time. Statement calls
  (`SAnw.call`) are NOT substituted here: they would appear in a thread
  call log observed by `FolgeG`, so they keep their refusal; likewise any
  timing duty `ZeitAb` would observe stays refused. Only value positions
  (`SExpr.call` of an admitted const function with closed arguments) are
  replaced, and every other const-call shape keeps the program refused. -/

/-- Closed source arguments: literals, the negative form, truth values and
    the integer operators `uKonstWert` evaluates. Variables, calls, fields
    and everything else are open and keep the program refused. -/
def geschlossenSExprB : SExpr → Bool
  | .lit _ => true
  | .tru => true
  | .fls => true
  | .un "-" (.lit _) => true
  | .bin op a b =>
    (strEq op "+" || strEq op "-" || strEq op "*" || strEq op "/" ||
     strEq op "%" || strEq op "&" || strEq op "|" || strEq op "^" ||
     strEq op "<<" || strEq op ">>") && geschlossenSExprB a && geschlossenSExprB b
  | _ => false

def geschlossenSExprListB : List SExpr → Bool
  | [] => true
  | e :: rest => geschlossenSExprB e && geschlossenSExprListB rest

/-- Exact surface literal of an integer: non-negative as `.lit`,
    negative via the negative form `.un "-" (.lit _)`. -/
def literalVonInt : Int → SExpr
  | v => if 0 ≤ v then .lit v.toNat else .un "-" (.lit (-v).toNat)

/-- Exact surface literal of a boolean. -/
def literalVonBool : Bool → SExpr
  | true => .tru
  | false => .fls

mutual
/-- Substitute certified const calls in one expression. Non-const calls
    keep their (recursively substituted) arguments; a const call with open
    arguments or without a certified value is an error naming the callee. -/
def ersetzeSExpr (fns : List UKonstFn) : SExpr → Except String SExpr
  | .lit n => .ok (.lit n)
  | .float s => .ok (.float s)
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .variable x => .ok (.variable x)
  | .field e m =>
    match ersetzeSExpr fns e with
    | .error e => .error e
    | .ok e' => .ok (.field e' m)
  | .index a i =>
    match ersetzeSExpr fns a, ersetzeSExpr fns i with
    | .ok a', .ok i' => .ok (.index a' i')
    | .error e, _ | _, .error e => .error e
  | .arrow e m =>
    match ersetzeSExpr fns e with
    | .error e => .error e
    | .ok e' => .ok (.arrow e' m)
  | .un op e =>
    match ersetzeSExpr fns e with
    | .error e => .error e
    | .ok e' => .ok (.un op e')
  | .bin op a b =>
    match ersetzeSExpr fns a, ersetzeSExpr fns b with
    | .ok a', .ok b' => .ok (.bin op a' b')
    | .error e, _ | _, .error e => .error e
  | .call g args =>
    match ersetzeSExprList fns args with
    | .error e => .error e
    | .ok args' =>
      match fns.find? (fun k => strEq k.name g) with
      | none => .ok (.call g args')
      | some k =>
        if !geschlossenSExprListB args' then
          .error ("const open argument at `" ++ g ++ "`: certified substitution needs closed arguments")
        else
          match k.erg, k.rumpf with
          | .int lo hi, .block [] (some (.ret (some _))) =>
            match uKonstWert lo hi fns [] 64 (.call g args') with
            | some v => .ok (literalVonInt v)
            | none => .error ("const uncertified call at `" ++ g ++ "`: no certified value in range")
          | .bool, .block [] (some (.ret (some _))) =>
            match uKonstWert 0 1 fns [] 64 (.call g args') with
            | some v => .ok (literalVonBool (v != 0))
            | none => .error ("const uncertified call at `" ++ g ++ "`: no certified value in range")
          | _, _ => .error ("const block body at `" ++ g ++ "`: certified evaluation unavailable")
  | .fnref f => .ok (.fnref f)
  | .built f args =>
    match ersetzeSExprList fns args with
    | .error e => .error e
    | .ok args' => .ok (.built f args')
  | .old e =>
    match ersetzeSExpr fns e with
    | .error e => .error e
    | .ok e' => .ok (.old e')
  | .res => .ok .res
  | .why g f => .ok (.why g f)
  | .ext k names subs =>
    match ersetzeSExprList fns subs with
    | .error e => .error e
    | .ok subs' => .ok (.ext k names subs')
def ersetzeSExprList (fns : List UKonstFn) : List SExpr → Except String (List SExpr)
  | [] => .ok []
  | e :: rest =>
    match ersetzeSExpr fns e, ersetzeSExprList fns rest with
    | .ok e', .ok rest' => .ok (e' :: rest')
    | .error e, _ | _, .error e => .error e
end

mutual
/-- Substitute in one statement body. Value positions recurse;
    statement calls (`SAnw.call`) are left for the downstream refusal:
    they would appear in a call log observed by `FolgeG`. -/
def ersetzeSAnw (fns : List UKonstFn) : SAnw → Except String SAnw
  | .bind m n ty v =>
    match ersetzeSExpr fns v with
    | .error e => .error e
    | .ok v' => .ok (.bind m n ty v')
  | .bindElse n ty v x b =>
    match ersetzeSExpr fns v, ersetzeSAnw fns b with
    | .ok v', .ok b' => .ok (.bindElse n ty v' x b')
    | .error e, _ | _, .error e => .error e
  | .bindQ m n ty v =>
    (ersetzeSExpr fns v).map (fun v' => .bindQ m n ty v')
  | .bindAxiomOpt n ty v =>
    (ersetzeSExpr fns v).map (fun v' => .bindAxiomOpt n ty v')
  | .bindAxiomOptElse n ty v x b =>
    match ersetzeSExpr fns v, ersetzeSAnw fns b with
    | .ok v', .ok b' => .ok (.bindAxiomOptElse n ty v' x b')
    | .error e, _ | _, .error e => .error e
  | .bindLib m n ty c => .ok (.bindLib m n ty c)
  | .set z op x =>
    match ersetzeSExpr fns z, ersetzeSExpr fns x with
    | .ok z', .ok x' => .ok (.set z' op x')
    | .error e, _ | _, .error e => .error e
  | .shift z a b =>
    match ersetzeSExpr fns z with
    | .error e => .error e
    | .ok z' => .ok (.shift z' a b)
  | .call f args =>
    match ersetzeSExprList fns args with
    | .error e => .error e
    | .ok args' => .ok (.call f args')
  | .callQ f args =>
    (ersetzeSExprList fns args).map (fun args' => .callQ f args')
  | .genericCall f words args =>
    (ersetzeSExprList fns args).map (fun args' => .genericCall f words args')
  | .lcall c => .ok (.lcall c)
  | .cond c t eis fb =>
    match ersetzeSExpr fns c, ersetzeSAnw fns t, ersetzeSAnwList fns eis with
    | .ok c', .ok t', .ok eis' =>
      match fb with
      | none => .ok (.cond c' t' eis' none)
      | some f =>
        match ersetzeSAnw fns f with
        | .ok f' => .ok (.cond c' t' eis' (some f'))
        | .error e => .error e
    | .error e, _, _ | _, .error e, _ | _, _, .error e => .error e
  | .elsif c b =>
    match ersetzeSExpr fns c, ersetzeSAnw fns b with
    | .ok c', .ok b' => .ok (.elsif c' b')
    | .error e, _ | _, .error e => .error e
  | .cases g arms =>
    match ersetzeSExpr fns g, ersetzeSAnwList fns arms with
    | .ok g', .ok arms' => .ok (.cases g' arms')
    | .error e, _ | _, .error e => .error e
  | .arm v b t =>
    match ersetzeSAnw fns t with
    | .error e => .error e
    | .ok t' => .ok (.arm v b t')
  | .each b o k s m r i d =>
    match o, ersetzeSExpr fns s with
    | _, .error e => .error e
    | none, .ok s' =>
      match i, ersetzeSAnw fns d with
      | none, .ok d' => .ok (.each b none k s' m r none d')
      | some iv, .ok d' =>
        match ersetzeSExpr fns iv with
        | .ok iv' => .ok (.each b none k s' m r (some iv') d')
        | .error e => .error e
      | _, .error e => .error e
    | some ov, .ok s' =>
      match ersetzeSExpr fns ov with
      | .error e => .error e
      | .ok ov' =>
        match i, ersetzeSAnw fns d with
        | none, .ok d' => .ok (.each b (some ov') k s' m r none d')
        | some iv, .ok d' =>
          match ersetzeSExpr fns iv with
          | .ok iv' => .ok (.each b (some ov') k s' m r (some iv') d')
          | .error e => .error e
        | _, .error e => .error e
  | .retry h b =>
    match ersetzeSAnw fns b with
    | .error e => .error e
    | .ok b' => .ok (.retry h b')
  | .loop h b =>
    match ersetzeSAnw fns b with
    | .error e => .error e
    | .ok b' => .ok (.loop h b')
  | .waive inv b =>
    match ersetzeSAnw fns b with
    | .error e => .error e
    | .ok b' => .ok (.waive inv b')
  | .trim o z s =>
    match ersetzeSExpr fns o, ersetzeSAnw fns s with
    | .ok o', .ok s' => .ok (.trim o' z s')
    | .error e, _ | _, .error e => .error e
  | .trimReq o z =>
    match ersetzeSExpr fns o with
    | .error e => .error e
    | .ok o' => .ok (.trimReq o' z)
  | .locks g o b =>
    match ersetzeSExpr fns o, ersetzeSAnw fns b with
    | .ok o', .ok b' => .ok (.locks g o' b')
    | .error e, _ | _, .error e => .error e
  | .watch d b =>
    match ersetzeSAnw fns b with
    | .error e => .error e
    | .ok b' => .ok (.watch d b')
  | .leave l => .ok (.leave l)
  | .next l => .ok (.next l)
  | .emit z w p =>
    match ersetzeSExpr fns z, ersetzeSExpr fns w with
    | .ok z', .ok w' => .ok (.emit z' w' p)
    | .error e, _ | _, .error e => .error e
  | .await n ty q e =>
    match ersetzeSExpr fns q with
    | .error e => .error e
    | .ok q' => .ok (.await n ty q' e)
  | .swap n ty o k =>
    match ersetzeSExpr fns o with
    | .error e => .error e
    | .ok o' => .ok (.swap n ty o' k)
  | .retires m => .ok (.retires m)
  | .step a b => .ok (.step a b)
  | .ret x =>
    match x with
    | none => .ok (.ret none)
    | some e =>
      match ersetzeSExpr fns e with
      | .error err => .error err
      | .ok e' => .ok (.ret (some e'))
  | .alloc m n ty t v s =>
    match ersetzeSExpr fns v with
    | .error e => .error e
    | .ok v' =>
      match s with
      | none => .ok (.alloc m n ty t v' none)
      | some b =>
        match ersetzeSAnw fns b with
        | .ok b' => .ok (.alloc m n ty t v' (some b'))
        | .error e => .error e
  | .reset a r =>
    match r with
    | none => .ok (.reset a none)
    | some (x, y) =>
      match ersetzeSExpr fns x, ersetzeSExpr fns y with
      | .ok x', .ok y' => .ok (.reset a (some (x', y')))
      | .error e, _ | _, .error e => .error e
  | .grow a e b =>
    match ersetzeSExpr fns e, ersetzeSAnw fns b with
    | .ok e', .ok b' => .ok (.grow a e' b')
    | .error e, _ | _, .error e => .error e
  | .free e =>
    match ersetzeSExpr fns e with
    | .error err => .error err
    | .ok e' => .ok (.free e')
  | .child b =>
    match ersetzeSAnw fns b with
    | .error e => .error e
    | .ok b' => .ok (.child b')
  | .start ss => .ok (.start ss)
  | .other s => .ok (.other s)
  | .block ss e =>
    match ersetzeSAnwList fns ss with
    | .error err => .error err
    | .ok ss' =>
      match e with
      | none => .ok (.block ss' none)
      | some (.ret x) =>
        match x with
        | none => .ok (.block ss' (some (.ret none)))
        | some v =>
          match ersetzeSExpr fns v with
          | .error err => .error err
          | .ok v' => .ok (.block ss' (some (.ret (some v'))))
      | some (.leave l) => .ok (.block ss' (some (.leave l)))
      | some (.next l) => .ok (.block ss' (some (.next l)))
  | .allocVon m n ty t => .ok (.allocVon m n ty t)
def ersetzeSAnwList (fns : List UKonstFn) : List SAnw → Except String (List SAnw)
  | [] => .ok []
  | a :: rest =>
    match ersetzeSAnw fns a, ersetzeSAnwList fns rest with
    | .ok a', .ok rest' => .ok (a' :: rest')
    | .error e, _ | _, .error e => .error e
def ersetzeOptAnw (fns : List UKonstFn) : Option SAnw → Except String (Option SAnw)
  | none => .ok none
  | some a =>
    match ersetzeSAnw fns a with
    | .error e => .error e
    | .ok a' => .ok (some a')
end

end Gabbro.Grammatik.Parser.Konst
