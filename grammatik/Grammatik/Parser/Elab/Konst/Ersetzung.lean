module

public import Grammatik.Parser.Elab.Konst.Replacement
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
  checked `Scalar.CheckedCall` retains the original parameter types, the
  body/predicate elaboration equations, the candidate computation and
  `Scalar.Function.Certificate.sound` for the ordinary machine G call.

  A const call contributes no runtime trace/call-log entry and no budget:
  closed arguments and exact literals read no places, so `World.lese` is the
  identity. Candidate evaluation is bounded by explicit compile-time fuel. Statement calls
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
  | .field (.variable _) _ => true
  | .un op e => (strEq op "-" || strEq op "!") && geschlossenSExprB e
  | .bin op a b =>
    (strEq op "+" || strEq op "-" || strEq op "*" || strEq op "/" ||
     strEq op "%" || strEq op "&" || strEq op "|" || strEq op "^" ||
     strEq op "<<" || strEq op ">>" || strEq op "==" || strEq op "!=" ||
     strEq op "<" || strEq op "<=" || strEq op ">" || strEq op ">=" ||
     strEq op "&&" || strEq op "||") && geschlossenSExprB a && geschlossenSExprB b
  | _ => false

def geschlossenSExprListB : List SExpr → Bool
  | [] => true
  | e :: rest => geschlossenSExprB e && geschlossenSExprListB rest

/-- Exact surface literal of a boolean. -/
def literalVonBool : Bool → SExpr
  | true => .tru
  | false => .fls

mutual
/-- Substitute certified const calls in one expression. Non-const calls
    keep their (recursively substituted) arguments; a const call with open
    arguments or without a certified value is an error naming the callee. -/
def ersetzeSExprIn (shadowed : List String) (fns : List UKonstFn) : SExpr → Except String SExpr
  | .lit n => .ok (.lit n)
  | .float s => .ok (.float s)
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .variable x => .ok (.variable x)
  | .field e m =>
    match ersetzeSExprIn shadowed fns e with
    | .error e => .error e
    | .ok e' => .ok (.field e' m)
  | .index a i =>
    match ersetzeSExprIn shadowed fns a, ersetzeSExprIn shadowed fns i with
    | .ok a', .ok i' => .ok (.index a' i')
    | .error e, _ | _, .error e => .error e
  | .arrow e m =>
    match ersetzeSExprIn shadowed fns e with
    | .error e => .error e
    | .ok e' => .ok (.arrow e' m)
  | .un op e =>
    match ersetzeSExprIn shadowed fns e with
    | .error e => .error e
    | .ok e' => .ok (.un op e')
  | .bin op a b =>
    match ersetzeSExprIn shadowed fns a, ersetzeSExprIn shadowed fns b with
    | .ok a', .ok b' => .ok (.bin op a' b')
    | .error e, _ | _, .error e => .error e
  | .call g args =>
    match ersetzeSExprListIn shadowed fns args with
    | .error e => .error e
    | .ok args' =>
      match fns.find? (fun k => strEq k.name g) with
      | none => .ok (.call g args')
      | some k =>
        let values := k.constants.filter (fun entry => !shadowed.contains entry.1)
        let normalized := args'.map (Scalar.normalizeNames ([] : Scalar.Locals []) values)
        if !geschlossenSExprListB normalized then
          .error ("const open argument at `" ++ g ++ "`: certified substitution needs closed arguments")
        else do
          let checked ← checkReplacement k fns values args'
          pure checked.syntax
  | .fnref f => .ok (.fnref f)
  | .built f args =>
    match ersetzeSExprListIn shadowed fns args with
    | .error e => .error e
    | .ok args' => .ok (.built f args')
  | .old e =>
    match ersetzeSExprIn shadowed fns e with
    | .error e => .error e
    | .ok e' => .ok (.old e')
  | .res => .ok .res
  | .why g f => .ok (.why g f)
  | .ext kind (binder :: domain :: names) subs =>
    if kind == .all || kind == .any || kind == .count then
      (ersetzeQuantOperandsIn shadowed fns binder subs).map (.ext kind (binder :: domain :: names))
    else (ersetzeSExprListIn shadowed fns subs).map (.ext kind (binder :: domain :: names))
  | .ext k names subs =>
    match ersetzeSExprListIn shadowed fns subs with
    | .error e => .error e
    | .ok subs' => .ok (.ext k names subs')
def ersetzeSExprListIn (shadowed : List String) (fns : List UKonstFn) : List SExpr → Except String (List SExpr)
  | [] => .ok []
  | e :: rest =>
    match ersetzeSExprIn shadowed fns e, ersetzeSExprListIn shadowed fns rest with
    | .ok e', .ok rest' => .ok (e' :: rest')
    | .error e, _ | _, .error e => .error e
/-- Only the last quantifier operand is scoped by its binder. -/
def ersetzeQuantOperandsIn (shadowed : List String) (fns : List UKonstFn) (binder : String) :
    List SExpr → Except String (List SExpr)
  | [] => .ok []
  | [body] => (ersetzeSExprIn (binder :: shadowed) fns body).map (fun body => [body])
  | operand :: rest => do
    return (← ersetzeSExprIn shadowed fns operand) :: (← ersetzeQuantOperandsIn shadowed fns binder rest)

end

/-- Names introduced by a statement belong to its continuation only. -/
def boundNames : SAnw → List String
  | .bind _ name _ _ | .bindQ _ name _ _ | .bindElse name _ _ _ _ |
    .bindAxiomOpt name _ _ | .bindAxiomOptElse name _ _ _ _ | .bindLib _ name _ _ |
    .alloc _ name _ _ _ _ | .allocVon _ name _ _ | .await name _ _ _ | .swap name _ _ _ => [name]
  | _ => []

mutual
/-- Substitute in one statement body. Value positions recurse;
    statement calls (`SAnw.call`) are left for the downstream refusal:
    they would appear in a call log observed by `FolgeG`. -/
def ersetzeSAnwIn (shadowed : List String) (fns : List UKonstFn) : SAnw → Except String SAnw
  | .bind m n ty v =>
    match ersetzeSExprIn shadowed fns v with
    | .error e => .error e
    | .ok v' => .ok (.bind m n ty v')
  | .bindElse n ty v x b =>
    match ersetzeSExprIn shadowed fns v, ersetzeSAnwIn (x :: shadowed) fns b with
    | .ok v', .ok b' => .ok (.bindElse n ty v' x b')
    | .error e, _ | _, .error e => .error e
  | .bindQ m n ty v =>
    (ersetzeSExprIn shadowed fns v).map (fun v' => .bindQ m n ty v')
  | .bindAxiomOpt n ty v =>
    (ersetzeSExprIn shadowed fns v).map (fun v' => .bindAxiomOpt n ty v')
  | .bindAxiomOptElse n ty v x b =>
    match ersetzeSExprIn shadowed fns v, ersetzeSAnwIn (x :: shadowed) fns b with
    | .ok v', .ok b' => .ok (.bindAxiomOptElse n ty v' x b')
    | .error e, _ | _, .error e => .error e
  | .bindLib m n ty c => .ok (.bindLib m n ty c)
  | .set z op x =>
    match ersetzeSExprIn shadowed fns z, ersetzeSExprIn shadowed fns x with
    | .ok z', .ok x' => .ok (.set z' op x')
    | .error e, _ | _, .error e => .error e
  | .shift z a b =>
    match ersetzeSExprIn shadowed fns z with
    | .error e => .error e
    | .ok z' => .ok (.shift z' a b)
  | .call f args =>
    match ersetzeSExprListIn shadowed fns args with
    | .error e => .error e
    | .ok args' => .ok (.call f args')
  | .callIndElse pointer args reason body => do
    let pointer ← ersetzeSExprIn shadowed fns pointer
    let args ← ersetzeSExprListIn shadowed fns args
    let body ← ersetzeSAnwIn (reason :: shadowed) fns body
    pure (.callIndElse pointer args reason body)
  | .callElse name args reason body => do
    let args ← ersetzeSExprListIn shadowed fns args
    let body ← ersetzeSAnwIn (reason :: shadowed) fns body
    pure (.callElse name args reason body)
  | .callQ f args =>
    (ersetzeSExprListIn shadowed fns args).map (fun args' => .callQ f args')
  | .genericCall f words args =>
    (ersetzeSExprListIn shadowed fns args).map (fun args' => .genericCall f words args')
  | .lcall c => .ok (.lcall c)
  | .cond c t eis fb =>
    match ersetzeSExprIn shadowed fns c, ersetzeSAnwIn shadowed fns t, ersetzeSAnwListIn shadowed fns eis with
    | .ok c', .ok t', .ok eis' =>
      match fb with
      | none => .ok (.cond c' t' eis' none)
      | some f =>
        match ersetzeSAnwIn shadowed fns f with
        | .ok f' => .ok (.cond c' t' eis' (some f'))
        | .error e => .error e
    | .error e, _, _ | _, .error e, _ | _, _, .error e => .error e
  | .elsif c b =>
    match ersetzeSExprIn shadowed fns c, ersetzeSAnwIn shadowed fns b with
    | .ok c', .ok b' => .ok (.elsif c' b')
    | .error e, _ | _, .error e => .error e
  | .cases g arms =>
    match ersetzeSExprIn shadowed fns g, ersetzeSAnwListIn shadowed fns arms with
    | .ok g', .ok arms' => .ok (.cases g' arms')
    | .error e, _ | _, .error e => .error e
  | .arm v b t =>
    match ersetzeSAnwIn (b.toList ++ shadowed) fns t with
    | .error e => .error e
    | .ok t' => .ok (.arm v b t')
  | .each b o k s m r i d =>
    match o, ersetzeSExprIn shadowed fns s with
    | _, .error e => .error e
    | none, .ok s' =>
      match i, ersetzeSAnwIn (b :: shadowed) fns d with
      | none, .ok d' => .ok (.each b none k s' m r none d')
      | some iv, .ok d' =>
        match ersetzeSExprIn (b :: shadowed) fns iv with
        | .ok iv' => .ok (.each b none k s' m r (some iv') d')
        | .error e => .error e
      | _, .error e => .error e
    | some ov, .ok s' =>
      match ersetzeSExprIn shadowed fns ov with
      | .error e => .error e
      | .ok ov' =>
        match i, ersetzeSAnwIn (b :: shadowed) fns d with
        | none, .ok d' => .ok (.each b (some ov') k s' m r none d')
        | some iv, .ok d' =>
          match ersetzeSExprIn (b :: shadowed) fns iv with
          | .ok iv' => .ok (.each b (some ov') k s' m r (some iv') d')
          | .error e => .error e
        | _, .error e => .error e
  | .retry h b =>
    match ersetzeSAnwIn shadowed fns b with
    | .error e => .error e
    | .ok b' => .ok (.retry h b')
  | .loop h b =>
    match ersetzeSAnwIn shadowed fns b with
    | .error e => .error e
    | .ok b' => .ok (.loop h b')
  | .waive inv b =>
    match ersetzeSAnwIn shadowed fns b with
    | .error e => .error e
    | .ok b' => .ok (.waive inv b')
  | .trim o z s =>
    match ersetzeSExprIn shadowed fns o, ersetzeSAnwIn shadowed fns s with
    | .ok o', .ok s' => .ok (.trim o' z s')
    | .error e, _ | _, .error e => .error e
  | .trimReq o z =>
    match ersetzeSExprIn shadowed fns o with
    | .error e => .error e
    | .ok o' => .ok (.trimReq o' z)
  | .locks g o b =>
    match ersetzeSExprIn shadowed fns o, ersetzeSAnwIn shadowed fns b with
    | .ok o', .ok b' => .ok (.locks g o' b')
    | .error e, _ | _, .error e => .error e
  | .watch d b =>
    match ersetzeSAnwIn shadowed fns b with
    | .error e => .error e
    | .ok b' => .ok (.watch d b')
  | .leave l => .ok (.leave l)
  | .next l => .ok (.next l)
  | .emit z w p =>
    match ersetzeSExprIn shadowed fns z, ersetzeSExprIn shadowed fns w with
    | .ok z', .ok w' => .ok (.emit z' w' p)
    | .error e, _ | _, .error e => .error e
  | .await n ty q e =>
    match ersetzeSExprIn shadowed fns q with
    | .error e => .error e
    | .ok q' => .ok (.await n ty q' e)
  | .swap n ty o k =>
    match ersetzeSExprIn shadowed fns o with
    | .error e => .error e
    | .ok o' => .ok (.swap n ty o' k)
  | .retires m => .ok (.retires m)
  | .step a b => .ok (.step a b)
  | .ret x =>
    match x with
    | none => .ok (.ret none)
    | some e =>
      match ersetzeSExprIn shadowed fns e with
      | .error err => .error err
      | .ok e' => .ok (.ret (some e'))
  | .alloc m n ty t v s =>
    match ersetzeSExprIn shadowed fns v with
    | .error e => .error e
    | .ok v' =>
      match s with
      | none => .ok (.alloc m n ty t v' none)
      | some b =>
        match ersetzeSAnwIn shadowed fns b with
        | .ok b' => .ok (.alloc m n ty t v' (some b'))
        | .error e => .error e
  | .reset a r =>
    match r with
    | none => .ok (.reset a none)
    | some (x, y) =>
      match ersetzeSExprIn shadowed fns x, ersetzeSExprIn shadowed fns y with
      | .ok x', .ok y' => .ok (.reset a (some (x', y')))
      | .error e, _ | _, .error e => .error e
  | .grow a e b =>
    match ersetzeSExprIn shadowed fns e, ersetzeSAnwIn shadowed fns b with
    | .ok e', .ok b' => .ok (.grow a e' b')
    | .error e, _ | _, .error e => .error e
  | .free e =>
    match ersetzeSExprIn shadowed fns e with
    | .error err => .error err
    | .ok e' => .ok (.free e')
  | .child b =>
    match ersetzeSAnwIn shadowed fns b with
    | .error e => .error e
    | .ok b' => .ok (.child b')
  | .start ss => .ok (.start ss)
  | .other s => .ok (.other s)
  | .block ss e =>
    match ersetzeSAnwListIn shadowed fns ss with
    | .error err => .error err
    | .ok ss' =>
      match e with
      | none => .ok (.block ss' none)
      | some (.ret x) =>
        match x with
        | none => .ok (.block ss' (some (.ret none)))
        | some v =>
          match ersetzeSExprIn (ss.flatMap boundNames ++ shadowed) fns v with
          | .error err => .error err
          | .ok v' => .ok (.block ss' (some (.ret (some v'))))
      | some (.leave l) => .ok (.block ss' (some (.leave l)))
      | some (.next l) => .ok (.block ss' (some (.next l)))
  | .allocVon m n ty t => .ok (.allocVon m n ty t)
def ersetzeSAnwListIn (shadowed : List String) (fns : List UKonstFn) : List SAnw → Except String (List SAnw)
  | [] => .ok []
  | a :: rest =>
    match ersetzeSAnwIn shadowed fns a, ersetzeSAnwListIn (boundNames a ++ shadowed) fns rest with
    | .ok a', .ok rest' => .ok (a' :: rest')
    | .error e, _ | _, .error e => .error e

end

/-- The public empty-context entry points retain the single traversal above. -/
abbrev ersetzeSExpr := ersetzeSExprIn []
abbrev ersetzeSAnw := ersetzeSAnwIn []

/-- Success of the actual call branch supplies its certificate; original argument
    expressions reach checkReplacement before any name normalization is erased. -/
theorem ersetzeSExpr_call_certified (shadowed : List String) (fns : List UKonstFn) (name : String)
    (args args' : List SExpr) (fn : UKonstFn) (replacement : SExpr)
    (arguments : ersetzeSExprListIn shadowed fns args = .ok args')
    (callee : fns.find? (fun k => strEq k.name name) = some fn)
    (success : ersetzeSExprIn shadowed fns (.call name args) = .ok replacement) :
    ∃ checked : Replacement fn fns (fn.constants.filter (fun entry => !shadowed.contains entry.1)) args',
      checkReplacement fn fns (fn.constants.filter (fun entry => !shadowed.contains entry.1)) args' = .ok checked ∧
      replacement = checked.syntax ∧ checked.evidence.Sound := by
  simp only [ersetzeSExprIn, arguments, callee] at success
  split at success
  · contradiction
  · cases hc : checkReplacement fn fns (fn.constants.filter (fun entry => !shadowed.contains entry.1)) args' with
    | error error =>
      simp only [hc, bind, Except.bind, pure, Except.pure] at success
      change (Except.error error : Except String SExpr) = Except.ok replacement at success
      cases success
    | ok checked =>
      simp only [hc, bind, Except.bind, pure, Except.pure] at success
      change (Except.ok checked.syntax : Except String SExpr) = Except.ok replacement at success
      exact ⟨checked, rfl, (Except.ok.inj success).symm, checked.sound⟩

end Gabbro.Grammatik.Parser.Konst
