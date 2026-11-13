module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The header of a `retry`: the label, the pass bound, the predicate, the handler. `progress` must name an
    `assume` item. -/
def uRetryKopf (ctx : UCtx) (h : String) : Except String (String × Nat × UEns × String) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "until", uOpsZahl ctx (uAbschnitt secs "bounded"), uEinName (uAbschnitt secs "progress"),
        uEinName (uAbschnitt secs "on_exceeded") with
    | some pt, some n, some a, some y =>
      if !(ctx.annahmen.any (strEq · a)) then .error ("assumption unknown: " ++ a)
      else
        match parseTop (pt ++ [Token.ende]) with
        | .error _ => .error "retry condition without G form"
        | .ok p =>
          match uBool ctx p with
          | .error e => .error e
          | .ok pv => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), n, pv, y)
    | none, _, _, _ => .error "retry without until without G form"
    | _, _, _, _ => .error "retry header without G form"

/-- The header of a `forever`: the label and the position of the assumption `progress` names. -/
def uForeverKopf (ctx : UCtx) (h : String) : Except String (String × Nat) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "leaves" with
    | some _ => .error "forever leaves without G form"
    | none =>
      match uEinName (uAbschnitt secs "progress") with
      | none => .error "forever without progress without G form"
      | some a =>
        match ctx.annahmen.findIdx? (fun x => strEq x a) with
        | none => .error ("assumption unknown: " ++ a)
        | some k => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), k)

/-- The header of `traverse b over slots of S by unvisited [touches …] [invariant p]`: the table (named
    directly or through a pointer parameter), the invariant over the OUTER context (the binder is not in
    scope there), and the context of the body, where the binder is an index into the table and the
    innermost loop label. Other domains, `of e` and `by consuming` have no G form. -/
def uSchleifenKopf (ctx : UCtx) (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m : String)
    (inv : Option SExpr) : Except String (String × UEns × UCtx) :=
  if o.isSome then .error "traverse of without G form"
  else if !strEq k "slots" then .error "traverse domain without G form"
  else if !strEq m "unvisited" then .error "traverse by consuming without G form"
  else
    match (match s with
        | .variable tn =>
          match ctx.tabs.findIdx? (fun x => strEq x.name tn) with
          | .some num => .ok (tn, num)
          | .none =>
            match uParamNr ctx tn with
            | .error e => .error e
            | .ok j =>
              match uArtBei ctx.kinds j with
              | .ok (.ptr ⟨_, _, .table num⟩) =>
                match ctx.tabs[num]? with
                | .some tb => .ok (tb.name, num)
                | .none => .error "pointer table unknown"
              | _ => .error "traverse domain without G form"
        | _ => .error "traverse domain without G form" : Except String (String × Nat)) with
    | .error e => .error e
    | .ok (tab, num) =>
      match (match inv with
          | .none => .ok UEns.tru
          | .some p => uBool ctx p : Except String UEns) with
      | .error e => .error e
      | .ok iv =>
        let cnt : Int := match ctx.tabs[num]? with | .some tb => tb.count | .none => 0
        .ok (tab, iv, { ctx with names := b :: ctx.names, kinds := .index num :: ctx.kinds,
                                 types := .index cnt :: ctx.types, bits := 0 :: ctx.bits,
                                 loops := b :: ctx.loops })


end Gabbro.Grammatik.Parser.Uebersetze
