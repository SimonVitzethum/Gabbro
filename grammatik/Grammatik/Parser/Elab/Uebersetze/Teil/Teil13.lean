module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
public import Grammatik.Parser.Elab.Modules.Frontend
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The sole source expansion path: modules, generic functions, spec calls and literals,
    followed by adapter/reason and tagged/dyn desugaring. Static obligations stay attached. -/
def expandU (items : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) :=
  Modules.prepare items

/-- Preserve canonical const-body admission before scope collection. Stage 0 supplies its
    separately certified evaluator for block-bodied constants. -/
def checkCanonicalConstants (msE : List SItemTief) : Except String Unit := do
  uRestFehler msE
  let blockiert := msE.find? (fun item => match item with
    | .fnT sig body => strEq sig.art "const" && (match body with
      | .block [] (some (.ret (some _))) => false
      | _ => true)
    | _ => false)
  if blockiert.isSome then
    (match (uKonstFns msE).find? (fun k => match k.rumpf with
      | .block [] (some (.ret (some _))) => false
      | _ => true) with
    | some k => (Gabbro.Grammatik.Parser.constBlockVerweigerung k).map (fun _ => ())
    | _ => .error "const function with a block body: certified evaluation unavailable") else
  pure ()

/-- Canonical scope collection on the expanded program. -/
def elabUExpanded (expanded : List SItemTief × List (STyp × String)) : Except String UProg := do
  let (msE, requirements) := expanded
  checkCanonicalConstants msE
  let consts := uConstsRech (uKonstFns msE) msE []
  let alias := uAliase consts msE ++ uAliasBreiten msE ++ consts.map (fun c => (c.1, (c.2, c.2)))
  elabExpandedWithScopes msE consts alias (uKonstFns (uOhneSenken msE)) (uTabelle consts alias) requirements

/-- Canonical export and Stage 0 consume the same expanded declarations and phase body. -/
def elabU (items : List SItemTief) : Except String UProg :=
  (expandU items).bind elabUExpanded

/-! ## Lowering: from U to the exporter's declaration universe -/

/-- The body context of `einzahlen`: its parameters. -/
abbrev UCtxEin := G104_referenz.gCtx_einzahlen

/-- The held resources of `einzahlen`. -/
abbrev ULEin := G104_referenz.gL_einzahlen

/-- The `ensures` type of `einzahlen`. -/
abbrev UEnsEin :=
  Expr G104_referenz.gD (ErgCtx (G104_referenz.gD.params G104_referenz.g_einzahlen) (G104_referenz.gD.erg G104_referenz.g_einzahlen))
    (vertragVon G104_referenz.gD G104_referenz.g_einzahlen).ende .bool

/-- The body type of `einzahlen`. -/
abbrev UKoerpEin :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen

/-- A parameter variable of `einzahlen` by position and type
    (positions are the known signature; anything else is an
    explicit error). -/
def varNumEin : (j : Nat) → (τ : Ty) → Except String (Var UCtxEin τ)
  | 0, .ptr (.table 0 (true, true)) => .ok .here
  | 1, .int 0 1 => .ok (.there .here)
  | 2, .int 0 10 => .ok (.there (.there .here))
  | _, _ => .error "parameter without G form"

/-- An index into `Konto` in `einzahlen`: the `i` parameter or
    a literal inside `count` (the `tr_index` of `lean_g.rs`,
    with the range check as an explicit error). -/
def lowerIdxEin : UIdx →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.there Var.here))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | _ => .error "index without G form"

/-- The field range recorded for (`Konto`, `stand`) must be
    the exporter's `(0, 100)`; otherwise the G term below
    would ascribe the wrong type silently. -/
def uFeldWeite (tabs : List UTab) (t f : String) (lo hi : Int) :
    Except String Unit :=
  match tabs.find? (fun x => strEq x.name t) with
  | .none => .error ("table unknown: " ++ t)
  | .some tb =>
    match tb.cols.find? (fun (g, _) => strEq g f) with
    | .none => .error "field unknown"
    | .some (_, (a, b)) =>
      if a == lo && b == hi then .ok () else .error "field range foreign"
/-- One side in `einzahlen`, with its range (the `tr_side` of
    `lean_g.rs`; a pointer parameter in a comparison is an
    explicit error). -/
structure USeiteT where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxEin ULEin (.int range.1 range.2)

def lowerSeiteEin (tabs : List UTab) (names : List String)
    (types : List Ty) : USide → Except String USeiteT
  | .truth _ | .predicate _ => .error "truth value as a number"
  | .taggedEmpty .. | .taggedValue .. | .option .. | .absent _ | .present .. |
    .reason .. | .function .. => .error "aggregate without G form in the 104 lowering"
  | .product .. | .field .. | .replace .. => .error "product without G form in the 104 lowering"
  | .glob _ => .error "static without G form in the 104 lowering"
  | .refSlot .. => .error "reference without G form in the 104 lowering"
  | .idx .. | .len _ | .text _ | .arrNil | .arrCons .. | .upd .. | .typed .. => .error "aggregate without G form in the 104 lowering"
  | .eng .. => .error "narrowing without G form in the 104 lowering"
  | .ib1 .. | .ib2 .. => .error "builtin without G form in the 104 lowering"
  | .zaehle .. | .zaehleBaum .. | .zaehleFeld .. => .error "count without G form in the 104 lowering"
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumEin j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100), term := Expr.thru (Expr.var Var.here) G104_referenz.GTab.Konto rfl G104_referenz.GKontoFeld.stand i G104_referenz.gDarf_einzahlen_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100), term := Expr.slot G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand i G104_referenz.gDarf_einzahlen_Konto }
  | .old b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100), term := Expr.oldS G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand i G104_referenz.gDarf_einzahlen_Konto }
  | .erg => .error "result in a body"
  | .add .. | .sub .. | .mul .. | .conv .. | .band .. | .bor .. | .bxor .. | .div .. | .rem .. | .shl .. | .shr .. | .neg .. =>
    .error "arithmetic without G form in the 104 lowering"
/-- One comparison in `einzahlen` (the `tr_cmp` of `lean_g.rs`;
    G folds all but `lt`/`le`/`eq`). -/
def lowerVglEin (tabs : List UTab) (names : List String)
    (types : List Ty) : String → USide → USide → Except String UEnsEin
  | op, a, b =>
    match lowerSeiteEin tabs names types a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEin tabs names types b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

end Gabbro.Grammatik.Parser.Uebersetze
