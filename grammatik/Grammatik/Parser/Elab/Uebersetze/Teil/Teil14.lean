module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- One `ensures` predicate in `einzahlen`. -/
def lowerSichertEin (tabs : List UTab) (names : List String)
    (types : List Ty) : UEns → Except String UEnsEin
  | .globB _ | .var _ | .ergB => .error "static without G form in the 104 lowering"
  | .alle .. | .einige .. => .error "quantifier without G form in the 104 lowering"
  | .cmp op a b => lowerVglEin tabs names types op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs names types b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs names types b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowerSichertEin tabs names types a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .slotB .. | .tabB .. => .error "bool place without G form in the 104 lowering"
  | .held .. => .error "held predicate without G form in the 104 lowering"
  | .imp .. => .error "implication without G form in the 104 lowering"
  | .reach .. | .member .. | .filtered .. | .arrayElements .. => .error "source relation without G form in the 104 lowering"
  | .istSome .. => .error "option test without G form in the 104 lowering"

/-- The `ensures` conjunction in `einzahlen` (empty is `.tru`,
    like the exporter's conjunction). -/
def lowerSichertListeEin (tabs : List UTab) (names : List String)
    (types : List Ty) : List UEns → Except String UEnsEin
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowerSichertEin tabs names types e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeEin tabs names types rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

/-- A value at an expected range in `einzahlen` (the
    `tr_value`/`fit` of `lean_g.rs`: literals widen with their
    proofs from the data, parameters widen from their recorded
    range, slot reads widen from the field range). -/
def lowerWertEin (tabs : List UTab) (names : List String)
    (types : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "literal outside"
    else .error "literal outside"
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumEin j (.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.widen h1 h2 (Expr.var v))
              else .error "parameter outside"
            else .error "parameter outside"
      | _, _ => .error "parameter without G form"
  | s =>
    match lowerSeiteEin tabs names types s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.range.1 then
        if h2 : t.range.2 ≤ hi then .ok (Expr.widen h1 h2 t.term)
        else .error "value outside"
      else .error "value outside"

/-- The statement type of `einzahlen` (all straight-line steps
    keep the held resources). -/
abbrev UStmtEin :=
  Stmt G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin ULEin ULEin

/-- A slot write in `einzahlen` (the assignment arm of
    `tr_stmt`; through a pointer it needs the `rw` right). -/
def lowerAssignEin (tabs : List UTab) (names : List String)
    (types : List Ty) : String → String → UIdx → USide →
    Except String UStmtEin
  | b, f, ix, v =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "write place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerWertEin tabs names types 0 100 v with
        | .error e => .error e
        | .ok w =>
          match lowerIdxEin ix with
          | .error e => .error e
          | .ok i =>
            if strEq b "k" then
              .ok (Stmt.assignThru (Expr.var Var.here)
                G104_referenz.GTab.Konto rfl
                G104_referenz.GKontoFeld.stand i w (by decide)
                G104_referenz.gDarf_einzahlen_Konto)
            else
              .ok (Stmt.assignSlot G104_referenz.GTab.Konto
                G104_referenz.GKontoFeld.stand i w
                (by decide) G104_referenz.gDarf_einzahlen_Konto)

/-- The arguments of a `lies` call in `einzahlen`: the fresh
    `rw`-to-`r` pointer and the index (the `tr_arg` of
    `lean_g.rs` for this pair; any other shape is an explicit
    error). -/
def lowerArgsLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UArg →
    Except String (Args G104_referenz.gD UCtxEin ULEin (G104_referenz.gD.params G104_referenz.g_lies))
  | [.freshPtr "Konto" (.table 0 (true, false)), .val (.param "i")] =>
    match names[1]?, types[1]? with
    | .some q, .some (Ty.int 0 1) =>
      if !strEq q "i" then .error "argument swapped"
      else
        match tabs.find? (fun x => strEq x.name "Konto") with
        | .none => .error "table unknown: Konto"
        | .some tb =>
          if tb.count != 2 then .error "count foreign"
          else
            .ok (Args.cons (Expr.ptrOf G104_referenz.GTab.Konto 0 rfl (true, false))
              (Args.cons (Expr.var (Var.there Var.here)) Args.nil))
    | _, _ => .error "argument without G form"
  | _ => .error "argument without G form"

/-- Straight-line steps after a `lies` call: assignments and
    the return only (a second call has no `RufPasst` proof in
    this lowering -- an explicit error). -/
def lowerNachLies (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet →
    Except String
      (Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin
        (nach G104_referenz.gD G104_referenz.g_lies ULEin))
  | .assignGlob .. :: _, _ | .assignGlobB .. :: _, _ | .storeAtom .. :: _, _ | .storeAtomB .. :: _, _ =>
    .error "static without G form in the 104 lowering"
  | .assignRef .. :: _, _ => .error "reference without G form in the 104 lowering"
  | .floatLit .. :: _, _ | .float .. :: _, _ => .error "float without G form in the 104 lowering"
  | .bindW .. :: _, _ | .assignGlobO .. :: _, _ | [], .wert _ => .error "aggregate without G form in the 104 lowering"
  | .tausch .. :: _, _ => .error "exchange without G form in the 104 lowering"
  | .ifEnde .. :: _, _ | [], .keins => .error "terminal if without G form in the 104 lowering"
  | [], .empty => .ok (.ret .empty (List.Perm.refl _))
  | [], .bool _ | [], .opt _ | [], .why _ | [], .sum _ | [], .grund _ => .error "truth value returned without result"
  | [], .val _ => .error "return with value without result"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  /- `reset A at i count n;` (C18): the 104 program has no array statics (`lowerProg`
      requires `globs = []`), so the checked range-store expansion of the generic lowering
      (`lowResetRangeL`) has no target here; the form stays refused, by reason rather than
      by name. -/
  | .retireMark .. :: _, _ => .error "check Duty retirement requires the generic lowering"
  | .retires .. :: _, _ => .error "mark retirement without G form in the 104 lowering (no marks)"
  | .breakingBeg .. :: _, _ => .error "breaking without G form in the 104 lowering (no invariants)"
  | .resetRange .. :: _, _ =>
    .error "static array reset without G form in the 104 lowering (no array statics)"
  | .assignB .. :: _, _ | .assignTabB .. :: _, _ | .lockBeg _ :: _, _ | .blkEnd :: _, _ | .bind .. :: _, _ | .bindCall .. :: _, _ | .axCall .. :: _, _ | .bindAx .. :: _, _ | .narrowBeg .. :: _, _ | .narrowReqBeg .. :: _, _ | .retryBeg .. :: _, _ | .foreverBeg .. :: _, _ | .bindOpt .. :: _, _ | .assignOpt .. :: _, _ | .assignTabOpt .. :: _, _ | .matchBeg .. :: _, _ | .startS :: _, _ | .allocBeg .. :: _, _ | .bindOptBeg .. :: _, _ | .bindOptElseBeg .. :: _, _ | .callIndElseBeg .. :: _, _ | .axCallElseBeg .. :: _, _ | .allocReqBeg .. :: _, _ | .bindElse .. :: _, _ | .matchWhyBeg .. :: _, _ | .bindSum .. :: _, _ | .matchTagBeg .. :: _, _ | .bindAxElse .. :: _, _ | .bindB .. :: _, _ | .bindMut .. :: _, _ | .setVar .. :: _, _ | .setVarB .. :: _, _ | .ifBeg _ :: _, _ | .ifElse :: _, _
    | .consumeLoopBeg .. :: _, _ | .arrayLoopBeg .. :: _, _ | .loopBeg .. :: _, _ | .ret _ :: _, _ | .leave _ :: _, _ | .next _ :: _, _
    | .regRead .. :: _, _ | .regReadElse .. :: _, _ | .regWrite .. :: _, _ | .regWriteB .. :: _, _ | .awaitBind .. :: _, _
    | .bindFnref .. :: _, _ | .callInd .. :: _, _ | .bindCallInd .. :: _, _ | .bindCallIndElse .. :: _, _ | .shiftTab .. :: _, _ =>
    .error "statement without G form in the 104 lowering"
  | .call _ _ :: _, _ => .error "call after call without G form"

/-- The body of `einzahlen`: straight-line writes, at most
    one direct `lies` call, and the trailing return (the
    `tr_body` of `lean_g.rs`). -/
def lowerSaetzeEin (tabs : List UTab) (names : List String)
    (types : List Ty) : List UStmt → URet → Except String UKoerpEin
  | .assignGlob .. :: _, _ | .assignGlobB .. :: _, _ | .storeAtom .. :: _, _ | .storeAtomB .. :: _, _ =>
    .error "static without G form in the 104 lowering"
  | .assignRef .. :: _, _ => .error "reference without G form in the 104 lowering"
  | .floatLit .. :: _, _ | .float .. :: _, _ => .error "float without G form in the 104 lowering"
  | .bindW .. :: _, _ | .assignGlobO .. :: _, _ | [], .wert _ => .error "aggregate without G form in the 104 lowering"
  | .tausch .. :: _, _ => .error "exchange without G form in the 104 lowering"
  | .ifEnde .. :: _, _ | [], .keins => .error "terminal if without G form in the 104 lowering"
  | [], .empty => .ok (.ret .empty (List.Perm.refl _))
  | [], .bool _ | [], .opt _ | [], .why _ | [], .sum _ | [], .grund _ => .error "truth value returned without result"
  | [], .val _ => .error "return with value without result"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs names types b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs names types rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .call "lies" args :: rest, r =>
    match lowerArgsLies tabs names types args with
    | .error e => .error e
    | .ok a =>
      match lowerNachLies tabs names types rest r with
      | .error e => .error e
      | .ok t =>
        .ok (.cons (.call G104_referenz.g_lies a G104_referenz.gHp_einzahlen_lies rfl) t)
  /- `reset A at i count n;` (C18): as above, the 104 program has no array statics, so the
      checked range-store expansion of the generic lowering has no target here. -/
  | .retireMark .. :: _, _ => .error "check Duty retirement requires the generic lowering"
  | .retires .. :: _, _ => .error "mark retirement without G form in the 104 lowering (no marks)"
  | .breakingBeg .. :: _, _ => .error "breaking without G form in the 104 lowering (no invariants)"
  | .resetRange .. :: _, _ =>
    .error "static array reset without G form in the 104 lowering (no array statics)"
  | .assignB .. :: _, _ | .assignTabB .. :: _, _ | .lockBeg _ :: _, _ | .blkEnd :: _, _ | .bind .. :: _, _ | .bindCall .. :: _, _ | .axCall .. :: _, _ | .bindAx .. :: _, _ | .narrowBeg .. :: _, _ | .narrowReqBeg .. :: _, _ | .retryBeg .. :: _, _ | .foreverBeg .. :: _, _ | .bindOpt .. :: _, _ | .assignOpt .. :: _, _ | .assignTabOpt .. :: _, _ | .matchBeg .. :: _, _ | .startS :: _, _ | .allocBeg .. :: _, _ | .bindOptBeg .. :: _, _ | .bindOptElseBeg .. :: _, _ | .callIndElseBeg .. :: _, _ | .axCallElseBeg .. :: _, _ | .allocReqBeg .. :: _, _ | .bindElse .. :: _, _ | .matchWhyBeg .. :: _, _ | .bindSum .. :: _, _ | .matchTagBeg .. :: _, _ | .bindAxElse .. :: _, _ | .bindB .. :: _, _ | .bindMut .. :: _, _ | .setVar .. :: _, _ | .setVarB .. :: _, _ | .ifBeg _ :: _, _ | .ifElse :: _, _
    | .consumeLoopBeg .. :: _, _ | .arrayLoopBeg .. :: _, _ | .loopBeg .. :: _, _ | .ret _ :: _, _ | .leave _ :: _, _ | .next _ :: _, _
    | .regRead .. :: _, _ | .regReadElse .. :: _, _ | .regWrite .. :: _, _ | .regWriteB .. :: _, _ | .awaitBind .. :: _, _
    | .bindFnref .. :: _, _ | .callInd .. :: _, _ | .bindCallInd .. :: _, _ | .bindCallIndElse .. :: _, _ | .shiftTab .. :: _, _ =>
    .error "statement without G form in the 104 lowering"
  | .call _ _ :: _, _ => .error "call without G form"

/-! ## Lowering `lies` -/

/-- The body context of `lies`: its parameters. -/
abbrev UCtxLies := G104_referenz.gCtx_lies

/-- The held resources of `lies`. -/
abbrev ULLies := G104_referenz.gL_lies

/-- The `ensures` context of `lies`: the result first. -/
abbrev UCtxEnsLies :=
  ErgCtx (G104_referenz.gD.params G104_referenz.g_lies)
    (G104_referenz.gD.erg G104_referenz.g_lies)

/-- The `ensures` type of `lies`. -/
abbrev UEnsLies :=
  Expr G104_referenz.gD UCtxEnsLies
    (vertragVon G104_referenz.gD G104_referenz.g_lies).ende .bool

/-- The body type of `lies`. -/
abbrev UKoerpLies :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_lies)
    false G104_referenz.gCtx_lies G104_referenz.gL_lies

/-- A parameter variable of `lies` by position and type. -/
def varNumLies : (j : Nat) → (τ : Ty) → Except String (Var UCtxLies τ)
  | 0, .ptr (.table 0 (true, false)) => .ok Var.here
  | 1, .int 0 1 => .ok (Var.there Var.here)
  | _, _ => .error "parameter without G form"

/-- A variable of the `lies` `ensures` context: the result or
    a parameter (positions are the known signature). -/
def varEnsLies : (j : Nat) → (τ : Ty) →
    Except String (Var UCtxEnsLies τ)
  | 0, .int 0 100 => .ok Var.here
  | 1, .ptr (.table 0 (true, false)) => .ok (Var.there Var.here)
  | 2, .int 0 1 => .ok (Var.there (Var.there Var.here))
  | _, _ => .error "parameter without G form"

/-- One side in the `lies` body, with its range. -/
structure USeiteL where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxLies ULLies (.int range.1 range.2)

/-- An index into `Konto` in `lies`. -/
def lowerIdxLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.there Var.here))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | _ => .error "index without G form"

def lowerSeiteLies (tabs : List UTab) (names : List String)
    (types : List Ty) : USide → Except String USeiteL
  | .product .. | .field .. | .replace .. => .error "product without G form in the 104 lowering"
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varNumLies j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var Var.here)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | _ => .error "side in a body without G form"

/-- One side in the `lies` `ensures`, with its range (`result`
    travels here; the recorded result range must be the
    exporter's `(0, 100)`). -/
structure USeiteE where
  range : Int × Int
  term : Expr G104_referenz.gD UCtxEnsLies ULLies (.int range.1 range.2)

def lowerSeiteEnsLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    USide → Except String USeiteE
  | .product .. | .field .. | .replace .. => .error "product without G form in the 104 lowering"
  | .glob _ => .error "static without G form in the 104 lowering"
  | .refSlot .. => .error "reference without G form in the 104 lowering"
  | .idx .. | .len _ | .text _ | .arrNil | .arrCons .. | .upd .. | .typed .. => .error "aggregate without G form in the 104 lowering"
  | .eng .. => .error "narrowing without G form in the 104 lowering"
  | .ib1 .. | .ib2 .. => .error "builtin without G form in the 104 lowering"
  | .zaehle .. | .zaehleBaum .. | .zaehleFeld .. => .error "count without G form in the 104 lowering"
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match names[j]?, types[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "parameter swapped"
        else
          match varEnsLies (j + 1) (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { range := (lo, hi), term := Expr.var v }
      | _, _ => .error "parameter without G form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var (Var.there Var.here))
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .old b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.oldS G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .erg =>
    match res with
    | .some (0, 100) => .ok { range := (0, 100), term := Expr.var Var.here }
    | _ => .error "result range foreign"
  | .add .. | .sub .. | .mul .. | .conv .. | .band .. | .bor .. | .bxor .. | .div .. | .rem .. | .shl .. | .shr .. | .neg .. =>
    .error "arithmetic without G form in the 104 lowering"
where
  lowerIdxEnsLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxEnsLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
    | .param "i" => .ok (Expr.var (Var.there (Var.there Var.here)))
    | .lit n =>
      if h1 : 0 ≤ n then
        if h2 : n ≤ 1 then .ok (Expr.widen h1 h2 (Expr.lit n))
        else .error "index outside count"
      else .error "index outside count"
    | _ => .error "index without G form"

/-- One comparison and one `ensures` predicate in `lies`. -/
def lowerVglLies (tabs : List UTab) (names : List String)
    (types : List Ty) (res : Option (Int × Int)) :
    String → USide → USide → Except String UEnsLies
  | op, a, b =>
    match lowerSeiteEnsLies tabs names types res a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEnsLies tabs names types res b with
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
