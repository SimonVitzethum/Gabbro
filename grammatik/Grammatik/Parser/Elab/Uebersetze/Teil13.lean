module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil12
public import Grammatik.Parser.Elab.Uebersetze.Transition.Generate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-! ## Function-pointer types (2026-10-21)

  A `fn(..) [-> T] effects { .. } costs <= e ops` type of the unit is read once by its text (the type reader keeps
  it raw, `STyp.raw`) into a head like a function's and a signature with an empty body (`UProg.ptrs`). Its number
  stands behind the functions'; a function conforms to it by `Deklaration.passt` (`passtAt`, decided). The model
  has no contract on a signature: a `requires` (`Held(..)` included) or an `ensures` is refused by name (TODO O43);
  `costs` travels nowhere, as at a function. No lock crosses an indirect call (a `locks` effect at the type is
  refused, as `N036` does): the floor of the type is one above the highest rank of the unit. -/

/-- The parameters of a pointer type up to `)`: `[name :] type`, comma separated (an unnamed one is `p<k>`). -/
def uZeigerParams : Nat → Nat → List Token → Except String (List (String × STyp) × List Token)
  | 0, _, _ => .error "out of fuel"
  | _ + 1, _, .zeichen ")" :: r => .ok ([], r)
  | f + 1, k, toks =>
    let (n, toks') : String × List Token := match toks with
      | t :: .zeichen ":" :: r => match nameText t with
        | some n => (n, r)
        | none => ("p" ++ toString k, toks)
      | _ => ("p" ++ toString k, toks)
    match parseTyp f toks' with
    | .error e => .error e
    | .ok (ty, .zeichen "," :: r) =>
      match uZeigerParams f (k + 1) r with
      | .error e => .error e
      | .ok (ps, r') => .ok ((n, ty) :: ps, r')
    | .ok (ty, .zeichen ")" :: r) => .ok ([(n, ty)], r)
    | .ok _ => .error "pointer type parameters without G form"

/-- A contract on a pointer type: refused (the model's signatures carry none, TODO O43; `N589` in the checker).
    `requires Held(..)` is refused too: no lock crosses an indirect call. The lowering guard
    `ptrVertragGebunden` in `UebersetzeAllg3.Rest2` repeats this refusal at `lowerAllg`: a nontrivial
    `needs`/`gives` on a pointer type never silently becomes `trivial`; the export admits the target
    only where the full O43 duty (`PtrVerfeinert`, candidate table, interface caller duty) is bound. -/
def uZeigerVertrag : List SKlausel → Except String Unit
  | [] => .ok ()
  | .needs .tru :: rest => uZeigerVertrag rest
  | .gives .tru :: rest => uZeigerVertrag rest
  | .needs _ :: _ => .error "contract on a function-pointer type without G form"
  | .gives _ :: _ => .error "contract on a function-pointer type without G form"
  | _ :: rest => uZeigerVertrag rest

/-- The text of a pointer type as a function head (`FnSig`, art `impl`, no name). -/
def uZeigerSig (raw : String) : Except String FnSig :=
  match lex raw with
  | .error _ => .error "pointer type unreadable"
  | .ok (.wort "fn" :: .zeichen "(" :: r) =>
    match uZeigerParams 10000 0 r with
    | .error e => .error e
    | .ok (ps, r1) =>
      match parseErgebnis 10000 r1 with
      | .error e => .error e
      | .ok (_, some _, _) => .error "pointer type with a reason channel without G form"
      | .ok (erg, none, r2) =>
        match parseKlauseln 10000 r2 with
        | .error e => .error e
        | .ok (ks, r3) =>
          if !(r3.all (fun t => match t with | .ende => true | _ => false)) then .error "pointer type without G form"
          else .ok { art := "impl", name := "", params := ps, res := erg, fehler := none, klauseln := ks }
  | .ok _ => .error "pointer type without G form"

/-- The texts of the pointer types a surface type list names (`fn (` raw types). -/
def uZeigerTexte : List STyp → List String
  | [] => []
  | .raw r :: rest => if r.startsWith "fn (" then r :: uZeigerTexte rest else uZeigerTexte rest
  | _ :: rest => uZeigerTexte rest

/-- The pointer types written at a `let` of a body. -/
def uZeigerAnw : Nat → SAnw → List String
  | 0, _ => []
  | f + 1, a => match a with
    | .bind _ _ (some t) _ => uZeigerTexte [t]
    | .bindElse _ (some t) _ _ b => uZeigerTexte [t] ++ uZeigerAnw f b
    | .bindElse _ none _ _ b => uZeigerAnw f b
    | .cond _ t es e => uZeigerAnw f t ++ (es.flatMap (uZeigerAnw f)) ++ (match e with | some b => uZeigerAnw f b | none => [])
    | .elsif _ b => uZeigerAnw f b
    | .cases _ as => as.flatMap (uZeigerAnw f)
    | .arm _ _ b => uZeigerAnw f b
    | .each _ _ _ _ _ _ _ b => uZeigerAnw f b
    | .retry _ b => uZeigerAnw f b
    | .loop _ b => uZeigerAnw f b
    | .waive _ b => uZeigerAnw f b
    | .trim _ _ b => uZeigerAnw f b
    | .locks _ _ b => uZeigerAnw f b
    | .watch _ b => uZeigerAnw f b
    | .alloc _ _ _ _ _ (some b) => uZeigerAnw f b
    | .grow _ _ b => uZeigerAnw f b
    | .child b => uZeigerAnw f b
    | .block as _ => as.flatMap (uZeigerAnw f)
    | _ => []

/-- A pointer type of the unit as a head (named `fn#j`) and an elaborated signature with an empty body. -/
def elabZeigerTyp (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum) (zeiger : List String)
    (zb j : Nat) (raw : String) : Except String (UFnKopf × UFn) :=
  match uZeigerSig raw with
  | .error e => .error e
  | .ok sig =>
    match uZeigerVertrag sig.klauseln with
    | .error e => .error e
    | .ok _ =>
      match elabKopf consts alias tabs locks globs whys sums sig [] zeiger zb with
      | .error e => .error e
      | .ok (kopf0, schreibt) =>
        let name := "fn#" ++ toString j
        let kopf := { kopf0 with name := name }
        let genommen := (uEffekte kopf tabs locks globs sig.klauseln).toOption.map (·.locks) |>.getD []
        if !genommen.isEmpty then .error "locks at a function-pointer type do not cross an indirect call" else
        -- No lock crosses an indirect call: the floor is one above the highest rank of the unit, so a
        -- conforming function takes no lock (`SigPasst.boden`), and a caller may hold any.
        let boden : Option Int := if locks.isEmpty then none else some ((locks.map (·.rank)).foldl max 0 + 1)
        .ok (kopf, { name := name, params := kopf.names.zip kopf.types, kinds := kopf.kinds,
                     res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum,
                     gruende := 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, gives := [], needs := [],
                     body := [], ret := .empty, boden := boden })

/-- The names a unit declares as memory: tables, arenas, statics, atomics. -/
def uSpeicherNamen (ms : List SItemTief) : List String :=
  ms.filterMap fun
    | .tableT n .. => some n
    | .arenaT n .. => some n
    | .globT _ n .. => some n
    | .atomT n .. => some n
    | _ => none

/-- The writes of a clause list that name no memory of the unit. -/
def uFremdeSchreibe (mem : List String) (ks : List SKlausel) : List String :=
  ks.flatMap fun
    | .effs es => es.filterMap fun
      | .writes (.variable n) => if mem.any (strEq · n) then none else some n
      | _ => none
    | _ => []

/-- The clause list without the writes of the sinks. -/
def uKlauselnOhne (senken : List String) (ks : List SKlausel) : List SKlausel :=
  ks.map fun
    | .effs es => .effs (es.filter fun
      | .writes (.variable n) => !(senken.any (strEq · n))
      | _ => true)
    | k => k

/-- **Sinks** (`writes ausgabe` at an `extern fn`): a name that is no memory of the unit, written by a foreign body,
    is what lies behind it outside the program -- no carrier of G; the call itself is the trace event
    (`Ereignis.fremd`). Such a name may stand in the `writes` of the foreign bodies and of the functions that call
    them; it is dropped there. A name no foreign body declares stays and is refused as an unknown carrier. -/
def uOhneSenken (ms : List SItemTief) : List SItemTief :=
  let mem := uSpeicherNamen ms
  let senken := ms.flatMap fun
    | .protoT sig => uFremdeSchreibe mem sig.klauseln
    | .asmT sig _ => uFremdeSchreibe mem sig.klauseln
    | .axiomT _ _ _ _ effs _ => uFremdeSchreibe mem [.effs effs]
    | _ => []
  if senken.isEmpty then ms else
  ms.map fun
    | .fnT sig b => .fnT { sig with klauseln := uKlauselnOhne senken sig.klauseln } b
    | .protoT sig => .protoT { sig with klauseln := uKlauselnOhne senken sig.klauseln }
    | .asmT sig c => .asmT { sig with klauseln := uKlauselnOhne senken sig.klauseln } c
    | .axiomT n ps r q effs k =>
      .axiomT n ps r q (match uKlauselnOhne senken [.effs effs] with | [.effs es] => es | _ => effs) k
    | m => m

/-- The signature of a foreign body item and whether it is `= asm { .. }`: `extern`/`raw`/`prim`/`divergent` declarations,
    `asm` bodies, and `axiom` items without a `requires` (read as an `extern fn` with their effects). -/
def uFremdSig : SItemTief → Option (FnSig × Bool)
  | .protoT sig => some (sig, false)
  | .asmT sig _ => some (sig, true)
  | .axiomT n ps res .none effs _ =>
    some ({ art := "extern", name := n, params := ps, res, fehler := .none, klauseln := [.effs effs] }, false)
  | _ => none

/-- The elaborator: a parsed surface tree to the exported
    fragment (tables, locks, `impl` functions). -/
def elabU : List SItemTief → Except String UProg
  | items =>
    let ms0 := uMembers items
    let consts := uConstsRech (uKonstFns ms0) ms0 []
    let alias := uAliase consts ms0 ++ uAliasBreiten ms0 ++ consts.map (fun c => (c.1, (c.2, c.2)))
    match uRestFehler ms0 with
    | .error e => .error e
    | .ok _ =>
    match ExportMetadata.checkConstants ms0 with
    | .error error => .error error
    | .ok () =>
    let ms := uOhneSenken ms0
    match uGlobs consts alias ms with
    | .error e => .error e
    | .ok globs0 =>
    let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)
    match uSeq ((ms.filter (fun
        | .tableT _ _ _ _ _ _ _ => true | _ => false)).map (uTabelle consts alias tnames)) with
    | .error e => .error e
    | .ok tabs0 =>
    match uArenen consts alias ms with
    | .error e => .error e
    | .ok (arTabs, arGlobs) =>
    let tabs := uIdxTabs (tabs0 ++ arTabs ++ uArrayCarriers alias ms0)
    match uOptGlobs tabs (globs0 ++ arGlobs) with
    | .error e => .error e
    | .ok globs =>
    -- C16: every `check` item elaborates now, with its generated probe below.
    match uChecks tabs globs ms with
    | .error e => .error e
    | .ok checks =>
    match uSeq ((ms.filter (fun
        | .lockT _ _ _ _ _ _ _ => true | _ => false)).map (fun item => uSperre globs tabs item consts)) with
    | .error e => .error e
    | .ok locks0 =>
    match uSperrInvs consts alias globs tabs ms locks0 with
    | .error e => .error e
    | .ok locks =>
    let bewacht : String → Bool := fun c => locks.any (fun l => l.guard.any (strEq · c))
    if !tabs.all (fun t => !t.shared || bewacht t.name) then .error "shared table without a guard" else
    if !globs.all (fun g => !g.shared || g.atomic || bewacht g.name) then .error "shared static without a guard" else
    if !globs.all (fun g => g.nutzlast.all (fun n => globs.any (fun h => strEq h.name n))) then
      .error "payload names no static" else
    let fnItems := ms.filterMap (fun
      | .fnT sig koerper => if strEq sig.art "const" then none else some (sig, koerper)
      | _ => none)
    match uWhys ms alias with
    | .error e => .error e
    | .ok whys =>
    match uSums alias ms with
    | .error e => .error e
    | .ok sums =>
    match uSumGlobs consts sums ms globs with
    | .error e => .error e
    | .ok globs =>
    match uSumTabs sums tabs with
    | .error e => .error e
    | .ok tabs =>
    match uRegs alias consts tabs globs ms with
    | .error e => .error e
    | .ok regs =>
    match uInvs consts alias tabs locks globs ms with
    | .error e => .error e
    | .ok invs =>
    let transitionCtx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held := [],
                                  res := none, fname := "transition", alias, lits := consts, globs }
    match uSeq (ms.filterMap (fun | .stateT n ts => some (uZustand n ts transitionCtx) | _ => none)) with
    | .error e => .error e
    | .ok zustaende =>
    if (uEindeutig (zustaende.map (·.name))).length != zustaende.length then
      .error "duplicate state identity" else
    match uGenerateTransitions tabs globs zustaende with
    | .error e => .error e
    | .ok transitionFns =>
    if transitionFns.any (fun g => fnItems.any (fun (s, _) => strEq s.name g.name)) then
      .error "generated transition function conflicts with an explicit function" else
    let devs := ms.filterMap (fun | .devT n _ _ _ => some n | _ => none)
    let zeiger := uOhneDoppelte (fnItems.flatMap (fun (s, b) => uZeigerTexte (s.params.map (·.2)) ++ uZeigerAnw 100000 b))
    let zb := fnItems.length + transitionFns.length
    match uSeq ((List.range zeiger.length).zip zeiger |>.map (fun (j, r) =>
        elabZeigerTyp consts alias tabs locks globs whys sums zeiger zb j r)) with
    | .error e => .error e
    | .ok zeigerPaare =>
    match uSeq (fnItems.map (fun (s, _) => elabKopf consts alias tabs locks globs whys sums s devs zeiger zb)) with
    | .error e => .error e
    | .ok [] => .error "unit without a fn"
    | .ok kopfPaare =>
    match uSeq ((ms.filterMap uFremdSig).map (fun (sig, asm) => elabAxKopf alias tabs whys globs asm sig)) with
    | .error e => .error e
    | .ok axKoepfe0 =>
    match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (elabGateKopf alias tabs whys globs)) with
    | .error e => .error e
    | .ok gateKoepfe =>
    let axKoepfe := axKoepfe0 ++ gateKoepfe
    let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
    let annahmen := ms.filterMap (fun | .assumT n _ _ _ => some n | _ => none)
    -- C16: every `can_fail` body elaborates into its generated Boolean producer now.
    match uProbeFns consts alias tabs locks globs koepfe whys sums devs regs zustaende (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none)) (uKonstArrays alias (uKonstFns ms) consts ms) zeiger zb (fnItems.map (fun (s, _) => s.name) ++ axKoepfe.map (·.name) ++ zeigerPaare.map (fun p => p.1.name)) (ms.filterMap (fun | .checkT c => some c | _ => none)) with
    | .error e => .error e
    | .ok probeFns =>
    match uSeq (fnItems.map (fun (s, b) =>
        elabUFunktion consts alias tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
          (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none))
          (uKonstArrays alias (uKonstFns ms) consts ms))) with
    | .error e => .error e
    | .ok fns =>
    let fns := fns ++ transitionFns
    match uWurzeln tabs fns ms with
    | .error e => .error e
    | .ok roots =>
    match uSeq ((uOhneDoppelte (fnItems.flatMap (fun (_, b) => uStartNamen 100000 b))).map
        (fun d => uStart (fns ++ probeFns) "start" d)) with
    | .error e => .error e
    | .ok gestartet =>
      if !uU003 locks (fns ++ zeigerPaare.map (·.2)) invs then .error "a writer of an invariant's carrier does not hold all its locks" else
      match uRegiert fns zustaende with
      | .error e => .error e
      | .ok regiert =>
      let u : UProg :=
        { tabs := tabs, locks := locks, fns := fns ++ probeFns, roots := roots, hands := uHandler ms, globs := globs,
          gestartet := gestartet,
          axs := axKoepfe.map (fun k => { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
                                          gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs }),
          annahmen := annahmen, whys := whys, sums := sums, regs := regs, invs := invs,
          zustaende := zustaende, regiert := regiert, ptrs := zeigerPaare.map (·.2), ptrKeys := zeiger,
          exportGate := ExportMetadata.check ms0, checks := checks }
      .ok (uMitBoden u)

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
  | 0, .ptr 0 true => .ok .here
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
          .ok { range := (0, 100),
                term := Expr.thru (Expr.var Var.here)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "place without G form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { range := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
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
          .ok { range := (0, 100),
                term := Expr.oldS G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
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
