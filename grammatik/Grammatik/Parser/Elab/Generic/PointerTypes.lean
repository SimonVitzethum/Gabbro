module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

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

/-- The contract of a pointer type (C06): `needs`/`gives` ride the type into
    `UProg.ptrs`, elaborated exactly like a function's (`elabKlauseln`, with
    `refines` inlined), and lower to `Programm.ptrVertrag` (`lowerPtrAt`,
    mirroring `lowerFnPlain`'s contract part). Conformance is per-pair
    (`passtAt` with `vertragPasstAt`): a function value is admitted only where
    it includes the interface contract. `costs` travels nowhere, as at a
    function. `requires Held(..)` is refused by the caller: no lock crosses
    an indirect call. -/
def uZeigerVertrag (ctx : UCtx) : List SKlausel → Except String (List UEns × List UEns)
  | ks => elabKlauseln ctx ks

/-- The text of a pointer type as a function head (`FnSig`, art `impl`, no name). A reason channel
    (`-> T or R`) is admitted («C07»): the name resolves against the unit's reasons in `elabKopf` (unknown
    reasons and empty channels are refused there), and `elabZeigerTyp` carries the case count as `gruende`. -/
def uZeigerSig (raw : String) : Except String FnSig :=
  match lex raw with
  | .error _ => .error "pointer type unreadable"
  | .ok (.wort "fn" :: .zeichen "(" :: r) =>
    match uZeigerParams 10000 0 r with
    | .error e => .error e
    | .ok (ps, r1) =>
      match parseErgebnis 10000 r1 with
      | .error e => .error e
      | .ok (erg, fehler, r2) =>
        match parseKlauseln 10000 r2 with
        | .error e => .error e
        | .ok (ks, r3) =>
          if !(r3.all (fun t => match t with | .ende => true | _ => false)) then .error "pointer type without G form"
          else .ok { art := "impl", name := "", params := ps, res := erg, fehler := fehler, klauseln := ks }
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
    (zb j : Nat) (raw : String) (spaces : List String := []) (named : List (String × Ty) := []) : Except String (UFnKopf × UFn) :=
  match uZeigerSig raw with
  | .error e => .error e
  | .ok sig =>
    match elabKopf consts alias tabs locks globs whys sums sig [] zeiger zb spaces named with
    | .error e => .error e
    | .ok (kopf0, schreibt) =>
      let name := "fn#" ++ toString j
      let kopf := { kopf0 with name := name }
      if !kopf.held.isEmpty then .error "locks at a function-pointer type do not cross an indirect call" else
      let ctx := { uCtxVon alias consts tabs locks globs kopf name [] whys sums [] [] [] [] with zeiger := zeiger, zeigerBasis := zb, spaces := spaces, namedTypes := named }
      match uZeigerVertrag ctx sig.klauseln with
      | .error e => .error e
      | .ok (gives, needs) =>
        let genommen := (uEffekte kopf tabs locks globs sig.klauseln).toOption.map (·.locks) |>.getD []
        if !genommen.isEmpty then .error "locks at a function-pointer type do not cross an indirect call" else
        -- No lock crosses an indirect call: the floor is one above the highest rank of the unit, so a
        -- conforming function takes no lock (`SigPasst.boden`), and a caller may hold any.
        let boden : Option Int := if locks.isEmpty then none else some ((locks.map (·.rank)).foldl max 0 + 1)
        .ok (kopf, { name := name, params := kopf.names.zip kopf.types, kinds := kopf.kinds, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, gruende := (kopf.kanal.map (·.2)).getD 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, gives, needs, body := [], ret := .empty, boden := boden })

end Gabbro.Grammatik.Parser.Uebersetze
