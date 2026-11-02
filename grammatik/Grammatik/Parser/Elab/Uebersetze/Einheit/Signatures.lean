module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
public import Grammatik.Parser.Elab.Uebersetze.Transition.Generate
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.TaggedDispatch.Frontend
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil17
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
public import Grammatik.Parser.Elab.Konst.Export
public import Grammatik.Parser.Elab.Konst.ErsetzungTor

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
    match uZeigerVertrag sig.klauseln with
    | .error e => .error e
    | .ok _ =>
      match elabKopf consts alias tabs locks globs whys sums sig [] zeiger zb spaces named with
      | .error e => .error e
      | .ok (kopf0, schreibt) =>
        let name := "fn#" ++ toString j
        let kopf := { kopf0 with name := name }
        let genommen := (uEffekte kopf tabs locks globs sig.klauseln).toOption.map (·.locks) |>.getD []
        if !genommen.isEmpty then .error "locks at a function-pointer type do not cross an indirect call" else
        -- No lock crosses an indirect call: the floor is one above the highest rank of the unit, so a
        -- conforming function takes no lock (`SigPasst.boden`), and a caller may hold any.
        let boden : Option Int := if locks.isEmpty then none else some ((locks.map (·.rank)).foldl max 0 + 1)
        .ok (kopf, { name := name, params := kopf.names.zip kopf.types, kinds := kopf.kinds, res := kopf.res, resBool := kopf.resBool, resOpt := kopf.resOpt, resSum := kopf.resSum, resWhy := kopf.resWhy, resTy := kopf.resTy, gruende := (kopf.kanal.map (·.2)).getD 0, held := kopf.held, puts := schreibt, gputs := kopf.gputs, gives := [], needs := [], body := [], ret := .empty, boden := boden })

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

end Gabbro.Grammatik.Parser.Uebersetze
