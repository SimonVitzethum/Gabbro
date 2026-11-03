module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Syntactic contract coverage is a refusal check, never an isolation proof.
    Only resolved table subjects count; a similarly named scalar does not. -/
def guestMentions : Nat → String → SExpr → Bool
  | 0, _, _ => false
  | fuel + 1, region, .ext _ _ args => args.any fun
      | .variable name => strEq name region
      | e => guestMentions fuel region e
  | fuel + 1, region, .bin _ a b => guestMentions fuel region a || guestMentions fuel region b
  | fuel + 1, region, .un _ a => guestMentions fuel region a
  | _ + 1, _, _ => false

/-- Resolve a declared C08 item, retaining its exact requires/ensures. Gate
    ABI metadata remains the ordinary backend binding's responsibility. -/
def guestService (items : List SItemTief) (name : String) : Except String FnSig := do
  let candidates := items.filterMap fun
    | .protoT sig => if strEq sig.name name then some sig else none
    | .callT sc => if strEq sc.name name then
        some { art := "extern", name := sc.name, params := sc.params, res := sc.res,
          fehler := sc.fail, klauseln := sc.gate.pre.map SKlausel.needs ++
            sc.gate.post.map SKlausel.gives ++ [.effs sc.gate.uses] }
      else none
    | _ => none
  match candidates with
  | [sig] => pure sig
  | [] => throw "entrust: missing isolation service binding"
  | _ => throw "entrust: ambiguous isolation service binding"

/-- A wrapper preserves both the success result and the actual failure reason.
    It is ordinary source sugar for the existing optional foreign-call binder. -/
def guestWrapper (name reason : String) (cases : List String) (fallback : String) (sig : FnSig) : SItemTief :=
  .fnT { sig with art := "impl", name }
    (.block [.bindAxiomOptElse "#guest-result" none
      (.call sig.name (sig.params.map fun p => .variable p.1)) "#guest-error"
      (.block [.cases (.variable "#guest-error") (cases.map fun c =>
        .arm c none (.block [] (some (.ret (some (.why reason c))))))]
        (some (.ret (some (.why reason fallback)))))]
      (some (.ret (sig.res.map fun _ => .variable "#guest-result"))))

/-- All non-code region inputs need real owner resources and exact transfer
    descriptors. This source adapter does not export those descriptors yet, so
    additional regions fail by name rather than losing their owner transfer. -/
def guestSource (items : List SItemTief) : SItemTief → Except String (UGuest × SItemTief)
  | .trustT name code arch regs stack assumption service => do
    ProfilBindung.gastQuellePruefung arch regs stack assumption service
    let service ← match service with
      | some name => pure name
      | none => throw "entrust: missing isolation service binding"
    let sig ← guestService items service
    if strEq sig.art "divergent" then throw "entrust: returning service has a never result"
    match sig.res with
    | some (.atom "never") => throw "entrust: returning service has a never result"
    | some (.atom "bool") | some (.index ..) =>
      throw "entrust: isolation service result has no fallible C08 form"
    | _ => pure ()
    let reason ← match sig.fehler with
      | some reason => pure reason
      | none => throw "entrust: isolation service needs a failure channel"
    let cases ← match items.find? (fun | .whyT n _ _ => strEq n reason | _ => false) with
      | some (.whyT _ cases _) => pure (cases.map (·.1))
      | _ => throw "entrust: isolation service needs a declared failure channel"
    let fallback ← match cases with
      | first :: _ => pure first
      | [] => throw "entrust: isolation service needs a failure channel"
    let pointers := sig.params.filterMap fun
      | (_, .ptr space rights (.atom table)) => some (space, rights, table)
      | _ => none
    match pointers with
    | [(_, rights, table)] =>
      if !strEq table code || !strEq rights "r" then
        throw "entrust: code needs an immutable region capability"
    | [] => throw "entrust: code needs an immutable region capability"
    | _ => throw "entrust: caller does not own a transferred region"
    let pre := sig.klauseln.filterMap fun | .needs e => some e | _ => none
    let post := sig.klauseln.filterMap fun | .gives e => some e | _ => none
    if !pre.any (guestMentions 10000 code) || !post.any (guestMentions 10000 code) then
      throw "entrust: isolation service contract does not mention transferred regions"
    if items.any (fun | .fnT s _ => strEq s.name name | _ => false) then
      throw "entrust: guest wrapper conflicts with a declared function"
    pure (⟨name, code, arch, service⟩, guestWrapper name reason cases fallback sig)
  | _ => throw "entrust: expected guest declaration"

/-- Keep every descriptor in source order, and add exactly one ordinary
    wrapper per item. No item or contract is erased by this expansion. -/
def guestSources (items : List SItemTief) : Except String (List UGuest × List SItemTief) := do
  let declarations := items.filter fun | .trustT .. => true | _ => false
  let expanded ← uSeq (declarations.map (guestSource items))
  let guests := expanded.map (·.1)
  if (uEindeutig (guests.map (·.name))).length != guests.length then
    throw "entrust: duplicate guest declaration"
  pure (guests, items ++ expanded.map (·.2))

/-- Lower the declared foreign predicates in the foreign item's own scope.
    An entrust binding explicitly chooses software provenance; no assume is
    manufactured. A hardware query retains its independent named origin. -/
def guestForeign (alias : List (String × (Int × Int))) (consts : List (String × Int))
    (tabs : List UTab) (globs : List UGlob) (whys : List UWhy)
    (assumptions : List String) (guests : List UGuest) (k : UFnKopf)
    (eigner : List String := []) : Except String UAx := do
  let ctx := { uCtxVon alias consts tabs [] globs k k.name assumptions whys with eigner := eigner }
  let (gives, needs) ← elabKlauseln ctx k.clauses
  let software := guests.any fun g => strEq g.service k.name
  if software && k.annahme.isSome then
    throw "entrust: isolation service must be a software binding"
  pure { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
    gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs,
    beleg := k.annahme.bind (fun n => assumptions.findIdx? fun x => strEq x n),
    software, names := k.names, needs, gives }

end Gabbro.Grammatik.Parser.Uebersetze
