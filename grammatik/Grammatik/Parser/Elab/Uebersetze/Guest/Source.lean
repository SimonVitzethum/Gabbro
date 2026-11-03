module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Syntactic contract coverage is a refusal check, never an isolation proof.
    Only resolved table subjects count; a similarly named scalar does not. -/
def guestMentions (region : String) : SExpr → Bool
  | .ext _ _ args => args.any fun
      | .variable name => strEq name region
      | e => guestMentions region e
  | .bin _ a b => guestMentions region a || guestMentions region b
  | .un _ a => guestMentions region a
  | _ => false
termination_by e => sizeOf e

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
def guestWrapper (name : String) (sig : FnSig) : SItemTief :=
  .fnT { sig with art := "impl", name }
    (.block [.bindAxiomOptElse "#guest-result" none
      (.call sig.name (sig.params.map fun p => .variable p.1)) "#guest-error"
      (.block [] (some (.ret (some (.variable "#guest-error")))))]
      (some (.ret (sig.res.map fun _ => .variable "#guest-result"))))

/-- All non-code region inputs need real owner resources. The current source
    declaration exports Empty owners, so additional regions fail here by name;
    no transfer is dropped or repaired with a fabricated owner. -/
def guestSource (items : List SItemTief) : SItemTief → Except String (UGuest × SItemTief)
  | .trustT name code arch regs stack assumption service => do
    if (ProfilBindung.wertVon .arch arch).isNone then
      throw "entrust: unknown userspace ABI"
    if !regs.isEmpty || !stack.isEmpty || !assumption.isEmpty then
      if service.isNone && regs.isEmpty then
        throw "entrust: missing isolation service binding"
      throw "entrust: register-state or privileged transfer is excluded"
    let service ← match service with
      | some name => pure name
      | none => throw "entrust: missing isolation service binding"
    let sig ← guestService items service
    if sig.fehler.isNone then throw "entrust: isolation service needs a failure channel"
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
    if !pre.any (guestMentions code) || !post.any (guestMentions code) then
      throw "entrust: isolation service contract does not mention transferred regions"
    if items.any (fun | .fnT s _ => strEq s.name name | _ => false) then
      throw "entrust: guest wrapper conflicts with a declared function"
    pure (⟨name, code, arch, service⟩, guestWrapper name sig)
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
    (assumptions : List String) (guests : List UGuest) (k : UFnKopf) : Except String UAx := do
  let ctx := uCtxVon alias consts tabs [] globs k k.name assumptions whys
  let (gives, needs) ← elabKlauseln ctx k.clauses
  let software := guests.any fun g => strEq g.service k.name
  if software && k.annahme.isSome then
    throw "entrust: isolation service must be a software binding"
  pure { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
    gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs,
    beleg := k.annahme.bind (fun n => assumptions.findIdx? fun x => strEq x n),
    software, names := k.names, needs, gives }

end Gabbro.Grammatik.Parser.Uebersetze
