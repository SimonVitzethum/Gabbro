/- C16: the UCheck-to-CheckDecl derivation -- gate wrappers and the mark table.

   A declared check's Duty is a linear mark (`dutyName`): the probe consumes and produces
   it on every normal return (`Erzeuge.uProbeFn`), each gate wrapper threads it
   (`nimmt` and `gibt` both name the Duty): the wrapper consumes the Duty at its
   call and produces it back at its return, so the lowered body typechecks (the
   return needs the held marks to match the contract end up to order). The true
   retirement of a completed Duty -- dropping the mark instead of threading it --
   waits for the C14 test driver with an explicit retire step; until then no
   wrapper forges or drops a Duty: it threads exactly one. The formal admission
   (`checkOkB`, `CheckEntladung`) constrains only consumption membership, which
   threading satisfies, so no guarantee is weakened.

   `uMarken` is the declaration's mark table (the `linear`-flagged type items, then every
   check's Duty); `uMarkenPruef` refuses a `nimmt`/`gibt` that names no member.

   `uTorHuellen` derives one wrapper `UFn` per gate (`torHuellenName`): a nullary function
   that threads the check's Duty and invokes the gate, forwarding its parameters (none --
   a gate with parameters keeps its named refusal) and its result (empty, `bool`, range,
   option, tagged, reason value or aggregate, bound and returned; a reason channel or a
   `never` answer keeps its named refusal). The wrapper, not the written gate, is what the
   kernel `CheckDecl.gates` names: the written gate need not mention the Duty. A gate that
   names a sibling check keeps its named refusal: selecting among consumers is the
   test-driver policy (C14), not an auto-run of every gate.

   A gate may also name a C08 foreign body (`extern`/`raw`/`prim`/`divergent`
   declarations, `asm` bodies, `axiom` items without `requires`, `syscall`
   gates): the wrapper is still an ordinary nullary `UFn` threading the Duty,
   and the gate call is the ordinary foreign call Stage 0 already lowers.
   Infallible answer-less foreign bodies ride `axCall`; infallible `int`/`bool`
   answers ride `bindAx` with the forwarded result; fallible (reason-channel)
   `int`/`bool` answers ride `bindAxElse` whose error branch rethrows the exact
   declared reason while retaining the Duty -- a foreign failure never becomes
   a normal answer or successful discharge. Anything else keeps
   its named refusal: parameters, device handles, `never` answers, and answers
   without a wrapper form (references, options, tagged values, reason values,
   aggregates). An unclosed error branch is refused by the lowering, never
   silently admitted. -/

module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- The declaration's mark table: the names of the `linear`-flagged type items in
    declaration order, then every check's Duty, deduplicated. -/
def uMarken (ms : List SItemTief) (checks : List UCheck) : List String :=
  uEindeutig ((ms.filterMap fun | .typeT flags n _ _ _ => if flags.any (fun f => strEq f "linear") then some n else none | _ => none) ++ checks.map fun c => c.duty)

/-- Every consumed or produced mark of every function names a member of the mark table. -/
def uMarkenPruefAux (marken : List String) : List UFn → Except String Unit
  | [] => .ok ()
  | f :: rest =>
    match (f.nimmt ++ f.gibt).find? (fun m => !(marken.any (fun n => strEq n m))) with
    | some m => .error ("mark unknown: " ++ m)
    | none => uMarkenPruefAux marken rest

/-- The mark check of the unit: every `nimmt`/`gibt` names a declared mark. -/
def uMarkenPruef (marken : List String) (fns : List UFn) : Except String Unit :=
  uMarkenPruefAux marken fns

/-- A produced mark is never a table owner (C16): signatures never produce owners
    (`eigner_nie_erzeugt`); only the one-shot C09 mint creates one. A `gibt` naming
    a table's `owner` mark is refused by name. -/
def uGibtPruefAux (owners : List String) : List UFn → Except String Unit
  | [] => .ok ()
  | f :: rest =>
    match f.gibt.find? (fun m => owners.any (fun o => strEq o m)) with
    | some m => .error ("owner produced without mint: " ++ m)
    | none => uGibtPruefAux owners rest

/-- The owner-production check of the unit: no `gibt` names a table owner. -/
def uGibtPruef (owners : List String) (fns : List UFn) : Except String Unit :=
  uGibtPruefAux owners fns

/-- The wrapper of gate `gate` of check `cname`: it cannot collide with a written
    function, since `#` never stands in a source identifier. -/
def torHuellenName (cname gate : String) : String := cname ++ "#tor#" ++ gate

/-- The forwarded call and its return: the gate's value, bound and returned, or a bare
    call for a gate without a result. -/
def torErgebnis (gate : String) (f : UFn) : List UStmt × URet :=
  if f.resBool then ([.bindCall "ans" gate []], .bool (.var "ans"))
  else if f.res.isSome then ([.bindCall "ans" gate []], .val (.param "ans"))
  else if f.resOpt.isSome then ([.bindCall "ans" gate []], .opt (.var "ans"))
  else if f.resSum.isSome then ([.bindCall "ans" gate []], .sum (.var "ans"))
  else if f.resWhy.isSome then ([.bindCall "ans" gate []], .grund (.var "ans"))
  else if f.resTy.isSome then ([.bindCall "ans" gate []], .wert (.param "ans"))
  else ([.call gate []], .empty)

/-- Preserve every case of a closed foreign reason channel. Each arm returns
    that exact case; the final return only closes the syntactic continuation
    after the exhaustive match. All returns still owe the same Duty. -/
def torFehler (count : Nat) : List UStmt :=
  [.matchWhyBeg "e"] ++
    uMitTrenner ((List.range count).map fun i => [.ret (.why i)]) ++
    [.blkEnd, .ret (.why 0)]

/-- One gate wrapper over a C08 foreign body: a nullary function that threads the
    check's Duty and invokes the foreign body with the ordinary foreign call.
    The Duty threads on every path -- success and error alike -- so no path
    forges or drops it; foreign failures retain their exact reason channel and
    cannot complete the gate normally. -/
def uFremdHuelle (duty cname gate : String) (k : UFnKopf) : Except String UFn :=
  if !k.names.isEmpty then .error ("gate with parameters without wrapper form: " ++ gate)
  else if !k.griffe.isEmpty then .error ("gate with device handles without wrapper form: " ++ gate)
  else if k.resNever then .error ("gate without a return without wrapper form: " ++ gate)
  else match k.kanal with
  | .none =>
    match UFnKopf.axErg k with
    | .none =>
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := none, resBool := false, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := 0, held := [], puts := k.puts, gputs := k.gputs, nimmt := [duty], gibt := [duty], gives := [], needs := [], body := [.axCall gate []], ret := .empty, boden := none }
    | .some (.int lo hi) =>
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := some (lo, hi), resBool := false, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := 0, held := [], puts := k.puts, gputs := k.gputs, nimmt := [duty], gibt := [duty], gives := [], needs := [], body := [.bindAx "ans" gate []], ret := .val (.param "ans"), boden := none }
    | .some .bool =>
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := none, resBool := true, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := 0, held := [], puts := k.puts, gputs := k.gputs, nimmt := [duty], gibt := [duty], gives := [], needs := [], body := [.bindAx "ans" gate []], ret := .bool (.var "ans"), boden := none }
    | .some _ => .error ("foreign gate answer without wrapper form: " ++ gate)
  | .some (_, count) =>
    if count == 0 then .error ("foreign gate has an empty reason channel: " ++ gate) else
    match UFnKopf.axErg k with
    | .some (.int lo hi) =>
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := some (lo, hi), resBool := false, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := count, held := [], puts := k.puts, gputs := k.gputs, nimmt := [duty], gibt := [duty], gives := [], needs := [], body := [.bindAxElse "ans" gate [] "e"] ++ torFehler count ++ [.blkEnd], ret := .val (.param "ans"), boden := none }
    | .some .bool =>
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := none, resBool := true, resOpt := none, resSum := none, resWhy := none, resTy := none, gruende := count, held := [], puts := k.puts, gputs := k.gputs, nimmt := [duty], gibt := [duty], gives := [], needs := [], body := [.bindAxElse "ans" gate [] "e"] ++ torFehler count ++ [.blkEnd], ret := .bool (.var "ans"), boden := none }
    | _ => .error ("foreign gate answer without wrapper form: " ++ gate)

/-- One gate wrapper: a nullary function that threads the check's Duty and invokes
    the gate, forwarding its result shape. A gate naming no function of the unit
    falls through to the foreign bodies (`uFremdHuelle`). -/
def uTorHuelle (duty : String) (fns : List UFn) (fremd : List UFnKopf)
    (cname gate : String) : Except String UFn :=
  match fns.find? (fun f => strEq f.name gate) with
  | some f =>
    if !f.params.isEmpty then .error ("gate with parameters without wrapper form: " ++ gate)
    else if f.gruende != 0 then .error ("gate with a reason channel without wrapper form: " ++ gate)
    else if f.resTy == some Ty.never then .error ("gate without a return without wrapper form: " ++ gate)
    else
      let (body, ret) := torErgebnis gate f
      .ok { name := torHuellenName cname gate, params := [], kinds := [], res := f.res, resBool := f.resBool, resOpt := f.resOpt, resSum := f.resSum, resWhy := f.resWhy, resTy := f.resTy, gruende := 0, held := [], puts := [], gputs := [], nimmt := [duty], gibt := [duty], gives := [], needs := [], body := body, ret := ret, boden := none }
  | none =>
    match fremd.find? (fun k => strEq k.name gate) with
    | none => .error ("gate without wrapper form: " ++ gate)
    | some k => uFremdHuelle duty cname gate k

def uTorTore (fns : List UFn) (fremd : List UFnKopf) (cname duty : String) :
    List String → List String → Except String (List UFn)
  | [], _ => .ok []
  | g :: rest, gesehen =>
    if gesehen.any (fun m => strEq m g) then .error ("duplicate gate: " ++ g)
    else match uTorHuelle duty fns fremd cname g with
    | .error e => .error e
    | .ok w =>
      match uTorTore fns fremd cname duty rest (g :: gesehen) with
      | .error e => .error e
      | .ok ws => .ok (w :: ws)

def uTorHuellenAux (fns : List UFn) (fremd : List UFnKopf) (checks : List UCheck) :
    List UCheck → Except String (List UFn)
  | [] => .ok []
  | c :: rest =>
    match c.tore.find? (fun g => checks.any (fun d => strEq d.name g)) with
    | some g => .error ("gate naming a check without driver form: " ++ g)
    | none =>
      match uTorTore fns fremd c.name c.duty c.tore [] with
      | .error e => .error e
      | .ok ws =>
        match uTorHuellenAux fns fremd checks rest with
        | .error e => .error e
        | .ok mehr => .ok (ws ++ mehr)

/-- Every gate of every check derives its Duty-threading wrapper. -/
def uTorHuellen (fns : List UFn) (fremd : List UFnKopf) (checks : List UCheck) :
    Except String (List UFn) :=
  uTorHuellenAux fns fremd checks checks

end Gabbro.Grammatik.Parser.Uebersetze
