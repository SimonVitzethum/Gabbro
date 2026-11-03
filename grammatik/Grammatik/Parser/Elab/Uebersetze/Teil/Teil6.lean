module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Payload

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def uEffekte (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) (globs : List UGlob) :
    List SKlausel → Except String UEffekte
  | ks =>
    let es := uWirkungen ks
    -- An omitted `effects` is DERIVED by the checker (lane 191); here it is read as the empty
    -- set. That is never more permissive than the derived one: a body that writes a table or
    -- takes a lock is refused by the lowering (`hw : V.schreibt t = true` has no proof).
    uEffekteAux kopf tabs locks globs es
where
  uWirkungen : List SKlausel → List SEffekt
    | [] => []
    | .effs es :: rest => es ++ uWirkungen rest
    | _ :: rest => uWirkungen rest
  uHatWirkung : List SKlausel → Bool
    | [] => false
    | .effs _ :: _ => true
    | _ :: rest => uHatWirkung rest

/-- Select the original decreases expression. -/
def dropsOf : SKlausel → Option SExpr
  | .drops e => some e
  | _ => none

/-- Every conversion in a collected measure names a type of the unit's alias scope;
    a call to anything else is a call and stays refused, including below arithmetic. -/
def uMeasureCheck (alias : List (String × (Int × Int))) : UMeasure → Except String Unit
  | .conv f a =>
    match uTypName alias f with
    | .ok _ => uMeasureCheck alias a
    | .error _ => .error "unsupported call in decreases"
  | .bin _ a b =>
    match uMeasureCheck alias a with
    | .ok _ => uMeasureCheck alias b
    | .error e => .error e
  | .un _ a => uMeasureCheck alias a
  | _ => .ok ()

/-- Collect exactly one written measure. The surface grammar has one expression, not a tuple. -/
def uMeasureClause (alias : List (String × (Int × Int))) (ks : List SKlausel) :
    Except String (Option UMeasure) :=
  match ks.filterMap dropsOf with
  | [] => .ok none
  | [e] =>
    match uMeasureSource e with
    | .ok m =>
      match uMeasureCheck alias m with
      | .ok _ => .ok (some m)
      | .error err => .error err
    | .error err => .error err
  | _ => .error "duplicate or ambiguous decreases clause"

/-- Clauses without G counterpart (the refused row of `check_fn`): `refines`, `maintains`,
    `by`, `advances`, `retires`. `costs`, `section` and `payload` travel nowhere and are ignored, like in
    `lean_g.rs`; so is `deadline <= n ops arch X falsifier p` (with its `arch` word): the date is owed to the
    machine and discharged by a probe, so the clause is dropped like `costs` (lane 255 of the exporter). -/
def uOhneKlauselForm : List SKlausel → Except String Unit
  | [] => .ok ()
  | .moves _ _ :: _ => .error "clause without G form"
  | .quits _ :: _ => .error "clause without G form"
  | _ :: rest => uOhneKlauselForm rest

/-- Deduplicate while keeping order (the `seen` loop of
    `check_fn`). -/
def uEindeutigAux : List String → List String → List String
  | [], _ => []
  | x :: rest, seen =>
    if seen.any (strEq · x) then uEindeutigAux rest seen
    else x :: uEindeutigAux rest (x :: seen)

def uEindeutig (xs : List String) : List String :=
  uEindeutigAux xs []

/-- A device handle type: `D` or `ptr<space, rights> D` for a device `D` of the unit. -/
def uGriffTyp (devs : List String) : STyp → Option String
  | .atom d => if devs.any (strEq · d) then some d else none
  | .ptr _ _ (.atom d) => if devs.any (strEq · d) then some d else none
  | _ => none

/-- The device handles of a written parameter list: position, name, device. -/
def uGriffe (devs : List String) : Nat → List (String × STyp) → List (Nat × String × String)
  | _, [] => []
  | k, (n, ty) :: rest =>
    match uGriffTyp devs ty with
    | some d => (k, n, d) :: uGriffe devs (k + 1) rest
    | none => uGriffe devs (k + 1) rest

/-- The written parameters without the device handles (a handle is no value of the model). -/
def uOhneGriffe (devs : List String) (ps : List (String × STyp)) : List (String × STyp) :=
  ps.filter (fun p => (uGriffTyp devs p.2).isNone)

/-- Pass one: the head of an `impl` function (non-`impl`,
    bodiless and clause-carrying forms are explicit errors).
    Returns the head and the written tables. -/
def elabKopf (_consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (sums : List USum := [])
    (sig : FnSig) (devs : List String := []) (zeiger : List String := []) (zb : Nat := 0) (spaces : List String := []) (named : List (String × Ty) := []) (eigner : List String := []) :
    Except String (UFnKopf × List String) :=
  match sig with
  | { art, name, params := params0, res, fehler, klauseln } =>
    let params := uOhneGriffe devs params0
    -- a `fn` without a kind word and with a body is an implemented function, like `impl fn` (the checker's
    -- `None | Some(Impl)`)
    -- A `library fn` is an ordinary implemented function: its body elaborates like `impl`. The
    -- payload calling convention lives in the CALLERS, expanded by `exportLibraryUnit` before the
    -- lowering runs; the certificate side is `TranslationDecl`/`LibraryExpansion`.
    if !(strEq art "impl" || strEq art "" || strEq art "library") then .error "fn is not impl"
    else
      match uMeasureClause alias klauseln, uOhneKlauselForm klauseln with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok _, .ok _ =>
        match uSeq (params.map (uParam alias tabs sums whys zeiger zb spaces named eigner)) with
        | .error e => .error e
        | .ok ps =>
          let names := ps.map (·.1)
          let types := ps.map (·.2.1)
          let kinds := ps.map (·.2.2)
          match uGehalten locks klauseln with
          | .error e => .error e
          | .ok held =>
            match (match fehler with
                | .none => .ok none
                | .some r =>
                  match whys.findIdx? (fun w => strEq w.name r) with
                  | .none => .error ("reason unknown: " ++ r)
                  | .some k =>
                    match whys[k]? with
                    | .some w => if w.cases.isEmpty then .error "reason without cases" else .ok (some (k, w.cases.length))
                    | .none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) with
            | .error e => .error e
            | .ok kn =>
            let kopf : UFnKopf :=
              { name, names, kinds, types, res := .none, bits := params.map (fun p => uParamBreite p.2), held := uEindeutig held, kanal := kn, griffe := uGriffe devs 0 params0 }
            match uEffekte kopf tabs locks globs klauseln with
            | .error e => .error e
            | .ok eff =>
              -- A `locks L` effect needs no `requires Held(L)`: a `locks L { .. }` statement acquires
              -- it inside the body, and an access whose guard is not held is refused by the LOWERING
              -- (`access without held guard`), so nothing is claimed here.
              let puts := uEindeutig eff.puts
              let kopf := { kopf with gputs := uEindeutig eff.gputs, nimmt := uEindeutig eff.nimmt, gibt := uEindeutig eff.gibt, leiht := uEindeutig eff.leiht }
              match res with
              | .none => .ok (kopf, puts)
              | .some (.atom "bool") =>
                .ok ({ kopf with resBool := true }, puts)
              | .some (.atom "never") =>
                .ok ({ kopf with resTy := some Ty.never }, puts)
              | .some (.index true tn) =>
                match uTabNr tabs tn with
                | .error e => .error e
                | .ok (num, c) => .ok ({ kopf with resOpt := some (num, c) }, puts)
              | .some (.atom a) =>
                match sums.findIdx? (fun s => strEq s.name a) with
                | .some k =>
                  match sums[k]? with
                  | .some s => .ok ({ kopf with resSum := some (k, s.spec) }, puts)
                  | .none => .error ("type unknown: " ++ a)
                | .none =>
                  match whys.findIdx? (fun w => strEq w.name a) with
                  | .some k =>
                    match whys[k]? with
                    | .some w => .ok ({ kopf with resWhy := some (k, w.cases.length) }, puts)
                    | .none => .error ("reason unknown: " ++ a)
                  | .none =>
                  match uTypIn alias tabs named spaces eigner (.atom a) with
                  | .error e => .error e
                  | .ok (.int lo hi) => .ok ({ kopf with res := some (lo, hi) }, puts)
                  | .ok ty => .ok ({ kopf with resTy := some ty }, puts)
              | .some t =>
                match t with
                | .array _ _ | .str _ =>
                  match uTypIn alias tabs named spaces eigner t with
                  | .error e => .error e
                  | .ok τ => .ok ({ kopf with resTy := .some τ }, puts)
                | _ =>
                match uErgBereich alias t with
                | .error e => .error e
                | .ok r =>
                  .ok ({ kopf with res := .some r }, puts)

def uSValEin (ctx : UCtx) : SExpr → Except String (USVal × Nat)
  | .variable v =>
    match uParamNr ctx v with
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.sum s) => .ok (.var v, s)
      | _ => .error "tagged value without G form"
    | .error _ =>
      match ctx.sums.findIdx? (fun s => s.cases.any (fun c => strEq c.1 v && c.2.isNone)) with
      | .none => .error ("name unknown: " ++ v)
      | .some k =>
        match ctx.sums[k]? with
        | .none => .error "tagged type unknown"
        | .some s =>
          match s.cases.findIdx? (fun c => strEq c.1 v) with
          | .some i => .ok (.fall i .none, k)
          | .none => .error ("name unknown: " ++ v)
  | .call c [a] =>
    match ctx.sums.findIdx? (fun s => s.cases.any (fun x => strEq x.1 c && x.2.isSome)) with
    | .none => .error "tagged value without G form"
    | .some k =>
      match ctx.sums[k]? with
      | .none => .error "tagged type unknown"
      | .some s =>
        match s.cases.findIdx? (fun x => strEq x.1 c) with
        | .none => .error "tagged value without G form"
        | .some i =>
          match (s.cases[i]?).bind (·.2) with
          | none => .error "case has no payload"
          | some τ =>
            match uPayload ctx τ a with
            | .error e => .error e
            | .ok sd => .ok (.fall i (.some sd), k)
  | _ => .error "tagged value without G form"

/-- A tagged value of the type at `sidx`. -/
def uSVal (ctx : UCtx) (sidx : Nat) (e : SExpr) : Except String USVal :=
  match uSValEin ctx e with
  | .error x => .error x
  | .ok (v, k) => if k == sidx then .ok v else .error "tagged value of a foreign type"

/-- One call argument against the callee's parameter kind (the
    `tr_arg` of `lean_g.rs`): a pointer variable through, a
    fresh pointer where the rights differ, an index literal or
    parameter, a value otherwise. -/
def uArg (ctx : UCtx) (tabs : List UTab) : UParamArt → SExpr →
    Except String UArg
  | .ptr cap, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr source) =>
        if source = cap then .ok (.var p)
        else if source.attenuates cap then
          match cap.target with
          | .table num =>
            match tabs[num]? with
            | some tb => .ok (.freshPtr tb.name cap)
            | none => .error "pointer table unknown"
        else .error "pointer argument would widen rights, owner, space or target"
      | _ => .error "pointer argument without G form"
  | .ptr cap, .fnref t =>
    match cap.target with
    | .table num =>
      match tabs[num]? with
      | some tb => if strEq tb.name t then .ok (.freshPtr tb.name cap) else .error "argument of foreign table"
      | none => .error "pointer table unknown"
  | .index num, a =>
    match tabs[num]? with
    | .none => .error "index table unknown"
    | .some tb =>
      match uIndex ctx tb.name num a with
      | .error e => .error e
      | .ok (.lit v) => .ok (.val (.lit v))
      | .ok (.param p) => .ok (.val (.param p))
  | .wert, a => (uWertBody ctx a).map UArg.val
  | .int, a =>
    match uWertBody ctx a with
    | .error e => .error e
    | .ok s => .ok (.val s)
  | .bool, a =>
    match uBool ctx a with
    | .error e => .error e
    | .ok b => .ok (.bval b)
  | .opt num, a =>
    match uOpt ctx num a with
    | .error e => .error e
    | .ok o => .ok (.oval o)
  | .why k, .why r c =>
    match ctx.whys[k]? with
    | .some w =>
      if !strEq w.name r then .error "argument of a foreign reason"
      else
        match w.cases.findIdx? (fun x => strEq x c) with
        | .some i => .ok (.gval (.fall i))
        | .none => .error ("reason case unknown: " ++ c)
    | .none => .error "reason unknown"
  | .why k, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.why k') => if k' == k then .ok (.gval (.var p)) else .error "argument of a foreign reason"
      | _ => .error "argument without G form"
  | .fnptr m, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.fnptr m2) =>
        if m == m2 then .ok (.var p) else .error "function pointer of another type as an argument"
      | _ => .error "pointer argument without G form"
  | .fnptr _, .fnref f => .ok (.fnref f)
  | _, _ => .error "argument without G form"

def uArgs (ctx : UCtx) (tabs : List UTab) : List UParamArt → List SExpr →
    Except String (List UArg)
  | [], [] => .ok []
  | k :: ks, a :: rest =>
    match uArg ctx tabs k a with
    | .error e => .error e
    | .ok x =>
      match uArgs ctx tabs ks rest with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)
  | _, _ => .error "argument count without G form"

/-- `a[i] = v` on an aggregate held by the static at the root of `a`: the static and its new value, the element at
    `i` replaced (`USide.upd`) at every level (`M[i][j] = v` replaces row `i` of `M` by the row with element `j`
    replaced). -/
def uElemSchreib (ctx : UCtx) : SExpr → SExpr → USide → Except String (String × USide)
  | .variable g, i, v =>
    match uWertBody ctx i with
    | .error x => .error x
    | .ok y => .ok (g, .upd (.glob g) y v)
  | .index a j, i, v =>
    match uWertBody ctx (.index a j), uWertBody ctx i with
    | .ok cur, .ok y => uElemSchreib ctx a j (.upd cur y v)
    | .error x, _ | _, .error x => .error x
  | _, _, _ => .error "element write without G form"

/-- `X = v;` where `X` is a static (the place reader found no slot): only a `mut` static is written. -/
def uGlobSchreib (ctx : UCtx) (ziel wert : SExpr) (e : String) : Except String UStmt :=
  match ziel with
  | .variable g =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .none => .error e
    | .some gl =>
      if !gl.var then .error "write to an immutable static"
      else if gl.atomic then .error "plain write to an atomic: every store is a publish"
      else
        match gl.ty, gl.optNum with
        | _, .some num =>
          match uOpt ctx num wert with
          | .error x => .error x
          | .ok o => .ok (.assignGlobO g o)
        | .bool, _ =>
          match uBool ctx wert with
          | .error x => .error x
          | .ok v => .ok (.assignGlobB g v)
        | _, _ =>
          match uWertBody ctx wert with
          | .error x => .error x
          | .ok v => .ok (.assignGlob g v)
  | .index a i =>
    match uWertBody ctx wert with
    | .error x => .error x
    | .ok v =>
      match uElemSchreib ctx a i v with
      | .error x => .error x
      | .ok (g, w) =>
        match ctx.globs.find? (fun x => strEq x.name g) with
        | .some gl =>
          if !gl.var then .error "write to an immutable static"
          else if gl.atomic then .error "plain write to an atomic: every store is a publish"
          else .ok (.assignGlob g w)
        | .none => .error e
  | _ => .error e

/-- The words of a raw payload, as character lists (split at blanks and commas). -/
def uWoerter : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc =>
    if c == ' ' || c == ',' then (if acc.isEmpty then uWoerter cs [] else acc.reverse :: uWoerter cs [])
    else uWoerter cs (c :: acc)

/-- The names of a payload as the statement reader keeps it (raw words: `p , q `, or `nothing`). -/
def uNutzNamen (p : String) : List (List Char) :=
  if strEq p "nothing" then [] else uWoerter p.toList []

/-- A payload as written names exactly the declared list. -/
def uNamenGleich : List (List Char) → List String → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b.toList && uNamenGleich as bs
  | _, _ => false

/-- `A = v publishes { p, q };` (or `nothing`): the store of an atomic with exactly its declared payload
    (`Stmt.publish`, the payload `D.nutzlast A`). -/
def uAtomSchreib (ctx : UCtx) (ziel wert : SExpr) (p : String) : Except String UStmt :=
  match ziel with
  | .variable g =>
    match ctx.globs.find? (fun x => strEq x.name g) with
    | .none => .error "publishes without an atomic without G form"
    | .some gl =>
      if !gl.atomic then .error "publishes without an atomic without G form"
      else if !uNamenGleich (uNutzNamen p) gl.nutzlast then .error "publishes a payload other than the declared one"
      else
        match gl.ty with
        | .bool =>
          match uBool ctx wert with
          | .error x => .error x
          | .ok v => .ok (.storeAtomB g v)
        | _ =>
          match uWertBody ctx wert with
          | .error x => .error x
          | .ok v => .ok (.storeAtom g v)
  | _ => .error "publishes without an atomic without G form"

/-- The arguments of a call without those at the callee's device handles; each of those must be a handle of
    the same device in the caller (a handle is no value of the model: the register is named by the device). -/
def uOhneGriffArgs (ctx : UCtx) (gs : List (Nat × String × String)) : Nat → List SExpr →
    Except String (List SExpr)
  | _, [] => .ok []
  | k, a :: rest =>
    match gs.find? (fun g => g.1 == k) with
    | none =>
      match uOhneGriffArgs ctx gs (k + 1) rest with
      | .error e => .error e
      | .ok xs => .ok (a :: xs)
    | some (_, _, d) =>
      match a with
      | .variable h =>
        if ctx.griffe.any (fun p => strEq p.1 h && strEq p.2 d) then uOhneGriffArgs ctx gs (k + 1) rest
        else .error "device argument without G form"
      | _ => .error "device argument without G form"

/-- A register place through a device handle in scope: `d.R` (`some` of the register, or of an error for an
    unknown register); `d.R.F` (a register field) has no G form; anything else is no register place. -/
def uRegOrt (ctx : UCtx) : SExpr → Option (Except String UReg)
  | .field (.variable h) r =>
    if ctx.names.any (strEq · h) then none else
    match ctx.griffe.find? (fun p => strEq p.1 h) with
    | none => none
    | some (_, d) =>
      some (match ctx.regs.find? (fun g => strEq g.dev d && strEq g.name r) with
        | some g => .ok g
        | none => .error ("register unknown: " ++ r))
  | .field (.field (.variable h) _) _ =>
    if ctx.names.any (strEq · h) then none
    else if ctx.griffe.any (fun p => strEq p.1 h) then some (.error "register field without G form")
    else none
  | _ => none

/-- A direct call: the callee and its arguments against the callee's parameter kinds. The callee's required
    locks must be held (`RufPasst.hh`); an extra lock of the caller must rank below the callee's floor
    (`RufPasst.hx`), which the lowering decides (`floorUeberB`). -/
def uRuf (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (c : String) (args : List SExpr) :
    Except String (UFnKopf × List UArg) :=
  match koepfe.find? (fun k => strEq k.name c) with
  | .none => .error ("call unknown: " ++ c)
  | .some callee =>
    if !(callee.held.all (fun l => ctx.held.any (strEq · l))) then .error "call without held guard"
    else
      match uOhneGriffArgs ctx callee.griffe 0 args with
      | .error e => .error e
      | .ok args' =>
        match uArgs ctx tabs callee.kinds args' with
        | .error e => .error e
        | .ok xs => .ok (callee, xs)

/-- The scope after `let e` of a reason (`Ty.why n`, `n` the number of cases). -/
def UFn.mitWhy (f : UFn) (x : String) (num n : Nat) : UFn :=
  { f with params := (x, Ty.why n) :: f.params, kinds := .why num :: f.kinds }

/-- The value written into a wrapping field: `(v + m) % m` (the `+ m` keeps a difference that went below zero by
    at most `m` non-negative); any other field takes `v` as it is. -/
def uWrap (ctx : UCtx) (tb f : String) (v : USide) : USide :=
  match (ctx.tabs.find? (fun t => strEq t.name tb)).bind (fun t => t.wraps.find? (fun p => strEq p.1 f)) with
  | some (_, m) => .rem (.add v (.lit m)) (.lit m)
  | none => v

end Gabbro.Grammatik.Parser.Uebersetze
