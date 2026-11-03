module

public import Grammatik.Parser.Elab.Uebersetze.Akku.Erzeuge
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-! ## Use-site expansion

    Supported positions rewrite to calls of the generated functions; every
    other mention of an accumulator name is refused by name (reads go through
    the sampled fold under the cell locks, never bare). A unit that binds an
    accumulator name as a local is refused up front, so the rewrite stays
    scope-unaware without misreading a shadowed name. -/

/-- The locally bound names of a body (binders only; types and places cannot
    bind; loop labels live in their own namespace). -/
def uAkkuBinder : Nat → SAnw → List String
  | 0, _ => []
  | _ + 1, .bind _ x _ _ => [x]
  | f + 1, .bindElse x _ _ y b => x :: y :: uAkkuBinder f b
  | f + 1, .bindLib _ x _ _ => [x]
  | f + 1, .bindQ _ x _ _ => [x]
  | f + 1, .alloc _ x _ _ _ cont =>
    x :: (match cont with | none => [] | some b => uAkkuBinder f b)
  | f + 1, .allocVon _ x _ _ => [x]
  | f + 1, .await x _ _ _ => [x]
  | f + 1, .swap x _ _ _ => [x]
  | f + 1, .arm _ bnd b => (match bnd with | none => [] | some y => [y]) ++ uAkkuBinder f b
  | f + 1, .each b _ _ _ _ _ _ body => b :: uAkkuBinder f body
  | f + 1, .bindAxiomOpt x _ _ => [x]
  | f + 1, .bindAxiomOptElse x _ _ y b => x :: y :: uAkkuBinder f b
  | f + 1, .cond _ t ei els =>
    uAkkuBinder f t ++ ei.flatMap (uAkkuBinder f) ++
      (match els with | none => [] | some b => uAkkuBinder f b)
  | f + 1, .elsif _ b => uAkkuBinder f b
  | f + 1, .cases _ arms => arms.flatMap (uAkkuBinder f)
  | f + 1, .retry _ b => uAkkuBinder f b
  | f + 1, .loop _ b => uAkkuBinder f b
  | f + 1, .trim _ _ b => uAkkuBinder f b
  | f + 1, .locks _ _ b => uAkkuBinder f b
  | f + 1, .watch _ b => uAkkuBinder f b
  | f + 1, .waive _ b => uAkkuBinder f b
  | f + 1, .grow _ _ b => uAkkuBinder f b
  | f + 1, .child b => uAkkuBinder f b
  | f + 1, .block ss _ => ss.flatMap (uAkkuBinder f)
  | _, _ => []

/-- No plan name is bound as a local in the unit's bodies or parameters:
    otherwise the rewrite below could misread a shadowed name. -/
def uAkkuKeinSchatten (ps : List AkkuPlan) (fns : List (FnSig × SAnw)) :
    Except String Unit :=
  let gebunden := fns.flatMap fun (s, b) => s.params.map (·.1) ++ uAkkuBinder 100000 b
  match ps.find? (fun p => gebunden.any (strEq · p.name)) with
  | some p => .error ("accumulator name bound as a local without G form: " ++ p.name)
  | none => .ok ()

/-- The plan of an accumulator mention, if any. -/
def uAkkuPlanFuer (ps : List AkkuPlan) (n : String) : Option AkkuPlan :=
  ps.find? (fun p => strEq p.name n)

/-- The accumulator names of the plans. -/
def uAkkuPlanNamen (ps : List AkkuPlan) : List String :=
  ps.map (·.name)

/-- The sampled-fold binder of a read. -/
def uAkkuLese (p : AkkuPlan) : String :=
  p.name ++ "#lese"

/-- Refuse a bare mention in an expression position: reads go through the
    sampled fold under the cell locks, never bare. -/
def uAkkuBareRefuse {α : Type} (_e : SExpr) : Except String α :=
  .error "accumulator read without G form: reads go through the sampled fold under the cell locks, never bare"

/-- Expand the effects: `writes n` names every cell, `reads n` reads every
    cell; any other mention of `n` is refused. -/
def uAkkuExpandEffs (ps : List AkkuPlan) (ns : List String) :
    List SEffekt → Except String (List SEffekt)
  | [] => .ok []
  | e :: rest =>
    match e with
    | .writes (.variable n) =>
      match uAkkuPlanFuer ps n with
      | some p =>
        match uAkkuExpandEffs ps ns rest with
        | .error x => .error x
        | .ok rs => .ok ((List.range p.kernZahl).map (fun i =>
            .writes (.variable (p.name ++ "#zelle" ++ toString i))) ++ rs)
      | none =>
        if uAkkuInExpr 100000 ns (.variable n) then
          .error "accumulator use without G form: writes go through the update, never bare"
        else
          match uAkkuExpandEffs ps ns rest with
          | .error x => .error x
          | .ok rs => .ok (e :: rs)
    | .reads (.variable n) =>
      match uAkkuPlanFuer ps n with
      | some p =>
        match uAkkuExpandEffs ps ns rest with
        | .error x => .error x
        | .ok rs => .ok ((List.range p.kernZahl).map (fun i =>
            .reads (.variable (p.name ++ "#zelle" ++ toString i))) ++ rs)
      | none =>
        if uAkkuInExpr 100000 ns (.variable n) then uAkkuBareRefuse (.variable n)
        else
          match uAkkuExpandEffs ps ns rest with
          | .error x => .error x
          | .ok rs => .ok (e :: rs)
    | _ =>
      if uAkkuInEffekt 100000 ns e then uAkkuBareRefuse (.variable "")
      else
        match uAkkuExpandEffs ps ns rest with
        | .error x => .error x
        | .ok rs => .ok (e :: rs)

/-- Expand the contract clauses: effects expand to the full carrier set;
    any other mention of an accumulator name is refused. -/
def uAkkuExpandKlauseln (ps : List AkkuPlan) (ns : List String) :
    List SKlausel → Except String (List SKlausel)
  | [] => .ok []
  | .effs es :: rest =>
    match uAkkuExpandEffs ps ns es with
    | .error x => .error x
    | .ok es' =>
      match uAkkuExpandKlauseln ps ns rest with
      | .error x => .error x
      | .ok rs => .ok (.effs es' :: rs)
  | k :: rest =>
    if uAkkuInKlausel 100000 ns k then
      .error "accumulator contract without G form: contracts name the generated cells, never the accumulator"
    else
      match uAkkuExpandKlauseln ps ns rest with
      | .error x => .error x
      | .ok rs => .ok (k :: rs)

/-- Expand a signature's clauses. -/
def uAkkuExpandSig (ps : List AkkuPlan) (sig : FnSig) : Except String FnSig :=
  let ns := uAkkuPlanNamen ps
  match uAkkuExpandKlauseln ps ns sig.klauseln with
  | .error x => .error x
  | .ok ks => .ok { sig with klauseln := ks }

mutual

/-- Expand one statement; a trailing bare read splices a fold binding, so
    the result is a statement list. -/
def uAkkuExpandAnw (ps : List AkkuPlan) (ns : List String) : Nat → SAnw →
    Except String (List SAnw)
  | 0, _ => .error "accumulator expansion without fuel"
  | _ + 1, .set (.variable n) op v =>
    match uAkkuPlanFuer ps n with
    | some p =>
      if !(strEq op "=") then
        .error "accumulator compound update without G form: only plain assignment merges"
      else if uAkkuInExpr 100000 ns v then uAkkuBareRefuse v
      else .ok [.call p.akt [v]]
    | none =>
      if uAkkuInExpr 100000 ns (.variable n) || uAkkuInExpr 100000 ns v then
        uAkkuBareRefuse v
      else .ok [.set (.variable n) op v]
  | f + 1, .set t op v =>
    if uAkkuInExpr 100000 ns t || uAkkuInExpr 100000 ns v then uAkkuBareRefuse v
    else .ok [.set t op v]
  | f + 1, .bind mu x t (.variable n) =>
    match uAkkuPlanFuer ps n with
    | some p =>
      if mu then .error "accumulator mut fold without G form: bind the sampled fold plainly"
      else .ok [.bind false x t (.call p.falt [])]
    | none =>
      if uAkkuInExpr 100000 ns (.variable n) then uAkkuBareRefuse (.variable n)
      else .ok [.bind mu x t (.variable n)]
  | f + 1, .bind mu x t e =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else .ok [.bind mu x t e]
  | f + 1, .call g args =>
    if (uAkkuPlanFuer ps g).isSome then
      .error "accumulator call without G form: updates are plain assignments, reads are plain values"
    else if args.any (uAkkuInExpr 100000 ns) then uAkkuBareRefuse (.call g args)
    else .ok [.call g args]
  | f + 1, .ret (some (.variable n)) =>
    match uAkkuPlanFuer ps n with
    | some p => .ok [.bind false (uAkkuLese p) none (.call p.falt []),
        .ret (some (.variable (uAkkuLese p)))]
    | none =>
      if uAkkuInExpr 100000 ns (.variable n) then uAkkuBareRefuse (.variable n)
      else .ok [.ret (some (.variable n))]
  | f + 1, .ret v =>
    match v with
    | some e => if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e else .ok [.ret v]
    | none => .ok [.ret v]
  | f + 1, .block ss ende =>
    match uAkkuExpandAnws ps ns f ss with
    | .error x => .error x
    | .ok ss' =>
      match ende with
      | some (.ret (some (.variable n))) =>
        match uAkkuPlanFuer ps n with
        | some p => .ok [.block (ss' ++ [.bind false (uAkkuLese p) none
            (.call p.falt [])]) (some (.ret (some (.variable (uAkkuLese p)))))]
        | none =>
          if uAkkuInExpr 100000 ns (.variable n) then uAkkuBareRefuse (.variable n)
          else .ok [.block ss' ende]
      | some (.ret (some e)) =>
        if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
        else .ok [.block ss' ende]
      | _ => .ok [.block ss' ende]
  | f + 1, a => uAkkuExpandAnwAtom ps ns f a

/-- Expand a statement list. -/
def uAkkuExpandAnws (ps : List AkkuPlan) (ns : List String) : Nat →
    List SAnw → Except String (List SAnw)
  | _, [] => .ok []
  | 0, _ => .error "accumulator expansion without fuel"
  | f + 1, a :: rest =>
    match uAkkuExpandAnw ps ns f a with
    | .error x => .error x
    | .ok xs =>
      match uAkkuExpandAnws ps ns f rest with
      | .error x => .error x
      | .ok ys => .ok (xs ++ ys)

/-- Expand a nested statement: exactly one statement out (a bare read here is
    refused, as the parser only produces trailing reads at block enders). -/
def uAkkuExpandEins (ps : List AkkuPlan) (ns : List String) : Nat → SAnw →
    Except String SAnw
  | 0, _ => .error "accumulator expansion without fuel"
  | f + 1, a =>
    match uAkkuExpandAnw ps ns f a with
    | .error x => .error x
    | .ok [x] => .ok x
    | .ok _ => .error "accumulator return outside a block without G form"

/-- Expand the else branch of a conditional. -/
def uAkkuExpandElse (ps : List AkkuPlan) (ns : List String) : Nat →
    Option SAnw → Except String (Option SAnw)
  | _, none => .ok none
  | 0, _ => .error "accumulator expansion without fuel"
  | f + 1, some b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok (some b')

/-- Refuse a bare mention in a call position. -/
def uAkkuRufRefuse (g : String) (_args : List SExpr) : Except String (List SAnw) :=
  .error ("accumulator call without G form: updates are plain assignments, reads are plain values: " ++ g)

/-- Expand every remaining statement form: recurse into child statements,
    refuse bare mentions in expression positions. -/
def uAkkuExpandAnwAtom (ps : List AkkuPlan) (ns : List String) : Nat → SAnw →
    Except String (List SAnw)
  | 0, _ => .error "accumulator expansion without fuel"
  | f + 1, .cond c t ei els =>
    if uAkkuInExpr 100000 ns c then uAkkuBareRefuse c
    else
      match uAkkuExpandEins ps ns f t with
      | .error x => .error x
      | .ok t' =>
        match uSeq (ei.map (uAkkuExpandEins ps ns f)) with
        | .error x => .error x
        | .ok ei' =>
          match uAkkuExpandElse ps ns f els with
          | .error x => .error x
          | .ok els' => .ok [.cond c t' ei' els']
  | f + 1, .elsif c b =>
    if uAkkuInExpr 100000 ns c then uAkkuBareRefuse c
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.elsif c b']
  | f + 1, .cases e arms =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uSeq (arms.map (uAkkuExpandEins ps ns f)) with
      | .error x => .error x
      | .ok arms' => .ok [.cases e arms']
  | f + 1, .arm n bnd b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.arm n bnd b']
  | f + 1, .each b o k s m raw inv body =>
    if (o.map (uAkkuInExpr 100000 ns)).getD false || uAkkuInExpr 100000 ns s ||
        (inv.map (uAkkuInExpr 100000 ns)).getD false then uAkkuBareRefuse s
    else
      match uAkkuExpandEins ps ns f body with
      | .error x => .error x
      | .ok body' => .ok [.each b o k s m raw inv body']
  | f + 1, .retry h b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.retry h b']
  | f + 1, .loop h b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.loop h b']
  | f + 1, .trim e z b =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.trim e z b']
  | f + 1, .trimReq e z =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else .ok [.trimReq e z]
  | f + 1, .locks g e b =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.locks g e b']
  | f + 1, .grow a e b =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.grow a e b']
  | f + 1, .watch d b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.watch d b']
  | f + 1, .child b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.child b']
  | f + 1, .waive inv b =>
    match uAkkuExpandEins ps ns f b with
    | .error x => .error x
    | .ok b' => .ok [.waive inv b']
  | f + 1, .alloc mu x t an v cont =>
    if uAkkuInExpr 100000 ns v then uAkkuBareRefuse v
    else
      match cont with
      | none => .ok [.alloc mu x t an v none]
      | some b =>
        match uAkkuExpandEins ps ns f b with
        | .error x => .error x
        | .ok b' => .ok [.alloc mu x t an v (some b')]
  | f + 1, .bindElse x t e y b =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.bindElse x t e y b']
  | f + 1, .bindQ mu x t e =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else .ok [.bindQ mu x t e]
  | _ + 1, .genericCall .. =>
    .error "unexpanded generic call without G form"
  | f + 1, .callQ g args =>
    if (uAkkuPlanFuer ps g).isSome || args.any (uAkkuInExpr 100000 ns) then
      uAkkuRufRefuse g args
    else .ok [.callQ g args]
  | f + 1, .bindAxiomOpt x t e =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else .ok [.bindAxiomOpt x t e]
  | f + 1, .bindAxiomOptElse x t e y b =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else
      match uAkkuExpandEins ps ns f b with
      | .error x => .error x
      | .ok b' => .ok [.bindAxiomOptElse x t e y b']
  | f + 1, .bindLib mu x t c =>
    if c.args.any (uAkkuInExpr 100000 ns) then uAkkuBareRefuse (.call "" c.args)
    else .ok [.bindLib mu x t c]
  | f + 1, .lcall c =>
    if c.args.any (uAkkuInExpr 100000 ns) then uAkkuBareRefuse (.call "" c.args)
    else .ok [.lcall c]
  | f + 1, .shift z a b =>
    if uAkkuInExpr 100000 ns z then uAkkuBareRefuse z
    else .ok [.shift z a b]
  | f + 1, .emit a b c =>
    if uAkkuInExpr 100000 ns a || uAkkuInExpr 100000 ns b then uAkkuBareRefuse a
    else .ok [.emit a b c]
  | f + 1, .await x t a pl =>
    if uAkkuInExpr 100000 ns a then uAkkuBareRefuse a
    else .ok [.await x t a pl]
  | f + 1, .swap x t o k =>
    if uAkkuInExpr 100000 ns o then uAkkuBareRefuse o
    else .ok [.swap x t o k]
  | f + 1, .free e =>
    if uAkkuInExpr 100000 ns e then uAkkuBareRefuse e
    else .ok [.free e]
  | f + 1, .reset a r =>
    match r with
    | none => .ok [.reset a none]
    | some (x, y) =>
      if uAkkuInExpr 100000 ns x || uAkkuInExpr 100000 ns y then uAkkuBareRefuse x
      else .ok [.reset a r]
  | _, a => .ok [a]

end

/-- Expand a whole function: its clauses and its body. -/
def uAkkuExpandFn (ps : List AkkuPlan) : FnSig × SAnw → Except String (FnSig × SAnw)
  | (sig, b) =>
    match uAkkuExpandSig ps sig with
    | .error x => .error x
    | .ok sig' =>
      match uAkkuExpandAnw ps (uAkkuPlanNamen ps) 100000 b with
      | .error x => .error x
      | .ok [b'] => .ok (sig', b')
      | .ok _ => .error "accumulator return outside a block without G form"

/-- Expand the unit's user functions and foreign signatures; the generated
    functions are appended by the pipeline, never expanded. -/
def uAkkuExpandUnit (ps : List AkkuPlan) (fns : List (FnSig × SAnw))
    (fremd : List FnSig) : Except String (List (FnSig × SAnw) × List FnSig) :=
  match uAkkuKeinSchatten ps fns with
  | .error x => .error x
  | .ok _ =>
    match uSeq (fns.map (uAkkuExpandFn ps)) with
    | .error x => .error x
    | .ok fns' =>
      match uSeq (fremd.map (uAkkuExpandSig ps)) with
      | .error x => .error x
      | .ok fremd' => .ok (fns', fremd')

/-- The C15 pipeline step: generate the query, update and reduction per
    `accumulates` item, expand accumulator uses in the user functions and
    foreign signatures. Returns the user functions with the generated ones
    appended, the query heads and the expanded foreign pairs. -/
def uAkkuVorlauf (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (ms : List SItemTief)
    (fnItems : List (FnSig × SAnw)) : Except String
    (List (FnSig × SAnw) × List UFnKopf × List (FnSig × Bool)) :=
  match uAkkuGenFns consts alias ms with
  | .error e => .error e
  | .ok gen =>
    let fremdPaare := ms.filterMap uFremdSig
    match uAkkuExpandUnit (gen.map fun g => g.1) fnItems (fremdPaare.map (·.1)) with
    | .error e => .error e
    | .ok (fnItems', fremdSigs') =>
      .ok (fnItems' ++ gen.flatMap fun g => [g.2.2.1, g.2.2.2],
        gen.map fun g => g.2.1,
        (fremdPaare.map (·.2)).zip fremdSigs' |>.map Prod.swap)

end Gabbro.Grammatik.Parser.Uebersetze
