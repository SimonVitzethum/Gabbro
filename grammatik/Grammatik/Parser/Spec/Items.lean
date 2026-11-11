module

public import Grammatik.Parser.Spec.Walk

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

def Walk.invariant (w : Walk) (i : SGruppenInv) : Except String SGruppenInv := do
  return { i with kosten := ← w.expr [] 1000 i.kosten, pred := ← w.expr [] 1000 i.pred }

def Walk.field (w : Walk) (f : SFeld) : Except String SFeld := do
  return { f with ftyp := ← w.type [] 1000 f.ftyp, wo := ← f.wo.mapM (w.expr [] 1000) }

mutual
def Walk.constant (w : Walk) : Nat → SKonstWert → Except String SKonstWert
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, .one e => do return .one (← w.expr [] f e)
  | f + 1, .rows vs => do return .rows (← vs.mapM (w.constant f))
end

def Walk.tablePart (w : Walk) : STabTeil → Except String STabTeil
  | .tConst n t v => do return .tConst n (← w.type [] 1000 t) (← w.constant 1000 v)
  | .tSlot fs => do return .tSlot (← fs.mapM w.field)
  | .tInv i => do return .tInv (← w.invariant i)
  | p => pure p

def Walk.transition (w : Walk) (t : STrans) : Except String STrans := do
  let steps ← t.schritte.mapM fun (a, b, c) =>
    return (← w.expr [] 1000 a, ← w.expr [] 1000 b, ← w.expr [] 1000 c)
  return { t with
    schritte := steps
    voraus := ← t.voraus.mapM (w.expr [] 1000)
    wirkung := ← w.effects [] t.wirkung }

def Walk.devicePart (w : Walk) (locals : Locals) : SGerTeil → Except String SGerTeil
  | .copy a b => do return .copy (← w.expr locals 1000 a) (← w.expr locals 1000 b)
  | .reg r => do
    return .reg { r with
      rtyp := ← w.type locals 1000 r.rtyp
      addr := ← w.expr locals 1000 r.addr
      voraus := ← r.voraus.mapM (w.expr locals 1000) }
  | .trans t => do return .trans (← w.transition t)
  | .bank raw => do return .bank (← w.raw raw)

def Walk.binding (w : Walk) (b : SBind) : Except String SBind := do
  let codes ← b.codes.mapM fun (a, n, c) => return (a, ← n.mapM (w.expr [] 1000), c)
  return { b with id := ← w.expr [] 1000 b.id, codes }

def Walk.way (w : Walk) : SWay → Except String SWay
  | .lit a b c h => do return .lit a b (← w.binding c) h
  | way => pure way

/-- Every expression-bearing item is visited; no group declaration survives instantiation. -/
def Walk.item (w : Walk) : Nat → SItemTief → Except String SItemTief
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, it => do
    let ex := w.expr [] f
    let ty := w.type [] f
    match it with
    | .specGroupT n ts es fs => do
      if w.resolveSpecs then throw "spec.output.group"
      return .specGroupT n ts es (← fs.mapM w.signature)
    | .implGroupT n ts es fs => do
      if w.resolveSpecs then throw "spec.output.group"
      return .implGroupT n (← ts.mapM ty) es (← fs.mapM (w.item f))
    | .taggedByT decl spec => do
      if w.resolveSpecs then throw "tagged-dispatch-unexpanded-declaration"
      return .taggedByT (← w.item f decl) spec
    | .modT n its => return .modT n (← its.mapM (w.item f))
    | .pubT it => return .pubT (← w.item f it)
    | .gateT it => return .gateT (← w.item f it)
    | .fnT s body => do
      let s ← w.signature s
      return .fnT s (← { w with result := s.res }.statement s.params f body)
    | .protoT s => return .protoT (← w.signature s)
    | .specT s p => return .specT (← w.signature s) (← w.expr s.params f p)
    | .asmT s raw => return .asmT (← w.signature s) raw
    | .typeT fl n args ord t => return .typeT fl n (← args.mapM ty) ord (← t.mapM ty)
    | .constT n t v => return .constT n (← ty t) (← { w with expected := some (← ty t) }.constant f v)
    | .globT b n t v a s sh => return .globT b n (← ty t) (← { w with expected := some (← ty t) }.constant f v) (← a.mapM ex) s sh
    | .formatT n a b fs => return .formatT n (← a.mapM ex) b (← fs.mapM w.field)
    | .tableT n v c b o sh ps space => return .tableT n v (← c.mapM ex) b o sh (← ps.mapM w.tablePart) space
    | .arenaT n lo hi mx t pb => do
      let pb ← pb.mapM fun (ps, e) => return (ps, ← ex e)
      return .arenaT n (← ex lo) (← ex hi) (← mx.mapM ex) (← ty t) pb
    | .whyT n cs b => do
      let cs ← cs.mapM fun (n, e, text) => return (n, ← ex e, text)
      return .whyT n cs b
    | .stateT n ts => return .stateT n (← ts.mapM w.transition)
    | .devT n ps space parts => do
      let ps ← ps.mapM fun (n, t) => return (n, ← ty t)
      return .devT n ps space (← parts.mapM (w.devicePart ps))
    | .axiomT n ps res pred es h => do
      let ps ← ps.mapM fun (n, t) => return (n, ← ty t)
      return .axiomT n ps (← res.mapM ty) (← pred.mapM (w.expr ps f)) (← w.effects ps es) h
    | .checkT c =>
      return .checkT { c with
        misst := ← c.misst.mapM ex
        boden := ← c.boden.mapM ex
        canFail := ← w.statement [] f c.canFail }
    | .atomT n t ps a b => return .atomT n (← ty t) (← ps.mapM (fun es => es.mapM ex)) a b
    | .lockT n ps rk h sh m i => do
      return .lockT n (← ps.mapM ex) (← ex rk)
        (← h.mapM ex) (← sh.mapM ex) m (← i.mapM ex)
    | .rcuT n ps e => return .rcuT n (← ps.mapM ex) (← e.mapM ex)
    | .groupT n ns is => return .groupT n ns (← is.mapM w.invariant)
    | .concT ps => do
      let ps ← ps.mapM fun (p, args) => do
        let args ← args.mapM ex
        let joined := "::".intercalate p
        let n ← w.call [] joined none args
        -- An ordinary root keeps its written path: the root reader selects its last segment.
        return (if n == joined then p else [n], args)
      return .concT ps
    | .accT n t c e q => return .accT n (← ty t) c (← e.mapM ex) q
    | .walkT v =>
      return .walkT { v with
        stufen := ← ex v.stufen
        node := ← ty v.node
        dwhen := ← ex v.dwhen
        blatt := ← ex v.blatt
        invarianten := ← v.invarianten.mapM w.invariant }
    | .entryT e => return .entryT { e with vektor := ← e.vektor.mapM ex, ist := ← e.ist.mapM ex }
    | .bootT n arch ss keeps => do
      let ss ← ss.mapM fun
        | .set n e => return .set n (← ex e)
        | .call p args => do
          let args ← args.mapM ex
          let n ← w.call [] ("::".intercalate p) none args
          return .call [n] args
      return .bootT n arch ss keeps
    | .callT c => do
      let params ← c.params.mapM fun (n, t) => return (n, ← ty t)
      return .callT { c with
        params
        res := ← c.res.mapM ty
        way := ← w.way c.way
        gate := {
          pre := ← c.gate.pre.mapM (w.expr c.params f)
          post := ← c.gate.post.mapM (w.expr c.params f)
          uses := ← w.effects c.params c.gate.uses
          cost := ← c.gate.cost.mapM ex } }
    | .goalT n bs => do
      let bs ← bs.mapM fun (a, b, binds) => do
        let binds ← binds.mapM fun (v, binding, h) => return (v, ← w.binding binding, h)
        return (a, b, binds)
      return .goalT n bs
    | .transT n s body => return .transT n (← w.signature s) (← w.statement s.params f body)
    | it => return it

/-- Successful validation certifies the complete output uses ordinary front-end forms. -/
def ordinary (source output : List SItemTief) : Bool :=
  (output.mapM (({ source, instantiate := false } : Walk).item 100000)).toOption.isSome

end Gabbro.Grammatik.Parser.Spec
