module
public import Stage0.Senke.Anweisung
public import Stage0.Senke.Anweisung.Fast.Arguments
public import Stage0.Senke.Anweisung.Fast.Composition
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration} {V : Vertrag D}

/- The common lexical spine carries frame widths downwards and code lengths
   upwards. Other constructors call the original lowering, preserving every
   existing refusal. Only lowFun is replaced in compiled code, so these fallback
   calls cannot recurse through a compiler-simplification replacement. -/
mutual
def lowSFast (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
    (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    Option CodeCache :=
  match s with
  | .assignVar (τ := τ) x e =>
    if layout.internalResult ≤ frame.slot x reserved ∧
        pr.all (fun j => decide (j < frame.slot x reserved ∨ frame.slot x reserved + valueWords τ ≤ j)) then do
      let ce ← lowEFast L e (frame.free reserved) reserved true frame
      pure (CodeCache.ofPair (ce.1 ++ copyWords (valueWords τ) (frame.slot x reserved) (frame.free reserved),
        max ce.2 (frame.free reserved + valueWords τ)))
    else none
  | .ite c t e => do
    let cc ← lowEFast L c (frame.free reserved) reserved true frame
    let ce ← lowBFast passes A L layout ens pr ex e reserved sc frame
    let ct ← lowBFast passes A L layout ens pr (exPlus ex (ce.size + 1)) t reserved sc frame
    pure (CodeCache.join (cc.1 ++ [ci 19 (frame.free reserved) (16 * (ct.size + 2)) 0]) ct
      [ci 18 (16 * (ce.size + 1)) 0 0] ce (max cc.2 (max ct.value.2 ce.value.2)))
  | .call f args _ _ => do
    let ca ← lowAFast L frame args (frame.free reserved + FB) reserved
    pure (CodeCache.ofPair (callC A f (frame.free reserved) ca.1, callTop f (frame.free reserved) ca.2))
  | .retWhy r _ =>
    if sc = [] then some (CodeCache.ofPair (retWhyC layout r.val,
      max (frame.free reserved) (retTop layout))) else none
  | .ret e _ =>
    if sc = [] then do
      let ce ← lowErgFast L frame e (frame.free reserved) reserved
      pure (CodeCache.ofPair (ce.1 ++ retC layout (frame.free reserved) ens.1,
        max ce.2 (max ens.2 (retTop layout))))
    else none
  | .breaking _ body => lowBFast passes A L layout ens pr ex body reserved sc frame
  | .locks Lk _ body =>
    if ueberBodenB V.boden (D.rang Lk) = true ∧ lit32 (16 + ex.1 + 16 * 17) = true ∧
        lit32 (16 + ex.2) = true then do
      let cb ← lowBFast passes A L layout ens pr (16 * 17, 16 * 34) body reserved (Lk :: sc) frame
      -- The lock wrapper is counted once here; its specification emits the same bytes.
      pure (CodeCache.ofPair (locksCodeT L (L.lk Lk) (frame.free reserved) cb.value.1 ex.1 ex.2,
        max (cb.value.2 + 1) (frame.free reserved + 18)))
    else none
  | s => (lowS passes A L layout ens pr ex s reserved sc).map CodeCache.ofPair
termination_by structural s

def lowBFast (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
    (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    Option CodeCache :=
  match body with
  | .nil => some (CodeCache.ofPair ([], frame.free reserved))
  | .cons s rest => do
    let cr ← lowBFast passes A L layout ens pr ex rest reserved sc frame
    let cs ← lowSFast passes A L layout ens pr (exPlus ex cr.size) s reserved sc frame
    pure (CodeCache.append cs cr)
  | .bind e rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowBFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.append (CodeCache.ofPair ce) cr)
  | .bindCall f args _ _ _ rest => do
    let ca ← lowAFast L frame args (frame.free reserved + FB) reserved
    let cr ← lowBFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.append
      (CodeCache.ofPair (callC A f (frame.free reserved) ca.1 ++ receiveC (D.signatur f) (frame.free reserved),
        max (callTop f (frame.free reserved) ca.2) (receiveTop (D.signatur f) (frame.free reserved)))) cr)
  | .bindCallElse f args _ _ _ err rest => do
    let ca ← lowAFast L frame args (frame.free reserved + FB) reserved
    let ce ← lowEndFast passes A L layout ens pr ex err reserved sc (frame.push _)
    let cr ← lowBFast passes A L layout ens pr (exPlus ex (ce.size + 1)) rest reserved sc (frame.push _)
    pure (CodeCache.callElse (D := D) (D.signatur f) (frame.free reserved)
      (callC A f (frame.free reserved) ca.1) cr ce
      (elseTop f (frame.free reserved) ca.2 cr.value.2 ce.value.2))
  | .narrow (lo := lo) (hi := hi) e low high err rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowBFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    let cx ← lowEndFast passes A L layout ens pr (exPlus ex (cr.size + 1)) err reserved sc frame
    pure (CodeCache.narrow (frame.free reserved) lo hi low high ce.1 cx cr
      (max ce.2 (max (narrowTop (frame.free reserved) lo hi low high) (max cx.value.2 cr.value.2))))
  | .narrowRequired (lo := lo) (hi := hi) e low high rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowBFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.narrow (frame.free reserved) lo hi low high ce.1
      (CodeCache.ofPair (stopC 107 (frame.free reserved), frame.free reserved + 1)) cr
      (max ce.2 (max (narrowTop (frame.free reserved) lo hi low high)
        (max (frame.free reserved + 1) cr.value.2))))
  | .check c err rest => do
    let cc ← lowEFast L c (frame.free reserved) reserved true frame
    let ce ← lowEndFast passes A L layout ens pr ex err reserved sc frame
    let cr ← lowBFast passes A L layout ens pr (exPlus ex (ce.size + 1)) rest reserved sc frame
    pure (CodeCache.join (cc.1 ++ [ci 19 (frame.free reserved) (16 * (cr.size + 2)) 0]) cr
      [ci 18 (16 * (ce.size + 1)) 0 0] ce (max cc.2 (max cr.value.2 ce.value.2)))
  | body => (lowB passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair
termination_by structural body

def lowEndFast (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
    (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body : Endblock D V l Γ Λ) (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    Option CodeCache :=
  match body with
  | .leave _ => if lit32 (16 + ex.1) then
      some (CodeCache.ofPair ([ci 18 (16 + ex.1) 0 0], frame.free reserved)) else none
  | .next _ => if lit32 (16 + ex.2) then
      some (CodeCache.ofPair ([ci 18 (16 + ex.2) 0 0], frame.free reserved)) else none
  | .retWhy r _ => if sc = [] then
      some (CodeCache.ofPair (retWhyC layout r.val, max (frame.free reserved) (retTop layout))) else none
  | .ret e _ =>
    if sc = [] then do
      let ce ← lowErgFast L frame e (frame.free reserved) reserved
      pure (CodeCache.ofPair (ce.1 ++ retC layout (frame.free reserved) ens.1,
        max ce.2 (max ens.2 (retTop layout))))
    else none
  | .cons s rest => do
    let cr ← lowEndFast passes A L layout ens pr ex rest reserved sc frame
    let cs ← lowSFast passes A L layout ens pr (exPlus ex cr.size) s reserved sc frame
    pure (CodeCache.append cs cr)
  | .bind e rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowEndFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.append (CodeCache.ofPair ce) cr)
  | .bindCall f args _ _ _ rest => do
    let ca ← lowAFast L frame args (frame.free reserved + FB) reserved
    let cr ← lowEndFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.append
      (CodeCache.ofPair (callC A f (frame.free reserved) ca.1 ++ receiveC (D.signatur f) (frame.free reserved),
        max (callTop f (frame.free reserved) ca.2) (receiveTop (D.signatur f) (frame.free reserved)))) cr)
  | .bindCallElse f args _ _ _ err rest => do
    let ca ← lowAFast L frame args (frame.free reserved + FB) reserved
    let ce ← lowEndFast passes A L layout ens pr ex err reserved sc (frame.push _)
    let cr ← lowEndFast passes A L layout ens pr (exPlus ex (ce.size + 1)) rest reserved sc (frame.push _)
    pure (CodeCache.callElse (D := D) (D.signatur f) (frame.free reserved)
      (callC A f (frame.free reserved) ca.1) cr ce
      (elseTop f (frame.free reserved) ca.2 cr.value.2 ce.value.2))
  | .ite c t e => do
    let cc ← lowEFast L c (frame.free reserved) reserved true frame
    let ce ← lowEndFast passes A L layout ens pr ex e reserved sc frame
    let ct ← lowEndFast passes A L layout ens pr (exPlus ex ce.size) t reserved sc frame
    pure (CodeCache.join (cc.1 ++ [ci 19 (frame.free reserved) (16 * (ct.size + 1)) 0]) ct [] ce
      (max cc.2 (max ct.value.2 ce.value.2)))
  | .narrow (lo := lo) (hi := hi) e low high err rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowEndFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    let cx ← lowEndFast passes A L layout ens pr (exPlus ex (cr.size + 1)) err reserved sc frame
    pure (CodeCache.narrow (frame.free reserved) lo hi low high ce.1 cx cr
      (max ce.2 (max (narrowTop (frame.free reserved) lo hi low high) (max cx.value.2 cr.value.2))))
  | .narrowRequired (lo := lo) (hi := hi) e low high rest => do
    let ce ← lowEFast L e (frame.free reserved) reserved true frame
    let cr ← lowEndFast passes A L layout ens pr ex rest reserved sc (frame.push _)
    pure (CodeCache.narrow (frame.free reserved) lo hi low high ce.1
      (CodeCache.ofPair (stopC 107 (frame.free reserved), frame.free reserved + 1)) cr
      (max ce.2 (max (narrowTop (frame.free reserved) lo hi low high)
        (max (frame.free reserved + 1) cr.value.2))))
  | body => (lowEnd passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair
termination_by structural body
end

end Gabbro.Stage0.Senke
