module
public import Grammatik.Zielsatz.Einbettung.SyntaxBasis
@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')

mutual

/-- **An expression of `D` as an expression of `D'`.** -/
def exE : {Γ : Ctx} → {Λ : List (Res D)} → {τ : Ty} → Expr D Γ Λ τ →
    Expr D' (Γ.map E.tyE) (Λ.map E.resE) (E.tyE τ)
  | _, _, _, .lit n => .lit n
  | _, _, _, .tru => .tru
  | _, _, _, .fls => .fls
  | _, _, _, .var x => .var (varE E x)
  | _, _, _, .glob g hL => Expr.umTy (E.gtyp g) (Expr.glob (D := D') (E.glob g) (E.gdarfE hL))
  | _, _, _, .slot t f i hL =>
      Expr.umTy (E.typ t f)
        (Expr.slot (D := D') (E.tab t) (E.feld t f) (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .thru p t ht f i hL =>
      Expr.umTy (E.typ t f)
        (Expr.thru (D := D') (exE p) (E.tab t) (E.capTabE ht) (E.feld t f)
          (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .thruOwn p t ht f i m s ho he hg hL =>
      Expr.umTy (E.typ t f)
        (Expr.thruOwn (D := D') (exE p) (E.tab t) (E.capTabE ht) (E.feld t f)
          (Expr.umTy (E.countE t) (exE i)) (E.marke m) s (E.ownerNr _ m ho)
          (E.eignerE he) (E.brauchtE hg) (E.darfE hL))
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D') (E.tab t) (E.tnum n) (E.capTabE ht) rw
  | _, _, _, .fnref f n h => .fnref (D := D') (E.fn f) (E.num n) ((E.passt f n).trans h)
  | _, _, _, .refEq a b => .refEq (exE a) (exE b)
  | _, _, _, .slotRef r t ht ho f hL =>
      Expr.umTy (E.typ t f)
        (.slotRef (exE r) (E.tab t) (E.tabNrE ht) (by rw [E.offen]; exact ho) (E.feld t f)
          (E.darfE hL))
  | _, _, _, .oldG g hL => Expr.umTy (E.gtyp g) (Expr.oldG (D := D') (E.glob g) (E.gdarfE hL))
  | _, _, _, .oldS t f i hL =>
      Expr.umTy (E.typ t f)
        (Expr.oldS (D := D') (E.tab t) (E.feld t f) (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .widen h1 h2 e => .widen h1 h2 (exE e)
  | _, _, _, .add a b => .add (exE a) (exE b)
  | _, _, _, .sub a b => .sub (exE a) (exE b)
  | _, _, _, .neg a => .neg (exE a)
  | _, _, _, .mul a b => .mul (exE a) (exE b)
  | _, _, _, .div h0 h1 a b => .div h0 h1 (exE a) (exE b)
  | _, _, _, .rem h0 h1 a b => .rem h0 h1 (exE a) (exE b)
  | _, _, _, .sdiv hb a b => .sdiv hb (exE a) (exE b)
  | _, _, _, .srem hb a b => .srem hb (exE a) (exE b)
  | _, _, _, .getBytes t f hf n i hlo hhi hL =>
      .getBytes (D := D') (E.tab t) (E.feld t f) ((E.typ t f).trans (by rw [hf])) n (exE i) hlo
        (by rw [E.count]; exact hhi) (E.darfE hL)
  | _, _, _, .band h0 h0' a b => .band h0 h0' (exE a) (exE b)
  | _, _, _, .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (exE a) (exE b)
  | _, _, _, .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (exE a) (exE b)
  | _, _, _, .shl w hw1 hw2 h0 h0' a b => .shl w hw1 hw2 h0 h0' (exE a) (exE b)
  | _, _, _, .shr w hw1 hw2 h0 h0' a b => .shr w hw1 hw2 h0 h0' (exE a) (exE b)
  | _, _, _, .lt a b => .lt (exE a) (exE b)
  | _, _, _, .le a b => .le (exE a) (exE b)
  | _, _, _, .eq a b => .eq (exE a) (exE b)
  | _, _, _, .fllt a b => .fllt (exE a) (exE b)
  | _, _, _, .flle a b => .flle (exE a) (exE b)
  | _, _, _, .and a b => .and (exE a) (exE b)
  | _, _, _, .or a b => .or (exE a) (exE b)
  | _, _, _, .not a => .not (exE a)
  | _, _, _, .none n => .none n
  | _, _, _, .some e => .some (exE e)
  | _, _, _, .istSome e => .istSome (exE e)
  | _, _, _, .case cs i nutz =>
      .case (Ty.mapCases E.num E.tnum cs) ⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩
        ((Ty.mapCases_get E.num E.tnum cs i).symm ▸ exN nutz)
  | _, _, _, .why n r => .why n r
  | _, _, _, .forallSlots t body hL =>
      Expr.forallSlots (D := D') (E.tab t) (Expr.umΓ (by rw [List.map_cons, E.count]; try rfl) (exE body)) (E.darfE hL)
  | _, _, _, .existsSlots t body hL =>
      Expr.existsSlots (D := D') (E.tab t) (Expr.umΓ (by rw [List.map_cons, E.count]; try rfl) (exE body)) (E.darfE hL)
  | _, _, _, .reaches t f hf a b hL =>
      .reaches (D := D') (E.tab t) (E.feld t f) (by rw [E.typ t f, hf, E.count])
        (Expr.umTy (E.countE t) (exE a)) (Expr.umTy (E.countE t) (exE b)) (E.darfE hL)
  | _, _, _, .arrNil => .arrNil
  | _, _, _, .arrCons a b => .arrCons (exE a) (exE b)
  | _, _, _, .arrGet a i => .arrGet (exE a) (exE i)
  | _, _, _, .arrSet a i v => .arrSet (exE a) (exE i) (exE v)
  | _, _, _, .strLit bs h => .strLit bs h
  | _, _, _, .strLen e => .strLen (exE e)
  | _, _, _, .strCat e e' => .strCat (exE e) (exE e')
  | _, _, _, .strGet e e' => .strGet (exE e) (exE e')
  | _, _, _, .strEq e e' => .strEq (exE e) (exE e')
  | _, _, _, .strLt e e' => .strLt (exE e) (exE e')
  | _, _, _, .strWeit m e => .strWeit m (exE e)
  | _, _, _, .wenn c a b => .wenn (exE c) (exE a) (exE b)
  | _, _, _, .eng e lo hi s => .eng (exE e) lo hi (exE s)
  | _, _, _, .intBuiltin1 op a => .intBuiltin1 (ibE E op) (exE a)
  | _, _, _, .intBuiltin2 op a b => .intBuiltin2 (ibE E op) (exE a) (exE b)
  | _, _, _, .count n body => .count n (exE body)

/-- A payload expression. -/
def exN : {Γ : Ctx} → {Λ : List (Res D)} → {c : Option Ty} → NutzlastExpr D Γ Λ c →
    NutzlastExpr D' (Γ.map E.tyE) (Λ.map E.resE) (c.map E.tyE)
  | _, _, _, .empty => .empty
  | _, _, _, .val e => .val (exE e)

end

/-- Arguments. -/
def exA : {Γ : Ctx} → {Λ : List (Res D)} → {τs : List Ty} → Args D Γ Λ τs →
    Args D' (Γ.map E.tyE) (Λ.map E.resE) (τs.map E.tyE)
  | _, _, _, .nil => .nil
  | _, _, _, .cons e rest => .cons (exE E e) (exA rest)

/-- A result expression. -/
def exErg : {Γ : Ctx} → {Λ : List (Res D)} → {e : Option Ty} → ErgExpr D Γ Λ e →
    ErgExpr D' (Γ.map E.tyE) (Λ.map E.resE) (e.map E.tyE)
  | _, _, _, .empty => .empty
  | _, _, _, .val e => .val (exE E e)

variable {E}

mutual

/-- **A statement of `D` as a statement of `D'`.** -/
def exS (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Stmt D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE)
  | _, _, _, _, .assignSlot t f i e hw hL =>
      .assignSlot (E.tab t) (E.feld t f) (Expr.umTy (E.countE t) (exE E i))
        (Expr.umTy (E.typ t f).symm (exE E e)) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .assignThru p t ht f i e hw hL =>
      .assignThru (exE E p) (E.tab t) (E.capTabE ht) (E.feld t f) (Expr.umTy (E.countE t) (exE E i))
        (Expr.umTy (E.typ t f).symm (exE E e)) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .assignThruOwn p t ht f i e m s ho he hg hw hL =>
      .assignThruOwn (exE E p) (E.tab t) (E.capTabE ht) (E.feld t f) (Expr.umTy (E.countE t) (exE E i))
        (Expr.umTy (E.typ t f).symm (exE E e)) (E.marke m) s (E.ownerNr _ m ho)
        (E.eignerE he) (E.brauchtE hg) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .assignSlotRef r t ht ho f e hw hL =>
      .assignSlotRef (exE E r) (E.tab t) (E.tabNrE ht) (by rw [E.offen]; exact ho) (E.feld t f)
        (Expr.umTy (E.typ t f).symm (exE E e)) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .assignGlob g e hw hL =>
      .assignGlob (E.glob g) (Expr.umTy (E.gtyp g).symm (exE E e)) (E.gschreibtE hw) (E.gdarfE hL)
  | _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL =>
      .putBytes (E.tab t) (E.feld t f) ((E.typ t f).trans (by rw [hf])) n (exE E i) hlo
        (by rw [E.count]; exact hhi) (exE E e) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .assignVar x e => .assignVar (varE E x) (exE E e)
  | _, _, _, _, .shift t f hτ i von nach hn he hw hL =>
      .shift (E.tab t) (E.feld t f) ((E.typ t f).trans (by rw [hτ])) (Expr.umTy (E.countE t) (exE E i))
        von nach hn (by rw [E.erlaubt]; exact he) (E.schreibtE hw) (E.darfE hL)
  | _, _, _, _, .ite c t e => .ite (exE E c) (exB hS t) (exB hS e)
  | _, _, _, _, .onOption o p a => .onOption (exE E o) (exB hS p) (exB hS a)
  | _, _, _, _, .onTag v arms => .onTag (exE E v) (exArms hS arms)
  | _, _, _, _, .onWhy r arms => .onWhy (exE E r) (exGArms hS arms)
  | _, _, Λ, _, .call f args hp hr =>
      Stmt.nachΛ (nachE hS f Λ).symm
        (.call (E.fn f) (Args.umτs (paramsE hS f) (exA E args)) (rufPasstE_fn hS hp)
          (by rw [gruendeE hS]; exact hr))
  | _, _, Λ, _, .callInd (n := n) p args hp hr =>
      Stmt.nachΛ (nachSigE_nr hS n Λ).symm
        (.callInd (n := E.val n) (exE E p)
          (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args)) (rufPasstE_nr hS hp)
          (by rw [hS.sigNr]; exact hr))
  | _, _, Λ, _, .callIndElse (n := n) p args he hp hr err =>
      Stmt.nachΛ (nachSigE_nr hS n Λ).symm
        (.callIndElse (n := E.num n) (exE E p)
          (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
          (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
          (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
          (Endblock.umΓ (by rw [hS.sigNr]; rfl) (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS err))))
  | _, _, _, _, .locks L hr body =>
      .locks (E.lock L) (fun M hM => by
          obtain ⟨M0, rfl, hM0⟩ := E.held_mem_mapE hM
          rw [E.rang, E.rang]; exact hr M0 hM0) (exB hS body)
  | _, _, _, _, .breaking i body => .breaking (E.inv i) (exB hS body)
  | _, _, _, _, .traverse t inv body =>
      .traverse (E.tab t) (exE E inv) (Block.umΓ (by rw [List.map_cons, E.count]; try rfl) (exB hS body))
  | _, _, _, _, .consumeTraverse t member edge inv bound mass body =>
      .consumeTraverse (E.tab t) (Expr.umΓ (by rw [List.map_cons, E.count]; try rfl) (exE E member))
        (Expr.umΓ (by rw [List.map_cons, List.map_cons, E.count]; try rfl) (exE E edge)) (exE E inv)
        bound (exE E mass) (Block.umΓ (by rw [List.map_cons, E.count]; try rfl) (exB hS body))
  | _, _, _, _, .retry n bis body ueber => .retry n (exE E bis) (exB hS body) (exB hS ueber)
  | _, _, _, _, .forever a inv body => .forever (E.annahme a) (exE E inv) (exB hS body)
  | _, _, _, _, .axiomCall a args h hw hg hd hgd =>
      .axiomCall (E.ax a) (Args.umτs (E.aparams a).symm (exA E args)) (by rw [E.aerg, h]; rfl)
        (E.axSchreibtE hw) (E.axGSchreibtE hg) (E.axDarfE hd) (E.axGDarfE hgd)
  | _, _, _, _, .regWrite r hk e =>
      .regWrite (E.reg r) (by rw [E.rklasse]; exact hk) (Expr.umTy (E.rtyp r).symm (exE E e))
  | _, _, _, _, .transition r hk m hm hl maske bits =>
      .transition (E.reg r) (by rw [E.rklasse]; exact hk) (E.reg m) (by rw [E.spiegel, hm]; rfl)
        (by rw [E.rklasse]; exact hl) maske bits
  | _, _, _, _, .publish g e payload hp hw hL =>
      .publish (E.glob g) (Expr.umTy (E.gtyp g).symm (exE E e)) (payload.map E.glob)
        (by rw [E.nutzlast, hp]) (E.gschreibtE hw) (E.gdarfE hL)
  | _, _, Λ, _, .advances m a h hs =>
      Stmt.nachΛ (by rw [List.map_append, E.erase_mapE]; rfl)
        (.advances (E.marke m) a (E.mem_mapE.mpr h) (by rw [E.stufen]; exact hs))
  | _, _, Λ, _, .retires m s h a =>
      Stmt.nachΛ (by rw [E.erase_mapE]; rfl) (.retires (E.marke m) s (E.mem_mapE.mpr h) (E.annahme a))
  | _, _, _, _, .ret e hΛ => .ret (exErg E e) ((hΛ.map E.resE).trans (by rw [E.endeE]))
  | _, _, _, _, .retWhy r hΛ => .retWhy r ((hΛ.map E.resE).trans (by rw [E.endeE]))
  | _, _, _, _, .retScoped e R =>
      .retScoped (exErg E e) ⟨R.scopes.map E.lock, (R.genau.map E.resE).trans (by rw [List.map_append, E.endeE])⟩
  | _, _, _, _, .retWhyScoped r R =>
      .retWhyScoped r ⟨R.scopes.map E.lock, (R.genau.map E.resE).trans (by rw [List.map_append, E.endeE])⟩
  | _, _, _, _, .leave h => .leave h
  | _, _, _, _, .next h => .next h

/-- A block. -/
def exB (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Block D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons s rest => .cons (exS hS s) (exB hS rest)
  | _, _, _, _, .bind e rest => .bind (exE E e) (exB hS rest)
  | _, _, Λ, _, .bindCall f args he hp hr rest =>
      .bindCall (E.fn f) (Args.umτs (paramsE hS f) (exA E args))
        (by rw [← ergE_fn hS, he]; rfl) (rufPasstE_fn hS hp) (by rw [gruendeE hS]; exact hr)
        (Block.vorΛ (nachE hS f Λ) (exB hS rest))
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (n := E.val n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
        (Block.vorΛ (nachSigE_nr hS n Λ) (exB hS rest))
  | _, _, Λ, _, .bindCallIndElse (n := n) p args he hp hr err rest =>
      .bindCallIndElse (n := E.num n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
        (Endblock.umΓ (by rw [hS.sigNr]; rfl) (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS err)))
        (Block.vorΛ (nachSigE_nr hS n Λ) (exB hS rest))
  | _, _, Λ, _, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (E.fn f) (Args.umτs (paramsE hS f) (exA E args))
        (by rw [← ergE_fn hS, he]; rfl) (rufPasstE_fn hS hp) (by rw [gruendeE hS]; exact hr)
        (Endblock.umΓ (by rw [gruendeE hS]; rfl) (Endblock.umΛ (nachE hS f Λ) (exEnd hS err)))
        (Block.vorΛ (nachE hS f Λ) (exB hS rest))
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (E.ax a) (Args.umτs (E.aparams a).symm (exA E args)) (by rw [E.aerg, he]; rfl)
        (E.axSchreibtE hw) (E.axGSchreibtE hg) (E.axDarfE hd) (E.axGDarfE hgd) (exB hS rest)
  | _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      .bindAxiomElse (E.ax a) (Args.umτs (E.aparams a).symm (exA E args)) (by rw [E.aerg, he]; rfl)
        (by rw [E.agruende]; exact hr) (E.axSchreibtE hw) (E.axGSchreibtE hg) (E.axDarfE hd)
        (E.axGDarfE hgd) (Endblock.umΓ (by rw [E.agruende]; rfl) (exEnd hS err)) (exB hS rest)
  | _, _, _, _, .regRead r hk rest =>
      .regRead (E.reg r) (by rw [E.rklasse]; exact hk) (Block.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exB hS rest))
  | _, _, _, _, .regReadElse r hk zusage sonst rest =>
      .regReadElse (E.reg r) (by rw [E.rklasse]; exact hk) (Expr.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exE E zusage))
        (exEnd hS sonst) (Block.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exB hS rest))
  | _, _, _, _, .awaits g payload hp hL hat rest =>
      .awaits (E.glob g) (payload.map E.glob) (by rw [E.nutzlast, hp]) (E.gdarfE hL)
        (by rw [E.atomar]; exact hat) (Block.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (exB hS rest))
  | _, _, _, _, .exchange g neu hw hL rest =>
      .exchange (E.glob g) (Expr.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (Expr.umTy (E.gtyp g).symm (exE E neu)))
        (E.gschreibtE hw) (E.gdarfE hL) (Block.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (exB hS rest))
  | _, _, _, _, .narrow e lo' hi' sonst rest => .narrow (exE E e) lo' hi' (exEnd hS sonst) (exB hS rest)
  | _, _, _, _, .narrowRequired e lo' hi' rest => .narrowRequired (exE E e) lo' hi' (exB hS rest)
  | _, _, _, _, .check c sonst rest => .check (exE E c) (exEnd hS sonst) (exB hS rest)
  | _, _, _, _, .float op a b lo hi rest => .float op (exE E a) (exE E b) lo hi (exB hS rest)
  | _, _, _, _, .floatLit q lo hi rest => .floatLit q lo hi (exB hS rest)
  | _, _, _, _, .floatOf e lo hi rest => .floatOf (exE E e) lo hi (exB hS rest)
  | _, _, _, _, .floatNarrow e lo hi sonst rest =>
      .floatNarrow (exE E e) lo hi (exEnd hS sonst) (exB hS rest)

/-- An end block. -/
def exEnd (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Endblock D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE)
  | _, _, _, .ret e hΛ => .ret (exErg E e) ((hΛ.map E.resE).trans (by rw [E.endeE]))
  | _, _, _, .retWhy r hΛ => .retWhy r ((hΛ.map E.resE).trans (by rw [E.endeE]))
  | _, _, _, .retScoped e R =>
      .retScoped (exErg E e) ⟨R.scopes.map E.lock, (R.genau.map E.resE).trans (by rw [List.map_append, E.endeE])⟩
  | _, _, _, .retWhyScoped r R =>
      .retWhyScoped r ⟨R.scopes.map E.lock, (R.genau.map E.resE).trans (by rw [List.map_append, E.endeE])⟩
  | _, _, _, .leave h => .leave h
  | _, _, _, .next h => .next h
  | _, _, _, .cons s rest => .cons (exS hS s) (exEnd hS rest)
  | _, _, _, .bind e rest => .bind (exE E e) (exEnd hS rest)
  | _, _, Λ, .bindCall f args he hp hr rest =>
      .bindCall (E.fn f) (Args.umτs (paramsE hS f) (exA E args))
        (by rw [← ergE_fn hS, he]; rfl) (rufPasstE_fn hS hp) (by rw [gruendeE hS]; exact hr)
        (Endblock.umΛ (nachE hS f Λ) (exEnd hS rest))
  | _, _, Λ, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (E.fn f) (Args.umτs (paramsE hS f) (exA E args))
        (by rw [← ergE_fn hS, he]; rfl) (rufPasstE_fn hS hp) (by rw [gruendeE hS]; exact hr)
        (Endblock.umΓ (by rw [gruendeE hS]; rfl) (Endblock.umΛ (nachE hS f Λ) (exEnd hS err)))
        (Endblock.umΛ (nachE hS f Λ) (exEnd hS rest))
  | _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (E.ax a) (Args.umτs (E.aparams a).symm (exA E args)) (by rw [E.aerg, he]; rfl)
        (E.axSchreibtE hw) (E.axGSchreibtE hg) (E.axDarfE hd) (E.axGDarfE hgd) (exEnd hS rest)
  | _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      .bindAxiomElse (E.ax a) (Args.umτs (E.aparams a).symm (exA E args)) (by rw [E.aerg, he]; rfl)
        (by rw [E.agruende]; exact hr) (E.axSchreibtE hw) (E.axGSchreibtE hg) (E.axDarfE hd)
        (E.axGDarfE hgd) (Endblock.umΓ (by rw [E.agruende]; rfl) (exEnd hS err)) (exEnd hS rest)
  | _, _, _, .regRead r hk rest =>
      .regRead (E.reg r) (by rw [E.rklasse]; exact hk) (Endblock.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exEnd hS rest))
  | _, _, _, .regReadElse r hk zusage sonst rest =>
      .regReadElse (E.reg r) (by rw [E.rklasse]; exact hk) (Expr.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exE E zusage))
        (exEnd hS sonst) (Endblock.umΓ (by rw [List.map_cons, E.rtyp]; try rfl) (exEnd hS rest))
  | _, _, _, .awaits g payload hp hL hat rest =>
      .awaits (E.glob g) (payload.map E.glob) (by rw [E.nutzlast, hp]) (E.gdarfE hL)
        (by rw [E.atomar]; exact hat) (Endblock.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (exEnd hS rest))
  | _, _, Λ, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (n := E.val n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
        (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS rest))
  | _, _, Λ, .bindCallIndElse (n := n) p args he hp hr err rest =>
      .bindCallIndElse (n := E.num n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
        (Endblock.umΓ (by rw [hS.sigNr]; rfl) (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS err)))
        (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS rest))
  | _, _, _, .narrow e lo' hi' sonst rest => .narrow (exE E e) lo' hi' (exEnd hS sonst) (exEnd hS rest)
  | _, _, _, .narrowRequired e lo' hi' rest => .narrowRequired (exE E e) lo' hi' (exEnd hS rest)
  | _, _, _, .exchange g neu hw hL rest =>
      .exchange (E.glob g) (Expr.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (Expr.umTy (E.gtyp g).symm (exE E neu)))
        (E.gschreibtE hw) (E.gdarfE hL) (Endblock.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (exEnd hS rest))
  | _, _, _, .ite c t e => .ite (exE E c) (exEnd hS t) (exEnd hS e)

  | _, _, _, .float op a b lo hi rest => .float op (exE E a) (exE E b) lo hi (exEnd hS rest)
  | _, _, _, .floatLit q lo hi rest => .floatLit q lo hi (exEnd hS rest)
  | _, _, _, .floatOf e lo hi rest => .floatOf (exE E e) lo hi (exEnd hS rest)
  | _, _, _, .floatNarrow e lo hi sonst rest =>
      .floatNarrow (exE E e) lo hi (exEnd hS sonst) (exEnd hS rest)
/-- Arms (the arm scope `ArmCtx` is split on the case). -/
def exArms (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option Ty)} → Arms D V l Γ Λ Λ' cs →
      Arms D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE) (Ty.mapCases E.num E.tnum cs)
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons (c := none) b rest => .cons (c := none) (exB hS b) (exArms hS rest)
  | _, _, _, _, _, .cons (c := some τ) b rest =>
      .cons (c := some (E.tyE τ)) (exB hS b) (exArms hS rest)

/-- Reason arms. -/
def exGArms (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n →
      GrundArms D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE) n
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons b rest => .cons (exB hS b) (exGArms hS rest)

end

end Einbettung
end Gabbro.Grammatik.Einbettung
