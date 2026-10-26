import Grammatik.Zielsatz.Einbettung.Ressourcen

/-!
  File:      Grammatik/Zielsatz/Einbettung/Syntax.lean
  Subject:   The syntax of `D` as syntax of `D'` under an embedding (stage E0).

  Every constructor goes to the same constructor: items to their images, types by `tyE`,
  holdings by `resE`, contracts by `vertragE`. Where `D'` meets a side condition only
  propositionally (a field's type, a table's count, a parameter list), the term is transported
  along the equation the embedding provides.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

/-! ## Transports -/

def Expr.umTy {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} (h : τ = τ') (e : Expr D Γ Λ τ) :
    Expr D Γ Λ τ' := h ▸ e

def Block.umΓ {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : Γ = Γ')
    (b : Block D V l Γ Λ Λ') : Block D V l Γ' Λ Λ' := h ▸ b

def Endblock.umΓ {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} {Λ : List (Res D)} (h : Γ = Γ')
    (b : Endblock D V l Γ Λ) : Endblock D V l Γ' Λ := h ▸ b

def Endblock.umV {V V' : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (h : V = V')
    (b : Endblock D V l Γ Λ) : Endblock D V' l Γ Λ := h ▸ b

def Args.umτs {Γ : Ctx} {Λ : List (Res D)} {τs τs' : List Ty} (h : τs = τs') (a : Args D Γ Λ τs) :
    Args D Γ Λ τs' := h ▸ a

namespace Einbettung

variable (E : Einbettung D D')

/-! ## What `D'` knows of the image -/

theorem schreibtE {V : Vertrag D} {t : D.Tab} (h : V.schreibt t = true) :
    (E.vertragE V).schreibt (E.tab t) = true := by
  simp only [vertragE, E.tabZ_tab]; exact h

theorem gschreibtE {V : Vertrag D} {g : D.Glob} (h : V.gschreibt g = true) :
    (E.vertragE V).gschreibt (E.glob g) = true := by
  simp only [vertragE, E.globZ_glob]; exact h

theorem axSchreibtE {V : Vertrag D} {a : D.Ax} (h : ∀ t, D.aschreibt a t = true → V.schreibt t = true) :
    ∀ t', D'.aschreibt (E.ax a) t' = true → (E.vertragE V).schreibt t' = true := by
  intro t' ht'
  rw [E.aschreibt] at ht'
  simp only [vertragE]
  revert ht'
  cases E.tabZ t' with
  | none => intro ht'; cases ht'
  | some t => exact h t

theorem axGSchreibtE {V : Vertrag D} {a : D.Ax}
    (h : ∀ g, D.agschreibt a g = true → V.gschreibt g = true) :
    ∀ g', D'.agschreibt (E.ax a) g' = true → (E.vertragE V).gschreibt g' = true := by
  intro g' hg'
  rw [E.agschreibt] at hg'
  simp only [vertragE]
  revert hg'
  cases E.globZ g' with
  | none => intro hg'; cases hg'
  | some g => exact h g

theorem axDarfE {Λ : List (Res D)} {a : D.Ax} (h : ∀ t, D.aschreibt a t = true → darf D t Λ) :
    ∀ t', D'.aschreibt (E.ax a) t' = true → darf D' t' (Λ.map E.resE) := by
  intro t' ht'
  rw [E.aschreibt] at ht'
  cases hz : E.tabZ t' with
  | none => rw [hz] at ht'; cases ht'
  | some t =>
    rw [hz] at ht'
    rw [← E.tab_tabZ t' t hz]
    exact E.darfE (h t ht')

theorem axGDarfE {Λ : List (Res D)} {a : D.Ax} (h : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    ∀ g', D'.agschreibt (E.ax a) g' = true → gdarf D' g' (Λ.map E.resE) := by
  intro g' hg'
  rw [E.agschreibt] at hg'
  cases hz : E.globZ g' with
  | none => rw [hz] at hg'; cases hg'
  | some g =>
    rw [hz] at hg'
    rw [← E.glob_globZ g' g hz]
    exact E.gdarfE (h g hg')

theorem tabNrE {n : Nat} {t : D.Tab} (h : D.tabNr n = some t) : D'.tabNr (E.tnum n) = some (E.tab t) := by
  rw [E.tabNr, h]; rfl

theorem countE (t : D.Tab) : Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) := by
  rw [E.count]

variable {E}

theorem paramsE (hS : E.SigTreu) (f : D.Fn) : (D.params f).map E.tyE = D'.params (E.fn f) := by
  unfold Deklaration.params; rw [hS.signatur]; rfl

theorem ergE_fn (hS : E.SigTreu) (f : D.Fn) : (D.erg f).map E.tyE = D'.erg (E.fn f) := by
  unfold Deklaration.erg; rw [hS.signatur]; rfl

theorem gruendeE (hS : E.SigTreu) (f : D.Fn) : D'.gruende (E.fn f) = D.gruende f := by
  unfold Deklaration.gruende; rw [hS.signatur]; rfl

theorem vertragVonE (hS : E.SigTreu) (f : D.Fn) : E.vertragE (vertragVon D f) = vertragVon D' (E.fn f) := by
  unfold vertragVon; rw [hS.signatur]; rfl

theorem anfangE_fn (hS : E.SigTreu) (f : D.Fn) :
    (Signatur.anfang D (D.signatur f)).map E.resE = Signatur.anfang D' (D'.signatur (E.fn f)) := by
  rw [hS.signatur]; exact E.anfangE _

theorem rufPasstE_fn (hS : E.SigTreu) {V : Vertrag D} {f : D.Fn} {Λ : List (Res D)}
    (h : RufPasst D V (D.signatur f) Λ) :
    RufPasst D' (E.vertragE V) (D'.signatur (E.fn f)) (Λ.map E.resE) := by
  rw [hS.signatur]; exact E.rufPasstE h

theorem rufPasstE_nr (hS : E.SigTreu) {V : Vertrag D} {n : Nat} {Λ : List (Res D)}
    (h : RufPasst D V (D.sigNr n) Λ) :
    RufPasst D' (E.vertragE V) (D'.sigNr (E.num n)) (Λ.map E.resE) := by
  rw [hS.sigNr]; exact E.rufPasstE h

theorem nachSigE_nr (hS : E.SigTreu) (n : Nat) (Λ : List (Res D)) :
    (nachSig D (D.sigNr n) Λ).map E.resE = nachSig D' (D'.sigNr (E.num n)) (Λ.map E.resE) := by
  rw [hS.sigNr]; exact E.nachSigE _ Λ

variable (E)

/-! ## The translation -/

def varE : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Var (Γ.map E.tyE) (E.tyE τ)
  | _, _, .here => .here
  | _, _, .there x => .there (varE x)

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
        (Expr.thru (D := D') (exE p) (E.tab t) (E.tabNrE ht) (E.feld t f)
          (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D') (E.tab t) (E.tnum n) (E.tabNrE ht) rw
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
  | _, _, _, .case cs i nutz => .case cs i (exN nutz)
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

/-- A payload expression. -/
def exN : {Γ : Ctx} → {Λ : List (Res D)} → {c : Option (Int × Int)} → NutzlastExpr D Γ Λ c →
    NutzlastExpr D' (Γ.map E.tyE) (Λ.map E.resE) c
  | _, _, _, .empty => .empty
  | _, _, _, .num e => .num (exE e)

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
      .assignThru (exE E p) (E.tab t) (E.tabNrE ht) (E.feld t f) (Expr.umTy (E.countE t) (exE E i))
        (Expr.umTy (E.typ t f).symm (exE E e)) (E.schreibtE hw) (E.darfE hL)
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
        (.callInd (n := E.num n) (exE E p)
          (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args)) (rufPasstE_nr hS hp)
          (by rw [hS.sigNr]; exact hr))
  | _, _, _, _, .locks L hr body =>
      .locks (E.lock L) (fun M hM => by
          obtain ⟨M0, rfl, hM0⟩ := E.held_mem_mapE hM
          rw [E.rang, E.rang]; exact hr M0 hM0) (exB hS body)
  | _, _, _, _, .breaking i body => .breaking (E.inv i) (exB hS body)
  | _, _, _, _, .traverse t inv body =>
      .traverse (E.tab t) (exE E inv) (Block.umΓ (by rw [List.map_cons, E.count]; try rfl) (exB hS body))
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
      .bindCallInd (n := E.num n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
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
      .bindCallInd (n := E.num n) (exE E p) (Args.umτs (by rw [hS.sigNr]; rfl) (exA E args))
        (by rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl)
        (rufPasstE_nr hS hp) (by rw [hS.sigNr]; exact hr)
        (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS rest))
  | _, _, _, .narrow e lo' hi' sonst rest => .narrow (exE E e) lo' hi' (exEnd hS sonst) (exEnd hS rest)
  | _, _, _, .exchange g neu hw hL rest =>
      .exchange (E.glob g) (Expr.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (Expr.umTy (E.gtyp g).symm (exE E neu)))
        (E.gschreibtE hw) (E.gdarfE hL) (Endblock.umΓ (by rw [List.map_cons, E.gtyp]; try rfl) (exEnd hS rest))
  | _, _, _, .ite c t e => .ite (exE E c) (exEnd hS t) (exEnd hS e)

/-- Arms (the arm scope `ArmCtx` is split on the case). -/
def exArms (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs →
      Arms D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE) cs
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons (c := none) b rest => .cons (c := none) (exB hS b) (exArms hS rest)
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest =>
      .cons (c := some (lo, hi)) (exB hS b) (exArms hS rest)

/-- Reason arms. -/
def exGArms (hS : E.SigTreu) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n →
      GrundArms D' (E.vertragE V) l (Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE) n
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons b rest => .cons (exB hS b) (exGArms hS rest)

end

/-! ## A function's contracts and body -/

/-- The `requires` of `f`, as the `requires` of its image. -/
def requiresE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Expr D' (D'.params (E.fn f)) (Signatur.anfang D' (D'.signatur (E.fn f))) .bool :=
  Expr.umΓ (paramsE hS f) (Expr.umΛ (anfangE_fn hS f) (exE E (P.requires f)))

/-- The `ensures` of `f`, as the `ensures` of its image. -/
def ensuresE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Expr D' (ErgCtx (D'.params (E.fn f)) (D'.erg (E.fn f))) (vertragVon D' (E.fn f)).ende .bool :=
  Expr.umΓ (by rw [E.ergCtxE, paramsE hS f, ergE_fn hS f])
    (Expr.umΛ (by rw [E.endeE, vertragVonE hS f]) (exE E (P.ensures f)))

/-- The body of `f`, as the body of its image. -/
def rumpfE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Endblock D' (vertragVon D' (E.fn f)) false (D'.params (E.fn f))
      (Signatur.anfang D' (D'.signatur (E.fn f))) :=
  Endblock.umV (vertragVonE hS f)
    (Endblock.umΓ (paramsE hS f) (Endblock.umΛ (anfangE_fn hS f) (exEnd hS (P.rumpf f))))

/-- An invariant's predicate. -/
def invarianteE (P : Programm D) (i : D.Inv) : Expr D' [] (invSicht D' (E.inv i)) .bool :=
  Expr.umΛ (E.invSichtE i) (exE E (P.invariante i))

/-- **`P'` continues `P` along the embedding**: every function of `D` has, at its image, the
    translated contracts and body, every invariant of `D` the translated predicate, and the same
    dispatch fact. -/
structure Fortsetzung (hS : E.SigTreu) (P : Programm D) (P' : Programm D') : Prop where
  requires : ∀ f, P'.requires (E.fn f) = requiresE hS P f
  ensures : ∀ f, P'.ensures (E.fn f) = ensuresE hS P f
  rumpf : ∀ f, P'.rumpf (E.fn f) = rumpfE hS P f
  invariante : ∀ i, P'.invariante (E.inv i) = invarianteE P i
  unterbricht : ∀ f, P'.unterbricht (E.fn f) = P.unterbricht f

end Einbettung

end Gabbro.Grammatik.Einbettung
