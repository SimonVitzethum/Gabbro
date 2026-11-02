module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

mutual

/-- **An expression of `D` as an expression of `D.mitRuhe`**: the same
    constructor, `f ↦ some f` in `&f`. -/
def ruE : {Γ : Ctx} → {Λ : List (Res D)} → {τ : Ty} → Expr D Γ Λ τ →
    Expr D.mitRuhe (Γ.map tyR) (Λ.map resR) (tyR τ)
  | _, _, _, .lit n => .lit n
  | _, _, _, .tru => .tru
  | _, _, _, .fls => .fls
  | _, _, _, .var x => .var (varR x)
  | _, _, _, .glob g hL => Expr.glob (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .slot t f i hL => Expr.slot (D := D.mitRuhe) t f (ruE i) (darfR hL)
  | _, _, _, .thru p t ht f i hL => Expr.thru (D := D.mitRuhe) (ruE p) t ht f (ruE i) (darfR hL)
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D.mitRuhe) t n ht rw
  | _, _, _, .fnref f n h => .fnref (D := D.mitRuhe) (some f) (n + 1) h
  | _, _, _, .refEq a b => .refEq (ruE a) (ruE b)
  | _, _, _, .slotRef r t ht ho f hL => .slotRef (ruE r) t ht ho f (darfR hL)
  | _, _, _, .oldG g hL => Expr.oldG (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .oldS t f i hL => Expr.oldS (D := D.mitRuhe) t f (ruE i) (darfR hL)
  | _, _, _, .widen h1 h2 e => .widen h1 h2 (ruE e)
  | _, _, _, .add a b => .add (ruE a) (ruE b)
  | _, _, _, .sub a b => .sub (ruE a) (ruE b)
  | _, _, _, .neg a => .neg (ruE a)
  | _, _, _, .mul a b => .mul (ruE a) (ruE b)
  | _, _, _, .div h0 h1 a b => .div h0 h1 (ruE a) (ruE b)
  | _, _, _, .rem h0 h1 a b => .rem h0 h1 (ruE a) (ruE b)
  | _, _, _, .sdiv hb a b => .sdiv hb (ruE a) (ruE b)
  | _, _, _, .srem hb a b => .srem hb (ruE a) (ruE b)
  | _, _, _, .getBytes t f hf n i hlo hhi hL =>
      .getBytes (D := D.mitRuhe) t f (congrArg tyR hf) n (ruE i) hlo
        hhi (darfR hL)
  | _, _, _, .band h0 h0' a b => .band h0 h0' (ruE a) (ruE b)
  | _, _, _, .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (ruE a) (ruE b)
  | _, _, _, .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (ruE a) (ruE b)
  | _, _, _, .shl w hw1 hw2 h0 h0' a b => .shl w hw1 hw2 h0 h0' (ruE a) (ruE b)
  | _, _, _, .shr w hw1 hw2 h0 h0' a b => .shr w hw1 hw2 h0 h0' (ruE a) (ruE b)
  | _, _, _, .lt a b => .lt (ruE a) (ruE b)
  | _, _, _, .le a b => .le (ruE a) (ruE b)
  | _, _, _, .eq a b => .eq (ruE a) (ruE b)
  | _, _, _, .fllt a b => .fllt (ruE a) (ruE b)
  | _, _, _, .flle a b => .flle (ruE a) (ruE b)
  | _, _, _, .and a b => .and (ruE a) (ruE b)
  | _, _, _, .or a b => .or (ruE a) (ruE b)
  | _, _, _, .not a => .not (ruE a)
  | _, _, _, .none n => .none n
  | _, _, _, .some e => .some (ruE e)
  | _, _, _, .istSome e => .istSome (ruE e)
  | _, _, _, .case cs i nutz =>
      .case (Ty.mapCases (fun n => n + 1) id cs) ⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩
        ((Ty.mapCases_get (fun n => n + 1) id cs i).symm ▸ ruN nutz)
  | _, _, _, .why n r => .why n r
  | _, _, _, .forallSlots t body hL => Expr.forallSlots (D := D.mitRuhe) t (ruE body) (darfR hL)
  | _, _, _, .existsSlots t body hL => Expr.existsSlots (D := D.mitRuhe) t (ruE body) (darfR hL)
  | _, _, _, .reaches t f hf a b hL =>
      .reaches (D := D.mitRuhe) t f (congrArg tyR hf) (ruE a) (ruE b)
        (darfR hL)
  | _, _, _, .arrNil => .arrNil
  | _, _, _, .arrCons a b => .arrCons (ruE a) (ruE b)
  | _, _, _, .arrGet a i => .arrGet (ruE a) (ruE i)
  | _, _, _, .arrSet a i v => .arrSet (ruE a) (ruE i) (ruE v)
  | _, _, _, .strLit bs h => .strLit bs h
  | _, _, _, .strLen e => .strLen (ruE e)
  | _, _, _, .strCat e e' => .strCat (ruE e) (ruE e')
  | _, _, _, .strGet e e' => .strGet (ruE e) (ruE e')
  | _, _, _, .strEq e e' => .strEq (ruE e) (ruE e')
  | _, _, _, .strLt e e' => .strLt (ruE e) (ruE e')
  | _, _, _, .strWeit m e => .strWeit m (ruE e)
  | _, _, _, .wenn c a b => .wenn (ruE c) (ruE a) (ruE b)
  | _, _, _, .eng e lo hi s => .eng (ruE e) lo hi (ruE s)

/-- A payload expression, translated. -/
def ruN : {Γ : Ctx} → {Λ : List (Res D)} → {c : Option Ty} → NutzlastExpr D Γ Λ c →
    NutzlastExpr D.mitRuhe (Γ.map tyR) (Λ.map resR) (c.map tyR)
  | _, _, _, .empty => .empty
  | _, _, _, .val e => .val (ruE e)

end

/-- Arguments, translated. -/
def ruA : {Γ : Ctx} → {Λ : List (Res D)} → {τs : List Ty} → Args D Γ Λ τs →
    Args D.mitRuhe (Γ.map tyR) (Λ.map resR) (τs.map tyR)
  | _, _, _, .nil => .nil
  | _, _, _, .cons e rest => .cons (ruE e) (ruA rest)

/-- A result expression, translated. -/
def ruErg : {Γ : Ctx} → {Λ : List (Res D)} → {e : Option Ty} → ErgExpr D Γ Λ e →
    ErgExpr D.mitRuhe (Γ.map tyR) (Λ.map resR) (e.map tyR)
  | _, _, _, .empty => .empty
  | _, _, _, .val e => .val (ruE e)

mutual

/-- **A statement of `D` as a statement of `D.mitRuhe`**: the same
    constructor, `f ↦ some f` in calls, holdings transported where their
    equation is propositional. -/
def ruS {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Stmt D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR)
  | _, _, _, _, .assignSlot t f i e hw hL => .assignSlot t f (ruE i) (ruE e) hw (darfR hL)
  | _, _, _, _, .assignThru p t ht f i e hw hL =>
      .assignThru (ruE p) t ht f (ruE i) (ruE e) hw (darfR hL)
  | _, _, _, _, .assignSlotRef r t ht ho f e hw hL =>
      .assignSlotRef (ruE r) t ht ho f (ruE e) hw (darfR hL)
  | _, _, _, _, .assignGlob g e hw hL => .assignGlob g (ruE e) hw (gdarfR hL)
  | _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL =>
      .putBytes (V := vertragR V) t f (congrArg tyR hf) n (ruE i) hlo hhi
        (ruE e) hw (darfR hL)
  | _, _, _, _, .assignVar x e => .assignVar (varR x) (ruE e)
  | _, _, _, _, .shift t f hτ i von nach hn he hw hL =>
      .shift (V := vertragR V) t f (congrArg tyR hτ) (ruE i) von nach hn
        he hw (darfR hL)
  | _, _, _, _, .ite c t e => .ite (ruE c) (ruB t) (ruB e)
  | _, _, _, _, .onOption o p a => .onOption (ruE o) (ruB p) (ruB a)
  | _, _, _, _, .onTag v arms => .onTag (ruE v) (ruArms arms)
  | _, _, _, _, .onWhy r arms => .onWhy (ruE r) (ruGArms arms)
  | _, _, Λ, _, .call f args hp hr =>
      Stmt.nachΛ (nach_map f Λ).symm
        (.call (V := vertragR V) (some f) (ruA args) (rufPasstR hp) hr)
  | _, _, Λ, _, .callInd (n := n) p args hp hr =>
      Stmt.nachΛ (nachSig_map (D.sigNr n) Λ).symm
        (.callInd (V := vertragR V) (n := n + 1) (ruE p) (ruA args) (rufPasstR hp) hr)
  | _, _, _, _, .locks L hr body =>
      .locks L (fun M hM => hr M (held_mem_map.mp hM)) (ruB body)
  | _, _, _, _, .breaking i body => .breaking i (ruB body)
  | _, _, _, _, .traverse t inv body => .traverse t (ruE inv) (ruB body)
  | _, _, _, _, .retry n bis body ueber => .retry n (ruE bis) (ruB body) (ruB ueber)
  | _, _, _, _, .forever a inv body => .forever a (ruE inv) (ruB body)
  | _, _, _, _, .axiomCall a args h hw hg hd hgd =>
      .axiomCall (V := vertragR V) a (ruA args) (by show Option.map tyR (D.aerg a) = _; rw [h]; rfl)
        hw hg (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg'))
  | _, _, _, _, .regWrite r hk e => .regWrite r hk (ruE e)
  | _, _, _, _, .transition r hk m hm hl maske bits => .transition r hk m hm hl maske bits
  | _, _, _, _, .publish g e payload hp hw hL => .publish g (ruE e) payload hp hw (gdarfR hL)
  | _, _, Λ, _, .advances m a h hs =>
      Stmt.nachΛ (by rw [List.map_append, erase_map_rm]; rfl)
        (.advances (V := vertragR V) m a (mem_map_rm.mpr h) hs)
  | _, _, Λ, _, .retires m s h a =>
      Stmt.nachΛ (by rw [erase_map_rm]; rfl) (.retires (V := vertragR V) m s (mem_map_rm.mpr h) a)
  | _, _, _, _, .ret e hΛ => .ret (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .retWhy r hΛ => .retWhy r ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .leave h => .leave h
  | _, _, _, _, .next h => .next h

/-- A block, translated. -/
def ruB {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Block D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons s rest => .cons (ruS s) (ruB rest)
  | _, _, _, _, .bind e rest => .bind (ruE e) (ruB rest)
  | _, _, Λ, _, .bindCall f args he hp hr rest =>
      .bindCall (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nach_map f Λ) (ruB rest))
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (V := vertragR V) (n := n + 1) (ruE p) (ruA args)
        (by show Option.map tyR (D.sigNr n).erg = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nachSig_map (D.sigNr n) Λ) (ruB rest))
  | _, _, Λ, _, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nach_map f Λ) (ruEnd err)) (Block.vorΛ (nach_map f Λ) (ruB rest))
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (V := vertragR V) a (ruA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (ruB rest)
  | _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      .bindAxiomElse (V := vertragR V) a (ruA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hr hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (ruEnd err) (ruB rest)
  | _, _, _, _, .regRead r hk rest => .regRead r hk (ruB rest)
  | _, _, _, _, .regReadElse r hk zusage sonst rest =>
      .regReadElse r hk (ruE zusage) (ruEnd sonst) (ruB rest)
  | _, _, _, _, .awaits g payload hp hL hat rest => .awaits g payload hp (gdarfR hL) hat (ruB rest)
  | _, _, _, _, .exchange g neu hw hL rest => .exchange g (ruE neu) hw (gdarfR hL) (ruB rest)
  | _, _, _, _, .narrow e lo' hi' sonst rest => .narrow (ruE e) lo' hi' (ruEnd sonst) (ruB rest)
  | _, _, _, _, .check c sonst rest => .check (ruE c) (ruEnd sonst) (ruB rest)
  | _, _, _, _, .float op a b lo hi rest => .float op (ruE a) (ruE b) lo hi (ruB rest)
  | _, _, _, _, .floatLit q lo hi rest => .floatLit q lo hi (ruB rest)
  | _, _, _, _, .floatOf e lo hi rest => .floatOf (ruE e) lo hi (ruB rest)
  | _, _, _, _, .floatNarrow e lo hi sonst rest =>
      .floatNarrow (ruE e) lo hi (ruEnd sonst) (ruB rest)

/-- An end block, translated. -/
def ruEnd {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Endblock D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR)
  | _, _, _, .ret e hΛ => .ret (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, .retWhy r hΛ => .retWhy r ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, .leave h => .leave h
  | _, _, _, .next h => .next h
  | _, _, _, .cons s rest => .cons (ruS s) (ruEnd rest)
  | _, _, _, .bind e rest => .bind (ruE e) (ruEnd rest)
  | _, _, Λ, .bindCall f args he hp hr rest =>
      .bindCall (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nach_map f Λ) (ruEnd rest))
  | _, _, Λ, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nach_map f Λ) (ruEnd err)) (Endblock.umΛ (nach_map f Λ) (ruEnd rest))
  | _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (V := vertragR V) a (ruA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (ruEnd rest)
  | _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      .bindAxiomElse (V := vertragR V) a (ruA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hr hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (ruEnd err) (ruEnd rest)
  | _, _, _, .regRead r hk rest => .regRead r hk (ruEnd rest)
  | _, _, _, .regReadElse r hk zusage sonst rest =>
      .regReadElse r hk (ruE zusage) (ruEnd sonst) (ruEnd rest)
  | _, _, _, .awaits g payload hp hL hat rest => .awaits g payload hp (gdarfR hL) hat (ruEnd rest)
  | _, _, Λ, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (V := vertragR V) (n := n + 1) (ruE p) (ruA args)
        (by show Option.map tyR (D.sigNr n).erg = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nachSig_map (D.sigNr n) Λ) (ruEnd rest))
  | _, _, _, .narrow e lo' hi' sonst rest => .narrow (ruE e) lo' hi' (ruEnd sonst) (ruEnd rest)
  | _, _, _, .exchange g neu hw hL rest => .exchange g (ruE neu) hw (gdarfR hL) (ruEnd rest)
  | _, _, _, .ite c t e => .ite (ruE c) (ruEnd t) (ruEnd e)

/-- Arms, translated (the arm scope `ArmCtx` is split on the case). -/
def ruArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option Ty)} → Arms D V l Γ Λ Λ' cs →
      Arms D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR) (Ty.mapCases (fun n => n + 1) id cs)
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons (c := none) b rest => .cons (c := none) (ruB b) (ruArms rest)
  | _, _, _, _, _, .cons (c := some τ) b rest =>
      .cons (c := some (tyR τ)) (ruB b) (ruArms rest)

/-- Reason arms, translated. -/
def ruGArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → GrundArms D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR) n
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons b rest => .cons (ruB b) (ruGArms rest)

end

/-! ## 5. The program, the oracle, the lock invariants -/

/-- **`P` over `D.mitRuhe`**: every function `some f` is `f` translated;
    the idle root `none` has `requires true`, `ensures true`, body
    `return`. -/
def Programm.mitRuhe (P : Programm D) : Programm D.mitRuhe where
  invariante i := Expr.umΛ (invSicht_map (D := D) i) (ruE (P.invariante i))
  requires
    | none => .tru
    | some f => Expr.umΛ (anfang_map (D.signatur f)) (ruE (P.requires f))
  ensures
    | none => .tru
    | some f => Expr.umΓ (ergCtx_map (D.params f) (D.erg f))
        (Expr.umΛ (ende_map (vertragVon D f)) (ruE (P.ensures f)))
  rumpf
    | none => .ret .empty List.Perm.nil
    | some f => Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))
  -- the idle root is no handler; a user function keeps its dispatch fact (Opus agent H)
  unterbricht
    | none => false
    | some f => P.unterbricht f

/-- The member list of `D.mitRuhe`'s functions: the root, then `fs`. -/
def fsRuhe (fs : List D.Fn) : List D.mitRuhe.Fn := none :: fs.map some

theorem fsRuhe_voll {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    ∀ g : D.mitRuhe.Fn, g ∈ fsRuhe fs
  | none => List.mem_cons_self
  | some g => List.mem_cons_of_mem _ (List.mem_map_of_mem (hvoll g))

/-- The declared starts, as functions of `D.mitRuhe`. -/
def wsRuhe (ws : List D.Fn) : List D.mitRuhe.Fn := ws.map some

/-- **The oracle of `D.mitRuhe`**: `O` on the translated-back world and
    arguments, its world translated forth. -/
def Orakel.mitRuhe (O : Orakel D) : Orakel D.mitRuhe where
  wirkt a σ ρ :=
    (worldR (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).1,
      (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).2)
  regLies r σ := O.regLies r (worldZ σ)
  regSchreib := O.regSchreib
  sichtbar g σ := O.sichtbar g (worldZ σ)
  zeiger k := (O.zeiger k).map some

/-- **The lock invariants of `D.mitRuhe`**: the same carriers, `S.inv` on the
    translated-back memory. -/
def SperrInv.mitRuhe (S : SperrInv D) : SperrInv D.mitRuhe :=
  ⟨S.orte, fun L s => S.inv L (speicherZ s)⟩

end Gabbro.Grammatik
