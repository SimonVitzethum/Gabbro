/-
  File:      Grammatik/HoareRegeln.lean
  Subject:   SEQUENTIAL HOARE RULES OVER execBlock, blocks WITHOUT calls.

  `HTripel` is partial correctness over the actual sequential semantics:
  starting from any world/env where `Pre` holds, if the block ends normally
  (`.ok σ' ρ'`), then `Post` holds there. Contracts hold at their place
  with the actual values; pre/post are predicates over the actual world
  AND environment, never quantified over environments.

  `BlockOhneRuf` says a block performs no call: no `call`/`callInd` in any
  statement, no `bindCall`/`bindCallInd`/`bindCallElse` in any block spine,
  and nested blocks preserve the property. Lemma `ohneRuf_Runabhaengig`
  proves the meaning: on such blocks `execBlock` is independent of the
  call-meaning parameter `R`.
-/
module
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Triples and call-freedom. -/

/-- Partial correctness over the actual sequential semantics: for every
    world and environment where `Pre` holds, if the block ends normally
    (`.ok σ' ρ'`), then `Post` holds at the outcome. -/
def HTripel (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ')
    (Pre : World D → Env D Γ → Prop) (Post : World D → Env D Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ →
    ∀ σ' ρ', execBlock O passes R b σ ρ = Ausgang.ok σ' ρ' → Post σ' ρ'

/-- Statement-level triple over `execStmt`. -/
def STTripel (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ')
    (Pre : World D → Env D Γ → Prop) (Post : World D → Env D Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ →
    ∀ σ' ρ', execStmt O passes R s σ ρ = Ausgang.ok σ' ρ' → Post σ' ρ'

/- A statement performs no call: `call`/`callInd`/`callIndElse` are excluded; nested
    blocks (branches, lock bodies, loops, breaking) must preserve the
    property. Oracle/hardware leaves (`axiomCall`, registers, transitions,
    publish/awaits) stay allowed: they are not calls. -/
mutual

inductive StmtOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Prop where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignSlot t f i e hw hL)
  | assignThru {read : Bool} (n : Nat) (p : Expr D Γ Λ (.ptr (.table n (read, true) space))) (t : D.Tab) (ht : D.capTab space n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignThru p t ht f i e hw hL)
  | assignThruOwn {read : Bool} (n : Nat) (o : Nat) (p : Expr D Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table n⟩))
      (t : D.Tab) (ht : D.capTab space n = some t) (f : D.Feld t)
      (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (m : D.Marke) (s : Nat) (ho : D.ownerNr o = some m) (he : m ∈ D.eigner t)
      (hg : Sum.inr (m, s) ∈ D.braucht t)
      (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignThruOwn p t ht f i e m s ho he hg hw hL)
  | assignSlotRef (n : Nat) (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t)
      (ho : D.offen t = true) (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignSlotRef r t ht ho f e hw hL)
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) :
      StmtOhneRuf (.assignGlob g e hw hL)
  | putBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.putBytes t f hf n i hlo hhi e hw hL)
  | assignVar {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ) :
      StmtOhneRuf (.assignVar (τ := τ) x e)
  | shift (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.shift t f hτ i von nach hn he hw hL)
  | ite (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
      (ht : BlockOhneRuf t) (he : BlockOhneRuf e) :
      StmtOhneRuf (.ite c t e)
  | onOption (o : Expr D Γ Λ (.opt n)) (p : Block D V l (.index n :: Γ) Λ Λ')
      (a : Block D V l Γ Λ Λ') (hp : BlockOhneRuf p) (ha : BlockOhneRuf a) :
      StmtOhneRuf (.onOption o p a)
  | onTag (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
      (ha : ArmsOhneRuf arms) :
      StmtOhneRuf (.onTag v arms)
  | onWhy (r : Expr D Γ Λ (.why n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsOhneRuf arms) :
      StmtOhneRuf (.onWhy r arms)
  | locks (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (hb : BlockOhneRuf body) :
      StmtOhneRuf (.locks L hr body)
  | breaking (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : BlockOhneRuf body) :
      StmtOhneRuf (.breaking i body)
  | traverse (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (hb : BlockOhneRuf body) :
      StmtOhneRuf (.traverse t inv body)
  | retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueberlauf : Block D V l Γ Λ Λ)
      (hb : BlockOhneRuf body) (hu : BlockOhneRuf ueberlauf) :
      StmtOhneRuf (.retry n bis body ueberlauf)
  | forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (hb : BlockOhneRuf body) :
      StmtOhneRuf (.forever a inv body)
  | axiomCall (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
      StmtOhneRuf (.axiomCall a args h hw hg hd hgd)
  | axiomCallElse (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
      (err : Endblock D V l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (herr : EndOhneRuf err) :
      StmtOhneRuf (.axiomCallElse e a args he hp hd hgd hr err)
  | regWrite (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r)) :
      StmtOhneRuf (.regWrite r hk e)
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      StmtOhneRuf (.transition r hk m hm hl maske bits)
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) :
      StmtOhneRuf (.publish g e payload hp hw hL)
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      StmtOhneRuf (.advances m a h hs)
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      StmtOhneRuf (.retires m s h a)
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : List.Perm Λ V.ende) :
      StmtOhneRuf (.ret e hΛ)
  | retWhy (r : Fin V.gruende) (hΛ : List.Perm Λ V.ende) :
      StmtOhneRuf (.retWhy r hΛ)
  | leave (h : l = true) :
      StmtOhneRuf (.leave h)
  | next (h : l = true) :
      StmtOhneRuf (.next h)

inductive BlockOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop where
  | nil : BlockOhneRuf .nil
  | cons (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
      (hs : StmtOhneRuf s) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.cons s rest)
  | bind (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.bind e rest)
  | regRead (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.regRead r hk rest)
  | regReadElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.regReadElse r hk zusage sonst rest)
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (hat : D.atomar g = true)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.awaits g payload hp hL hat rest)
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.exchange g neu hw hL rest)
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.narrow e lo' hi' sonst rest)
  | check (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l Γ Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.check c sonst rest)
  | float (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.float op a b lo hi rest)
  | floatLit (q : Int × Int) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.floatLit q lo hi rest)
  | floatOf (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.floatOf e lo hi rest)
  | floatNarrow (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
      (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.floatNarrow e lo hi sonst rest)

inductive EndOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Prop where
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : List.Perm Λ V.ende) :
      EndOhneRuf (.ret e hΛ)
  | retWhy (r : Fin V.gruende) (hΛ : List.Perm Λ V.ende) :
      EndOhneRuf (.retWhy r hΛ)
  | leave (h : l = true) :
      EndOhneRuf (.leave h)
  | next (h : l = true) :
      EndOhneRuf (.next h)
  | cons (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
      (hs : StmtOhneRuf s) (hr : EndOhneRuf rest) :
      EndOhneRuf (.cons s rest)
  | bind (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
      (hr : EndOhneRuf rest) :
      EndOhneRuf (.bind e rest)

inductive ArmsOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option Ty)} → Arms D V l Γ Λ Λ' cs → Prop where
  | nil : ArmsOhneRuf .nil
  | cons (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs)
      (hb : BlockOhneRuf b) (hr : ArmsOhneRuf rest) :
      ArmsOhneRuf (.cons b rest)

inductive GrundArmsOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Prop where
  | nil : GrundArmsOhneRuf .nil
  | cons (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
      (hb : BlockOhneRuf b) (hr : GrundArmsOhneRuf rest) :
      GrundArmsOhneRuf (.cons (l := l) (Γ := Γ) b rest)
end

end Gabbro.Grammatik
