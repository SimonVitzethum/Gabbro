import Grammatik.Bausteine.Arena.Ownership.Body.CallInd

/-! **The general ownership body judgment** over G's actual syntax.

`OB A I out k c b c'` says: started in the source context `c`, the block `b`
of a function with result kind `out` keeps the ownership discipline and
falls off in `c'`; a `leave`/`next` leaves in a context that exits to the
loop context `k`. One rule per G form: every expression evaluated is
access-checked against the current context, every store keeps the
allocator words and links, the executed allocator forms move rights, every
call (direct or through a pointer) hands its arguments over by the callee's
interface, branches join in a common weaker context and loops keep an
invariant context. A form without a rule (a raw store into a link or an
allocator word, an unframed foreign body, an access without a current
right) has no derivation. Soundness: `Body/Sound.lean`. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Context operations of the rules -/

/-- A store into table `t` at index `i`: into the arena only through a current right. -/
def storeCheck (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) {lo hi : Int}
    (i : Expr D Γ Λ (.int lo hi)) : Bool :=
  if t = A.tab then accessCheck c i else true

/-- Assigning a variable gives its name the origin of the new value. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Source.Context.assign (c : Context) {Γ : Ctx} {τ : Ty}
    (x : Var Γ τ) (o : Option Nat) : Context :=
  { c with references := c.references.set x.unten o }

/-- The context inside a case arm: a payload binder carries no grant. -/
def armBind (c : Context) : Option (Int × Int) → Context
  | none => c
  | some _ => c.bind none

def armDrop (c : Context) : Option (Int × Int) → Context
  | none => c
  | some _ => c.drop

/-- The caller context after a discarded result, by result kind. -/
def dropContextB (c : Context) (owner : Bool) : Context := if owner then c.bindFresh.drop else c

/-! ## 2. What an outcome promises -/

section Post

variable (A : FreiForm D) (fr : Frame) (s0 : State) {V : Vertrag D} (out : Flow.Output A V.erg)

/-- A value return meets the function's interface postcondition. -/
def DoneValue (σ : World D) (v : ErgVal D V.erg) : Prop :=
  ∃ s, s.agrees A σ ∧ A.FreiOk σ ∧ s0.local s fr ∧ s0.progress s ∧ out.result A fr s v

/-- A reason return leaves no allocation owned by the activation. -/
def DoneReason (σ : World D) : Prop :=
  ∃ s, s.agrees A σ ∧ A.FreiOk σ ∧ s0.local s fr ∧ s0.progress s ∧ s.closed fr

/-- **The promise of a block outcome.** -/
def BPost (k c' : Context) {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .ok σ ρ => Holds A fr s0 c' σ ρ
  | .zurueck σ v => DoneValue A fr s0 out σ v
  | .why σ _ => DoneReason A fr s0 σ
  | .leave _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .next _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .logik _ => True
  | .hardware _ => True

/-- **The promise of an end-block outcome.** -/
def EPost (k : Context) {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ v => DoneValue A fr s0 out σ v
  | .why σ _ => DoneReason A fr s0 σ
  | .leave _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .next _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .logik _ => True
  | .hardware _ => True

end Post

/-! ## 3. The judgment -/

mutual

/-- **A statement.** -/
inductive OS (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Context → Context → Stmt D V l Γ Λ Λ' →
      Context → Prop where
  | assignSlot {l Γ Λ k c} (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
      (hn : NotLink A t f) (hi : checkExpression A c i = true) (he : checkExpression A c e = true)
      (hs : storeCheck A c t i = true) :
      OS A I out (l := l) k c (.assignSlot t f i e hw hL) c
  | assignThru {l Γ Λ k c n} (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab) (ht : D.tabNr n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) (hn : NotLink A t f)
      (hp : checkExpression A c p = true) (hi : checkExpression A c i = true)
      (he : checkExpression A c e = true) (hs : storeCheck A c t i = true) :
      OS A I out (l := l) k c (.assignThru p t ht f i e hw hL) c
  | assignGlob {l Γ Λ k c} (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (hg : NotMetaGlob A g) (he : checkExpression A c e = true) :
      OS A I out (l := l) k c (.assignGlob g e hw hL) c
  | putBytes {l Γ Λ k c lo hi} (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ)
      (ht : t ≠ A.tab) (hi : checkExpression A c i = true) (he : checkExpression A c e = true) :
      OS A I out (l := l) k c (.putBytes t f hf n i hlo hhi e hw hL) c
  | assignVar {l Γ Λ k c τ} (x : Var Γ τ) (e : Expr D Γ Λ τ) (he : checkExpression A c e = true) :
      OS A I out (l := l) (Λ := Λ) k c (.assignVar x e) (c.assign x (origin c e))
  | shift {l Γ Λ k c lo hi} (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ)
      (hl : NotLink A t f) (hi : checkExpression A c i = true) (hs : storeCheck A c t i = true) :
      OS A I out (l := l) k c (.shift t f hτ i von nach hn he hw hL) c
  | ite {l Γ Λ Λ' k c c'} (cond : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
      (hc : checkExpression A c cond = true) (ht : OB A I out k c t c') (he : OB A I out k c e c') :
      OS A I out k c (.ite cond t e) c'
  | onOption {l Γ Λ Λ' k c c' c1 n} (o : Expr D Γ Λ (.opt n)) (p : Block D V l (.index n :: Γ) Λ Λ')
      (a : Block D V l Γ Λ Λ') (ho : checkExpression A c o = true)
      (hp : OB A I out k (c.bind none) p c1) (hw : Weaker c' c1.drop) (ha : OB A I out k c a c') :
      OS A I out k c (.onOption o p a) c'
  | onTag {l Γ Λ Λ' k c c' cs} (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
      (hv : checkExpression A c v = true) (ha : OArms A I out k c arms c') :
      OS A I out k c (.onTag v arms) c'
  | onWhy {l Γ Λ Λ' k c c' n} (r : Expr D Γ Λ (.why n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (hr : checkExpression A c r = true) (ha : OGrund A I out k c arms c') :
      OS A I out k c (.onWhy r arms) c'
  | call {l Γ Λ k c} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
      (hr : D.gruende f = 0) (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList (I f).parameters) (originList c args) = true) :
      OS A I out (l := l) k c (.call f args hp hr)
        (dropContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output)
  | callInd {l Γ Λ k c n} (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (J : Modes (D.sigNr n).params) (owner : Bool) (hJ : SigCompatible I n J owner)
      (hpc : checkExpression A c p = true) (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList J) (originList c args) = true) :
      OS A I out (l := l) k c (.callInd p args hp hr)
        (dropContextB (c.afterCall (modeList J) (originList c args)) owner)
  | locks {l Γ Λ k c c'} (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (hb : OB A I out k c body c') :
      OS A I out k c (.locks L hr body) c'
  | breaking {l Γ Λ Λ' k c c'} (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : OB A I out k c body c') :
      OS A I out k c (.breaking i body) c'
  | traverse {l Γ Λ k c kk c1} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (hentry : Weaker kk c)
      (hinv : checkExpression A kk inv = true) (hb : OB A I out kk (kk.bind none) body c1)
      (hback : Weaker kk c1.drop) :
      OS A I out (l := l) k c (.traverse t inv body) kk
  | retry {l Γ Λ k c kk c1} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueberlauf : Block D V l Γ Λ Λ) (hentry : Weaker kk c) (hbis : checkExpression A kk bis = true)
      (hb : OB A I out kk kk body c1) (hback : Weaker kk c1) (hu : OB A I out k kk ueberlauf kk) :
      OS A I out k c (.retry n bis body ueberlauf) kk
  | forever {l Γ Λ k c kk c1} (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (hentry : Weaker kk c) (hinv : checkExpression A kk inv = true) (hb : OB A I out kk kk body c1)
      (hback : Weaker kk c1) :
      OS A I out (l := l) k c (.forever a inv body) kk
  | axiomCall {l Γ Λ k c} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (hfree : AxiomFree A a) (ha : checkArguments A c args = true) :
      OS A I out (l := l) k c (.axiomCall a args h hw hg hd hgd) c
  | regWrite {l Γ Λ k c} (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r))
      (he : checkExpression A c e = true) :
      OS A I out (l := l) k c (.regWrite r hk e) c
  | transition {l Γ Λ k c} (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      OS A I out (l := l) (Γ := Γ) (Λ := Λ) k c (.transition r hk m hm hl maske bits) c
  | publish {l Γ Λ k c} (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
      (hg : NotMetaGlob A g) (he : checkExpression A c e = true) :
      OS A I out (l := l) k c (.publish g e payload hp hw hL) c
  | advances {l Γ Λ k c} (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      OS A I out (l := l) (Γ := Γ) k c (.advances m a h hs) c
  | retires {l Γ Λ k c} (m : D.Marke) (st : Nat) (h : Res.marke m st ∈ Λ) (a : D.Annahme) :
      OS A I out (l := l) (Γ := Γ) k c (.retires m st h a) c
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c c' : Context} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (he : out.check A c e = true) :
      OS A I out (l := l) k c (.ret e hΛ) c'
  | retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c c' : Context} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) (hf : finish c none = true) :
      OS A I out (l := l) (Γ := Γ) k c (.retWhy r hΛ) c'
  | leave {Γ Λ k c c'} (h : true = true) (hx : ExitsTo k c) :
      OS A I out (Γ := Γ) (Λ := Λ) k c (.leave h) c'
  | next {Γ Λ k c c'} (h : true = true) (hx : ExitsTo k c) :
      OS A I out (Γ := Γ) (Λ := Λ) k c (.next h) c'

/-- **A block.** -/
inductive OB (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Context → Context → Block D V l Γ Λ Λ' →
      Context → Prop where
  | nil {l Γ Λ k c} : OB A I out (l := l) (Γ := Γ) (Λ := Λ) k c .nil c
  | cons {l Γ Λ Λ1 Λ' k c c1 c2} (s : Stmt D V l Γ Λ Λ1) (rest : Block D V l Γ Λ1 Λ')
      (hs : OS A I out k c s c1) (hr : OB A I out k c1 rest c2) : OB A I out k c (.cons s rest) c2
  | weaken {l Γ Λ Λ' k c c1 c2} (b : Block D V l Γ Λ Λ') (hb : OB A I out k c b c1) (hw : Weaker c2 c1) :
      OB A I out k c b c2
  | bind {l Γ Λ Λ' k c c1 τ} (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (he : checkExpression A c e = true) (hr : OB A I out k (c.bind (origin c e)) rest c1) :
      OB A I out k c (.bind e rest) c1.drop
  | bindCall {l Γ Λ Λ' k c c1 τ} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
      (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList (I f).parameters) (originList c args) = true)
      (hrest : OB A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest c1) :
      OB A I out k c (.bindCall f args he hp hr rest) c1.drop
  | bindCallInd {l Γ Λ Λ' k c c1 τ n} (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
      (J : Modes (D.sigNr n).params) (owner : Bool) (hJ : SigCompatible I n J owner)
      (hpc : checkExpression A c p = true) (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList J) (originList c args) = true)
      (hrest : OB A I out k (resultContextB (c.afterCall (modeList J) (originList c args)) owner) rest c1) :
      OB A I out k c (.bindCallInd p args he hp hr rest) c1.drop
  | bindCallElse {l Γ Λ Λ' k c c1 τ} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList (I f).parameters) (originList c args) = true)
      (herr : OE A I out k ((c.afterCall (modeList (I f).parameters) (originList c args)).bind none) err)
      (hrest : OB A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest c1) :
      OB A I out k c (.bindCallElse f args he hp hr err rest) c1.drop
  | bindAxiom {l Γ Λ Λ' k c c1 τ} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hfree : AxiomFree A a) (ha : checkArguments A c args = true)
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.bindAxiom a args he hw hg hd hgd rest) c1.drop
  | bindAxiomElse {l Γ Λ Λ' k c c1 τ} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hfree : AxiomFree A a) (ha : checkArguments A c args = true)
      (herr : OE A I out k (c.bind none) err) (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.bindAxiomElse a args he hr hw hg hd hgd err rest) c1.drop
  | regRead {l Γ Λ Λ' k c c1} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.regRead r hk rest) c1.drop
  | regReadElse {l Γ Λ Λ' k c c1} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hz : checkExpression A (c.bind none) zusage = true)
      (hs : OE A I out k c sonst) (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.regReadElse r hk zusage sonst rest) c1.drop
  | awaits {l Γ Λ Λ' k c c1} (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (ha : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.awaits g payload hp hL ha rest) c1.drop
  | exchange {l Γ Λ Λ' k c c1} (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : V.gschreibt g = true) (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
      (hg : NotMetaGlob A g) (hn : checkExpression A (c.bind none) neu = true)
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.exchange g neu hw hL rest) c1.drop
  | narrow {l Γ Λ Λ' k c c1 lo hi} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (he : checkExpression A c e = true)
      (hs : OE A I out k c sonst) (hrest : OB A I out k (c.bind (origin c e)) rest c1) :
      OB A I out k c (.narrow e lo' hi' sonst rest) c1.drop
  | check {l Γ Λ Λ' k c c1} (cond : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ')
      (hc : checkExpression A c cond = true) (hs : OE A I out k c sonst) (hrest : OB A I out k c rest c1) :
      OB A I out k c (.check cond sonst rest) c1
  | float {l Γ Λ Λ' k c c1 l1 h1 l2 h2} (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1))
      (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (ha : checkExpression A c a = true) (hb : checkExpression A c b = true)
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.float op a b lo hi rest) c1.drop
  | floatLit {l Γ Λ Λ' k c c1} (q : Int × Int) (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.floatLit q lo hi rest) c1.drop
  | floatOf {l Γ Λ Λ' k c c1 l1 h1} (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (he : checkExpression A c e = true)
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.floatOf e lo hi rest) c1.drop
  | floatNarrow {l Γ Λ Λ' k c c1 l1 h1} (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
      (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (he : checkExpression A c e = true) (hs : OE A I out k c sonst)
      (hrest : OB A I out k (c.bind none) rest c1) :
      OB A I out k c (.floatNarrow e lo hi sonst rest) c1.drop
  /-- `let x = alloc A (v) else voll;` from the free list: the binder is a new owning origin. -/
  | allocList {l Γ Λ Λ' k c c1} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
      (hv : checkExpression A c v = true) (hvoll : OE A I out k c voll)
      (hrest : OB A I out k c.bindFresh rest c1) :
      OB A I out k c (Block.freiNimm A v hwT hLT hwK hLK voll rest) c1.drop
  /-- `let x = alloc A (v) else voll;` from the used counter. -/
  | allocCounter {l Γ Λ Λ' k c c1} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwG : V.gschreibt A.zaehl = true)
      (hLG : gdarf D A.zaehl Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
      (hv : checkExpression A c v = true) (hvoll : OE A I out k c voll)
      (hrest : OB A I out k c.bindFresh rest c1) :
      OB A I out k c (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) c1.drop
  /-- `free A[x];` consumes the owning origin of `x`. -/
  | release {l Γ Λ Λ' k c c2 c1 i} (x : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ')
      (hc : consume c (.var (Λ := Λ) x) = some (c2, i)) (hrest : OB A I out k c2 rest c1) :
      OB A I out k c (Block.freiVar A x hwT hLT hwK hLK rest) c1

/-- **An end block** (a body, or an `else` that does not fall off). -/
inductive OE (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Context → Context → Endblock D V l Γ Λ → Prop where
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (he : out.check A c e = true) :
      OE A I out (l := l) k c (.ret e hΛ)
  | retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) (hf : finish c none = true) :
      OE A I out (l := l) (Γ := Γ) k c (.retWhy r hΛ)
  | leave {Γ Λ k c} (h : true = true) (hx : ExitsTo k c) :
      OE A I out (Γ := Γ) (Λ := Λ) k c (.leave h)
  | next {Γ Λ k c} (h : true = true) (hx : ExitsTo k c) :
      OE A I out (Γ := Γ) (Λ := Λ) k c (.next h)
  | cons {l Γ Λ Λ1 k c c1} (s : Stmt D V l Γ Λ Λ1) (rest : Endblock D V l Γ Λ1)
      (hs : OS A I out k c s c1) (hr : OE A I out k c1 rest) : OE A I out k c (.cons s rest)
  | bind {l Γ Λ k c τ} (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
      (he : checkExpression A c e = true) (hr : OE A I out k (c.bind (origin c e)) rest) :
      OE A I out k c (.bind e rest)
  | bindCall {l Γ Λ k c τ} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) (rest : Endblock D V l (τ :: Γ) (nach D f Λ))
      (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList (I f).parameters) (originList c args) = true)
      (hrest : OE A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest) :
      OE A I out k c (.bindCall f args he hp hr rest)
  | bindCallElse {l Γ Λ k c τ} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList (I f).parameters) (originList c args) = true)
      (herr : OE A I out k ((c.afterCall (modeList (I f).parameters) (originList c args)).bind none) err)
      (hrest : OE A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest) :
      OE A I out k c (.bindCallElse f args he hp hr err rest)
  | bindAxiom {l Γ Λ k c τ} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (rest : Endblock D V l (τ :: Γ) Λ)
      (hfree : AxiomFree A a) (ha : checkArguments A c args = true)
      (hrest : OE A I out k (c.bind none) rest) :
      OE A I out k c (.bindAxiom a args he hw hg hd hgd rest)
  | bindAxiomElse {l Γ Λ k c τ} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ) (rest : Endblock D V l (τ :: Γ) Λ)
      (hfree : AxiomFree A a) (ha : checkArguments A c args = true)
      (herr : OE A I out k (c.bind none) err) (hrest : OE A I out k (c.bind none) rest) :
      OE A I out k c (.bindAxiomElse a args he hr hw hg hd hgd err rest)
  | regRead {l Γ Λ k c} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Endblock D V l (D.rtyp r :: Γ) Λ) (hrest : OE A I out k (c.bind none) rest) :
      OE A I out k c (.regRead r hk rest)
  | regReadElse {l Γ Λ k c} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Endblock D V l (D.rtyp r :: Γ) Λ) (hz : checkExpression A (c.bind none) zusage = true)
      (hs : OE A I out k c sonst) (hrest : OE A I out k (c.bind none) rest) :
      OE A I out k c (.regReadElse r hk zusage sonst rest)
  | awaits {l Γ Λ k c} (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (ha : D.atomar g = true) (rest : Endblock D V l (D.gtyp g :: Γ) Λ)
      (hrest : OE A I out k (c.bind none) rest) :
      OE A I out k c (.awaits g payload hp hL ha rest)
  | bindCallInd {l Γ Λ k c τ n} (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ))
      (J : Modes (D.sigNr n).params) (owner : Bool) (hJ : SigCompatible I n J owner)
      (hpc : checkExpression A c p = true) (ha : checkArguments A c args = true)
      (hplan : planFits c (modeList J) (originList c args) = true)
      (hrest : OE A I out k (resultContextB (c.afterCall (modeList J) (originList c args)) owner) rest) :
      OE A I out k c (.bindCallInd p args he hp hr rest)

/-- **The arms of a `match` over a tagged value.** All arms end in one context. -/
inductive OArms (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option (Int × Int))} →
      Context → Context → Arms D V l Γ Λ Λ' cs → Context → Prop where
  | nil {l Γ Λ k c c'} : OArms A I out (l := l) (Γ := Γ) (Λ := Λ) k c .nil c'
  | cons {l Γ Λ Λ' k c c' c1 ca cs} (b : Block D V l (ArmCtx Γ ca) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs)
      (hb : OB A I out k (armBind c ca) b c1) (hw : Weaker c' (armDrop c1 ca))
      (hr : OArms A I out k c rest c') : OArms A I out k c (.cons b rest) c'

/-- **The arms of a `match` over a reason.** -/
inductive OGrund (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
      Context → Context → GrundArms D V l Γ Λ Λ' n → Context → Prop where
  | nil {l Γ Λ k c c'} : OGrund A I out (l := l) (Γ := Γ) (Λ := Λ) k c .nil c'
  | cons {l Γ Λ Λ' k c c' c1 n} (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
      (hb : OB A I out k c b c1) (hw : Weaker c' c1) (hr : OGrund A I out k c rest c') :
      OGrund A I out k c (.cons b rest) c'

end

end Gabbro.Grammatik.ArenaOwnership.Body
