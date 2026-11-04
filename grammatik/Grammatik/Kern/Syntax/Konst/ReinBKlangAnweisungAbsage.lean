module

public import Grammatik.Kern.Syntax.Konst.ReinB

public section

namespace Gabbro.Grammatik

/- Refused `Stmt`/`Block`/`Endblock` cases evaluate to `false`: proved once here so the
    soundness proof can rewrite with them instead of unfolding the deciders. -/

variable (c : ConstProgram) {V : Vertrag c.D} {Γ : Ctx}

theorem constStmtB_absage_assignSlot {l : Bool} {Λ : List (Res c.D)} (t : c.D.Tab) (f : c.D.Feld t)
    (i : Expr c.D Γ Λ (.index (c.D.count t))) (e : Expr c.D Γ Λ (c.D.typ t f)) (hw : V.schreibt t = true)
    (hL : darf c.D t Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.assignSlot t f i e hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_assignThru {l : Bool} {read : Bool} {Λ : List (Res c.D)}
    (p : Expr c.D Γ Λ (.ptr (.table n (read, true) space))) (t : c.D.Tab) (ht : c.D.capTab space n = some t)
    (f : c.D.Feld t) (i : Expr c.D Γ Λ (.index (c.D.count t))) (e : Expr c.D Γ Λ (c.D.typ t f))
    (hw : V.schreibt t = true) (hL : darf c.D t Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.assignThru p t ht f i e hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_assignThruOwn {l : Bool} {read : Bool} {Λ : List (Res c.D)}
    {space o n : Nat} (p : Expr c.D Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table n⟩))
    (t : c.D.Tab) (ht : c.D.capTab space n = some t)
    (f : c.D.Feld t) (i : Expr c.D Γ Λ (.index (c.D.count t))) (e : Expr c.D Γ Λ (c.D.typ t f))
    (m : c.D.Marke) (s : Nat) (ho : c.D.ownerNr o = some m) (he : m ∈ c.D.eigner t)
    (hg : Sum.inr (m, s) ∈ c.D.braucht t)
    (hw : V.schreibt t = true) (hL : darf c.D t Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.assignThruOwn p t ht f i e m s ho he hg hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_assignGlob {l : Bool} {Λ : List (Res c.D)} (g : c.D.Glob) (e : Expr c.D Γ Λ (c.D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf c.D g Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.assignGlob g e hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_putBytes {l : Bool} {Λ : List (Res c.D)} (t : c.D.Tab) (f : c.D.Feld t)
    (hf : c.D.typ t f = .int 0 255) (n : Nat) (i : Expr c.D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo)
    (hhi : hi + n ≤ c.D.count t) (e : Expr c.D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true)
    (hL : darf c.D t Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.putBytes t f hf n i hlo hhi e hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_shift {l : Bool} {Λ : List (Res c.D)} (t : c.D.Tab) (f : c.D.Feld t)
    (hτ : c.D.typ t f = .int lo hi) (i : Expr c.D Γ Λ (.index (c.D.count t))) (von nach : Int)
    (hn : lo ≤ nach ∧ nach ≤ hi) (he : c.D.erlaubt t f von nach = true) (hw : V.schreibt t = true)
    (hL : darf c.D t Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.shift t f hτ i von nach hn he hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_callInd {l : Bool} {Λ : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (hp : RufPasst c.D V (c.D.sigNr n) Λ)
    (hr : (c.D.sigNr n).gruende = 0) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.callInd p args hp hr) = false := by simp only [constStmtB]

theorem constStmtB_absage_callIndElse {l : Bool} {Λ : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (he : (c.D.sigNr n).erg = some τ)
    (hp : RufPasst c.D V (c.D.sigNr n) Λ) (hr : 0 < (c.D.sigNr n).gruende)
    (err : Endblock c.D V l (.why (c.D.sigNr n).gruende :: Γ) (nachSig c.D (c.D.sigNr n) Λ)) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.callIndElse p args he hp hr err) = false := by simp only [constStmtB]

theorem constStmtB_absage_locks {l : Bool} {Λ : List (Res c.D)} (L : c.D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → c.D.rang M < c.D.rang L) (body : Block c.D V l Γ (.held L :: Λ) (.held L :: Λ)) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.locks L hr body) = false := by simp only [constStmtB]

theorem constStmtB_absage_breaking {l : Bool} {Λ Λout : List (Res c.D)} (i : c.D.Inv) (body : Block c.D V l Γ Λ Λout) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.breaking i body) = false := by simp only [constStmtB]

theorem constStmtB_absage_traverse {l : Bool} {Λ : List (Res c.D)} (t : c.D.Tab) (inv : Expr c.D Γ Λ .bool)
    (body : Block c.D V true (.index (c.D.count t) :: Γ) Λ Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.traverse t inv body) = false := by simp only [constStmtB]

theorem constStmtB_absage_retry {l : Bool} {Λ : List (Res c.D)} (n : Nat) (bis : Expr c.D Γ Λ .bool)
    (body : Block c.D V true Γ Λ Λ) (ueberlauf : Block c.D V l Γ Λ Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retry n bis body ueberlauf) = false := by simp only [constStmtB]

theorem constStmtB_absage_forever {l : Bool} {Λ : List (Res c.D)} (a : c.D.Annahme) (inv : Expr c.D Γ Λ .bool)
    (body : Block c.D V true Γ Λ Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.forever a inv body) = false := by simp only [constStmtB]

theorem constStmtB_absage_axiomCall {l : Bool} {Λ : List (Res c.D)} (a : c.D.Ax) (args : Args c.D Γ Λ (c.D.aparams a))
    (h : c.D.aerg a = none) (hw : ∀ t, c.D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, c.D.agschreibt a g = true → V.gschreibt g = true) (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ)
    (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.axiomCall a args h hw hg hd hgd) = false := by simp only [constStmtB]

theorem constStmtB_absage_axiomCallElse {l : Bool} {Λ : List (Res c.D)} (e : Option Ty) (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = e) (hp : RufPasst c.D V (c.D.asignatur a) Λ)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (hr : 0 < c.D.agruende a) (err : Endblock c.D V l (reasonTy (c.D.agruende a) :: Γ) (nachSig c.D (c.D.asignatur a) Λ)) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.axiomCallElse e a args he hp hd hgd hr err) = false := by simp only [constStmtB]

theorem constStmtB_absage_regWrite {l : Bool} {Λ : List (Res c.D)} (r : c.D.Reg) (hk : (c.D.rklasse r).schreibbar = true)
    (e : Expr c.D Γ Λ (c.D.rtyp r)) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.regWrite r hk e) = false := by simp only [constStmtB]

theorem constStmtB_absage_transition {l : Bool} {Λ : List (Res c.D)} (r : c.D.Reg) (hk : (c.D.rklasse r).schreibbar = true)
    (m : c.D.Reg) (hm : c.D.spiegel r = some m) (hl : (c.D.rklasse m).lesbar = true) (maske bits : Int) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.transition r hk m hm hl maske bits) = false := by simp only [constStmtB]

theorem constStmtB_absage_publish {l : Bool} {Λ : List (Res c.D)} (g : c.D.Glob) (e : Expr c.D Γ Λ (c.D.gtyp g))
    (payload : List c.D.Glob) (hp : payload = c.D.nutzlast g) (hw : V.gschreibt g = true)
    (hL : gdarf c.D g Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.publish g e payload hp hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_advances {l : Bool} {Λ : List (Res c.D)} (m : c.D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ)
    (hs : a + 1 < c.D.stufen m) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.advances m a h hs) = false := by simp only [constStmtB]

theorem constStmtB_absage_retires {l : Bool} {Λ : List (Res c.D)} (m : c.D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ)
    (a : c.D.Annahme) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retires m s h a) = false := by simp only [constStmtB]

theorem constStmtB_absage_retWhy {l : Bool} {Λ : List (Res c.D)} (r : Fin V.gruende) (hP : Λ.Perm V.ende) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retWhy r hP) = false := by simp only [constStmtB]

theorem constStmtB_absage_leave {l : Bool} {Λ : List (Res c.D)} (h : l = true) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.leave h) = false := by simp only [constStmtB]

theorem constStmtB_absage_next {l : Bool} {Λ : List (Res c.D)} (h : l = true) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.next h) = false := by simp only [constStmtB]

theorem constStmtB_absage_assignSlotRef {l : Bool} {Λ : List (Res c.D)} (r : Expr c.D Γ Λ (.ref n)) (t : c.D.Tab)
    (ht : c.D.tabNr n = some t) (ho : c.D.offen t = true) (f : c.D.Feld t) (e : Expr c.D Γ Λ (c.D.typ t f))
    (hw : V.schreibt t = true) (hL : darf c.D t Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.assignSlotRef r t ht ho f e hw hL) = false := by simp only [constStmtB]

theorem constStmtB_absage_consumeTraverse {l : Bool} {Λ : List (Res c.D)} (t : c.D.Tab)
    (member : Expr c.D (.index (c.D.count t) :: Γ) Λ .bool)
    (edge : Expr c.D (.index (c.D.count t) :: .index (c.D.count t) :: Γ) Λ .bool) (inv : Expr c.D Γ Λ .bool)
    (bound : Int) (mass : Expr c.D Γ Λ (.int 0 bound)) (body : Block c.D V true (.index (c.D.count t) :: Γ) Λ Λ) :
    constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.consumeTraverse t member edge inv bound mass body) = false := by simp only [constStmtB]

theorem constStmtB_absage_retScoped {l : Bool} {Λ : List (Res c.D)} (e : ErgExpr c.D Γ Λ V.erg)
    (R : RueckRessourcen c.D V Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retScoped e R) = false := by simp only [constStmtB]

theorem constStmtB_absage_retWhyScoped {l : Bool} {Λ : List (Res c.D)} (r : Fin V.gruende)
    (R : RueckRessourcen c.D V Λ) : constStmtB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retWhyScoped r R) = false := by simp only [constStmtB]

theorem constBlockB_absage_bindCallInd {l : Bool} {Λ Λout : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (he : (c.D.sigNr n).erg = some τ)
    (hp : RufPasst c.D V (c.D.sigNr n) Λ) (hr : (c.D.sigNr n).gruende = 0)
    (rest : Block c.D V l (τ :: Γ) (nachSig c.D (c.D.sigNr n) Λ) Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallInd p args he hp hr rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindCallIndElse {l : Bool} {Λ Λout : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (he : (c.D.sigNr n).erg = some τ)
    (hp : RufPasst c.D V (c.D.sigNr n) Λ) (hr : 0 < (c.D.sigNr n).gruende)
    (err : Endblock c.D V l (.why (c.D.sigNr n).gruende :: Γ) (nachSig c.D (c.D.sigNr n) Λ))
    (rest : Block c.D V l (τ :: Γ) (nachSig c.D (c.D.sigNr n) Λ) Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallIndElse p args he hp hr err rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindCallElse {l : Bool} {Λ Λout : List (Res c.D)} (f : c.D.Fn)
    (args : Args c.D Γ Λ (c.D.params f)) (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) Λ)
    (hr : 0 < c.D.gruende f) (err : Endblock c.D V l (.why (c.D.gruende f) :: Γ) (nach c.D f Λ))
    (rest : Block c.D V l (τ :: Γ) (nach c.D f Λ) Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallElse f args he hp hr err rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindAxiom {l : Bool} {Λ Λout : List (Res c.D)} (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = some τ)
    (hw : ∀ t, c.D.aschreibt a t = true → V.schreibt t = true) (hg : ∀ g, c.D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (rest : Block c.D V l (τ :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiom a args he hw hg hd hgd rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindAxiomElse {l : Bool} {Λ Λout : List (Res c.D)} (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = some τ) (hr : 0 < c.D.agruende a)
    (hw : ∀ t, c.D.aschreibt a t = true → V.schreibt t = true) (hg : ∀ g, c.D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (err : Endblock c.D V l (.why (c.D.agruende a) :: Γ) Λ) (rest : Block c.D V l (τ :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomElse a args he hr hw hg hd hgd err rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindAxiomOpt {l : Bool} {Λ Λout : List (Res c.D)} (e : Option Ty) (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = e) (hp : RufPasst c.D V (c.D.asignatur a) Λ)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (rest : Block c.D V l (ErgCtx Γ e) (nachSig c.D (c.D.asignatur a) Λ) Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomOpt e a args he hp hd hgd rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_bindAxiomOptElse {l : Bool} {Λ Λout : List (Res c.D)} (e : Option Ty) (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = e) (hp : RufPasst c.D V (c.D.asignatur a) Λ)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (hr : 0 < c.D.agruende a) (err : Endblock c.D V l (reasonTy (c.D.agruende a) :: Γ) (nachSig c.D (c.D.asignatur a) Λ))
    (rest : Block c.D V l (ErgCtx Γ e) (nachSig c.D (c.D.asignatur a) Λ) Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomOptElse e a args he hp hd hgd hr err rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_regRead {l : Bool} {Λ Λout : List (Res c.D)} (r : c.D.Reg) (hk : (c.D.rklasse r).lesbar = true)
    (rest : Block c.D V l (c.D.rtyp r :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.regRead r hk rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_regReadElse {l : Bool} {Λ Λout : List (Res c.D)} (r : c.D.Reg)
    (hk : (c.D.rklasse r).lesbar = true) (zusage : Expr c.D (c.D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock c.D V l Γ Λ) (rest : Block c.D V l (c.D.rtyp r :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.regReadElse r hk zusage sonst rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_awaits {l : Bool} {Λ Λout : List (Res c.D)} (g : c.D.Glob) (payload : List c.D.Glob)
    (hp : payload = c.D.nutzlast g) (hL : gdarf c.D g Λ) (ha : c.D.atomar g = true)
    (rest : Block c.D V l (c.D.gtyp g :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.awaits g payload hp hL ha rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_exchange {l : Bool} {Λ Λout : List (Res c.D)} (g : c.D.Glob)
    (neu : Expr c.D (c.D.gtyp g :: Γ) Λ (c.D.gtyp g)) (hw : V.gschreibt g = true) (hL : gdarf c.D g Λ)
    (rest : Block c.D V l (c.D.gtyp g :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.exchange g neu hw hL rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_narrow {l : Bool} {Λ Λout : List (Res c.D)} (e : Expr c.D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock c.D V l Γ Λ) (rest : Block c.D V l (.int lo' hi' :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.narrow e lo' hi' sonst rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_narrowRequired {l : Bool} {Λ Λout : List (Res c.D)} (e : Expr c.D Γ Λ (.int lo hi))
    (lo' hi' : Int) (rest : Block c.D V l (.int lo' hi' :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.narrowRequired e lo' hi' rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_check {l : Bool} {Λ Λout : List (Res c.D)} (cond : Expr c.D Γ Λ .bool)
    (sonst : Endblock c.D V l Γ Λ) (rest : Block c.D V l Γ Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.check cond sonst rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_float {l : Bool} {Λ Λout : List (Res c.D)} (op : GleitOp)
    (a : Expr c.D Γ Λ (.fl l1 h1)) (b : Expr c.D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Block c.D V l (.fl lo hi :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.float op a b lo hi rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_floatLit {l : Bool} {Λ Λout : List (Res c.D)} (q : Int × Int) (lo hi : Int × Int)
    (rest : Block c.D V l (.fl lo hi :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatLit q lo hi rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_floatOf {l : Bool} {Λ Λout : List (Res c.D)} (e : Expr c.D Γ Λ (.int l1 h1))
    (lo hi : Int × Int) (rest : Block c.D V l (.fl lo hi :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatOf e lo hi rest) = false := by simp only [constBlockB]

theorem constBlockB_absage_floatNarrow {l : Bool} {Λ Λout : List (Res c.D)} (e : Expr c.D Γ Λ (.fl l1 h1))
    (lo hi : Int × Int) (sonst : Endblock c.D V l Γ Λ) (rest : Block c.D V l (.fl lo hi :: Γ) Λ Λout) :
    constBlockB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatNarrow e lo hi sonst rest) = false := by simp only [constBlockB]

theorem constEndB_absage_retWhy {l : Bool} {Λ : List (Res c.D)} (r : Fin V.gruende) (hP : Λ.Perm V.ende) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retWhy r hP) = false := by simp only [constEndB]

theorem constEndB_absage_leave {l : Bool} {Λ : List (Res c.D)} (h : l = true) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.leave h) = false := by simp only [constEndB]

theorem constEndB_absage_next {l : Bool} {Λ : List (Res c.D)} (h : l = true) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.next h) = false := by simp only [constEndB]

theorem constEndB_absage_narrowRequired {l : Bool} {Λ : List (Res c.D)} (e : Expr c.D Γ Λ (.int lo hi))
    (lo' hi' : Int) (rest : Endblock c.D V l (.int lo' hi' :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.narrowRequired e lo' hi' rest) = false := by simp only [constEndB]

theorem constEndB_absage_retScoped {l : Bool} {Λ : List (Res c.D)} (e : ErgExpr c.D Γ Λ V.erg)
    (R : RueckRessourcen c.D V Λ) : constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retScoped e R) = false := by simp only [constEndB]

theorem constEndB_absage_retWhyScoped {l : Bool} {Λ : List (Res c.D)} (r : Fin V.gruende)
    (R : RueckRessourcen c.D V Λ) : constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.retWhyScoped r R) = false := by simp only [constEndB]

theorem constEndB_absage_bindCallElse {l : Bool} {Λ : List (Res c.D)} (f : c.D.Fn) (args : Args c.D Γ Λ (c.D.params f))
    (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) Λ) (hr : 0 < c.D.gruende f)
    (err : Endblock c.D V l (.why (c.D.gruende f) :: Γ) (nach c.D f Λ)) (rest : Endblock c.D V l (τ :: Γ) (nach c.D f Λ)) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallElse f args he hp hr err rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindAxiom {l : Bool} {Λ : List (Res c.D)} (a : c.D.Ax) (args : Args c.D Γ Λ (c.D.aparams a))
    (he : c.D.aerg a = some τ) (hw : ∀ t, c.D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, c.D.agschreibt a g = true → V.gschreibt g = true) (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ)
    (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ) (rest : Endblock c.D V l (τ :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiom a args he hw hg hd hgd rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindAxiomElse {l : Bool} {Λ : List (Res c.D)} (a : c.D.Ax) (args : Args c.D Γ Λ (c.D.aparams a))
    (he : c.D.aerg a = some τ) (hr : 0 < c.D.agruende a)
    (hw : ∀ t, c.D.aschreibt a t = true → V.schreibt t = true) (hg : ∀ g, c.D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (err : Endblock c.D V l (.why (c.D.agruende a) :: Γ) Λ) (rest : Endblock c.D V l (τ :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomElse a args he hr hw hg hd hgd err rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindAxiomOpt {l : Bool} {Λ : List (Res c.D)} (e : Option Ty) (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = e) (hp : RufPasst c.D V (c.D.asignatur a) Λ)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (rest : Endblock c.D V l (ErgCtx Γ e) (nachSig c.D (c.D.asignatur a) Λ)) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomOpt e a args he hp hd hgd rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindAxiomOptElse {l : Bool} {Λ : List (Res c.D)} (e : Option Ty) (a : c.D.Ax)
    (args : Args c.D Γ Λ (c.D.aparams a)) (he : c.D.aerg a = e) (hp : RufPasst c.D V (c.D.asignatur a) Λ)
    (hd : ∀ t, c.D.aschreibt a t = true → darf c.D t Λ) (hgd : ∀ g, c.D.agschreibt a g = true → gdarf c.D g Λ)
    (hr : 0 < c.D.agruende a) (err : Endblock c.D V l (reasonTy (c.D.agruende a) :: Γ) (nachSig c.D (c.D.asignatur a) Λ))
    (rest : Endblock c.D V l (ErgCtx Γ e) (nachSig c.D (c.D.asignatur a) Λ)) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindAxiomOptElse e a args he hp hd hgd hr err rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindCallInd {l : Bool} {Λ : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (he : (c.D.sigNr n).erg = some τ)
    (hp : RufPasst c.D V (c.D.sigNr n) Λ) (hr : (c.D.sigNr n).gruende = 0)
    (rest : Endblock c.D V l (τ :: Γ) (nachSig c.D (c.D.sigNr n) Λ)) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallInd p args he hp hr rest) = false := by simp only [constEndB]

theorem constEndB_absage_bindCallIndElse {l : Bool} {Λ : List (Res c.D)} (p : Expr c.D Γ Λ (.fnptr n))
    (args : Args c.D Γ Λ (c.D.sigNr n).params) (he : (c.D.sigNr n).erg = some τ)
    (hp : RufPasst c.D V (c.D.sigNr n) Λ) (hr : 0 < (c.D.sigNr n).gruende)
    (err : Endblock c.D V l (.why (c.D.sigNr n).gruende :: Γ) (nachSig c.D (c.D.sigNr n) Λ))
    (rest : Endblock c.D V l (τ :: Γ) (nachSig c.D (c.D.sigNr n) Λ)) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.bindCallIndElse p args he hp hr err rest) = false := by simp only [constEndB]

theorem constEndB_absage_regRead {l : Bool} {Λ : List (Res c.D)} (r : c.D.Reg) (hk : (c.D.rklasse r).lesbar = true)
    (rest : Endblock c.D V l (c.D.rtyp r :: Γ) Λ) : constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.regRead r hk rest) = false := by simp only [constEndB]

theorem constEndB_absage_regReadElse {l : Bool} {Λ : List (Res c.D)} (r : c.D.Reg)
    (hk : (c.D.rklasse r).lesbar = true) (zusage : Expr c.D (c.D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock c.D V l Γ Λ) (rest : Endblock c.D V l (c.D.rtyp r :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.regReadElse r hk zusage sonst rest) = false := by simp only [constEndB]

theorem constEndB_absage_awaits {l : Bool} {Λ : List (Res c.D)} (g : c.D.Glob) (payload : List c.D.Glob)
    (hp : payload = c.D.nutzlast g) (hL : gdarf c.D g Λ) (ha : c.D.atomar g = true)
    (rest : Endblock c.D V l (c.D.gtyp g :: Γ) Λ) : constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.awaits g payload hp hL ha rest) = false := by simp only [constEndB]

theorem constEndB_absage_narrow {l : Bool} {Λ : List (Res c.D)} (e : Expr c.D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock c.D V l Γ Λ) (rest : Endblock c.D V l (.int lo' hi' :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.narrow e lo' hi' sonst rest) = false := by simp only [constEndB]

theorem constEndB_absage_exchange {l : Bool} {Λ : List (Res c.D)} (g : c.D.Glob)
    (neu : Expr c.D (c.D.gtyp g :: Γ) Λ (c.D.gtyp g)) (hw : V.gschreibt g = true) (hL : gdarf c.D g Λ)
    (rest : Endblock c.D V l (c.D.gtyp g :: Γ) Λ) : constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.exchange g neu hw hL rest) = false := by simp only [constEndB]

theorem constEndB_absage_float {l : Bool} {Λ : List (Res c.D)} (op : GleitOp)
    (a : Expr c.D Γ Λ (.fl l1 h1)) (b : Expr c.D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Endblock c.D V l (.fl lo hi :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.float op a b lo hi rest) = false := rfl

theorem constEndB_absage_floatLit {l : Bool} {Λ : List (Res c.D)} (q : Int × Int) (lo hi : Int × Int)
    (rest : Endblock c.D V l (.fl lo hi :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatLit q lo hi rest) = false := rfl

theorem constEndB_absage_floatOf {l : Bool} {Λ : List (Res c.D)} (e : Expr c.D Γ Λ (.int l1 h1))
    (lo hi : Int × Int) (rest : Endblock c.D V l (.fl lo hi :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatOf e lo hi rest) = false := rfl

theorem constEndB_absage_floatNarrow {l : Bool} {Λ : List (Res c.D)} (e : Expr c.D Γ Λ (.fl l1 h1))
    (lo hi : Int × Int) (sonst : Endblock c.D V l Γ Λ) (rest : Endblock c.D V l (.fl lo hi :: Γ) Λ) :
    constEndB c (V := V) (l := l) (Γ := Γ) (Λ := Λ) (.floatNarrow e lo hi sonst rest) = false := rfl

end Gabbro.Grammatik
