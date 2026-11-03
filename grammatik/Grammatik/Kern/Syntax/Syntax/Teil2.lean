module

public import Grammatik.Kern.Syntax.Syntax.Teil2Expr

@[expose] public section

namespace Gabbro.Grammatik
variable (D : Deklaration)
variable (V : Vertrag D)

mutual

inductive Stmt : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  /-- A store requires write permission independently of read permission, plus the contract frame and guards. -/
  | assignThru {read : Bool} (p : Expr D Γ Λ (.ptr (.table n (read, true) space))) (t : D.Tab) (ht : D.capTab space n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `n` Bytes ab Index `i` schreiben («SG-16») -- ein Feld eines `format` ueber einem
      Bytetraeger setzen. -/
  | putBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | assignVar (x : Var Γ τ) (e : Expr D Γ Λ τ) : Stmt l Γ Λ Λ
  /-- `T.slots[i].s = B;` an einem `state`-Feld: der Uebergang `von -> nach` ist ERKLAERT
      (`state S { … }`), und dass das Feld gerade auf `von` steht, ist die Logik des
      Schreibers (`Logik.uebergang`). -/
  | shift (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | ite (c : Expr D Γ Λ .bool) (t e : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | onOption (o : Expr D Γ Λ (.opt n)) (p : Block l (.index n :: Γ) Λ Λ') (a : Block l Γ Λ Λ') :
      Stmt l Γ Λ Λ'
  | onTag (v : Expr D Γ Λ (.sum cs)) (arms : Arms l Γ Λ Λ' cs) : Stmt l Γ Λ Λ'
  | onWhy (r : Expr D Γ Λ (.why n)) (arms : GrundArms l Γ Λ Λ' n) : Stmt l Γ Λ Λ'
  /-- `f(a, b);` -/
  | call (f : D.Fn) (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
      (hr : D.gruende f = 0) : Stmt l Γ Λ (nach D f Λ)
  /-- `p(a, b);` durch einen Funktionszeiger («B8»): der Vertrag steht am TYP. -/
  | callInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0) :
      Stmt l Γ Λ (nachSig D (D.sigNr n) Λ)
  /-- `locks L { … }` / `observes R { … }` -- Rang groesser als alles Gehaltene (`H006`). -/
  | locks (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block l Γ (.held L :: Λ) (.held L :: Λ)) : Stmt l Γ Λ Λ
  /-- `breaking I { … }` -- die Invariante ruht; ihre Wiederherstellung wird am `return`
      verlangt wie ohne `breaking` (`schuldet`). Der Name steht im Term, damit er
      nachgelesen werden kann (`D013`). -/
  | breaking (i : D.Inv) (body : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | traverse (t : D.Tab) (inv : Expr D Γ Λ .bool) (body : Block true (.index (D.count t) :: Γ) Λ Λ) :
      Stmt l Γ Λ Λ
  | retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) (ueberlauf : Block l Γ Λ Λ) :
      Stmt l Γ Λ Λ
  | forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) : Stmt l Γ Λ Λ
  | axiomCall (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `R = e;` an einem Register (`transition` ist dieselbe Anweisung mit dem Spiegel): die
      Klasse erlaubt das Schreiben, oder die Anweisung ist nicht ableitbar (`R005`/`R006`). -/
  | regWrite (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r)) :
      Stmt l Γ Λ Λ
  /-- `transition t { R.b : 0 -> 1 }` (Falle 4): EIN Lesen des Spiegels `m`, EIN Schreiben
      auf `R` -- die Bits `bits` unter der Maske `maske` ersetzt, alle anderen aus dem
      Spiegel. Dass `m` der Spiegel von `R` ist, steht in der Deklaration (`mirrors`); dass
      das Geraet die zwei Zugriffe in dieser Reihenfolge sieht, ist die Annahme am Geraet. -/
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      Stmt l Γ Λ Λ
  /-- `A = e publishes { p, q };` -- die Nutzlast D.Fn D.passt ist die erklaerte (`V001`-`V004` als Form);
      die Sichtbarkeit ist das Speichermodell, Annahme A10. -/
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `advances a -> b` («B37»): die Marke steht auf Stufe `a`, und `b` ist die naechste. -/
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      Stmt l Γ Λ ((Λ.erase (.marke m a)) ++ [.marke m (a + 1)])
  /-- `retires t from space falsifier s` (S3): die Marke wird verbraucht, die Annahme genannt. -/
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      Stmt l Γ Λ (Λ.erase (.marke m s))
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | retWhy (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | leave (h : l = true) : Stmt l Γ Λ Λ
  | next (h : l = true) : Stmt l Γ Λ Λ
  /-- `r->f = e;` into the OPEN table number `n` (`Expr.slotRef`). -/
  | assignSlotRef (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t) (ho : D.offen t = true)
      (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  /-- `traverse ... by consuming` (C11): consuming loop over the finite domain
      of `t` with current-state selection. `member` tests membership of a
      represented index in the CURRENT world, `edge` the declared edge relation
      between two represented indices (`edge j k` means "`j` precedes `k`",
      the candidate bound second), `inv` the loop invariant, `mass` the
      strictly falling measure over `0 .. bound`, and `body` the pass over the
      selected index; the body's declared `touches ... consumes` performs the
      actual removal. Each round selects the least remaining member that is
      minimal w.r.t. `edge` (first in ascending index order) in the current
      world, checks `inv`, reads `mass` and runs `body`; the next round
      re-selects in the post-body world. The loop ends when no member is
      left; a cyclic edge with members left, a failed `inv` and a post-body
      measure that does not strictly fall inside `0 .. bound` are the
      writer's logic (`.logik .schleife`), like a failed `decreases`. -/
  | consumeTraverse (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block true (.index (D.count t) :: Γ) Λ Λ) : Stmt l Γ Λ Λ
  /-- `return [v]` through locally acquired scopes (C11): exact residual
      `V.ende` plus `R.scopes` to close innermost first. Placeholder keeps
      the immediate value pop; unwinding each scope with its owed invariant
      (`GRest.rueckBereit`) is OPEN. -/
  | retScoped (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ) : Stmt l Γ Λ Λ
  | retWhyScoped (r : Fin V.gruende) (R : RueckRessourcen D V Λ) : Stmt l Γ Λ Λ
  /-- `g(…) else (e) { … };` -- a fallible foreign call as a statement («C08»): the
      normal answer is discarded and the statement continues in `Γ`, a reason runs
      `err` with the reason bound. Checked sugar over `Block.bindAxiomOptElse`
      with an empty success tail and the generalized binder; the option index `e`
      with `he` lets the machine discard either a void or a value answer. The
      exit holdings are the canonical signature's (`nachSig`), with the caller's
      duty as `RufPasst` over `D.asignatur a` and the held guards beside it. -/
  | axiomCallElse (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
      (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
      (err : Endblock l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ)) :
      Stmt l Γ Λ (nachSig D (D.asignatur a) Λ)
  /-- `p(a, b); else (e) { … };` -- fallible call through a function pointer («C07»):
      nonempty channel (`hr`); normal return drops the value, a reason runs `err` bound.
      Sugar over `Block.bindCallIndElse` with an empty success tail; no source form yet. -/
  | callIndElse (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
      (err : Endblock l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ)) :
      Stmt l Γ Λ (nachSig D (D.sigNr n) Λ)
  /-- `r->f = e;` through an OWNED capability (`own@m`): the same guarded
      store to the underlying table as `assignThru`, with the same guards --
      plus the held owner mark itself. The pointer carries the resolved owner
      identity `o` (`D.ownerNr o = some m`), the table declares `m` as its
      owner (`he`) and the guard at the held stage (`hg`); `hw` and `hL` are
      the table's write right and remaining guards. Machine G executes it
      exactly like `assignThru` on `t`. -/
  | assignThruOwn {read : Bool} (p : Expr D Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table n⟩))
      (t : D.Tab) (ht : D.capTab space n = some t) (f : D.Feld t)
      (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (m : D.Marke) (s : Nat) (ho : D.ownerNr o = some m) (he : m ∈ D.eigner t)
      (hg : Sum.inr (m, s) ∈ D.braucht t)
      (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ

inductive Block : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | nil : Block l Γ Λ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Block l Γ Λ' Λ'') : Block l Γ Λ Λ''
  | bind (e : Expr D Γ Λ τ) (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | bindCall (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindCallInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Block l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ') : Block l Γ Λ Λ'
  | bindCallElse (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindAxiom (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = g(…) else (e) { … }` over a FALLIBLE foreign body (C-free lane, 2026-09-30):
      the answer is a value (`rest`) or a reason of the channel (`err`, an end block that does
      not fall off) -- `bindCallElse`'s shape over `D.agruende` instead of a signature. -/
  | bindAxiomElse (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = R;` -- eine Registerlesung, lesbar nach Klasse; `requires … else` (B26) ist die
      Form `regLiesElse`. -/
  | regRead (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (rest : Block l (D.rtyp r :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `let x = R else (e) { … }` -- die Lesung ist fehlbar; die Geraetezusage (`requires`) ist
      die Bedingung, der `else`-Zweig faellt nicht ab. -/
  | regReadElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock l Γ Λ)
      (rest : Block l (D.rtyp r :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A awaits { p, q };` -- the same payload as at the `publishes`; only at an atomic static
      (an await at a plain static would be an unordered read, Simon 2026-10-21). -/
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hL : gdarf D g Λ)
      (ha : D.atomar g = true) (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A exchange update(v) { … } …` -- Lesen, Rechnen, Schreiben: als EINE Anweisung
      (die Atomizitaet ist A10); `bounded`/`on_exceeded` sind die von `retry`. -/
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.int lo' hi' :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `where`-Bedingung eines `format`-Felds, `requires` einer Lesung, jede benannte Absage
      (Regel 3): die Bedingung gilt, oder der `else`-Zweig -- der nicht abfaellt. -/
  | check (c : Expr D Γ Λ .bool) (sonst : Endblock l Γ Λ) (rest : Block l Γ Λ Λ') :
      Block l Γ Λ Λ'
  /-- Gleitkomma («F»): `let y = a op b;` mit erklaertem Bereich `lo .. hi` -- die Maschine
      rechnet (IEEE), das Ergebnis wird gegen den Bereich gehalten, und ein Ergebnis
      ausserhalb (oder NaN, Unendlich) ist `Logik.bereich` (since 2026-09-15, verdict F1:
      the kernel IEEE model decides it from the program's values; was `Hardware.ieee`). -/
  | float (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Ein Gleitkommaliteral `1.5 rounded` in seinem Bereich. -/
  | floatLit (q : Int × Int) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Eine Zahl als Gleitkommazahl, in ihrem Bereich. -/
  | floatOf (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `narrow x to finite` -- eine Gleitkommazahl in einen engeren Bereich, sonst der
      `else`-Zweig. -/
  | floatNarrow (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `narrowRequired x to lo .. hi` (C11): the same typed narrowing as
      `narrow`, with a logical failure instead of a source `else`. Out of
      range is `Logik.kapazitaet`, excluded by the caller's capacity duty;
      the supplied `else` semantics of `narrow` is unchanged. -/
  | narrowRequired (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
      (rest : Block l (.int lo' hi' :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x? = g(…);` over an OPTIONAL foreign result («C08»): the generalized
      nonfallible binder -- `Block.bindAxiom` with the result option `e` made
      explicit (`he`), so void (`none`) adds no local and a value binds. The
      exit holdings are the canonical signature's (`nachSig`), with the caller's
      duty as `RufPasst` over `D.asignatur a` and the held guards beside it. -/
  | bindAxiomOpt (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
      (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ') : Block l Γ Λ Λ'
  /-- `let x? = g(…) else (e) { … };` over an OPTIONAL foreign result («C08»): the
      generalized fallible binder -- `Block.bindAxiomElse` with the result option
      `e` made explicit (`he`) and the reason channel as `reasonTy`. Success
      continues over `ErgCtx`, the reason over the channel, both under the same
      `nachSig`; the caller's duty is `RufPasst` over `D.asignatur a` with the
      held guards beside it. -/
  | bindAxiomOptElse (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
      (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
      (err : Endblock l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Block l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ') : Block l Γ Λ Λ'
  /-- `let x = p(a, b) else (e) { … };` -- fallible call through a function pointer («C07»):
      `bindCallElse` over the pointer type `(D.sigNr n)`; nonempty channel (`hr`), value by
      `SigPasst.erg` into `rest`, reason by `SigPasst.gruende` into `err`. No source form yet. -/
  | bindCallIndElse (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
      (err : Endblock l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
      (rest : Block l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ') : Block l Γ Λ Λ'

inductive Endblock : Bool → Ctx → List (Res D) → Type where
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | retWhy (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | leave (h : l = true) : Endblock l Γ Λ
  | next (h : l = true) : Endblock l Γ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Endblock l Γ Λ') : Endblock l Γ Λ
  | bind (e : Expr D Γ Λ τ) (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = f(…);` at the top level of a body (or in an `else` that must not fall off):
      `Block.bindCall` with an end-block rest (Track P, 2026-10-18). Same premises; the rest is
      where the body ends. -/
  | bindCall (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
      (rest : Endblock l (τ :: Γ) (nach D f Λ)) : Endblock l Γ Λ
  /-- `let x = f(…) else (e) { … }` at the top level of a body: `Block.bindCallElse` with an
      end-block rest (Track P, 2026-10-18); the `else` branch is an end block over the reason. -/
  | bindCallElse (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Endblock l (τ :: Γ) (nach D f Λ)) : Endblock l Γ Λ
  /-- `let x = g(…);` of a FOREIGN body at the top level of a body (or in an `else` that
      must not fall off): `Block.bindAxiom` with an end-block rest (C-free lane,
      2026-09-30). The same premises; the rest is where the body ends. -/
  | bindAxiom (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `Block.bindAxiomElse` with an end-block rest: a fallible foreign call at the top level
      of a body (C-free lane, 2026-09-30). -/
  | bindAxiomElse (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = R;` at the top level of a body (or in an `else` that must not fall off):
      `Block.regRead` with an end-block rest (Track P, 2026-10-21). -/
  | regRead (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (rest : Endblock l (D.rtyp r :: Γ) Λ) :
      Endblock l Γ Λ
  /-- `let x = R else (e) { … }` at the top level of a body: `Block.regReadElse` with an
      end-block rest (Track P, 2026-10-21). -/
  | regReadElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock l Γ Λ)
      (rest : Endblock l (D.rtyp r :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = A awaits { p, q };` at the top level of a body: `Block.awaits` with an end-block
      rest (Track P, 2026-10-21). -/
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hL : gdarf D g Λ)
      (ha : D.atomar g = true) (rest : Endblock l (D.gtyp g :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = p(…);` through a function pointer at the top level of a body: `Block.bindCallInd`
      with an end-block rest (Track P, 2026-10-21). -/
  | bindCallInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Endblock l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) : Endblock l Γ Λ
  /-- `narrow x to lo .. hi else { … }` at the top level of a body (or in an `else` that must not fall off):
      `Block.narrow` with an end-block rest (stage 0, 2026-10-26). -/
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock l Γ Λ)
      (rest : Endblock l (.int lo' hi' :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = A exchange update(v) { … } …` at the top level of a body: `Block.exchange` with an end-block
      rest (stage 0, 2026-10-26). -/
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (rest : Endblock l (D.gtyp g :: Γ) Λ) : Endblock l Γ Λ
  /-- `if c { … } else { … }` as the last statement of a body, both branches ending (stage 0, 2026-10-26). -/
  | ite (c : Expr D Γ Λ .bool) (t e : Endblock l Γ Λ) : Endblock l Γ Λ
  /-- `narrowRequired x to lo .. hi` at the top level of a body (C11):
      `Block.narrowRequired` with an end-block rest; out of range is
      `Logik.kapazitaet`, never a clipped value. -/
  | narrowRequired (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
      (rest : Endblock l (.int lo' hi' :: Γ) Λ) : Endblock l Γ Λ
  /-- `return [v]` through scopes at the top level of a body (C11):
      `Stmt.retScoped` in end-block position; same placeholder status. -/
  | retScoped (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ) : Endblock l Γ Λ
  | retWhyScoped (r : Fin V.gruende) (R : RueckRessourcen D V Λ) : Endblock l Γ Λ
  /-- `let x? = g(…);` at the top level of a body («C08»): `Block.bindAxiomOpt`
      with an end-block rest. The optional result binds over `ErgCtx`, the exit
      holdings are the canonical signature's (`nachSig`). -/
  | bindAxiomOpt (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
      (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ)) : Endblock l Γ Λ
  /-- `let x? = g(…) else (e) { … };` at the top level of a body («C08»):
      `Block.bindAxiomOptElse` with an end-block rest. Success continues over
      `ErgCtx`, the reason over the `reasonTy` channel, both under the same
      `nachSig`. -/
  | bindAxiomOptElse (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
      (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
      (err : Endblock l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Endblock l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ)) : Endblock l Γ Λ
  /-- `let x = p(a, b) else (e) { … };` at the top level of a body: `Block.bindCallIndElse`
      with an end-block rest («C07»). -/
  | bindCallIndElse (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
      (err : Endblock l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
      (rest : Endblock l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) : Endblock l Γ Λ

inductive Arms : Bool → Ctx → List (Res D) → List (Res D) → List (Option Ty) → Type where
  | nil : Arms l Γ Λ Λ []
  | cons (b : Block l (ArmCtx Γ c) Λ Λ') (rest : Arms l Γ Λ Λ' cs) : Arms l Γ Λ Λ' (c :: cs)

inductive GrundArms : Bool → Ctx → List (Res D) → List (Res D) → Nat → Type where
  | nil : GrundArms l Γ Λ Λ 0
  | cons (b : Block l Γ Λ Λ') (rest : GrundArms l Γ Λ Λ' n) : GrundArms l Γ Λ Λ' (n + 1)

end

end Gabbro.Grammatik
