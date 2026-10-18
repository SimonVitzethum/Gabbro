/-
  File:      Grammatik/ArenaErkenner.lean
  Subject:   THE RECOGNIZER (PLAN-DYNAMISCH.md section 8a.1): which BODIES keep the invariant of an arena that carries a
             list, a tree, both or neither, decided from their syntax and the static facts of the checker (`N586`: single
             release, no use after release, a pushed or hung slot is a bound, owned name).

  A body is a `Block`. The recognizer `Erk K a b a'` says: started in an abstract state `a` (what is known about each bound
  index variable), the block `b` is built ONLY from the proved moves, and ends in the abstract state `a'`. The moves are
  the executed forms of `ArenaAllocForm.lean`, `ArenaLinkForm.lean`, `ArenaBaumForm.lean`, `ArenaBaumFormG.lean` and
  `ArenaWachs.lean`; every constructor names the form it matches, so a body that does anything else (a store into a link
  field that is no move, a push of a slot that is not owned, a second release, a hang below a slot that is not in the
  tree) has no derivation.

  THE ABSTRACT STATE (the Lean model of the checker's name table). A status per bound variable, by de Bruijn position:
    `frei`  -- an OWNED slot: live and in NEITHER structure (a fresh allocation, a popped, unlinked or cut slot);
    `liste` -- a MEMBER of the list;
    `baum`  -- a MEMBER of the tree;
    `offen` -- nothing known: a parameter, a copy, a released name (`N586`: a dead name is never `frei`).

  GUARDS. Every `else` of a guard must be store-free (`Rein`: only `return` and `return why`), so the guard's failure ends
  the run in the world the guard saw. A `leave` or a `next` is NOT recognized: a recognized body never produces one, which
  is what makes the loop rules sound without an exit state.

  LOOPS (`forever`, `traverse`, `retry`). A loop is recognized when its body, started in a LOOP STATE `k0` (what is known
  at the head of every pass), ends in a state at least as strong as `k0`: the abstract state is an invariant of the loop.
  `traverse` and `retry` fall off in `k0`; `forever` never falls off (only `leave` could end it, which no recognized body
  has), so what follows it is recognized from the entry state.

  THE CLAIM. `Dekl.Ok` is the invariant of the arena. `StrukturPasst K a σ ρ` says the world and the variables keep what `a` says.
  `erk_erhaelt` (`ArenaErkennerBeweis.lean`): if `Erk K a b a'`, `K.Ok σ` and `StrukturPasst K a σ ρ`, then EVERY outcome of running
  `b` has `K.Ok`, a block that falls off also has `StrukturPasst K a'`, and `leave`/`next` never happen.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaDekl
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaLinkForm

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. The abstract state -/

/-- What the recognizer knows of one bound index variable. -/
inductive Status where
  | frei
  | liste
  | baum
  | offen
  deriving DecidableEq

/-- An abstract state: a status per de Bruijn position of the context. -/
abbrev Abs := Nat → Status

namespace Abs

/-- Nothing is known of any variable (the state at the entry of a function). -/
def leer : Abs := fun _ => .offen

/-- A new binder at the front, with the status `s`. -/
def ext (a : Abs) (s : Status) : Abs
  | 0 => s
  | n + 1 => a n

/-- The state without the newest binder. -/
def tail (a : Abs) : Abs := fun n => a (n + 1)

/-- The position `m` takes the status `s`. -/
def set (a : Abs) (m : Nat) (s : Status) : Abs := fun n => if n = m then s else a n

/-- Every variable of status `s` forgets it (a pop may have removed a member; a cut may have removed one). -/
def forget (a : Abs) (s : Status) : Abs := fun n => if a n = s then .offen else a n

/-- `b` knows no more than `a`: every position keeps its status or becomes unknown. -/
def Schwacher (b a : Abs) : Prop := ∀ n, b n = a n ∨ b n = .offen

end Abs

/-- The de Bruijn position of a variable. -/
def Var.pos {Γ : Ctx} {τ : Ty} : Var Γ τ → Nat
  | .here => 0
  | .there x => x.pos + 1

/-! ## 2. What the abstract state means -/

section Bedeutung
variable {A : FreiForm D} (K : Dekl A)

/-- **The meaning of an abstract state in a world and an environment.** A `frei` variable names a live slot that is in
    neither structure; a `liste` variable names a list member; a `baum` variable a tree member; two `frei` variables name
    two slots. -/
def StrukturPasst (a : Abs) {Γ : Ctx} (σ : World D) (ρ : Env D Γ) : Prop :=
  (∀ x : Var Γ (Ty.index (D.count A.tab)), a x.pos = .frei →
      A.Lebt σ (ρ.get x).n ∧ ¬ K.InL σ (ρ.get x).n ∧ ¬ K.InB σ (ρ.get x).n) ∧
  (∀ x : Var Γ (Ty.index (D.count A.tab)), a x.pos = .liste → K.InL σ (ρ.get x).n) ∧
  (∀ x : Var Γ (Ty.index (D.count A.tab)), a x.pos = .baum → K.InB σ (ρ.get x).n) ∧
  (∀ x y : Var Γ (Ty.index (D.count A.tab)), a x.pos = .frei → a y.pos = .frei → x.pos ≠ y.pos →
      (ρ.get x).n ≠ (ρ.get y).n)

/-- **What the recognizer promises of an outcome:** wherever the run ends the arena is well formed; a block that falls
    off also meets the abstract state it ends in; a block never ends in a `leave` or a `next`. -/
def StrukturPost {V : Vertrag D} {l : Bool} {Γ : Ctx} (a : Abs) : Ausgang V l Γ → Prop
  | .ok σ ρ => K.Ok σ ∧ StrukturPasst K a σ ρ
  | .zurueck σ _ => K.Ok σ
  | .why σ _ => K.Ok σ
  | .leave _ _ _ => False
  | .next _ _ _ => False
  | .logik _ => True
  | .hardware _ => True

end Bedeutung

/-! ## 3. The `else` branches: they end the function and move no structure -/

/-- **An `else` branch that stores nothing:** `return` or `return why`. The recognizer demands it of every `else` of a
    guard, because such a branch ends the run in the world the guard saw, so the invariant that held there holds at the
    exit. -/
inductive Rein {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Prop where
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      Rein (l := l) (.ret e hΛ)
  | retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) :
      Rein (l := l) (Γ := Γ) (Λ := Λ) (.retWhy r hΛ)

/-! ## 4. The recognizer -/

section Erkenner
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D}

/-- **`Erk K a b a'`: the block `b` is built only from the proved moves, from the abstract state `a` to `a'`.** One
    constructor per move; each names the executed form it matches. -/
inductive Erk : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Abs → Block D V l Γ Λ Λ' → Abs → Prop where
  /-- The empty block. -/
  | nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : Abs) : Erk (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ) a Block.nil a
  /-- LIST. `lnk[x] = head; head = x;` for an OWNED slot `x`; afterwards `x` is a member and no longer owned. -/
  | push {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (d : ListDekl A) (hd : K.liste = some d)
      (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (hwG : V.gschreibt d.G.g = true) (hLG : gdarf D d.G.g Λ) (rest : Block D V l Γ Λ Λ')
      (hx : a x.pos = .frei) (h : Erk (a.set x.pos .liste) rest a') :
      Erk a (Block.linkPush d.L d.G x hwT hLT hwG hLG rest) a'
  /-- LIST. `let i = head else voll; head = lnk[i];` -- the binder is a new OWNED slot; list members are forgotten. -/
  | pop {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
      (hwG : V.gschreibt d.G.g = true) (hLG : gdarf D d.G.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk ((a.forget .liste).ext .frei) rest a'') : Erk a (Block.linkPop d.L d.G hwG hLG hLT voll rest) a''.tail
  /-- LIST. `let i = lnk[p] else voll; lnk[p] = lnk[i];` for a list MEMBER `p` -- the binder is a new owned slot. -/
  | unlink {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
      (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
      (hp : a p.pos = .liste) (hv : Rein voll) (h : Erk ((a.forget .liste).ext .frei) rest a'') :
      Erk a (Block.linkUnlink d.L p hwT hLT voll rest) a''.tail
  /-- LIST. `let i = head else voll;` -- the binder is a member. -/
  | kopf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
      (hLG : gdarf D d.G.g Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .liste) rest a'') : Erk a (Block.linkKopfBind d.G hLG voll rest) a''.tail
  /-- LIST. `let q = lnk[p] else voll;` for a member `p` -- the binder is a member. -/
  | nach {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
      (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .liste) (hv : Rein voll)
      (h : Erk (a.ext .liste) rest a'') : Erk a (Block.linkNachBind d.L p hLT voll rest) a''.tail
  /-- ALLOCATOR. `let i = alloc A (v) else voll;` from the counter -- the binder is a new OWNED slot. -/
  | frisch {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwG : V.gschreibt A.zaehl = true)
      (hLG : gdarf D A.zaehl Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .frei) rest a'') :
      Erk a (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) a''.tail
  /-- ALLOCATOR. `let i = alloc A (v) else voll;` from the free list -- the binder is a new OWNED slot. -/
  | nimm {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .frei) rest a'') : Erk a (Block.freiNimm A v hwT hLT hwK hLK voll rest) a''.tail
  /-- ALLOCATOR. `free A[x];` of an OWNED slot; afterwards `x` is unknown, so it is neither released nor linked again. -/
  | frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (x : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei)
      (h : Erk (a.set x.pos .offen) rest a') : Erk a (Block.freiVar A x hwT hLT hwK hLK rest) a'
  /-- ALLOCATOR. `grow A by n else voll;` -- the committed word moves, nothing the structures read; the binder is unknown.
      `0 ≤ n`: a commit never shrinks the committed word (the surface demands `n >= 1`, `R-grow-const`; step 3 of Phase A, 2026-10-18). -/
  | wachs {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (n : Int) (hn : 0 ≤ n)
      (hwK : V.gschreibt A.komm = true)
      (hLK : gdarf D A.komm Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .offen) rest a'') : Erk a (Block.dynGrowB A.toDynForm n hwK hLK voll rest) a''.tail
  /-- A guard (`requires`-style check): its `else` ends the run without a store. -/
  | pruefe {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (c : Expr D Γ Λ .bool) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l Γ Λ Λ') (hv : Rein voll) (h : Erk a rest a') : Erk a (Block.check c voll rest) a'
  /-- A store into the PAYLOAD field of any slot: no link, no head and no allocator word moves. -/
  | nutzlast {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (i : Expr D Γ Λ (.index (D.count A.tab)))
      (e : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (rest : Block D V l Γ Λ Λ') (h : Erk a rest a') :
      Erk a (Block.cons (Stmt.assignSlot A.tab A.feld i e hwT hLT) rest) a'
  /-- A two-way branch of recognized blocks; the state after is what BOTH branches guarantee. -/
  | ite {l : Bool} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)} {a a1 a2 a3 a' : Abs} (c : Expr D Γ Λ .bool)
      (t e : Block D V l Γ Λ Λ1) (rest : Block D V l Γ Λ1 Λ') (ht : Erk a t a1) (he : Erk a e a2)
      (h1 : Abs.Schwacher a3 a1) (h2 : Abs.Schwacher a3 a2) (h : Erk a3 rest a') :
      Erk a (Block.cons (Stmt.ite c t e) rest) a'
  /-- TREE. `check root == nil else voll; Lf[x] = nil; Rf[x] = nil; root = x;` for an OWNED slot `x`: the first node. -/
  | wurzelEin {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (hwG : V.gschreibt b.Wz.g = true) (hLG : gdarf D b.Wz.g Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei) (hv : Rein voll) (h : Erk (a.set x.pos .baum) rest a') :
      Erk a (Block.wurzelEin b.Lf b.Rf b.Wz x hwT hLT hwG hLG voll rest) a'
  /-- TREE. `let i = root else voll;` -- the binder is a tree member. -/
  | wurzelKopf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (hLG : gdarf D b.Wz.g Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .baum) rest a'') : Erk a (Block.linkKopfBind b.Wz hLG voll rest) a''.tail
  /-- TREE. `let q = C[p] else voll;` for a tree member `p` and one of the two child places -- the binder is a member. -/
  | kind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (C : LinkFeld A) (hC : C = b.Lf ∨ C = b.Rf) (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ)
      (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
      (hp : a p.pos = .baum) (hv : Rein voll) (h : Erk (a.ext .baum) rest a'') :
      Erk a (Block.linkNachBind C p hLT voll rest) a''.tail
  /-- TREE. `check Cp[p] == nil else voll; Cp[i] = nil; Co[i] = nil; Cp[p] = i;` -- hang the OWNED slot `i` at the empty
      child place `Cp` of the tree member `p`; afterwards `i` is a tree member. -/
  | haengen {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (Cp Co : LinkFeld A) (hs : (Cp = b.Lf ∧ Co = b.Rf) ∨ (Cp = b.Rf ∧ Co = b.Lf))
      (p i : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (voll : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (hp : a p.pos = .baum) (hi : a i.pos = .frei)
      (hv : Rein voll) (h : Erk (a.set i.pos .baum) rest a') :
      Erk a (Block.haengen Cp Co p i hwT hLT voll rest) a'
  /-- TREE. `let i = C[p] else voll; check leaf(i) else voll2; C[p] = nil;` -- cut the LEAF child off the tree member `p`;
      the binder is a new OWNED slot; tree members are forgotten. -/
  | abschneiden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (C : LinkFeld A) (hC : C = b.Lf ∨ C = b.Rf) (p : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .baum) (hv : Rein voll)
      (hv2 : Rein voll2) (h : Erk ((a.forget .baum).ext .frei) rest a'') :
      Erk a (Block.abschneiden b.Lf b.Rf C p hwT hLT voll voll2 rest) a''.tail
  /-- TREE. `let i = root else voll; check leaf(i) else voll2; root = nil;` -- the root, a leaf, goes; the binder is a new
      OWNED slot; tree members are forgotten. -/
  | wurzelAus {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
      (hwG : V.gschreibt b.Wz.g = true) (hLG : gdarf D b.Wz.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll) (hv2 : Rein voll2)
      (h : Erk ((a.forget .baum).ext .frei) rest a'') :
      Erk a (Block.wurzelAus b.Lf b.Rf b.Wz hwG hLG hLT voll voll2 rest) a''.tail
  /-- LOOP. `forever` from the loop state `k0`: the body keeps `k0`. Nothing falls off a `forever`, so what follows is
      recognized from the entry state. -/
  | forever {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a1 a' k0 : Abs} (an : D.Annahme) (inv : Expr D Γ Λ .bool)
      (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ') (hin : Abs.Schwacher k0 a) (hb : Erk k0 body a1)
      (hs : Abs.Schwacher k0 a1) (h : Erk a rest a') :
      Erk a (Block.cons (Stmt.forever an inv body) rest) a'
  /-- LOOP. `traverse` from the loop state `k0`: the body (with the index binder, unknown) keeps `k0`; the loop falls off
      in `k0`. -/
  | traverse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a1 a' k0 : Abs} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (Ty.index (D.count t) :: Γ) Λ Λ) (rest : Block D V l Γ Λ Λ')
      (hin : Abs.Schwacher k0 a) (hb : Erk (k0.ext .offen) body a1) (hs : Abs.Schwacher k0 a1.tail)
      (h : Erk k0 rest a') : Erk a (Block.cons (Stmt.traverse t inv body) rest) a'
  /-- LOOP. `retry` from the loop state `k0`: the body keeps `k0`; the loop falls off in `k0`, or leaves through the
      overflow block (recognized from `k0`); the state after is what both guarantee. -/
  | retry {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a1 au a3 a' k0 : Abs} (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (rest : Block D V l Γ Λ Λ')
      (hin : Abs.Schwacher k0 a) (hb : Erk k0 body a1) (hs : Abs.Schwacher k0 a1) (hu : Erk k0 ueber au)
      (h3 : Abs.Schwacher a3 k0) (h4 : Abs.Schwacher a3 au) (h : Erk a3 rest a') :
      Erk a (Block.cons (Stmt.retry n bis body ueber) rest) a'

end Erkenner

end Gabbro.Grammatik
