/-
  File:      Grammatik/ArenaErkenner.lean
  Subject:   THE RECOGNIZER (PLAN-DYNAMISCH.md section 8a.1, step (3)): which BODIES keep the structure invariant, decided
             from their syntax and the static facts of the checker (`N586`: single release, no use after release, a pushed
             slot is a bound, owned name).

  A body is a `Block`. The recognizer `Erk a b a'` says: started in an abstract state `a` (what is known about each
  bound index variable), the block `b` is built ONLY from the proved moves, and ends in the abstract state `a'`. The
  moves are exactly the executed forms of `ArenaAllocForm.lean`, `ArenaLinkForm.lean` and `ArenaWachs.lean`; every
  constructor of `Erk` names the form it matches, so a body that does anything else (a store into a link field that is
  no move, a push of a slot that is not owned, a second release) has no derivation.

  THE ABSTRACT STATE (the Lean model of the checker's name table). A status per bound variable, by de Bruijn position:
    `frei`  -- an OWNED slot: live and not linked into the structure (a fresh allocation, a popped or unlinked slot);
    `glied` -- a MEMBER of the list (read as the head or as a successor of a member);
    `offen` -- nothing known: a parameter, a copy, a released name (`N586`: a dead name is never `frei`, so it can be
               neither linked nor released again).

  THE CLAIM. `Inv` is the structure invariant (`FreiOk` and `ListOk`). `Passt a σ ρ` says the world and the variables
  keep what `a` says. `erk_erhaelt` (`ArenaErkennerBeweis.lean`): if `Erk a b a'`, `Inv σ` and `Passt a σ ρ`, then EVERY
  outcome of running `b` (it falls off, returns, fails, leaves) has `Inv`, and a block that falls off also has `Passt a'`.
  The proof applies the executed-form theorems (`liste_*_zug`, `frischAlloc_ausfuehren`, `freiVar_lebt`, `grow_liste`, ...):
  the recognizer is exactly the side conditions of those theorems, discharged by the abstract state.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaAllocForm
import Grammatik.Bausteine.Arena.Struktur.ArenaLinkForm
import Grammatik.Bausteine.Arena.Struktur.ArenaWachs

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. The abstract state -/

/-- What the recognizer knows of one bound index variable. -/
inductive Status where
  | frei
  | glied
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

/-- Every member forgets that it is one (a pop or an unlink may have removed it). -/
def entglied (a : Abs) : Abs := fun n => if a n = .glied then .offen else a n

/-- `b` knows no more than `a`: every position keeps its status or becomes unknown. -/
def Schwacher (b a : Abs) : Prop := ∀ n, b n = a n ∨ b n = .offen

end Abs

/-- The de Bruijn position of a variable. -/
def Var.pos {Γ : Ctx} {τ : Ty} : Var Γ τ → Nat
  | .here => 0
  | .there x => x.pos + 1

/-! ## 2. The invariant and what the abstract state means -/

section Bedeutung
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- **The structure invariant of a list arena:** the free list and the list are well formed. -/
def StrukturOk (σ : World D) : Prop := A.FreiOk σ ∧ ListOk A L G σ

/-- **The meaning of an abstract state in a world and an environment.** A `frei` variable names a live slot that is not
    linked; a `glied` variable names a member; two `frei` variables name two slots. -/
def Passt (a : Abs) {Γ : Ctx} (σ : World D) (ρ : Env D Γ) : Prop :=
  (∀ x : Var Γ (Ty.index (D.count A.tab)), a x.pos = .frei →
      A.Lebt σ (ρ.get x).n ∧ ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get x).n) ∧
  (∀ x : Var Γ (Ty.index (D.count A.tab)), a x.pos = .glied →
      Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get x).n) ∧
  (∀ x y : Var Γ (Ty.index (D.count A.tab)), a x.pos = .frei → a y.pos = .frei → x.pos ≠ y.pos →
      (ρ.get x).n ≠ (ρ.get y).n)

/-- **What the recognizer promises of an outcome:** wherever the run ends the structure is well formed; a block that falls
    off also meets the abstract state it ends in. -/
def Post {V : Vertrag D} {l : Bool} {Γ : Ctx} (a : Abs) : Ausgang V l Γ → Prop
  | .ok σ ρ => StrukturOk A L G σ ∧ Passt A L G a σ ρ
  | .zurueck σ _ => StrukturOk A L G σ
  | .why σ _ => StrukturOk A L G σ
  | .leave _ σ _ => StrukturOk A L G σ
  | .next _ σ _ => StrukturOk A L G σ
  | .logik _ => True
  | .hardware _ => True

end Bedeutung

/-! ## 3. The `else` branches: they end the function and move no structure -/

/-- **An `else` branch that stores nothing:** only the four ways to end a function (`return`, `return why`, `leave`,
    `next`). The recognizer demands it of every `else` of a guard, because such a branch ends the run in the world the
    guard saw, so the invariant that held there holds at the exit. -/
inductive Rein {V : Vertrag D} {l : Bool} : {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Prop where
  | ret {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Rein (.ret e hΛ)
  | retWhy {Γ : Ctx} {Λ : List (Res D)} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Rein (.retWhy r hΛ)
  | leave {Γ : Ctx} {Λ : List (Res D)} (h : l = true) : Rein (.leave (Γ := Γ) (Λ := Λ) h)
  | next {Γ : Ctx} {Λ : List (Res D)} (h : l = true) : Rein (.next (Γ := Γ) (Λ := Λ) h)

/-! ## 4. The recognizer -/

section Erkenner
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) {V : Vertrag D} {l : Bool}

/-- **`Erk a b a'`: the block `b` is built only from the proved moves, from the abstract state `a` to `a'`.** One
    constructor per move; each names the executed form it matches. -/
inductive Erk : {Γ : Ctx} → {Λ Λ' : List (Res D)} → Abs → Block D V l Γ Λ Λ' → Abs → Prop where
  /-- The empty block. -/
  | nil {Γ : Ctx} {Λ : List (Res D)} (a : Abs) : Erk (Γ := Γ) (Λ := Λ) (Λ' := Λ) a Block.nil a
  /-- `lnk[x] = head; head = x;` for an OWNED slot `x`; afterwards `x` is a member and no longer owned (`N586`: it is
      not pushed twice and not released while linked). -/
  | push {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (x : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ)
      (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei) (h : Erk (a.set x.pos .glied) rest a') :
      Erk a (Block.linkPush L G x hwT hLT hwG hLG rest) a'
  /-- `let i = head else voll; head = lnk[i];` -- the binder is a new OWNED slot; members are forgotten. -/
  | pop {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs}
      (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.entglied.ext .frei) rest a'') : Erk a (Block.linkPop L G hwG hLG hLT voll rest) a''.tail
  /-- `let i = lnk[p] else voll; lnk[p] = lnk[i];` for a MEMBER `p` -- the binder is a new owned slot. -/
  | unlink {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (p : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .glied) (hv : Rein voll)
      (h : Erk (a.entglied.ext .frei) rest a'') : Erk a (Block.linkUnlink L p hwT hLT voll rest) a''.tail
  /-- `let i = head else voll;` -- the binder is a member. -/
  | kopf {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (hLG : gdarf D G.g Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .glied) rest a'') : Erk a (Block.linkKopfBind G hLG voll rest) a''.tail
  /-- `let q = lnk[p] else voll;` for a member `p` -- the binder is a member. -/
  | nach {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (p : Var Γ (Ty.index (D.count A.tab)))
      (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .glied) (hv : Rein voll)
      (h : Erk (a.ext .glied) rest a'') : Erk a (Block.linkNachBind L p hLT voll rest) a''.tail
  /-- `let i = alloc A (v) else voll;` from the counter -- the binder is a new OWNED slot. -/
  | frisch {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwG : V.gschreibt A.zaehl = true)
      (hLG : gdarf D A.zaehl Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .frei) rest a'') :
      Erk a (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) a''.tail
  /-- `let i = alloc A (v) else voll;` from the free list -- the binder is a new OWNED slot. -/
  | nimm {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .frei) rest a'') : Erk a (Block.freiNimm A v hwT hLT hwK hLK voll rest) a''.tail
  /-- `free A[x];` of an OWNED slot; afterwards `x` is unknown, so it is neither released nor linked again (`N586`). -/
  | frei {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (x : Var Γ (Ty.index (D.count A.tab)))
      (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei)
      (h : Erk (a.set x.pos .offen) rest a') : Erk a (Block.freiVar A x hwT hLT hwK hLK rest) a'
  /-- `grow A by n else voll;` -- the committed word moves, nothing the structure reads; the binder is unknown. -/
  | wachs {Γ : Ctx} {Λ Λ' : List (Res D)} {a a'' : Abs} (n : Int) (hwK : V.gschreibt A.komm = true)
      (hLK : gdarf D A.komm Λ) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
      (h : Erk (a.ext .offen) rest a'') : Erk a (Block.dynGrowB A.toDynForm n hwK hLK voll rest) a''.tail
  /-- A guard (`requires`-style check): its `else` ends the run without a store. -/
  | pruefe {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (c : Expr D Γ Λ .bool) (voll : Endblock D V l Γ Λ)
      (rest : Block D V l Γ Λ Λ') (hv : Rein voll) (h : Erk a rest a') : Erk a (Block.check c voll rest) a'
  /-- A store into the PAYLOAD field of any slot: no link, no head and no allocator word moves. -/
  | nutzlast {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} (i : Expr D Γ Λ (.index (D.count A.tab)))
      (e : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (rest : Block D V l Γ Λ Λ') (h : Erk a rest a') :
      Erk a (Block.cons (Stmt.assignSlot A.tab A.feld i e hwT hLT) rest) a'
  /-- A two-way branch of recognized blocks; the state after is what BOTH branches guarantee. -/
  | ite {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)} {a a1 a2 a3 a' : Abs} (c : Expr D Γ Λ .bool)
      (t e : Block D V l Γ Λ Λ1) (rest : Block D V l Γ Λ1 Λ') (ht : Erk a t a1) (he : Erk a e a2)
      (h1 : Abs.Schwacher a3 a1) (h2 : Abs.Schwacher a3 a2) (h : Erk a3 rest a') :
      Erk a (Block.cons (Stmt.ite c t e) rest) a'

end Erkenner

end Gabbro.Grammatik
