module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Bausteine.Arena.Arena

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Recording a read touches the trace alone -- the globals are the globals. -/
@[simp] theorem World.globs_lese (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) : (σ.lese Λ o).globs = σ.globs := by rfl

/-! ## 1. The shape of an arena in a declaration -/

/-- **What a declaration must carry for `arena A capacity lo .. hi of T`.** The hard bound
    `hi` is the table's `count` -- the array `buf[hi]` the emitter writes -- and the
    reservation `lo` is not here: it is the checker's static count (`N212`), and its
    consequence is `arenaAlloc_unter_schranke`. -/
structure ArenaForm (D : Deklaration) where
  /-- The slot carrier: `count tab` is the hard bound. -/
  tab : D.Tab
  /-- The element field. -/
  feld : D.Feld tab
  /-- The `used` counter. -/
  zaehl : D.Glob
  /-- The counter ranges over `0 .. hi` -- `hi` inclusive, because a FULL arena is a
      state the counter must be able to name. -/
  hz : D.gtyp zaehl = Ty.int 0 (D.count tab)
  /-- The arena holds at least one slot; an arena of no slots has no `alloc` that can
      ever succeed, and every statement below would be vacuous. -/
  hpos : 0 < D.count tab

namespace ArenaForm

/-- **The used count, read out of a world.** Every statement below speaks in this. -/
def stand (A : ArenaForm D) (σ : World D) : Int := (Wert.umTyp A.hz (σ.globs A.zaehl)).n

theorem stand_le (A : ArenaForm D) (σ : World D) : A.stand σ ≤ D.count A.tab :=
  (Wert.umTyp A.hz (σ.globs A.zaehl)).le_hi

theorem stand_nonneg (A : ArenaForm D) (σ : World D) : 0 ≤ A.stand σ :=
  (Wert.umTyp A.hz (σ.globs A.zaehl)).lo_le

/-- Recording a read does not move the counter -- `lese` touches the trace alone. -/
@[simp] theorem stand_lese (A : ArenaForm D) (σ : World D) (Λ : List (Res D))
    (o : List (D.Tab ⊕ D.Glob)) : A.stand (σ.lese Λ o) = A.stand σ := by rfl

/-- A slot store does not move the counter. -/
@[simp] theorem stand_schreibSlot (A : ArenaForm D) (σ : World D) (Λ : List (Res D))
    (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    A.stand (σ.schreibSlot t Λ k f v) = A.stand σ := by rfl

/-- A store into the counter puts exactly the written value there. -/
@[simp] theorem stand_schreibGlob (A : ArenaForm D) (σ : World D) (Λ : List (Res D))
    (v : Wert D (D.gtyp A.zaehl)) :
    A.stand (σ.schreibGlob A.zaehl Λ v) = (Wert.umTyp A.hz v).n := by
  simp only [stand, World.schreibGlob, World.merke, World.storeGlob, dif_pos]

end ArenaForm

/-! ## 2. `reset A;` -/

namespace Stmt
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The counter expression `0`, at the counter's declared type. -/
def arenaNull (A : ArenaForm D) : Expr D Γ Λ (D.gtyp A.zaehl) :=
  Expr.umTyp A.hz.symm
    (Expr.widen (lo := 0) (hi := 0) (lo' := 0) (hi' := D.count A.tab)
      (Int.le_refl 0) (by have := A.hpos; omega) (Expr.lit 0))

/-- **`reset A;`** -- a fresh generation is the counter back at zero. The generation
    itself is checker state (`N211` refuses a stale index); what the RUN does is this
    one store, and that is what the emitter writes (`A_arena_speicher.used = 0;`). -/
def arenaReset (A : ArenaForm D) (hw : V.gschreibt A.zaehl = true)
    (hL : gdarf D A.zaehl Λ) : Stmt D V l Γ Λ Λ :=
  .assignGlob A.zaehl (arenaNull A) hw hL

end Stmt

/-! ## 3. `let i = alloc A (v) else B;` -/

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The bumped counter `i + 1`, at the counter's declared type, under the binder the
    narrow introduced. -/
def arenaBump (A : ArenaForm D) :
    Expr D (Ty.index (D.count A.tab) :: Γ) Λ (D.gtyp A.zaehl) :=
  Expr.umTyp A.hz.symm
    (Expr.widen (lo := 0 + 1) (hi := (D.count A.tab - 1) + 1)
      (lo' := 0) (hi' := D.count A.tab) (by omega) (by omega)
      (Expr.add (Expr.var .here) (Expr.lit 1)))

/-- The body of an allocation: the store, then the bump. Named, because both theorems
    below speak about it. -/
def arenaRumpf (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ' :=
  .cons (.assignSlot A.tab A.feld (Expr.var .here) (Expr.weaken v) hwT hLT)
    (.cons (.assignGlob A.zaehl (arenaBump A) hwG hLG) rest)

/-- **`let i = alloc A (v) else B; …`** -- three existing forms in a row:

    1. `Block.narrow` on the counter into `0 ..< hi`: it fits, and `i` is the index it
       names; or it does not, and `B` runs (the arena is full). *This IS the emitted
       guard, and `narrow`'s `else` does not fall through -- the same promise the
       surface `else` carries.*
    2. `Stmt.assignSlot` at `i` -- the store.
    3. `Stmt.assignGlob` of `i + 1` -- the bump.

    The order is the emitter's: `i = used; buf[i] = v; used = i + 1;`. -/
def arenaAlloc (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp A.hz (Expr.glob A.zaehl hLG)) 0 (D.count A.tab - 1) voll
    (arenaRumpf A v hwT hLT hwG hLG rest)

end Block

end Gabbro.Grammatik
