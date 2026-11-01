module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Bausteine.Arena.Arena

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. Two casts, and the lemmas that make them harmless

    The counter's declared type is `D.gtyp zaehl`, and the sugar needs it AS
    `int 0 (count tab)`. That is a transport along an equation of `Ty`, and a transport
    inside a proof is where dependent types usually start to fight. They are confined to
    the two definitions here; every lemma below is proved by `subst`, which works because
    BOTH sides are variables in the lemma's own statement. -/

/-- A value at an equal type. -/
def Wert.umTyp {τ σ : Ty} (h : τ = σ) (v : Wert D τ) : Wert D σ := h ▸ v

/-- An expression at an equal type. -/
def Expr.umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ) (e : Expr D Γ Λ τ) :
    Expr D Γ Λ σ := h ▸ e

@[simp] theorem Wert.umTyp_rfl {τ : Ty} (v : Wert D τ) : Wert.umTyp rfl v = v := by rfl

@[simp] theorem Expr.umTyp_rfl {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Expr.umTyp rfl e = e := by rfl

/-- Down and up again is nothing. -/
@[simp] theorem Wert.umTyp_hin_her {τ σ : Ty} (h : τ = σ) (v : Wert D σ) :
    Wert.umTyp h (Wert.umTyp (D := D) h.symm v) = v := by subst h; rfl

/-- Evaluating a transported expression is transporting its value: the cast does not
    change what is read. -/
@[simp] theorem eval_umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ)
    (e : Expr D Γ Λ τ) (σ₀ w : World D) (ρ : Env D Γ) :
    eval σ₀ (Expr.umTyp h e) w ρ = Wert.umTyp h (eval σ₀ e w ρ) := by
  subst h; rfl

/-- The places a transported expression reads are the places it read. -/
@[simp] theorem orte_umTyp {Γ : Ctx} {Λ : List (Res D)} {τ σ : Ty} (h : τ = σ)
    (e : Expr D Γ Λ τ) : (Expr.umTyp h e).orte = e.orte := by
  subst h; rfl

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

/-! ## 4. What the two forms MEAN -/

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **`reset` leaves the counter at zero.** -/
theorem arenaReset_stand (A : ArenaForm D) (hw : V.gschreibt A.zaehl = true)
    (hL : gdarf D A.zaehl Λ) (σ : World D) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execStmt (V := V) O passes R (Stmt.arenaReset (l := l) A hw hL) σ ρ = .ok σ' ρ ∧
      A.stand σ' = 0 := by
  refine ⟨_, rfl, ?_⟩
  simp only [ArenaForm.stand_schreibGlob, Stmt.arenaNull, eval_umTyp, Wert.umTyp_hin_her]
  rfl

/-- **The bump raises the counter by exactly one.** -/
theorem arenaBump_stand (A : ArenaForm D) (hwG : V.gschreibt A.zaehl = true)
    (hLG : gdarf D A.zaehl Λ) (σ : World D)
    (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execStmt (V := V) O passes R
          (Stmt.assignGlob (l := l) A.zaehl (Block.arenaBump A) hwG hLG) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.stand σ' = k.n + 1 := by
  refine ⟨_, rfl, ?_⟩
  simp only [ArenaForm.stand_schreibGlob, Block.arenaBump, eval_umTyp, Wert.umTyp_hin_her]
  rfl

/-- **Below the hard bound, `alloc` does not take its `else`** -- and this is the
    syntactic half of `Arena.alloc_innerhalb_reserve`: the reservation is exactly the
    static reason the checker may omit the branch, and the branch it omits is one that
    cannot run. The index bound is the OLD counter. -/
theorem arenaAlloc_unter_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < D.count A.tab) :
    execBlock (V := V) O passes R
        (Block.arenaAlloc A v hwT hLT hwG hLG voll rest) σ ρ
      = (execBlock O passes R (Block.arenaRumpf A v hwT hLT hwG hLG rest)
          (σ.lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ, by omega⟩ ρ)).schrumpf := by
  have hc : (0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1 :=
    ⟨A.stand_nonneg σ, by have := h; unfold ArenaForm.stand at this; omega⟩
  simp only [Block.arenaAlloc, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_pos hc]
  rfl

/-- **At the hard bound, `alloc` takes its `else`** -- the full arena is the branch the
    surface `else` names, and `N212` is the rule that demands it be written whenever the
    static count cannot rule this case out. -/
theorem arenaAlloc_an_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ = D.count A.tab) :
    execBlock (V := V) O passes R
        (Block.arenaAlloc A v hwT hLT hwG hLG voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl]) ρ).zuAusgang := by
  have hp := A.hpos
  have hn : ¬ ((0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1) := by
    have := h; unfold ArenaForm.stand at this; omega
  simp only [Block.arenaAlloc, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_neg hn]

end Bedeutung

/-! ## 5. The bridge to `Arena.lean` -- the same arithmetic, on the same numbers

    `Arena.lean` proves the mathematics of the monotone region on `Arena k g`; section 4
    runs the syntax on a `World`. The bridge says the two agree on the one number that
    carries the discipline: the used count decides success, and success bumps it by one. -/

/-- **The syntax succeeds exactly when the model function does.** `arenaAlloc` runs its
    body (rather than its `else`) precisely while `Arena.alloc` returns `some` -- the two
    halves of the arena, decided by the same inequality. -/
theorem arenaAlloc_gdw_modell (A : ArenaForm D) (σ : World D)
    (k : Arena.Kap) (hk : (k.hi : Int) = D.count A.tab)
    (a : Arena.Arena k 0) (ha : (a.used : Int) = A.stand σ) :
    (A.stand σ < D.count A.tab) ↔ Arena.alloc a ≠ none := by
  constructor
  · intro h
    have hlt : a.used < k.hi := by omega
    rw [Arena.alloc_erfolg a hlt]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · intro h
    have hne : ¬ (a.used = k.hi) := fun he => h ((Arena.alloc_scheitert_gdw a).mpr he)
    have hle : a.used ≤ k.hi := a.hused
    omega

/-- **And a successful step bumps the same number by one on both sides.** -/
theorem arenaAlloc_bump_modell (A : ArenaForm D) (σ : World D)
    (k : Arena.Kap) (a : Arena.Arena k 0) (ha : (a.used : Int) = A.stand σ)
    (p : Arena.Arena k 0 × Arena.ArenaIdx 0 (a.used + 1)) (hp : Arena.alloc a = some p) :
    (p.1.used : Int) = A.stand σ + 1 ∧ (p.2.i : Int) = A.stand σ := by
  have h1 := Arena.alloc_used' a p hp
  have h2 := Arena.alloc_idx' a p hp
  omega

/-! ## 6. THE WITNESS -- a concrete declaration with an arena, and the run on it

    Not decorative: the table holds FOUR slots (so `full` and `not full` are both
    reachable), the element type is a byte range (so a stored value is a value and not a
    `Unit`), and BOTH branches of `arenaAlloc` are exercised below -- the one from an
    empty arena and the one from a full one. -/

namespace ArenaZeuge

/-- One table of four slots holding a byte, one global counter over `0 .. 4`. -/
def ZD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp only [Bool.false_eq_true] at h

/-- `arena Log capacity 2 .. 4 of u8` -- the hard bound is the table's `count`. -/
def Log : ArenaForm ZD where
  tab := ()
  feld := ()
  zaehl := ()
  hz := rfl
  hpos := by decide

/-- The witness is not degenerate: four slots, so a full arena and an empty one are two
    different worlds. -/
theorem Log_vier : ZD.count Log.tab = 4 := by rfl

/-- The contract of the witness body: it writes both carriers. -/
def ZV : Vertrag ZD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

/-- No guard is owed on either carrier of this declaration. -/
theorem zeuge_darf : darf ZD () ([] : List (Res ZD)) := by
  intro w hw; cases hw

theorem zeuge_gdarf : gdarf ZD () ([] : List (Res ZD)) := by
  intro w hw; cases hw

/-- A world whose counter stands at `c`, and every slot at zero. -/
def welt (c : Int) (h0 : 0 ≤ c) (h4 : c ≤ 4) : World ZD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨c, h0, h4⟩
  spur := []

theorem welt_stand (c : Int) (h0 : 0 ≤ c) (h4 : c ≤ 4) :
    Log.stand (welt c h0 h4) = c := by rfl

/-- The empty arena: the counter stands at zero, strictly under the bound. -/
theorem zeuge_leer_unter :
    Log.stand (welt 0 (by decide) (by decide)) < ZD.count Log.tab := by decide

/-- The FULL arena: the counter stands at the bound. Both sides of `arenaAlloc` are
    therefore reachable in this witness -- the reason it is one. -/
theorem zeuge_voll_an :
    Log.stand (welt 4 (by decide) (by decide)) = ZD.count Log.tab := by decide

/-- `reset` on the FULL arena brings the counter back to zero -- computed, not assumed. -/
theorem zeuge_reset (O : Orakel ZD) (passes : Nat)
    (R : ∀ f : ZD.Fn, World ZD → Env ZD (ZD.params f) → RufAusgang f) :
    ∃ σ' : World ZD,
      execStmt (V := ZV) (l := false) (Γ := []) (Λ := []) O passes R
          (Stmt.arenaReset Log rfl zeuge_gdarf)
          (welt 4 (by decide) (by decide)) .nil = .ok σ' .nil ∧
      Log.stand σ' = 0 :=
  arenaReset_stand O passes R Log rfl zeuge_gdarf _ .nil

/-- The value stored by an `alloc` of `7` into the EMPTY witness arena. -/
def sieben : Expr ZD [] [] (ZD.typ Log.tab Log.feld) :=
  Expr.widen (by decide) (by decide) (Expr.lit 7)

/-- **The `else` branch is not taken on the empty arena, and the index is `0`.** -/
theorem zeuge_alloc_leer (O : Orakel ZD) (passes : Nat)
    (R : ∀ f : ZD.Fn, World ZD → Env ZD (ZD.params f) → RufAusgang f)
    (voll : Endblock ZD ZV false [] [])
    (rest : Block ZD ZV false [Ty.index (ZD.count Log.tab)] [] []) :
    execBlock (V := ZV) O passes R
        (Block.arenaAlloc Log sieben rfl zeuge_darf rfl zeuge_gdarf voll rest)
        (welt 0 (by decide) (by decide)) .nil
      = (execBlock O passes R
          (Block.arenaRumpf Log sieben rfl zeuge_darf rfl zeuge_gdarf rest)
          ((welt 0 (by decide) (by decide)).lese [] [Sum.inr ()])
          (.cons ⟨0, by decide, by decide⟩ .nil)).schrumpf :=
  arenaAlloc_unter_schranke O passes R Log sieben rfl zeuge_darf rfl zeuge_gdarf voll rest
    _ .nil (by decide)

/-- **And it IS taken on the full one** -- the witness exercises both halves. -/
theorem zeuge_alloc_voll (O : Orakel ZD) (passes : Nat)
    (R : ∀ f : ZD.Fn, World ZD → Env ZD (ZD.params f) → RufAusgang f)
    (voll : Endblock ZD ZV false [] [])
    (rest : Block ZD ZV false [Ty.index (ZD.count Log.tab)] [] []) :
    execBlock (V := ZV) O passes R
        (Block.arenaAlloc Log sieben rfl zeuge_darf rfl zeuge_gdarf voll rest)
        (welt 4 (by decide) (by decide)) .nil
      = (execEnd O passes R voll
          ((welt 4 (by decide) (by decide)).lese [] [Sum.inr ()]) .nil).zuAusgang :=
  arenaAlloc_an_schranke O passes R Log sieben rfl zeuge_darf rfl zeuge_gdarf voll rest
    _ .nil (by decide)

end ArenaZeuge
end Gabbro.Grammatik
