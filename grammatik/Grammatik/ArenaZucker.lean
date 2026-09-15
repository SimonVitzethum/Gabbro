/-
  File:      Grammatik/ArenaZucker.lean
  Subject:   **`alloc` AND `reset` GET A FORM IN THE SPECIFICATION** -- as SUGAR over the
             existing `Stmt`/`Block`, not as two new constructors.

  THE FINDING THIS ANSWERS (`messung/muse/OPUS-BERICHT-GRAMMATIK-EMIT.md` sections 2.2 and
  5.3): the Rust checker accepts `let i = alloc A (v) [else …];` and `reset A;` with zero
  diagnostics, `emit.rs` writes C for them, that C compiles -- and `Syntax.lean` had no
  `Stmt` constructor for either. `SYNTAX.md`:934 said so verbatim (*"no `Stmt` constructor
  -- the generation is checker state"*), and `Arena.lean` carried the arithmetic of the
  arena with no tie to the syntax at all.

  WHY SUGAR AND NOT TWO CONSTRUCTORS. `Stmt` has 26 constructors and every exhaustive match
  over it is a proof obligation of the goal theorem: 30 Lean files carry 252 occurrences of
  the single leaf constructor `retGrund`, and 79 files name `assignSlot`. Two new
  constructors would be two new arms in the semantics, the machine, race freedom, deadlock,
  progress, cost, the invariant families and the non-interference layer -- and the arena
  would additionally be a NEW CARRIER, so `World` would grow a field and every frame lemma
  in the tree would move. **Sugar costs none of that**: an arena program is an ordinary term
  of the existing `Block`, so `theorem gabbro_ziel` covers it with no new case and no
  re-proof. That is the whole point of `Zucker.lean`, and the arena fits it exactly.

  THE SHAPE. An `arena A capacity lo .. hi of T` is, in the specification, a pair already in
  the language:

    * a table `tab` with `count tab = hi` and one field `feld : T` -- the slots;
    * a global `zaehl` of type `int 0 hi` -- the `used` counter.

  That is also literally what the emitter writes: `A_arena_speicher.buf[…]` beside
  `A_arena_speicher.used`. Then

    `reset A;`                    =  `zaehl = 0;`                  (`Stmt.assignGlob`)
    `let i = alloc A (v) else B;` =  narrow `zaehl` into `0 ..< hi`, else `B`;
                                     `tab.slots[i].feld = v;`  `zaehl = i + 1;`
                                                                   (`Block.narrow` +
                                                                    `Stmt.assignSlot` +
                                                                    `Stmt.assignGlob`)

  `Block.narrow` is the exact form of the emitted guard: the value fits the range, or the
  `else` branch runs and does not fall through. **The reservation `lo` is NOT in the Lean
  form and must not be**: it is a STATIC count the Rust checker keeps (`N212`), and its
  meaning here is `arenaAlloc_unter_schranke` below -- while the counter stands under the
  hard bound, the `else` branch is not entered, so the surface form that omits it is sound
  for any choice of branch. That is the syntactic half of `Arena.alloc_innerhalb_reserve`.

  WHAT IS STILL OPEN AND IS BOOKED, NOT HIDDEN (`dokumente/OFFEN.md` O14): the Rust exporter
  `lean_g.rs` refuses an arena declaration (`LG001`) instead of lowering it to this
  table-plus-global pair, so no arena program closes a translation-validation chain YET.
  The form now exists; the export does not.

  Core direction: imports `Zucker` (for `Expr.weaken`) and `Arena` (for the bridge).
-/
import Grammatik.Zucker
import Grammatik.Arena

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

@[simp] theorem Wert.umTyp_rfl {τ : Ty} (v : Wert D τ) : Wert.umTyp rfl v = v := rfl

@[simp] theorem Expr.umTyp_rfl {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    Expr.umTyp rfl e = e := rfl

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
    (o : List (D.Tab ⊕ D.Glob)) : (σ.lese Λ o).globs = σ.globs := rfl

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
    (o : List (D.Tab ⊕ D.Glob)) : A.stand (σ.lese Λ o) = A.stand σ := rfl

/-- A slot store does not move the counter. -/
@[simp] theorem stand_schreibSlot (A : ArenaForm D) (σ : World D) (Λ : List (Res D))
    (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    A.stand (σ.schreibSlot t Λ k f v) = A.stand σ := rfl

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
    (Expr.weiter (lo := 0) (hi := 0) (lo' := 0) (hi' := D.count A.tab)
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
    (Expr.weiter (lo := 0 + 1) (hi := (D.count A.tab - 1) + 1)
      (lo' := 0) (hi' := D.count A.tab) (by omega) (by omega)
      (Expr.add (Expr.var .hier) (Expr.lit 1)))

/-- The body of an allocation: the store, then the bump. Named, because both theorems
    below speak about it. -/
def arenaRumpf (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ' :=
  .cons (.assignSlot A.tab A.feld (Expr.var .hier) (Expr.weaken v) hwT hLT)
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
    simp
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

/-- `arena Log capacity 2 .. 4 of u8` -- the hard bound is the table's `count`. -/
def Log : ArenaForm ZD where
  tab := ()
  feld := ()
  zaehl := ()
  hz := rfl
  hpos := by decide

/-- The witness is not degenerate: four slots, so a full arena and an empty one are two
    different worlds. -/
theorem Log_vier : ZD.count Log.tab = 4 := rfl

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
    Log.stand (welt c h0 h4) = c := rfl

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
  Expr.weiter (by decide) (by decide) (Expr.lit 7)

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

/-- The bump, run: the counter stands at 1, the bound index is 2, and after the store it
    stands at 3. -/
theorem zeuge_bump (O : Orakel ZD) (passes : Nat)
    (R : ∀ f : ZD.Fn, World ZD → Env ZD (ZD.params f) → RufAusgang f) :
    ∃ σ' : World ZD,
      execStmt (V := ZV) (l := false) O passes R
          (Stmt.assignGlob Log.zaehl (Block.arenaBump Log) rfl zeuge_gdarf)
          (welt 1 (by decide) (by decide))
          (.cons ⟨2, by decide, by decide⟩ .nil)
        = .ok σ' (.cons ⟨2, by decide, by decide⟩ .nil) ∧
      Log.stand σ' = 3 := by
  obtain ⟨σ', h1, h2⟩ :=
    arenaBump_stand (V := ZV) (l := false) O passes R Log rfl zeuge_gdarf
      (welt 1 (by decide) (by decide)) ⟨2, by decide, by decide⟩ .nil
  exact ⟨σ', h1, by rw [h2]; decide⟩

/-- `arena Log capacity 2 .. 4` on the model side. -/
def kapLog : Arena.Kap := ⟨2, 4⟩

/-- The model arena of generation 0, empty. -/
def arenaLeer : Arena.Arena kapLog 0 := ⟨0, by decide⟩

/-- **The bridge, run:** on the empty witness arena the syntax runs its body exactly while
    `Arena.alloc` returns `some`. -/
theorem zeuge_modell :
    (Log.stand (welt 0 (by decide) (by decide)) < ZD.count Log.tab)
      ↔ Arena.alloc arenaLeer ≠ none :=
  arenaAlloc_gdw_modell Log (welt 0 (by decide) (by decide)) kapLog (by decide)
    arenaLeer (by decide)

end ArenaZeuge

#print axioms eval_umTyp
#print axioms arenaReset_stand
#print axioms arenaBump_stand
#print axioms arenaAlloc_unter_schranke
#print axioms arenaAlloc_an_schranke
#print axioms arenaAlloc_gdw_modell
#print axioms arenaAlloc_bump_modell
#print axioms ArenaZeuge.zeuge_reset
#print axioms ArenaZeuge.zeuge_bump
#print axioms ArenaZeuge.zeuge_modell
#print axioms ArenaZeuge.zeuge_alloc_leer
#print axioms ArenaZeuge.zeuge_alloc_voll
#print axioms ArenaZeuge.zeuge_leer_unter
#print axioms ArenaZeuge.zeuge_voll_an

end Gabbro.Grammatik

/-! CUTS -- what this file does NOT claim.

  * **The generation is not here.** `Arena.lean` carries it as a type index (`Marke g`,
    `ArenaIdx g n`) and a stale index does not typecheck there. In the SYNTAX the
    generation is checker state: `N211` refuses a use of an index bound before a `reset`.
    This file's `reset` is one store, and nothing here forbids reading an older index --
    that refusal is the Rust checker's and is not mirrored in Lean.
  * **The reservation `lo` is not here**, on purpose. It is a static count (`N212`), and
    its only model-side consequence -- the `else` branch cannot run while the counter is
    under the bound -- IS proved (`arenaAlloc_unter_schranke`).
  * **The exporter does not produce these terms.** `gabbro lean-g` refuses an arena
    declaration (`LG001`), so no arena program closes a chain yet. Booked as `OFFEN.md`
    O14; the form existing is the precondition for that work, not a substitute for it.
  * **`Arena.lookup` returns the slot POSITION, not a stored value** (`Arena.lean`'s own
    cuts), so the bridge in section 5 is about the counter and the index, not about
    content.
-/
