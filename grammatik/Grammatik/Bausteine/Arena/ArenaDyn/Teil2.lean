module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Bausteine.Arena.ArenaDyn.Teil1

@[expose] public section

namespace Gabbro.Grammatik.ArenaDyn
section Form
open Gabbro.Grammatik
variable {D : Deklaration}
section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Below the committed prefix, `alloc` does not take its `else`** -- the
    model half of the R-commit rule. The body is `ArenaZucker`'s
    `arenaRumpf`, unchanged: past the test, a dynamic arena IS a static one.
    The index bound is the OLD used counter, as there. -/
theorem dynAlloc_unter_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execBlock O passes R (Block.arenaRumpf A.toArenaForm v hwT hLT hwG hLG rest)
          (((σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm])).lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ,
            by have := A.komSt_le σ; omega⟩ ρ)).schrumpf := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · exact arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest _ ρ
      (by have := A.komSt_le σ
          show A.stand σ < D.count A.tab
          omega)
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

/-- **At or above the committed prefix, `alloc` takes its `else`** -- even
    with room to the ceiling. That is the whole difference between a
    reservation and storage: the arena is not full and the allocation is
    refused all the same, because the slot is not committed yet. -/
theorem dynAlloc_ueber_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.komSt σ ≤ A.stand σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ).zuAusgang := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · next hja =>
      exfalso
      revert hja
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      unfold DynForm.komSt ArenaForm.stand at h
      omega
  · rfl

/-- **THE SIMULATION** (the shape PLAN-DYNAMIC section 9 fixes): a dynamic
    allocation whose index stays under its path's committed prefix runs the
    STATIC-max form -- the very same `Block.arenaAlloc` over the very same
    `ArenaForm`, on a world that differs from the dynamic one only in the
    trace (the two recorded reads of the guard). The second and third
    conjuncts are that difference, measured: the storage is the same
    storage. Every static-arena theorem therefore transfers to the right
    hand side verbatim, and growth is an observable no-op -- `dynGrow_commit`
    is the frame that says the only thing a `grow` can change about this
    equation is the guard it passes. -/
theorem dynAlloc_simuliert (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = execBlock O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest)
          (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).globs = σ.globs ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).slots = σ.slots := by
  refine ⟨?_, rfl, rfl⟩
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · rfl
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

end Bedeutung

/-! #### THE WITNESS -- two words over one table, and both branches run

  Not decorative, and the non-degeneracy is the point of the whole section:
  the table holds FOUR slots (the ceiling `M = 4`) and the committed word
  stands at TWO. So the fixture has a state that the static form cannot
  even name -- an arena with room to the ceiling whose allocation is
  refused, because the slot is reserved and not committed. Both branches of
  `dynAlloc` are exercised below, and the one `grow` moves the committed
  word from 2 to the ceiling. -/

namespace DynZeuge

/-- One table of four slots holding a byte, and TWO globals over `0 .. 4`:
    the used counter (`false`) and the committed prefix (`true`). The two
    words are the whole difference to `ArenaZucker`'s `ZD`, which has one. -/
def DD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Bool
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

/-- `arena Halde capacity 2 .. 4 max 4 of u8` -- the ceiling is the table's
    `count`, the committed prefix is the second word. -/
def Halde : DynForm DD where
  tab := ()
  feld := ()
  zaehl := false
  hz := rfl
  hpos := by decide
  komm := true
  hk := rfl
  hzwei := by
    intro h
    exact Bool.noConfusion (show (true : Bool) = false from h)

/-- The ceiling is four: a committed prefix strictly under it is a state. -/
theorem Halde_vier : DD.count Halde.tab = 4 := by rfl

/-- The contract of the witness body: it writes the table and both words. -/
def DV : Vertrag DD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem zeuge_darf : darf DD () ([] : List (Res DD)) := by
  intro w hw; cases hw

theorem zeuge_gdarf (g : DD.Glob) : gdarf DD g ([] : List (Res DD)) := by
  intro w hw; cases hw

/-- A world whose used counter stands at `u` and whose committed word at
    `k`; every slot at zero. -/
def welt (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) : World DD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => cond g ⟨k, hk0, hk4⟩ ⟨u, hu0, hu4⟩
  spur := []

theorem welt_stand (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) :
    Halde.stand (welt u k hu0 hu4 hk0 hk4) = u := by rfl

theorem welt_komSt (u k : Int) (hu0 : 0 ≤ u) (hu4 : u ≤ 4) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) :
    Halde.komSt (welt u k hu0 hu4 hk0 hk4) = k := by rfl

/-- The world the witness runs in: nothing used, TWO of four slots
    committed. -/
def halb : World DD := welt 0 2 (by decide) (by decide) (by decide) (by decide)

/-- The same arena with its used counter AT the committed prefix -- and the
    committed prefix strictly under the ceiling. **This state is the reason
    the fixture is not degenerate:** there is room, and the allocation is
    refused all the same. -/
def gespannt : World DD := welt 2 2 (by decide) (by decide) (by decide) (by decide)

theorem halb_stand : Halde.stand halb = 0 := by rfl

theorem halb_komSt : Halde.komSt halb = 2 := by rfl

theorem zeuge_raum_ueber_dem_stand : Halde.stand halb < Halde.komSt halb := by decide

theorem zeuge_raum_unter_der_decke : Halde.komSt gespannt < DD.count Halde.tab := by decide

theorem zeuge_stand_an_der_verpflichtung : Halde.komSt gespannt ≤ Halde.stand gespannt := by
  decide

/-- The value an `alloc` stores in the witness. -/
def sieben : Expr DD [] [] (DD.typ Halde.tab Halde.feld) :=
  Expr.widen (by decide) (by decide) (Expr.lit 7)

/-- **`grow Halde by 2`, run:** the committed word moves from 2 to the
    ceiling 4, the used counter does not move, and no slot does. A real
    commit (`n = 2 > 0`) that ends exactly at `M`. -/
theorem zeuge_grow (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.int 0 (DD.count Halde.tab)] [] []) :
    ∃ σ' : World DD,
      execBlock (V := DV) O passes R
          (Block.dynGrowB Halde 2 rfl (zeuge_gdarf Halde.komm) voll rest) halb .nil
        = (execBlock O passes R rest σ'
            (.cons ⟨Halde.komSt halb + 2, by rw [halb_komSt]; decide,
              by rw [halb_komSt]; decide⟩ .nil)).schrumpf ∧
      Halde.komSt σ' = 4 ∧ Halde.stand σ' = 0 ∧ σ'.slots = halb.slots := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    dynGrow_commit (V := DV) (l := false) O passes R Halde 2 rfl (zeuge_gdarf Halde.komm)
      voll rest halb .nil (by decide) (by decide)
  exact ⟨_, h1, by rw [h2]; decide, by rw [h3]; decide, h4⟩

/-- **Under the committed prefix the `else` is not taken**, and the index is
    the old used counter -- the body is `ArenaZucker`'s, unchanged. -/
theorem zeuge_alloc_unter (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) halb .nil
      = (execBlock O passes R (Block.arenaRumpf Halde.toArenaForm sieben rfl zeuge_darf rfl
            (zeuge_gdarf Halde.zaehl) rest)
          ((halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).lese []
            [Sum.inr Halde.zaehl])
          (.cons ⟨Halde.stand halb, Halde.stand_nonneg halb, by decide⟩ .nil)).schrumpf :=
  dynAlloc_unter_commit (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest halb .nil (by decide)

/-- **And AT the committed prefix it IS taken, with the ceiling still two
    slots away.** This is the one line the static form cannot produce. -/
theorem zeuge_alloc_ueber (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) gespannt .nil
      = (execEnd O passes R voll
          (gespannt.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]) .nil).zuAusgang :=
  dynAlloc_ueber_commit (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest gespannt .nil (by decide)

/-- **The simulation, run:** under the committed prefix the dynamic form IS
    the static one, on a world that differs only in the trace. -/
theorem zeuge_simuliert (O : Orakel DD) (passes : Nat)
    (R : ∀ f : DD.Fn, World DD → Env DD (DD.params f) → RufAusgang f)
    (voll : Endblock DD DV false [] [])
    (rest : Block DD DV false [Ty.index (DD.count Halde.tab)] [] []) :
    execBlock (V := DV) O passes R
        (Block.dynAlloc Halde sieben rfl zeuge_darf rfl (zeuge_gdarf Halde.zaehl)
          (zeuge_gdarf Halde.komm) voll rest) halb .nil
      = execBlock O passes R
          (Block.arenaAlloc Halde.toArenaForm sieben rfl zeuge_darf rfl
            (zeuge_gdarf Halde.zaehl) voll rest)
          (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]) .nil ∧
      (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).globs = halb.globs ∧
      (halb.lese [] [Sum.inr Halde.zaehl, Sum.inr Halde.komm]).slots = halb.slots :=
  dynAlloc_simuliert (V := DV) (l := false) O passes R Halde sieben rfl zeuge_darf rfl
    (zeuge_gdarf Halde.zaehl) (zeuge_gdarf Halde.komm) voll rest halb .nil (by decide)

end DynZeuge

end Form

#print axioms dynGrowListe_gelingt
#print axioms dynGrowListe_scheitert
#print axioms dynGrowListe_gelingt_zeuge
#print axioms dynGrowListe_scheitert_zeuge
#print axioms dynGrowListe_zwilling
#print axioms dynGrow_monoton
#print axioms dynGrow_ueber_M
#print axioms dynGrow_isSome
#print axioms dynGrow1_gdw_alloc
#print axioms planted_ueber_M
#print axioms planted_defekt_sichtbar
#print axioms growKosten_pos
#print axioms DynForm.stand_schreibGlob_komm
#print axioms DynForm.komSt_schreibGlob
#print axioms dynGrow_commit
#print axioms dynCommit_monoton
#print axioms dynAlloc_unter_commit
#print axioms dynAlloc_ueber_commit
#print axioms dynAlloc_simuliert
#print axioms DynZeuge.zeuge_grow
#print axioms DynZeuge.zeuge_alloc_unter
#print axioms DynZeuge.zeuge_alloc_ueber
#print axioms DynZeuge.zeuge_simuliert
#print axioms DynZeuge.zeuge_raum_ueber_dem_stand
#print axioms DynZeuge.zeuge_raum_unter_der_decke
#print axioms DynZeuge.zeuge_stand_an_der_verpflichtung

end Gabbro.Grammatik.ArenaDyn

/-! CUTS -- what this file does NOT claim.

  * No checker rule is built here: R-max / R-commit / R-grow-else /
    R-grow-const / R-grow-form (PLAN-DYNAMIC section 4) are lane 240/241
    Rust work; this file is the Lean model half (section 9) only.
  * No emitter or runtime is built: the descriptor (`base`, `committed`),
    `gabbro_arena_reserve` / `gabbro_arena_grow`, and the OS-token guardian
    are lane 242 work; the `_Static_assert` pins are not stated here.
  * No cost arm is built: `growKosten` reads the per-slot commit cost as
    DATA from the named hardware assumption (Spec premise (c) latency
    entry); the `K003` wiring and the `K002`-falls probe are lane 243 work.
  * **No refinement is claimed** (review G08 F4, fix lane F2). `DynArena` is
    a Nat record that carries `c <= M` as a field; a membership fact over it
    (the former `dynVerfein`, "committed slots are reserved slots") restates
    that field, and the former `region_verpflichtet` tied it to a run only
    through a premise its witness discharged without looking at the run
    (the lane-147 pattern). Both are REMOVED, not renamed. What stands in
    their place is a statement about the one runtime fact this record does
    model -- the past-ceiling stop -- over a whole commit sequence
    (`dynGrowListe_gelingt` / `_scheitert`, with non-degenerate witnesses):
    the model half of `N426`'s upper-bound rule. Nothing links `DynArena` to
    the Rust checker's per-path accounting or to the C runtime by proof; the
    link is by name (`N426`, `gabbro_arena_grow`'s ceiling test) only.
    Proved as the linkage anchor to the static model: `dynGrow_isSome`
    (success is exactly the bound) and `dynGrow1_gdw_alloc` (one-slot commit
    agrees with `Arena.alloc` on `Kap ⟨hi, M⟩` via `arenaModell`, from the
    `alloc_erfolg` / `alloc_fehlschlag` pair).
  * **Section `Form` closes the section-9 residue** (server lane,
    2026-09-28): `DynForm` over `ArenaForm D` (the table spans `M`, the
    committed prefix is a second `stand`-style word `komSt`), the four
    theorems in `Block` form (`dynGrow_commit` with the frame conjuncts,
    `dynCommit_monoton`, `dynAlloc_unter_commit`, `dynAlloc_ueber_commit`)
    and the simulation `dynAlloc_simuliert`, each with a witness on `DD`
    (two globals over one four-slot table, committed prefix at 2). The
    estimated 40-80 lines of narrow-on-committed plumbing were NOT needed:
    the guard is `Block.pruefung` on `used < committed` -- no binder, an
    `else` that does not fall through -- with `Block.arenaAlloc` taken from
    `ArenaZucker.lean` UNCHANGED underneath, so the static theorems apply
    past the guard instead of being restated.
  * **The residue of the simulation is the TRACE, and it is named.**
    `dynAlloc_simuliert` equates the dynamic form with the static-max form
    run on `σ.lese Λ [used, committed]`, and measures the difference:
    `globs` and `slots` are equal (proved), the trace carries two more
    recorded reads (the guard's). A run-level bisimulation that erases
    those reads over an arbitrary `rest` is NOT proved and is not claimed;
    what is claimed is one step, exactly.
  * **The simulation is about `alloc`, not about `grow` as a step.**
    "Growth is an observable no-op" is carried here by the frame conjuncts
    of `dynGrow_commit` (a `grow` moves the committed word and no slot and
    not the used counter) plus the guard -- not by a theorem that quantifies
    over programs containing a `grow`.
  * **One arena, one thread** (OFFEN O20, unchanged here). The committed
    prefix is a SECOND carrier, so two threads growing one arena race on it
    exactly as they would on the used counter. Nothing in this section
    relaxes O20's restriction -- no `reset` concurrent with a reader, no
    arena shared across threads without the strict option -- and no
    `Spec.lean` diff naming a weaker run model was made. The goal's own
    footprint rule refuses such a program in any case: an unguarded global
    two threads write is not thread-local and not lock-guarded.
  * **The EXPORTER does not produce these terms** (measured 2026-09-28):
    `lean_g.rs` refuses `grow` by name (`LG005`) and builds the STATIC
    `ArenaForm` over `hi`, not over the ceiling `M`. So the forms here are
    covered by `gabbro_ziel` -- they are ordinary `Block` terms -- but no
    dynamic-arena PROGRAM is certified, and a green build says nothing about
    one. Same status `ArenaZucker.lean` had before O14 closed; the form
    existing is the precondition for that work, not a substitute for it.
  * The `Spec.lean` header diff (the two (d) assumption texts) is made in
    that file and not here, as a COMMENT-only diff with its own review
    (`messung/SERVER-0E-SPEC-DIFF.md`): no field of `Laufzeit` is added, and
    the reason is written there -- a new premise would weaken the statement,
    and the reservation is already carried by `Laufzeit.lader`.
  * `planted_ueber_M` is the planted-defect check: `dynGrow` on the full
    `max 64` arena returns `none` (by `rfl`); the unchecked `dynGrowFalsch`
     reaches `65`, past the ceiling (`planted_defekt_sichtbar`).
-/

namespace Gabbro.Grammatik.ArenaDyn

/- ## Freiliste (TODO §1-B): befreite Slots sind wiederverwendbar.

  Neben dem Committed-Präfix `c` trägt die Laufzeit eine Freiliste befreiter
  Slots (intrusiv, LIFO) und die Hochwassermarke `belegt`. `alloc` nimmt von
  der Liste (kein Commit, keine Abtastung -- der Speicher steht bereit) oder
  von der Marke; `free` legt den Slot auf die Liste. Der Prüfer (`N586`)
  hält Einfach-Freigabe und Tod; hier steht die Zustandsform mit den
  Erhaltungssätzen. Kein `sorry`: was nicht schließt, steht nicht hier.
-/

/-- Freilisten-Zustand: Hochwasser `belegt` (monoton) und befreite Slots
    (alle darunter -- nur belegte Slots werden je befreit). -/
structure FreiZustand where
  belegt : Nat
  frei : List Nat
  hfrei : ∀ i ∈ frei, i < belegt

/-- `alloc`: von der Liste (Marke unverändert) oder vom Hochwasser (+1). -/
def freiAlloc : FreiZustand → Nat × FreiZustand
  | ⟨belegt, [], _⟩ =>
    (belegt, ⟨belegt + 1, [], fun _ hm => absurd hm (by simp only [List.not_mem_nil, not_false_eq_true])⟩)
  | ⟨belegt, i :: rest, hfrei⟩ =>
    (i, ⟨belegt, rest, fun j hj => hfrei j (List.mem_cons_of_mem _ hj)⟩)

end Gabbro.Grammatik.ArenaDyn
