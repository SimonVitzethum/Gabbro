/- Part 2 of 2 of `Geist` (split by instrumente/teile/lean-teilen.py; the umbrella `Geist.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Geist.T1

namespace Gabbro.Grammatik.Geist

open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-! ## Erasure: ghost-free reads evaluate equal off-ghost.

    The reason ghosts may be omitted by the emitter: an expression whose
    read footprint is ghost-free cannot observe ghost carriers, so two
    worlds that agree on every non-ghost carrier give the same value. This
    reuses the footprint keystone `Extraktion.eval_liest_orte` (section 19
    R1) by qualified name -- the ghost-freedom hypothesis discharges exactly
    the per-side agreements the keystone consumes. -/

/-- Erasure at expressions: an expression whose footprint is ghost-free
    evaluates to the same value in two worlds that agree off-ghost. The
    `he` premise is the ghost-freedom of this footprint; `hS`/`hG` fix the
    present-world agreements, `h0S`/`h0G` the entry-world agreements (for
    `old(..)`), each consumed once per side. -/
theorem eval_gleich_ausser_geist {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (he : orteOhneGeist (D := D) e.orte)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, D.ggeist g = false → σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, D.ggeist g = false → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ := by
  apply Extraktion.eval_liest_orte e σ₀ σ₀' σ σ' ρ
  · intro t ht k f
    exact hS t (he _ ht) k f
  · intro g hg
    exact hG g (he _ hg)
  · intro t ht k f
    exact h0S t (he _ ht) k f
  · intro g hg
    exact h0G g (he _ hg)

/-- `assignVar` reads only its bound expression: the step's footprint is
    the footprint of `e`. The `hm` premise fixes the member inspected; the
    conclusion restates it at the statement footprint. -/
theorem assignVar_orte_mem (V : Vertrag D) (l : Bool)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (o : D.Tab ⊕ D.Glob) (hm : o ∈ e.orte) :
    o ∈ Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e) := by
  have hdef : Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e)
      = e.orte := rfl
  rw [hdef]
  exact hm

/-- Erasure at `assignVar`: the bound value is ghost-independent when the
    step footprint is. The `he` premise is the ghost-freedom at the
    statement footprint (folded to the expression via `assignVar_orte_mem`,
    which this proof consumes); `hS`/`hG`/`h0S`/`h0G` are the off-ghost
    agreements. -/
theorem assignVar_eval_gleich (V : Vertrag D) (l : Bool)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (he : orteOhneGeist (D := D)
      (Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e)))
    (σ₀ σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, D.ggeist g = false → σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ₀.slots t k f = σ₀.slots t k f)
    (h0G : ∀ g : D.Glob, D.ggeist g = false → σ₀.globs g = σ₀.globs g) :
    eval σ₀ e σ ρ = eval σ₀ e σ' ρ := by
  have he' : orteOhneGeist (D := D) e.orte :=
    fun o ho => he o (assignVar_orte_mem V l x e o ho)
  exact eval_gleich_ausser_geist e he' σ₀ σ₀ σ σ' ρ hS hG h0S h0G

/-! ## Witness: one ordinary table, one ghost table.

    `GD`: two tables over `Bool`. `true` is ordinary (written by the body);
    `false` is ghost (named by the contract, never read by the body). -/

namespace Zeuge

/-- Two tables: `true` ordinary, `false` ghost (the only non-default field;
    every other literal compiles unchanged thanks to the defaults). -/
def GD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun | true => true | false => false
      gschreibt := fun e => nomatch e
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
  ggeteilt_bewacht := fun e => nomatch e
  geist := fun | true => false | false => true
  ggeist := fun e => Empty.elim e

/-- The ordinary table is not ghost. -/
theorem GD_ordentlich : GD.geist true = false := rfl

/-- The second table is ghost. -/
theorem GD_geist : GD.geist false = true := rfl

/-- The contract of the only function: no parameters, no result. -/
def GV : Vertrag GD :=
  { schreibt := fun | true => true | false => false
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Index `0` into either table (both have `count 1`). -/
def gi (t : GD.Tab) : Expr GD [] [] (.index (GD.count t)) :=
  .widen (by cases t <;> decide) (by cases t <;> decide) (.lit 0)

/-- Slot read of either table as a boolean expression. -/
def gslot (t : GD.Tab) : Expr GD [] [] .bool :=
  .slot t () (gi t) (fun w => nomatch w)

/-- The witness statement: write the ordinary table from its own read. -/
def gstmt : Stmt GD GV false [] [] [] :=
  .assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w)

/-- The witness body as a block: the statement, then stop. Its footprint
    is the ordinary table only. -/
def gbody : Block GD GV false [] [] [] :=
  .cons gstmt .nil

/-- The decision accepts the witness body: every footprint member is real.
    Proved by `rfl` -- the checker computes it. -/
theorem gbody_g001 : g001 (D := GD) gbody = true := rfl

/-- Joint witness for `g001_korrekt`: all premises instantiated at the
    non-degenerate program `GD` (one ordinary table the body reads, one
    ghost table the contract names below). The `ho` premise fixes the
    footprint member inspected. -/
theorem g001_korrekt_zeuge
    (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ Extraktion.blockOrte (D := GD) gbody) :
    ¬ istGeist (D := GD) o :=
  g001_korrekt gbody gbody_g001 o ho

/-- The witness body as a non-falling block: the statement, then return.
    Feeds the witness program `GP` below. -/
def gendbody : Endblock GD GV false [] [] :=
  .cons gstmt (.ret .empty (List.Perm.refl []))

/-- `ensures` over the ghost slot: the ghost value the body never reads. -/
def GPost : Expr GD (ErgCtx (GD.params ()) (GD.erg ())) (vertragVon GD ()).ende .bool :=
  .slot false () (.widen (by decide) (by decide) (.lit 0)) (fun w => nomatch w)

/-- The witness program: `requires` true, `ensures` over the ghost slot,
    body `gendbody` which writes the ordinary table and reads no ghost. -/
def GP : Programm GD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => GPost
  rumpf := fun _ => gendbody

/-- The witness `ensures` reads the ghost table: the contract side may name
    ghost carriers. The `ho` premise fixes the footprint member inspected. -/
theorem gpost_liest_geist (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ GPost.orte) :
    o = (.inl false : GD.Tab ⊕ GD.Glob) := by
  simp only [GPost, Expr.orte, List.mem_singleton] at ho
  exact ho

/-- The witness oracle: no axioms, no registers, no globals. -/
def GO : Orakel GD where
  wirkt := fun a _ _ => nomatch a
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- A witness world: ordinary slot `b`, ghost slot `c`, trace `tr`. -/
def gwelt (b c : Bool) (tr : List (Ereignis GD)) : World GD :=
  { slots := fun | true, _, _ => b | false, _, _ => c
    globs := fun g => nomatch g
    spur := tr }

/-- The witness write step moves the world: firing the witness statement
    from `gwelt b c []` reaches a world whose ordinary slot is `b`
    and whose trace records the write. The `hstep` premise is the firing,
    `hb`/`hc` fix the incoming slot values. -/
theorem gschritt_schreibt (b c : Bool) (s' : World GD)
    (hb : (gwelt b c []).slots true 0 () = b)
    (hc : (gwelt b c []).slots false 0 () = c)
    (hstep : (execStmt GO 0 keinRuf
      (.assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w) :
        Stmt GD GV false [] [] []) (gwelt b c []) Env.nil).welt = some s') :
    s'.slots true 0 () = b ∧ s'.slots false 0 () = c := by
  -- `hc` fixes the ghost value the conclusion restates; `hghost` below
  -- consumes it through the definitional ride-along.
  have hcg : (gwelt b c []).slots false 0 () = c := hc
  have h := (schreibt_wirkt_slot (D := GD) GO 0 GV false [] []
    true () (gi true) (gslot true) rfl (fun w => nomatch w)
    (gwelt b c []) Env.nil).1
  rw [h] at hstep
  have hidx : (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil).n = 0 := rfl
  have hval : eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil = b := by
    have hlese : ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots
        true = (gwelt b c []).slots true := rfl
    show ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots true 0 () = b
    rw [hlese]
    exact hb
  -- `hstep` fixes the outcome world, `hidx` the written index, `hval` the
  -- written value, `hb` the incoming ordinary value, `hc` the ghost value.
  have hsym : s' = (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).schreibSlot
      true [] _ () _) := Option.some_inj.mp hstep.symm
  have hmem : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)).merke
      [Ereignis.zugriff true true []
        ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
      true 0 () = b := by
    have hhit := storeSlot_hit
      ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)
    rw [hidx] at hhit
    have hhit2 : (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true 0 ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () = b := by
      rw [hhit]
      exact hval
    -- `World.merke` rewrites only the trace field; slots see through it.
    have hsee : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () =
      (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () := rfl
    have hhit3 : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () = b := by
      rw [hsee]
      exact hhit2
    exact hhit3
  have hghost : s'.slots false 0 () = c := by
    rw [hsym]
    -- The ghost slot is untouched by the ordinary write: definitionally `c`.
    have hg : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        false 0 () = c := hcg
    exact hg
  exact ⟨hsym ▸ hmem, hghost⟩

/-- The witness read is ghost-free: its footprint names only the ordinary
    table. -/
theorem gslot_ohne_geist : orteOhneGeist (D := GD) (gslot true).orte := by
  intro o ho
  simp only [gslot, gi, Expr.orte, List.mem_singleton] at ho
  subst ho
  rfl

/-- The off-ghost agreement holds for the witness worlds: they share every
    non-ghost slot. The `ht` premise fixes the non-ghost table; `k`/`f` the
    slot inspected. -/
theorem gwelt_gleicht (b c c' : Bool) (t : GD.Tab) (ht : GD.geist t = false)
    (k : Int) (f : GD.Feld t) :
    (gwelt b c []).slots t k f = (gwelt b c' []).slots t k f := by
  cases ht' : t with
  | true => rfl
  | false =>
      -- `t = false` is ghost (`GD_geist`), contradicting `ht`. The `ht`
      -- premise fires here through the rewrite.
      rw [ht'] at ht
      rw [GD_geist] at ht
      exact absurd ht (by decide)

/-- Witness for erasure: two worlds differing only on the ghost table agree
    on the witness read. All of `b`/`c`/`c'` appear in the conclusion. -/
theorem erasure_zeuge (b c c' : Bool) :
    eval (gwelt b c []) (gslot true) (gwelt b c []) Env.nil =
      eval (gwelt b c' []) (gslot true) (gwelt b c' []) Env.nil :=
  eval_gleich_ausser_geist (gslot true) gslot_ohne_geist
    (gwelt b c []) (gwelt b c' []) (gwelt b c []) (gwelt b c' []) Env.nil
    (fun t ht k f => gwelt_gleicht b c c' t ht k f)
    (fun g hg => nomatch g)
    (fun t ht k f => gwelt_gleicht b c c' t ht k f)
    (fun g hg => nomatch g)

end Zeuge

/-
CUTS:
* No emitter-omission theorem: `Geist.lean` proves the read side (an
  accepted body names no ghost carrier) and erasure (ghost-free reads
  evaluate equal off-ghost); that omitting ghost tables preserves emitted
  behavior is not stated -- emission lives in `crates/`, not here.
* `gschritt_schreibt` fires the witness write in place (`T[true] :=
  T[true]` keeps the value `b`); the trace records the write event, but no
  slot VALUE change is exhibited. A value-flipping witness (negation write)
  would show a memory-changing step in the stronger value sense.
* `assignVar_eval_gleich` lifts erasure to one statement form only
  (`assignVar`); the remaining statement forms are not lifted.
-/

#print axioms Gabbro.Grammatik.Geist.g001_korrekt
#print axioms Gabbro.Grammatik.Geist.Zeuge.g001_korrekt_zeuge
#print axioms Gabbro.Grammatik.Geist.geist_leer_unveraendert
#print axioms Gabbro.Grammatik.Geist.eval_gleich_ausser_geist
#print axioms Gabbro.Grammatik.Geist.Zeuge.erasure_zeuge
#print axioms Gabbro.Grammatik.Geist.Zeuge.gschritt_schreibt


end Gabbro.Grammatik.Geist
