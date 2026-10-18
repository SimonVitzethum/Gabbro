import Grammatik.Code.Refine.Post

/-
  File:      Grammatik/Code/Refine/Stmt.lean
  Subject:   TRACK L, PHASE L1 -- THE STATEMENT OF THE REFINEMENT THEOREM: `OutOk`, `EndOk` and the
             lemmas that carry it over a prefix run, a larger counter and a dropped local.

  `lowerS_ok`, `lowerB_ok`, `lowerEnd_ok` (in `StmtOk.lean`): if the lowering of `s` (a statement,
  a block, an end block) to IR blocks succeeds, and the IR module holds those blocks (`hM`: the
  labels find them, the target label `k` finds a block without phis, and so do the `leave` and
  `next` targets `lv`), then in any memory that represents the world (`Rep`) with the locals in
  their cells (`EnvRep`), the memory having its global blocks (`WfL`) and the free registers above
  every variable's, the IR run from the entry label does what the SOURCE outcome says
  (`OutOk`, one clause per outcome of the source):
    * `ok`: the run reaches label `k` in a memory that represents the world with the environment in
      the cells (`Post`);
    * `zurueck` (return) of `v`: the run reaches a `ret` of the image of `v` and leaves a memory
      that represents the returned world (`RunRet`);
    * `leave` / `next` (only in a loop body): the run reaches the leave / next target of the loop,
      in a memory that represents the world (`Post`);
    * `why`, `logik`, `hardware`: nothing is said (a source run that stops there relates to no
      IR run).
  `R` (the semantics of calls) is arbitrary: the fragment has no call, so no case uses it.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl)

variable {D : Deklaration} {V : Vertrag D}

/-- A normal exit of a lowered statement. -/
def RunOk (lay : Layout D) (cenv : List Reg) (M : Modl) (S : Sees) (fn : Nat) (lb k : Lbl)
    (st' : St) {Γ : Ctx} (σ' : World D) (ρ' : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame)
    (dst : Option Reg) : Prop :=
  ∃ m' rs', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs', dst⟩ ks) ∧
    Post lay cenv σ' ρ' m' rs' st'.r

/-- A `return` of a lowered statement: the frame stands at a `ret` of the image of `v`, and the memory
    it leaves represents the world `σ'` the source left (the RETURNED world: what a caller sees). -/
def RunRet (lay : Layout D) (M : Modl) (S : Sees) (fn : Nat) (lb : Lbl) (σ' : World D)
    (v : ErgVal D V.erg) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg) : Prop :=
  ∃ m' f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
    RetAt M f' (ergImg lay V.erg v) ∧ Rep lay σ' m' ∧ WfL lay m'

/-- The blocks of a lowering are found by their labels, and the continuation is a block without phis. -/
def InM (M : Modl) (fn : Nat) (blks : List Block) : Prop := ∀ b ∈ blks, M.blk fn b.lbl = some b

def KOk (M : Modl) (fn : Nat) (k : Lbl) : Prop := ∃ bk, M.blk fn k = some bk ∧ bk.phis = []

/-- The `leave` and `next` targets of the enclosing loop are blocks without phis. -/
def LvOk (M : Modl) (fn : Nat) (lv : Lbl × Lbl) : Prop := KOk M fn lv.1 ∧ KOk M fn lv.2

/-- **What a lowered run does for an outcome of the source.** One clause per outcome. -/
def OutOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (M : Modl) (S : Sees) (fn : Nat)
    (lb k : Lbl) (st' : St) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .ok σ' ρ' => RunOk lay cenv M S fn lb k st' σ' ρ' m rs ks dst
  | .zurueck σ' v => RunRet lay M S fn lb σ' v m rs ks dst
  | .why _ _ => True
  | .leave _ σ' ρ' => RunOk lay cenv M S fn lb lv.1 st' σ' ρ' m rs ks dst
  | .next _ σ' ρ' => RunOk lay cenv M S fn lb lv.2 st' σ' ρ' m rs ks dst
  | .logik _ => True
  | .hardware _ => True

/-- The same for an end block, which never falls through. -/
def EndOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (M : Modl) (S : Sees) (fn : Nat)
    (lb : Lbl) (st' : St) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ' v => RunRet lay M S fn lb σ' v m rs ks dst
  | .why _ _ => True
  | .leave _ σ' ρ' => RunOk lay cenv M S fn lb lv.1 st' σ' ρ' m rs ks dst
  | .next _ σ' ρ' => RunOk lay cenv M S fn lb lv.2 st' σ' ρ' m rs ks dst
  | .logik _ => True
  | .hardware _ => True

theorem inm_sub {M : Modl} {fn : Nat} {b1 b2 : List Block} (h : InM M fn b1) (hs : ∀ b ∈ b2, b ∈ b1) :
    InM M fn b2 := fun b hb => h b (hs b hb)

/-- The entry block of a lowering is found, and has no phis. -/
theorem kok_of_shape {M : Modl} {fn : Nat} {lb : Lbl} {st st' : St} {blks : List Block}
    (hS : Shape lb st st' blks) (hM : InM M fn blks) : KOk M fn lb := by
  obtain ⟨⟨b, bs, hb, hl⟩, hp, _⟩ := hS
  have h1 := hM b (by rw [hb]; simp)
  rw [hl] at h1
  exact ⟨b, h1, hp b (by rw [hb]; simp)⟩

/-- Dropping the innermost local from a `Post`. -/
theorem post_tail {lay : Layout D} {cenv : List Reg} {a : Reg} {τ : GTy} {Γ : Ctx} {σ : World D}
    (ρ : Env D (τ :: Γ)) {m : Mem} {rs : Regs} {r : Nat} (h : Post lay (a :: cenv) σ ρ m rs r) :
    Post lay cenv σ ρ.tail m rs r := by
  cases ρ with
  | cons v ρ' =>
      obtain ⟨hR, ⟨_, hE⟩, hW, hc⟩ := h
      exact ⟨hR, hE, hW, fun x hx => hc x (List.mem_cons_of_mem _ hx)⟩

section Lemmas

variable {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {M : Modl} {S : Sees} {fn : Nat}
  {k : Lbl} {st' : St} {ks : List Frame} {dst : Option Reg}

theorem runOk_lift {lb lb1 k : Lbl} {m m1 : Mem} {rs rs1 : Regs} {Γ : Ctx} {σ' : World D} {ρ' : Env D Γ}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (h' : RunOk lay cenv M S fn lb1 k st' σ' ρ' m1 rs1 ks dst) :
    RunOk lay cenv M S fn lb k st' σ' ρ' m rs ks dst := by
  obtain ⟨m', rs', hr, hP⟩ := h'
  exact ⟨m', rs', Reach.trans h hr, hP⟩

theorem runRet_lift {lb lb1 : Lbl} {m m1 : Mem} {rs rs1 : Regs} {σ' : World D} {v : ErgVal D V.erg}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (h' : RunRet lay M S fn lb1 σ' v m1 rs1 ks dst) : RunRet lay M S fn lb σ' v m rs ks dst := by
  obtain ⟨m', f', hr, h1, h2, h3⟩ := h'
  exact ⟨m', f', Reach.trans h hr, h1, h2, h3⟩

theorem runOk_mono {lb k : Lbl} {m : Mem} {rs : Regs} {st1 st2 : St} {Γ : Ctx} {σ' : World D}
    {ρ' : Env D Γ} (hle : st1.r ≤ st2.r) (h' : RunOk lay cenv M S fn lb k st1 σ' ρ' m rs ks dst) :
    RunOk lay cenv M S fn lb k st2 σ' ρ' m rs ks dst := by
  obtain ⟨m', rs', hr, hP⟩ := h'
  exact ⟨m', rs', hr, post_mono hP hle⟩

theorem runOk_tail {lb k : Lbl} {m : Mem} {rs : Regs} {a : Reg} {τ : GTy} {Γ : Ctx} {σ' : World D}
    {ρ' : Env D (τ :: Γ)} (h' : RunOk lay (a :: cenv) M S fn lb k st' σ' ρ' m rs ks dst) :
    RunOk lay cenv M S fn lb k st' σ' ρ'.tail m rs ks dst := by
  obtain ⟨m', rs', hr, hP⟩ := h'
  exact ⟨m', rs', hr, post_tail ρ' hP⟩

/-- A run to the start of the continuation, followed by an outcome of the continuation. -/
theorem outok_lift {lb lb1 : Lbl} {m m1 : Mem} {rs rs1 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l Γ, OutOk lay cenv lv M S fn lb1 k st' m1 rs1 ks dst o →
      OutOk lay cenv lv M S fn lb k st' m rs ks dst o
  | .ok σ' ρ', h' => runOk_lift h h'
  | .zurueck σ' v, h' => runRet_lift h h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_lift h h'
  | .next _ σ' ρ', h' => runOk_lift h h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_lift {lb lb1 : Lbl} {m m1 : Mem} {rs rs1 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb1 st' m1 rs1 ks dst o →
      EndOk lay cenv lv M S fn lb st' m rs ks dst o
  | .zurueck σ' v, h' => runRet_lift h h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_lift h h'
  | .next _ σ' ρ', h' => runOk_lift h h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-- A larger counter bound keeps an outcome. -/
theorem outok_mono {lb : Lbl} {m : Mem} {rs : Regs} {st1 st2 : St} (hle : st1.r ≤ st2.r)
    {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l Γ, OutOk lay cenv lv M S fn lb k st1 m rs ks dst o →
      OutOk lay cenv lv M S fn lb k st2 m rs ks dst o
  | .ok σ' ρ', h' => runOk_mono hle h'
  | .zurueck σ' v, h' => h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_mono hle h'
  | .next _ σ' ρ', h' => runOk_mono hle h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_mono {lb : Lbl} {m : Mem} {rs : Regs} {st1 st2 : St} (hle : st1.r ≤ st2.r)
    {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb st1 m rs ks dst o →
      EndOk lay cenv lv M S fn lb st2 m rs ks dst o
  | .zurueck σ' v, h' => h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_mono hle h'
  | .next _ σ' ρ', h' => runOk_mono hle h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-- An end block's outcome, read as the outcome of a block that never falls through. -/
theorem outok_of_endok {lb : Lbl} {m : Mem} {rs : Regs} {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb st' m rs ks dst o →
      OutOk lay cenv lv M S fn lb k st' m rs ks dst o.zuAusgang
  | .zurueck σ' v, h' => h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => h'
  | .next _ σ' ρ', h' => h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-- The scope of a block that bound a local ends: its outcome, seen from outside. -/
theorem outok_schrumpf {lb : Lbl} {m : Mem} {rs : Regs} {a : Reg} {τ : GTy} {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l (τ :: Γ), OutOk lay (a :: cenv) lv M S fn lb k st' m rs ks dst o →
      OutOk lay cenv lv M S fn lb k st' m rs ks dst o.schrumpf
  | .ok σ' ρ', h' => runOk_tail h'
  | .zurueck σ' v, h' => h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_tail h'
  | .next _ σ' ρ', h' => runOk_tail h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_schrumpf {lb : Lbl} {m : Mem} {rs : Regs} {a : Reg} {τ : GTy} {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l (τ :: Γ), EndOk lay (a :: cenv) lv M S fn lb st' m rs ks dst o →
      EndOk lay cenv lv M S fn lb st' m rs ks dst o.schrumpf
  | .zurueck σ' v, h' => h'
  | .why _ _, _ => trivial
  | .leave _ σ' ρ', h' => runOk_tail h'
  | .next _ σ' ρ', h' => runOk_tail h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

end Lemmas

end Gabbro.Code.Lower
