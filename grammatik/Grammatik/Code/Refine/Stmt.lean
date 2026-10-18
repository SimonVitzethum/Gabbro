import Grammatik.Code.Refine.Post

/-
  File:      Grammatik/Code/Refine/Stmt.lean
  Subject:   TRACK L, PHASE L1 -- THE STATEMENT OF THE REFINEMENT THEOREM: `Fr`, `OutOk`, `EndOk` and
             the lemmas that carry it over a prefix run, a larger counter and a dropped local.

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
  Every relating clause also carries the FRAME of the run (`Fr`): registers below the entry bound
  are untouched, memory only grows, and a block that already existed, is no table and no global
  and is no cell of the local variables keeps what it held. This is what lets a loop keep its
  counter in a register and what lets a caller keep its own cells across a call.
  `R` (the semantics of calls) is arbitrary: the fragment has no call, so no case uses it.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl)

variable {D : Deklaration} {V : Vertrag D}

/-- A normal exit of a lowered statement. -/
def RunOk (lay : Layout D) (cenv : List Reg) (M : Modl) (S : Sees) (fn : Nat) (lb k : Lbl)
    (r0 r' : Nat) {Γ : Ctx} (σ' : World D) (ρ' : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame)
    (dst : Option Reg) : Prop :=
  ∃ m' rs', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs', dst⟩ ks) ∧
    Post lay cenv σ' ρ' m' rs' r' ∧ Fr lay cenv r0 m rs m' rs'

/-- A `return` of a lowered statement: the frame stands at a `ret` of the image of `v`, and the memory
    it leaves represents the world `σ'` the source left (the RETURNED world: what a caller sees). -/
def RunRet (lay : Layout D) (cenv : List Reg) (M : Modl) (S : Sees) (fn : Nat) (lb : Lbl) (r0 : Nat)
    (σ' : World D) (vo : Option Val) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg) : Prop :=
  ∃ m' f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
    RetAt M f' vo ∧ Rep lay σ' m' ∧ WfL lay m' ∧ Fr lay cenv r0 m rs m' f'.regs

/-- The blocks of a lowering are found by their labels, and the continuation is a block without phis. -/
def InM (M : Modl) (fn : Nat) (blks : List Block) : Prop := ∀ b ∈ blks, M.blk fn b.lbl = some b

def KOk (M : Modl) (fn : Nat) (k : Lbl) : Prop := ∃ bk, M.blk fn k = some bk ∧ bk.phis = []

/-- The `leave` and `next` targets of the enclosing loop are blocks without phis. -/
def LvOk (M : Modl) (fn : Nat) (lv : Lbl × Lbl) : Prop := KOk M fn lv.1 ∧ KOk M fn lv.2

/-- **What a lowered run does for an outcome of the source.** One clause per outcome; `r0` is the
    state the lowering started from, `r'` the one it ended in. -/
def OutOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (M : Modl) (S : Sees) (fn : Nat)
    (lb k : Lbl) (r0 r' : Nat) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .ok σ' ρ' => RunOk lay cenv M S fn lb k r0 r' σ' ρ' m rs ks dst
  | .zurueck σ' v => RunRet lay cenv M S fn lb r0 σ' (retImg lay V.gruende V.erg v) m rs ks dst
  | .why σ' r => RunRet lay cenv M S fn lb r0 σ' (whyImg V.gruende V.erg r.val) m rs ks dst
  | .leave _ σ' ρ' => RunOk lay cenv M S fn lb lv.1 r0 r' σ' ρ' m rs ks dst
  | .next _ σ' ρ' => RunOk lay cenv M S fn lb lv.2 r0 r' σ' ρ' m rs ks dst
  | .logik _ => True
  | .hardware _ => True

/-- The same for an end block, which never falls through. -/
def EndOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (M : Modl) (S : Sees) (fn : Nat)
    (lb : Lbl) (r0 r' : Nat) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ' v => RunRet lay cenv M S fn lb r0 σ' (retImg lay V.gruende V.erg v) m rs ks dst
  | .why σ' r => RunRet lay cenv M S fn lb r0 σ' (whyImg V.gruende V.erg r.val) m rs ks dst
  | .leave _ σ' ρ' => RunOk lay cenv M S fn lb lv.1 r0 r' σ' ρ' m rs ks dst
  | .next _ σ' ρ' => RunOk lay cenv M S fn lb lv.2 r0 r' σ' ρ' m rs ks dst
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
  {k : Lbl} {r0 r' : Nat} {ks : List Frame} {dst : Option Reg}

theorem runOk_lift {lb lb1 k : Lbl} {r1 : Nat} {m m1 : Mem} {rs rs1 : Regs} {Γ : Ctx} {σ' : World D}
    {ρ' : Env D Γ}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs1) (hle : r0 ≤ r1) (hc : ∀ x ∈ cenv, x < r0)
    (h' : RunOk lay cenv M S fn lb1 k r1 r' σ' ρ' m1 rs1 ks dst) :
    RunOk lay cenv M S fn lb k r0 r' σ' ρ' m rs ks dst := by
  obtain ⟨m', rs', hr, hP, hF2⟩ := h'
  exact ⟨m', rs', Reach.trans h hr, hP, fr_trans hF hF2 hle hc⟩

theorem runRet_lift {lb lb1 : Lbl} {r1 : Nat} {m m1 : Mem} {rs rs1 : Regs} {σ' : World D}
    {v : Option Val}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs1) (hle : r0 ≤ r1) (hc : ∀ x ∈ cenv, x < r0)
    (h' : RunRet lay cenv M S fn lb1 r1 σ' v m1 rs1 ks dst) :
    RunRet lay cenv M S fn lb r0 σ' v m rs ks dst := by
  obtain ⟨m', f', hr, h1, h2, h3, h4, h5, hF2⟩ := h'
  exact ⟨m', f', Reach.trans h hr, h1, h2, h3, h4, h5, fr_trans hF hF2 hle hc⟩

theorem runOk_mono {lb k : Lbl} {m : Mem} {rs : Regs} {r1 r2 : Nat} {Γ : Ctx} {σ' : World D}
    {ρ' : Env D Γ} (hle : r1 ≤ r2) (h' : RunOk lay cenv M S fn lb k r0 r1 σ' ρ' m rs ks dst) :
    RunOk lay cenv M S fn lb k r0 r2 σ' ρ' m rs ks dst := by
  obtain ⟨m', rs', hr, hP, hF⟩ := h'
  exact ⟨m', rs', hr, post_mono hP hle, hF⟩

/-- A run to the start of the continuation (its entry state `r1`), followed by an outcome of the
    continuation. -/
theorem outok_lift {lb lb1 : Lbl} {r1 : Nat} {m m1 : Mem} {rs rs1 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs1) (hle : r0 ≤ r1) (hc : ∀ x ∈ cenv, x < r0)
    {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l Γ, OutOk lay cenv lv M S fn lb1 k r1 r' m1 rs1 ks dst o →
      OutOk lay cenv lv M S fn lb k r0 r' m rs ks dst o
  | .ok σ' ρ', h' => runOk_lift h hF hle hc h'
  | .zurueck σ' v, h' => runRet_lift h hF hle hc h'
  | .why σ' r, h' => runRet_lift h hF hle hc h'
  | .leave _ σ' ρ', h' => runOk_lift h hF hle hc h'
  | .next _ σ' ρ', h' => runOk_lift h hF hle hc h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_lift {lb lb1 : Lbl} {r1 : Nat} {m m1 : Mem} {rs rs1 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs1, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs1) (hle : r0 ≤ r1) (hc : ∀ x ∈ cenv, x < r0)
    {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb1 r1 r' m1 rs1 ks dst o →
      EndOk lay cenv lv M S fn lb r0 r' m rs ks dst o
  | .zurueck σ' v, h' => runRet_lift h hF hle hc h'
  | .why σ' r, h' => runRet_lift h hF hle hc h'
  | .leave _ σ' ρ', h' => runOk_lift h hF hle hc h'
  | .next _ σ' ρ', h' => runOk_lift h hF hle hc h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-- A larger exit counter bound keeps an outcome. -/
theorem outok_mono {lb : Lbl} {m : Mem} {rs : Regs} {r1 r2 : Nat} (hle : r1 ≤ r2)
    {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l Γ, OutOk lay cenv lv M S fn lb k r0 r1 m rs ks dst o →
      OutOk lay cenv lv M S fn lb k r0 r2 m rs ks dst o
  | .ok σ' ρ', h' => runOk_mono hle h'
  | .zurueck σ' v, h' => h'
  | .why σ' r, h' => h'
  | .leave _ σ' ρ', h' => runOk_mono hle h'
  | .next _ σ' ρ', h' => runOk_mono hle h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_mono {lb : Lbl} {m : Mem} {rs : Regs} {r1 r2 : Nat} (hle : r1 ≤ r2)
    {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb r0 r1 m rs ks dst o →
      EndOk lay cenv lv M S fn lb r0 r2 m rs ks dst o
  | .zurueck σ' v, h' => h'
  | .why σ' r, h' => h'
  | .leave _ σ' ρ', h' => runOk_mono hle h'
  | .next _ σ' ρ', h' => runOk_mono hle h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-- An end block's outcome, read as the outcome of a block that never falls through. -/
theorem outok_of_endok {lb : Lbl} {m : Mem} {rs : Regs} {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l Γ, EndOk lay cenv lv M S fn lb r0 r' m rs ks dst o →
      OutOk lay cenv lv M S fn lb k r0 r' m rs ks dst o.zuAusgang
  | .zurueck σ' v, h' => h'
  | .why σ' r, h' => h'
  | .leave _ σ' ρ', h' => h'
  | .next _ σ' ρ', h' => h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ### A bound local going out of scope -/

theorem runOk_bind {lb lb1 : Lbl} {ri : Nat} {a : Reg} {τ : GTy} {m m1 : Mem} {rs rs3 : Regs} {Γ : Ctx}
    {σ' : World D} {ρ' : Env D (τ :: Γ)}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs3, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs3) (hcell : ∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b)
    (hca : ∀ x ∈ cenv, x < r0) (hri : r0 ≤ ri)
    (h' : RunOk lay (a :: cenv) M S fn lb1 k ri r' σ' ρ' m1 rs3 ks dst) :
    RunOk lay cenv M S fn lb k r0 r' σ' ρ'.tail m rs ks dst := by
  obtain ⟨m', rs', hr, hP, hF2⟩ := h'
  exact ⟨m', rs', Reach.trans h hr, post_tail ρ' hP, fr_bind hF hcell hca hri hF2⟩

theorem runRet_bind {lb lb1 : Lbl} {ri : Nat} {a : Reg} {m m1 : Mem} {rs rs3 : Regs} {σ' : World D}
    {v : Option Val}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs3, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs3) (hcell : ∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b)
    (hca : ∀ x ∈ cenv, x < r0) (hri : r0 ≤ ri)
    (h' : RunRet lay (a :: cenv) M S fn lb1 ri σ' v m1 rs3 ks dst) :
    RunRet lay cenv M S fn lb r0 σ' v m rs ks dst := by
  obtain ⟨m', f', hr, h1, h2, h3, h4, h5, hF2⟩ := h'
  exact ⟨m', f', Reach.trans h hr, h1, h2, h3, h4, h5, fr_bind hF hcell hca hri hF2⟩

/-- The scope of a block that bound a local ends: the run to the start of the scope, the frame of the
    binding step, and an outcome of the scope, give the outcome of the `let` seen from outside. -/
theorem outok_bind {lb lb1 : Lbl} {ri : Nat} {a : Reg} {τ : GTy} {m m1 : Mem} {rs rs3 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs3, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs3) (hcell : ∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b)
    (hca : ∀ x ∈ cenv, x < r0) (hri : r0 ≤ ri) {l : Bool} {Γ : Ctx} :
    ∀ o : Ausgang V l (τ :: Γ), OutOk lay (a :: cenv) lv M S fn lb1 k ri r' m1 rs3 ks dst o →
      OutOk lay cenv lv M S fn lb k r0 r' m rs ks dst o.schrumpf
  | .ok σ' ρ', h' => runOk_bind h hF hcell hca hri h'
  | .zurueck σ' v, h' => runRet_bind h hF hcell hca hri h'
  | .why σ' r, h' => runRet_bind h hF hcell hca hri h'
  | .leave _ σ' ρ', h' => runOk_bind h hF hcell hca hri h'
  | .next _ σ' ρ', h' => runOk_bind h hF hcell hca hri h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

theorem endok_bind {lb lb1 : Lbl} {ri : Nat} {a : Reg} {τ : GTy} {m m1 : Mem} {rs rs3 : Regs}
    (h : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, lb1, 0, rs3, dst⟩ ks))
    (hF : Fr lay cenv r0 m rs m1 rs3) (hcell : ∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b)
    (hca : ∀ x ∈ cenv, x < r0) (hri : r0 ≤ ri) {l : Bool} {Γ : Ctx} :
    ∀ o : EndAusgang V l (τ :: Γ), EndOk lay (a :: cenv) lv M S fn lb1 ri r' m1 rs3 ks dst o →
      EndOk lay cenv lv M S fn lb r0 r' m rs ks dst o.schrumpf
  | .zurueck σ' v, h' => runRet_bind h hF hcell hca hri h'
  | .why σ' r, h' => runRet_bind h hF hcell hca hri h'
  | .leave _ σ' ρ', h' => runOk_bind h hF hcell hca hri h'
  | .next _ σ' ρ', h' => runOk_bind h hF hcell hca hri h'
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

end Lemmas

end Gabbro.Code.Lower
