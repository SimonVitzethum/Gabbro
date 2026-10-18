import Grammatik.Code.Refine.Post

/-
  File:      Grammatik/Code/Refine/Stmt.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT THEOREM FOR STATEMENTS, BLOCKS AND END BLOCKS.

  `lowerS_ok`, `lowerB_ok`, `lowerEnd_ok`: if the lowering of `s` (a statement, a block, an end
  block) to IR blocks succeeds, and the IR module holds those blocks (`hM`: the labels find them,
  and the target label `k` finds a block without phis), then in any memory that represents the
  world (`Rep`) with the locals in their cells (`EnvRep`), the memory having its global blocks
  (`WfL`) and the free registers above every variable's:
    * if `execStmt` (resp. `execBlock`) ends normally in `σ'`, `ρ'`, the IR run from the entry
      label reaches label `k` (`Reach`) in a memory that represents `σ'` with `ρ'` in the cells
      (`Post`);
    * if it ends in a `return` of `v`, the IR run reaches a `ret` whose operand is the image of `v`
      (`RetAt`).
  `R` (the semantics of calls) is arbitrary: the fragment has no call, so no case uses it. The
  other outcomes (`why`, `leave`, `next`, `logik`, `hardware`) are not related: the statement is
  an implication from the source run, and a source run that stops there says nothing.
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

theorem inM_sub {M : Modl} {fn : Nat} {b1 b2 : List Block} (h : InM M fn b1) (hs : ∀ b ∈ b2, b ∈ b1) :
    InM M fn b2 := fun b hb => h b (hs b hb)

/-- The entry block of a lowering is found, and has no phis. -/
theorem kok_of_shape {M : Modl} {fn : Nat} {lb : Lbl} {st st' : St} {blks : List Block}
    (hS : Shape lb st st' blks) (hM : InM M fn blks) : KOk M fn lb := by
  obtain ⟨⟨b, bs, hb, hl⟩, hp, _⟩ := hS
  have h1 := hM b (by rw [hb]; simp)
  rw [hl] at h1
  exact ⟨b, h1, hp b (by rw [hb]; simp)⟩

end Gabbro.Code.Lower
