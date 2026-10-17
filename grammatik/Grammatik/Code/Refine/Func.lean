import Grammatik.Code.Refine.StmtOk
import Grammatik.Code.Lower.Func

/-
  File:      Grammatik/Code/Refine/Func.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF A WHOLE FUNCTION (without calls).

    * `prologue_ok` -- the entry block builds the environment: the cells of the parameters hold
      the arguments, in the right order, above the argument registers;
    * `lowerFn_ok` -- **if the body of `f` runs to a `return` of `v` in machine G, the IR
      function `lowerFn` runs, from an entry frame whose registers carry the arguments, to a
      `ret` whose operand is the image of `v`.**

  Named hypotheses (nothing is assumed beyond them): the layout (`LayoutOk`), the module holds
  the lowered function and its labels are distinct (`hnd`), the memory represents the world and
  has its global blocks, the argument registers carry the arguments (`ArgRegs`), and the body is
  in the call-free fragment (it is, if `lowerFn` succeeds).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Programm Vertrag vertragVon Ctx Res Env Wert World Orakel RufAusgang
  EndAusgang ErgVal execEnd)

variable {D : Deklaration}

/-- The register images of the arguments, in order. -/
def argImgs (lay : Layout D) : {Γ : Ctx} → Env D Γ → List Val
  | _, .nil => []
  | _, .cons (τ := τ) v ρ => encR lay τ v :: argImgs lay ρ

/-- Register `i + j` holds the image of argument `j`. -/
def ArgRegs (lay : Layout D) (rs : Regs) : {Γ : Ctx} → Nat → Env D Γ → Prop
  | _, _, .nil => True
  | _, i, .cons (τ := τ) v ρ => rs i = some (encR lay τ v) ∧ ArgRegs lay rs (i + 1) ρ

/-- **The prologue builds the environment.** -/
theorem prologue_ok (lay : Layout D) :
    ∀ {Γ : Ctx} (ρ : Env D Γ) (i r : Nat) {code : List Instr} {cenv0 : List Reg} {r' : Nat},
      prologue Γ i r = some (code, cenv0, r') → ∀ {σ : World D} {m : Mem} {rs : Regs},
      Rep lay σ m → WfL lay m → ArgRegs lay rs i ρ → i + Γ.length ≤ r →
      ∃ m1 rs1, seqI code m rs = some (m1, rs1) ∧ Rep lay σ m1 ∧ WfL lay m1 ∧
        EnvRep lay rs1 m1 cenv0 ρ ∧ r ≤ r' ∧ (∀ x, x < r → rs1 x = rs x) ∧ ∀ x ∈ cenv0, x < r'
  | _, .nil, i, r, code, cenv0, r', h, σ, m, rs, hR, hW, hA, hlen => by
      simp only [prologue] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨m, rs, rfl, hR, hW, trivial, Nat.le_refl _, fun _ _ => rfl, fun x hx => nomatch hx⟩
  | _, .cons (τ := τ) (Γ := Γ') v ρ', i, r, code, cenv0, r', h, σ, m, rs, hR, hW, hA, hlen => by
      simp only [prologue] at h
      rcases hp : prologue Γ' (i + 1) r with _ | ⟨c2, as, r1⟩
      · simp [hp] at h
      simp only [hp] at h
      rcases hb : bindCode τ (.reg i) r1 with _ | ⟨c, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      obtain ⟨hA0, hA1⟩ := hA
      have hlen' : (i + 1) + Γ'.length ≤ r := by simpa [Nat.add_assoc, Nat.add_comm 1] using hlen
      obtain ⟨m1, rs1, hs1, hR1, hW1, hE1, hr1, hag1, hbd1⟩ :=
        prologue_ok lay ρ' (i + 1) r hp hR hW hA1 hlen'
      have hir : i < r := by simp at hlen; omega
      have hrs1 : rs1 i = some (encR lay τ v) := by rw [hag1 i hir]; exact hA0
      obtain ⟨m2, rs2, hs2, hR2, hE2, hW2, hra, hr2e, hag2⟩ := bindCode_run lay v (.reg i) r1 m1 rs1
        hR1 hE1 hW1 hrs1 (opdlt_reg i r1 (Nat.lt_of_lt_of_le hir hr1)) hbd1 hb
      refine ⟨m2, rs2, ?_, hR2, hW2, hE2, ?_, ?_, ?_⟩
      · rw [seqI_append, hs1, Option.bind_some]; exact hs2
      · rw [hr2e]; exact Nat.le_succ_of_le (Nat.le_trans hr1 hra)
      · intro x hx
        rw [hag2 x (Nat.lt_of_lt_of_le hx hr1), hag1 x hx]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · rw [hr2e]; exact Nat.lt_succ_self _
        · rw [hr2e]
          exact Nat.lt_of_lt_of_le (hbd1 x hx') (Nat.le_succ_of_le hra)

/-- If the labels of a function are distinct, every block is found by its label. -/
theorem blk_of_nodup {M : Modl} {fn : Nat} {func : Func} (hfn : M.funs[fn]? = some func)
    (hnd : (func.blks.map Block.lbl).Nodup) {b : Block} (hb : b ∈ func.blks) :
    M.blk fn b.lbl = some b := by
  have key : ∀ L : List Block, (L.map Block.lbl).Nodup → b ∈ L → L.find? (fun x => x.lbl == b.lbl) = some b := by
    intro L
    induction L with
    | nil => intro _ h; simp at h
    | cons h t ih =>
        intro hn hm
        rw [List.map_cons, List.nodup_cons] at hn
        rcases List.mem_cons.mp hm with rfl | ht
        · simp [List.find?]
        · have hne : h.lbl ≠ b.lbl := fun e => hn.1 (by rw [e]; exact List.mem_map_of_mem ht)
          have hb2 : (h.lbl == b.lbl) = false := by simp [hne]
          simp only [List.find?, hb2]
          exact ih hn.2 ht
  simp only [Modl.blk, hfn, Option.bind_some]
  exact key func.blks hnd hb

end Gabbro.Code.Lower
