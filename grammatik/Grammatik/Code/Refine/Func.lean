import Grammatik.Code.Refine.StmtOk
import Grammatik.Code.Refine.Labels
import Grammatik.Code.Lower.Func

/-
  File:      Grammatik/Code/Refine/Func.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF A WHOLE FUNCTION (without calls).

    * `prologue_ok` -- the entry block builds the environment: the cells of the parameters hold
      the arguments, in the right order, above the argument registers;
    * `lowerFn_ok` -- **if the body of `f` runs to a `return` of `v` in machine G, the IR
      function `lowerFn` runs, from an entry frame whose registers carry the arguments, to a
      `ret` whose operand is the image of `v`.**

    * `lowerFn_nodup` -- the labels of a lowered function are distinct (proved from the lowering,
      `Labels.lean`; it is no hypothesis any more);
    * `reach_ret_fin` -- a frame at a `ret` with no caller finishes the run with that result;
    * `lowerFn_run` -- **the closing function theorem**: if the body of `f` returns `v` in
      machine G, the IR run from the entry frame reaches a `ret` of the image of `v` and leaves a
      memory that represents the returned world; with no caller it ends `fin m' (image of v)`.

  Named hypotheses (nothing is assumed beyond them): the layout (`LayoutOk`), the module holds
  the lowered function, the memory represents the world and has its global blocks, the argument
  registers carry the arguments (`ArgRegs`), and the body is in the call-free fragment (it is, if
  `lowerFn` succeeds).
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

/-- The labels of a lowered function are distinct: the entry block has label 0, the body uses 1 and
    the labels the counter hands out from 2. -/
theorem lowerFn_nodup (lay : Layout D) (P : Programm D) (f : D.Fn) (name : String) (func : Func)
    (hf : lowerFn lay P f name = some func) : (func.blks.map Block.lbl).Nodup := by
  unfold lowerFn at hf
  rcases hp : prologue (D.params f) 0 (D.params f).length with _ | ⟨pc, cenv, r⟩
  · simp [hp] at hf
  simp only [hp] at hf
  rcases hl : lowerEnd lay cenv (P.rumpf f) 1 ⟨r, 2⟩ with _ | ⟨blks, s'⟩
  · simp [hl] at hf
  simp only [hl, Option.some.injEq] at hf
  subst hf
  obtain ⟨m, n, a⟩ := lowerEnd_lbl lay cenv (P.rumpf f) 1 ⟨r, 2⟩ s' blks (by show (1 : Nat) < 2; omega) hl
  refine lw_head (b := ⟨0, [], pc, .jmp 1⟩) (a1 := fun x => 1 ≤ x) rfl (fun x hx => by show 0 < x; omega) n ?_
  intro x hx
  have : x.nl = 1 ∨ (2 ≤ x.nl ∧ x.nl < s'.l) := a x hx
  show 1 ≤ x.nl
  omega

/-- A frame at a `ret` with no caller finishes the run with that result. -/
theorem reach_ret_fin {M : Modl} {S : Sees} {f : Frame} {vo : Option Val} (h : RetAt M f vo)
    (m : Mem) : Reach M S (.run m f []) (.fin m vo) := by
  obtain ⟨blk, hb, hl, h2⟩ := h
  rcases h2 with ⟨ht, rfl⟩ | ⟨o, v, ht, rfl, hv⟩
  · exact Reach.one (step_term ⟨hb, hl, ht⟩ (by simp [stepTerm, finish]))
  · exact Reach.one (step_term ⟨hb, hl, ht⟩ (by simp [stepTerm, hv, finish]))

/-- **The closing function theorem.** The module holds the lowered function `f` as function number
    `fn`. If its body returns `v` in machine G (from a world that the memory represents, with the
    arguments in registers `0 ..`), the IR run from the entry frame reaches a `ret` of the image of
    `v`, and the memory it leaves represents the world the body returned. -/
theorem lowerFn_run (lay : Layout D) (hL : LayoutOk lay) (P : Programm D) (f : D.Fn) (name : String)
    (func : Func) (hf : lowerFn lay P f name = some func) (M : Modl) (S : Sees) (fn : Nat)
    (hfn : M.funs[fn]? = some func) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D (D.params f)) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hW : WfL lay m) (hA : ArgRegs lay rs 0 ρ) (σ' : World D) (v : ErgVal D (D.erg f))
    (hex : execEnd (V := vertragVon D f) O passes R (P.rumpf f) σ ρ = Gabbro.Grammatik.EndAusgang.zurueck σ' v) :
    ∃ m' f', Reach M S (.run m ⟨fn, 0, 0, rs, dst⟩ ks) (.run m' f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
      RetAt M f' (ergImg lay (D.erg f) v) ∧ Rep lay σ' m' ∧ WfL lay m' := by
  have hnd := lowerFn_nodup lay P f name func hf
  unfold lowerFn at hf
  rcases hp : prologue (D.params f) 0 (D.params f).length with _ | ⟨pc, cenv, r⟩
  · simp [hp] at hf
  simp only [hp] at hf
  rcases hl : lowerEnd lay cenv (P.rumpf f) 1 ⟨r, 2⟩ with _ | ⟨blks, s'⟩
  · simp [hl] at hf
  simp only [hl, Option.some.injEq] at hf
  subst hf
  have hM : ∀ b ∈ (⟨0, [], pc, .jmp 1⟩ :: blks : List Block), M.blk fn b.lbl = some b :=
    fun b hb => blk_of_nodup hfn hnd hb
  have hM2 : InM M fn blks := fun b hb => hM b (List.mem_cons_of_mem _ hb)
  have hb0 := hM _ (List.mem_cons_self ..)
  have SS := lowerEnd_shape lay cenv (P.rumpf f) 1 ⟨r, 2⟩ s' blks hl
  obtain ⟨bk, hbk, hkp⟩ := kok_of_shape SS hM2
  obtain ⟨m1, rs1, hs1, hR1, hW1, hE1, hr1, hag1, hbd1⟩ :=
    prologue_ok lay ρ 0 (D.params f).length hp hR hW hA (by omega)
  have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk hkp hs1
  obtain ⟨m', f', hr2, hf1, hf2, hret, hR', hW'⟩ := lowerEnd_ok lay hL cenv O passes R (P.rumpf f) 1 ⟨r, 2⟩ s'
    blks hl M S fn hM2 σ ρ m1 rs1 ks dst hR1 hE1 hW1 hbd1 σ' v hex
  exact ⟨m', f', Reach.trans hreach hr2, hf1, hf2, hret, hR', hW'⟩

/-- With no caller, the run of the lowered function ends with the image of the returned value. -/
theorem lowerFn_runs (lay : Layout D) (hL : LayoutOk lay) (P : Programm D) (f : D.Fn) (name : String)
    (func : Func) (hf : lowerFn lay P f name = some func) (M : Modl) (S : Sees) (fn : Nat)
    (hfn : M.funs[fn]? = some func) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D (D.params f)) (m : Mem) (rs : Regs)
    (hR : Rep lay σ m) (hW : WfL lay m) (hA : ArgRegs lay rs 0 ρ) (σ' : World D) (v : ErgVal D (D.erg f))
    (hex : execEnd (V := vertragVon D f) O passes R (P.rumpf f) σ ρ = Gabbro.Grammatik.EndAusgang.zurueck σ' v) :
    ∃ m', Runs M S (.run m ⟨fn, 0, 0, rs, none⟩ []) m' (ergImg lay (D.erg f) v) ∧ Rep lay σ' m' ∧ WfL lay m' := by
  obtain ⟨m', f', hr, _, _, hret, hR', hW'⟩ := lowerFn_run lay hL P f name func hf M S fn hfn O passes R σ ρ m rs [] none
    hR hW hA σ' v hex
  exact ⟨m', Reach.trans hr (reach_ret_fin hret m'), hR', hW'⟩

end Gabbro.Code.Lower
