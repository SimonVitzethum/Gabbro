import Grammatik.Code.Refine.Stmt
import Grammatik.Code.Lower.Func

/-
  File:      Grammatik/Code/Refine/CallDef.lean
  Subject:   TRACK L, PHASE L1 -- CALLS: what a call needs of the callee, and the run of a call.

    * `FnOk` -- the module holds, for every function `f` of the program, the IR function number
      `lay.fno f` with `f`'s IR parameters and an entry block (label 0) without phis, and every
      parameter type is one the lowering carries (`supp`);
    * `CallRef` -- THE ABSTRACT FRAME INVARIANT of a call: the callees refine the source meaning `R`
      of a call. If `R f σ ρ = ok σ' v`, then the IR function of `f`, entered with the images of the
      arguments in its first registers, runs (whatever the frames below it) to a `ret` of the image of
      `v`, leaves a memory that represents `σ'`, and keeps the caller's memory (`Keep`: what existed
      and is no table or global is as it was);
    * `call_run_none`, `call_run_some` -- a lowered call statement, from the arguments evaluated: the
      caller frame advances past the `call` instruction (the result lands in the destination
      register, if there is one), the memory represents the world the callee returned.

  `CallRef` is a hypothesis of the statement refinement; `lowerFn_callref` (in `Func.lean`) proves it
  for the source meaning of calls, `rufAt`, by induction on the recursion depth.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag ErgVal RufAusgang)

variable {D : Deklaration}

/-- The register images of the arguments, in order. -/
def argImgs (lay : Layout D) : {Γ : Ctx} → Env D Γ → List Val
  | _, .nil => []
  | _, .cons (τ := τ) v ρ => encR lay τ v :: argImgs lay ρ

/-- Register `i + j` holds the image of argument `j`. -/
def ArgRegs (lay : Layout D) (rs : Regs) : {Γ : Ctx} → Nat → Env D Γ → Prop
  | _, _, .nil => True
  | _, i, .cons (τ := τ) v ρ => rs i = some (encR lay τ v) ∧ ArgRegs lay rs (i + 1) ρ

/-- The module holds the IR function of every function of the program. -/
def FnOk (lay : Layout D) (M : Modl) : Prop :=
  ∀ f : D.Fn, (∀ τ ∈ D.params f, supp τ = true) ∧
    ∃ func blk, M.funs[lay.fno f]? = some func ∧ func.params = irParams (D.params f) ∧
      func.blks.head? = some blk ∧ blk.lbl = 0 ∧ blk.phis = []

/-- **The callees refine `R`** (the abstract frame invariant of a call). -/
def CallRef (lay : Layout D) (M : Modl) (S : Sees)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f)),
    R f σ ρ = RufAusgang.ok σ' v →
    ∀ (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
      Rep lay σ m → WfL lay m → ArgRegs lay rs 0 ρ →
      ∃ m' f', Reach M S (.run m ⟨lay.fno f, 0, 0, rs, dst⟩ ks) (.run m' f' ks) ∧
        f'.fn = lay.fno f ∧ f'.dst = dst ∧ RetAt M f' (ergImg lay (D.erg f) v) ∧
        Rep lay σ' m' ∧ WfL lay m' ∧ Keep lay m m'

/-! ## The callee frame -/

/-- The IR parameters from register `n` on. -/
def irParamsFrom (n : Nat) (ps : List GTy) : List Param :=
  (ps.zipIdx n).map fun (τ, i) => ⟨regTy τ, i⟩

theorem irParams_eq (ps : List GTy) : irParams ps = irParamsFrom 0 ps := rfl

theorem irParamsFrom_len (n : Nat) (ps : List GTy) : (irParamsFrom n ps).length = ps.length := by
  simp [irParamsFrom]

theorem irParamsFrom_ty (n : Nat) (ps : List GTy) : (irParamsFrom n ps).map Param.t = ps.map regTy := by
  induction ps generalizing n with
  | nil => rfl
  | cons τ ps ih => simp [irParamsFrom, List.zipIdx_cons] at ih ⊢; exact ih (n + 1)

theorem argImgs_len (lay : Layout D) : ∀ {Γ : Ctx} (ρ : Env D Γ), (argImgs lay ρ).length = Γ.length
  | _, .nil => rfl
  | _, .cons v ρ => by simp [argImgs, argImgs_len lay ρ]

theorem argImgs_ty (lay : Layout D) :
    ∀ {Γ : Ctx} (ρ : Env D Γ), (∀ τ ∈ Γ, supp τ = true) → (argImgs lay ρ).map Val.ty = Γ.map regTy
  | _, .nil, _ => rfl
  | _, .cons (τ := τ) v ρ, h => by
      simp only [argImgs, List.map_cons, List.cons.injEq]
      refine ⟨?_, argImgs_ty lay ρ (fun σ hσ => h σ (List.mem_cons_of_mem _ hσ))⟩
      have hs := h τ (List.mem_cons_self ..)
      cases τ <;> simp_all [supp, encR, regTy, Val.ty, Val.ofInt, Val.bool]
      rename_i n rw
      cases D.tabNr n <;> simp [Val.ty]

theorem foldl_set_ne (ps : List (Param × Val)) (rs : Regs) (x : Reg) (h : ∀ p ∈ ps, p.1.r ≠ x) :
    ps.foldl (fun rs pv => rs.set pv.1.r pv.2) rs x = rs x := by
  induction ps generalizing rs with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      exact regs_set_ne rs p.1.r x p.2 (fun e => h p (List.mem_cons_self ..) e.symm)

theorem callee_regs (lay : Layout D) :
    ∀ {Γ : Ctx} (ρ : Env D Γ) (n : Nat) (rs0 : Regs),
      ArgRegs lay (((irParamsFrom n Γ).zip (argImgs lay ρ)).foldl (fun rs pv => rs.set pv.1.r pv.2) rs0) n ρ
  | _, .nil, n, rs0 => trivial
  | _, .cons (τ := τ) (Γ := Γ') v ρ, n, rs0 => by
      simp only [irParamsFrom, List.zipIdx_cons, List.map_cons, argImgs, List.zip_cons_cons, List.foldl_cons]
      refine ⟨?_, ?_⟩
      · rw [foldl_set_ne]
        · exact regs_set_same _ _ _
        · intro p hp
          obtain ⟨pp, vv⟩ := p
          have h1 := (List.of_mem_zip hp).1
          obtain ⟨⟨τ', i⟩, hi, hpp⟩ := List.mem_map.mp h1
          have h2 := List.mem_zipIdx hi
          rw [← hpp]
          show i ≠ n
          omega
      · exact callee_regs lay ρ (n + 1) _

/-- The callee frame of a call with these arguments. -/
theorem callee_frame {lay : Layout D} {M : Modl} (hFn : FnOk lay M) (f : D.Fn) (ρ : Env D (D.params f))
    (d : Option Reg) :
    ∃ g, Frame.callee M (lay.fno f) (argImgs lay ρ) d = some g ∧ g.fn = lay.fno f ∧ g.lbl = 0 ∧
      g.pc = 0 ∧ g.dst = d ∧ ArgRegs lay g.regs 0 ρ := by
  obtain ⟨hsupp, func, blk, hfun, hpar, hhead, hlbl, hphi⟩ := hFn f
  have hent : M.entry (lay.fno f) = some blk := by simp [Modl.entry, hfun, hhead]
  have hlen : (argImgs lay ρ).length = func.params.length := by
    rw [argImgs_len, hpar, irParams_eq, irParamsFrom_len]
  have hty : func.params.map Param.t = (argImgs lay ρ).map Val.ty := by
    rw [hpar, irParams_eq, irParamsFrom_ty, argImgs_ty lay ρ hsupp]
  have hph : blk.phis.isEmpty = true := by simp [hphi]
  have hc : Frame.callee M (lay.fno f) (argImgs lay ρ) d = some
      { fn := lay.fno f, lbl := blk.lbl, pc := 0, dst := d,
        regs := (func.params.zip (argImgs lay ρ)).foldl (fun rs pv => rs.set pv.1.r pv.2) (fun _ => none) } := by
    simp only [Frame.callee, hfun, hent]
    rw [if_pos ⟨hlen, hty, hph⟩]
  refine ⟨_, hc, rfl, hlbl, rfl, rfl, ?_⟩
  show ArgRegs lay ((func.params.zip (argImgs lay ρ)).foldl (fun rs pv => rs.set pv.1.r pv.2) (fun _ => none)) 0 ρ
  rw [hpar, irParams_eq]
  exact callee_regs lay ρ 0 _

end Gabbro.Code.Lower
