import Grammatik.Code.Model.Need

/-
  File:      Grammatik/Code/Gate/Gate.lean
  Subject:   TRACK L -- A USER GATE IN `Code`: a call of an external function with a CONTRACT, the
             step it adds, and what a CPU model must provide for a user-declared trap.
             PLAN-HARDWARE.md section 16.6 (L1/L2, the `Code` side).

  A `syscall` item of the user's source (with the proposed `trap` clause, `Hardware/Tor/Abi.lean`) is
  lowered, for the ISA-neutral `Code`, to a CALL of a function number past the module's own functions:
  `Instr.call d f args` with `f >= M.funs.length` names gate `f - M.funs.length` of a gate table. No
  instruction, no register and no number appears in `Code`: those are the user's declaration, consumed
  by the backend (the trap text is handed to the assembler unread).

    * `GateSpec`   -- the CONTRACT as a precondition (`requires`) and a relation: memory and
                      arguments before, memory and answer after. It is machine G's `Ax` contract (`ensures`, the write frame) read
                      over `Code` memory; nothing else.
    * `GateStep`   -- the step a call of a gate takes: any outcome the contract allows. `Step` is STUCK
                      there (`step_stuck_am_tor`), so `StepG := Step or GateStep` is a conservative
                      extension, and for a module with no gate call it IS `Step`
                      (`stepG_gdw_step`, `reachG_gdw_reach`): programs that do not use gates keep their
                      meaning.
    * `GateNeed`   -- THE OBLIGATIONS ON A CPU MODEL for user-declared traps, in the style of
                      `Model/Need.lean` and `Conc/MaskNeed.lean`: a CPU state type `Mach`, the
                      relation `Rel`, and for every gate a relation `Trap k d vs x y` ("the CPU runs
                      the user's trap sequence of gate `k`, delivering the answer to local `d`, from
                      `x` to `y`"). The two obligations are exactly the gate's NAMED ASSUMPTION
                      (the kernel keeps its contract): the sequence runs (`ausfuehrbar`) and every
                      way it can end is an outcome the contract allows (`erlaubt`).
    * `gate_verfeinert` -- the refinement: a CPU run of the trap from a state holding a `Code`
                      configuration corresponds to a `GateStep` of that configuration, and the result
                      state holds the result configuration.

  NOT in `GateNeed`: the register convention, the trap text, the clobbers -- those are the user's data
  and the backend's lowering (an honest `clobbers` list is part of the gate's assumption). Nothing here
  names an instruction of any ISA.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Code

variable [Conf]

/-! ## 1. The contract of a gate and its step -/

/-- A gate seen from `Code`: its precondition (the gate's `requires`, over memory and the argument
    values) and the relation between the world before (memory, arguments) and after (memory,
    answer). -/
structure GateSpec where
  pre : Mem → List Val → Prop
  post : Mem → List Val → Mem → Option Val → Prop

/-- The gates of a module: gate `k` is function number `M.funs.length + k`. -/
abbrev GateTab := List GateSpec

/-- Deliver the answer to the caller's local (a call that wants no result ignores it). -/
def setAns (d : Option Reg) (a : Option Val) (rs : Regs) : Regs :=
  match d, a with
  | some r, some v => rs.set r v
  | _, _ => rs

/-- **The gate step**: the next instruction is a call of a function number past the module's own;
    the arguments evaluate and meet the precondition; the contract allows `(m', ans)`; a call that wants a result gets one. -/
inductive GateStep (M : Modl) (G : GateTab) : Cfg → Cfg → Prop where
  | call {m : Mem} {f : Frame} {ks : List Frame} {blk : Block} {d : Option Reg} {fi : Nat}
      {args : List Opd} {vs : List Val} {gs : GateSpec} {m' : Mem} {ans : Option Val}
      (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some (.call d fi args))
      (hge : M.funs.length ≤ fi) (hgs : G[fi - M.funs.length]? = some gs)
      (hv : args.mapM (Opd.ev f.regs) = some vs) (hl : gs.pre m vs)
      (hp : gs.post m vs m' ans) (hd : ∀ r, d = some r → ans.isSome = true) :
      GateStep M G (.run m f ks)
        (.run m' { f with pc := f.pc + 1, regs := setAns d ans f.regs } ks)

/-- The step relation with gates: a plain step, or a gate step. -/
def StepG (M : Modl) (S : Sees) (G : GateTab) (c c' : Cfg) : Prop :=
  Step M S c c' ∨ GateStep M G c c'

/-- Reachability with gates. -/
inductive ReachG (M : Modl) (S : Sees) (G : GateTab) : Cfg → Cfg → Prop where
  | refl (c : Cfg) : ReachG M S G c c
  | step (c c' c'' : Cfg) : StepG M S G c c' → ReachG M S G c' c'' → ReachG M S G c c''

/-! ## 2. A module without gate calls keeps its meaning -/

/-- No call of the module names a function past its own: the module uses no gate. -/
def GateFrei (M : Modl) : Prop :=
  ∀ fn ∈ M.funs, ∀ b ∈ fn.blks, ∀ i ∈ b.body, ∀ d fi args, i = .call d fi args → fi < M.funs.length

/-- The block `M.blk` finds belongs to its function. -/
theorem blk_mem {M : Modl} {f : Nat} {l : Lbl} {blk : Block} (h : M.blk f l = some blk) :
    ∃ fn ∈ M.funs, blk ∈ fn.blks := by
  unfold Modl.blk at h
  cases hf : M.funs[f]? with
  | none => simp [hf] at h
  | some fn =>
      simp only [hf, Option.bind_some] at h
      exact ⟨fn, List.mem_of_getElem? hf, List.mem_of_find?_eq_some h⟩

/-- **A gate step needs a gate call**: in a gate-free module no gate step exists. -/
theorem gateStep_false {M : Modl} {G : GateTab} (hM : GateFrei M) {c c' : Cfg}
    (h : GateStep M G c c') : False := by
  cases h with
  | call hb hi hge hgs hv hl hp hd =>
      obtain ⟨fn, hfn, hbm⟩ := blk_mem hb
      have hmem := List.mem_of_getElem? hi
      have := hM fn hfn _ hbm _ hmem _ _ _ rfl
      omega

/-- In a gate-free module `StepG` is `Step`. -/
theorem stepG_gdw_step {M : Modl} {S : Sees} {G : GateTab} (hM : GateFrei M) (c c' : Cfg) :
    StepG M S G c c' ↔ Step M S c c' := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact (gateStep_false hM h).elim
  · exact Or.inl

/-- In a gate-free module `ReachG` is `Reach`. -/
theorem reachG_gdw_reach {M : Modl} {S : Sees} {G : GateTab} (hM : GateFrei M) (c c' : Cfg) :
    ReachG M S G c c' ↔ Reach M S c c' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step a b d hs _ ih => exact .step a b d ((stepG_gdw_step hM a b).1 hs) ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step a b d hs _ ih => exact .step a b d ((stepG_gdw_step hM a b).2 hs) ih

/-- **`Step` is stuck at a gate call**: the plain semantics has no answer for a function it does not
    have -- the gate step is the only way past. -/
theorem step_stuck_am_tor {M : Modl} {O : Oracle} {m : Mem} {f : Frame} {ks : List Frame}
    {blk : Block} {d : Option Reg} {fi : Nat} {args : List Opd}
    (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some (.call d fi args))
    (hge : M.funs.length ≤ fi) : step M O (.run m f ks) = none := by
  simp only [step, hb, hi]
  cases hv : args.mapM (Opd.ev f.regs) with
  | none => rfl
  | some vs =>
      simp only
      have : M.funs[fi]? = none := List.getElem?_eq_none hge
      simp [Frame.callee, this]

/-! ## 3. What a CPU model must provide for user-declared traps -/

/-- A call site is well formed for a gate: a call that wants a result is a call of a gate that answers
    (the lowering never asks a non-answering gate, `exit` for one, for a value). -/
def WohlAnruf (gs : GateSpec) (d : Option Reg) (m : Mem) (vs : List Val) : Prop :=
  ∀ r, d = some r → ∀ m' a, gs.post m vs m' a → a.isSome = true

/-- **The obligations on the CPU side for the user's gates.** `Trap k d vs x y`: the CPU runs the
    machine code of gate `k` (the user's trap text with the register loads the ABI declares),
    delivering the answer to local `d`, with the argument values `vs`, from `x` to `y`. Both fields
    are the gate's named assumption: the environment keeps the contract. -/
structure GateNeed (Mach : Type) (Rel : Mem → Regs → Mach → Prop) (G : GateTab)
    (Trap : Nat → Option Reg → List Val → Mach → Mach → Prop) : Prop where
  /-- The trap sequence executes (the instruction exists and is legal in the program's mode). -/
  ausfuehrbar : ∀ k gs d vs m rs x, G[k]? = some gs → gs.pre m vs → WohlAnruf gs d m vs →
    Rel m rs x → ∃ y, Trap k d vs x y
  /-- Every way it can end is an outcome the contract allows, delivered as declared. -/
  erlaubt : ∀ k gs d vs m rs x y, G[k]? = some gs → gs.pre m vs → WohlAnruf gs d m vs →
    Rel m rs x → Trap k d vs x y → ∃ m' ans, gs.post m vs m' ans ∧ Rel m' (setAns d ans rs) y

/-- **The refinement.** The CPU runs the trap of the gate the configuration's next instruction calls;
    then the configuration has a gate step, and the CPU state holds its result. -/
theorem gate_verfeinert {Mach : Type} {Rel : Mem → Regs → Mach → Prop} {G : GateTab}
    {Trap : Nat → Option Reg → List Val → Mach → Mach → Prop} (N : GateNeed Mach Rel G Trap)
    {M : Modl} {m : Mem} {f : Frame} {ks : List Frame} {blk : Block} {d : Option Reg} {fi : Nat}
    {args : List Opd} {vs : List Val} {gs : GateSpec} {x y : Mach}
    (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some (.call d fi args))
    (hge : M.funs.length ≤ fi) (hgs : G[fi - M.funs.length]? = some gs)
    (hv : args.mapM (Opd.ev f.regs) = some vs) (hl : gs.pre m vs) (hw : WohlAnruf gs d m vs)
    (hrel : Rel m f.regs x) (hy : Trap (fi - M.funs.length) d vs x y) :
    ∃ m' g, GateStep M G (.run m f ks) (.run m' g ks) ∧ Rel m' g.regs y := by
  obtain ⟨m', ans, hp, hr⟩ := N.erlaubt _ gs d vs m f.regs x y hgs hl hw hrel hy
  exact ⟨m', { f with pc := f.pc + 1, regs := setAns d ans f.regs },
    GateStep.call hb hi hge hgs hv hl hp (fun r hr' => hw r hr' m' ans hp), hr⟩

/-- The CPU can always run the trap of a gate call whose arguments evaluate. -/
theorem gate_laeuft {Mach : Type} {Rel : Mem → Regs → Mach → Prop} {G : GateTab}
    {Trap : Nat → Option Reg → List Val → Mach → Mach → Prop} (N : GateNeed Mach Rel G Trap)
    {k : Nat} {gs : GateSpec} {d : Option Reg} {vs : List Val} {m : Mem} {rs : Regs} {x : Mach}
    (hgs : G[k]? = some gs) (hl : gs.pre m vs) (hw : WohlAnruf gs d m vs) (hrel : Rel m rs x) :
    ∃ y, Trap k d vs x y :=
  N.ausfuehrbar k gs d vs m rs x hgs hl hw hrel

end Gabbro.Code
