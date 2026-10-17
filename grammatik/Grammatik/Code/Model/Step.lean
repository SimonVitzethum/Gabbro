import Grammatik.Code.Model.Semantics

/-
  File:      Grammatik/Code/Model/Step.lean
  Subject:   TRACK L -- THE STEP FUNCTION, THE ORACLE, THE STEP RELATION, `Reach`.

  The design is in the header of `Semantics.lean`. This file adds control flow (phis, jumps,
  `br`, `brc`, `sw`, `ret`), calls with a stack of frames and an ABSTRACT frame (the arguments
  are the callee's first registers, the result goes to one register of the caller; no ABI
  numbers), the one oracle-driven instruction form (`aload`, the weak-memory interface), the
  legality of an oracle, and the relation.
-/

namespace Gabbro.Code

variable [Conf]

open Gabbro.Grammatik.Gleitkomma

/-! ## 1. Entering a block, calling a function -/

/-- Jump to block `l` of the running function: the phis of `l` read the registers of the
    jumping block simultaneously (the incoming edge is `f.lbl`). -/
def Frame.enter (M : Modl) (f : Frame) (l : Lbl) : Option Frame :=
  match M.blk f.fn l with
  | none => none
  | some blk =>
      match blk.phis.mapM (fun p =>
          ((p.ins.lookup f.lbl).bind (Opd.ev f.regs)).bind fun v =>
            if v.ty = p.t then some (p.d, v) else none) with
      | none => none
      | some vs =>
          some { f with lbl := l, pc := 0,
                        regs := vs.foldl (fun rs dv => rs.set dv.1 dv.2) f.regs }

/-- The frame a call of function `fi` with arguments `vs` starts in (result wanted in `d`).
    The entry block has no phis. -/
def Frame.callee (M : Modl) (fi : Nat) (vs : List Val) (d : Option Reg) : Option Frame :=
  match M.funs[fi]?, M.entry fi with
  | some fn, some blk =>
      if vs.length = fn.params.length ∧ (fn.params.map Param.t) = vs.map Val.ty
          ∧ blk.phis.isEmpty = true then
        some { fn := fi, lbl := blk.lbl, pc := 0, dst := d,
               regs := (fn.params.zip vs).foldl (fun rs pv => rs.set pv.1.r pv.2) (fun _ => none) }
      else none
  | _, _ => none

/-! ## 2. Leaving a function -/

/-- `ret`: hand the result to the caller (or finish the run). -/
def finish (m : Mem) (f : Frame) (ks : List Frame) (v : Option Val) : Option Cfg :=
  match ks with
  | [] => some (.fin m v)
  | k :: ks' =>
      match f.dst with
      | none => some (.run m k.adv ks')
      | some r =>
          match v with
          | some v => some (.run m (k.adv.setr r v) ks')
          | none => none

/-! ## 3. The oracle and the step function -/

/-- The one question `step` does not decide by itself. -/
structure Oracle where
  /-- What an atomic load of type `t` at block `b`, offset `o` in order `ord` returns. -/
  ld : Mem → Nat → Int → Ty → Order → Option Val

/-- The terminator step. -/
def stepTerm (M : Modl) : Term → Mem → Frame → List Frame → Option Cfg
  | .jmp l, m, f, ks => (f.enter M l).map fun g => .run m g ks
  | .br c t e, m, f, ks =>
      match c.ev f.regs with
      | some (.int 1 x) => (f.enter M (if x = 1 then t else e)).map fun g => .run m g ks
      | _ => none
  | .brc p w a b t e, m, f, ks =>
      match a.ev f.regs, b.ev f.regs with
      | some x, some y =>
          match Val.icmp p w x y with
          | some (.int 1 r) => (f.enter M (if r = 1 then t else e)).map fun g => .run m g ks
          | _ => none
      | _, _ => none
  | .sw w v d cs, m, f, ks =>
      match v.ev f.regs with
      | some (.int w' x) =>
          if h : w' = w then
            let l := match cs.find? (fun c => decide (BitVec.ofInt w c.1 = (h ▸ x : BitVec w))) with
              | some c => c.2
              | none => d
            (f.enter M l).map fun g => .run m g ks
          else none
      | _ => none
  | .ret none, m, f, ks => finish m f ks none
  | .ret (some o), m, f, ks =>
      match o.ev f.regs with
      | some v => finish m f ks (some v)
      | none => none
  | .dead, _, _, _ => none

/-- **One step.** `none` is stuck (undefined behaviour, a finished run, an ill-formed module). -/
def step (M : Modl) (O : Oracle) : Cfg → Option Cfg
  | .fin .. => none
  | .run m f ks =>
      match M.blk f.fn f.lbl with
      | none => none
      | some blk =>
          match blk.body[f.pc]? with
          | none => stepTerm M blk.term m f ks
          | some (.call d fi args) =>
              match args.mapM (Opd.ev f.regs) with
              | some vs =>
                  match Frame.callee M fi vs d with
                  | some g => some (.run m g (f :: ks))
                  | none => none
              | none => none
          | some (.aload d t p ord) =>
              match p.ev f.regs with
              | some (.ptr b o) =>
                  if atomicOk t ∧ Mem.inside (((m.blks b).map Blk.size).getD 0) o t then
                    match O.ld m b o t ord with
                    | some v => if v.ty = t then some (.run m (f.setr d v).adv ks) else none
                    | none => none
                  else none
              | _ => none
          | some ins =>
              (stepI ins m f.regs).map fun r => .run r.1 { f with regs := r.2, pc := f.pc + 1 } ks

/-! ## 4. Legality of an oracle and the step relation -/

/-- The memory-model interface for atomic loads: memory, block, offset, type, order, value. -/
abbrev Sees := Mem → Nat → Int → Ty → Order → Val → Prop

/-- Sequential consistency: an atomic load reads what the memory holds. -/
def Sees.sc : Sees := fun m b o t _ v => m.load b o t = some v

/-- The instruction a configuration is about to execute. -/
def Cfg.nextI (M : Modl) : Cfg → Option Instr
  | .fin .. => none
  | .run _ f _ => (M.blk f.fn f.lbl).bind fun blk => blk.body[f.pc]?

/-- An oracle is LEGAL at a configuration if its atomic-load answer respects the interface `S`.
    Elsewhere it is not consulted. -/
def Oracle.legal (S : Sees) (M : Modl) (O : Oracle) : Cfg → Prop
  | .fin .. => True
  | .run m f ks =>
      match Cfg.nextI M (.run m f ks) with
      | some (.aload _ t p ord) =>
          ∀ b o v, p.ev f.regs = some (.ptr b o) → O.ld m b o t ord = some v → S m b o t ord v
      | _ => True

/-- **The step relation**: some legal oracle makes `step` produce `c'`. -/
def Step (M : Modl) (S : Sees) (c c' : Cfg) : Prop :=
  ∃ O : Oracle, O.legal S M c ∧ step M O c = some c'

/-- Reachability (zero or more steps). -/
inductive Reach (M : Modl) (S : Sees) : Cfg → Cfg → Prop where
  | refl (c : Cfg) : Reach M S c c
  | step (c c' c'' : Cfg) : Step M S c c' → Reach M S c' c'' → Reach M S c c''

theorem Reach.trans {M : Modl} {S : Sees} {a b c : Cfg} (h1 : Reach M S a b) (h2 : Reach M S b c) :
    Reach M S a c := by
  induction h1 with
  | refl => exact h2
  | step x y z hs _ ih => exact .step x y c hs (ih h2)

theorem Reach.one {M : Modl} {S : Sees} {a b : Cfg} (h : Step M S a b) : Reach M S a b :=
  .step a b b h (.refl b)

/-- A finished run: from `c` the module reaches `fin m v`. -/
def Runs (M : Modl) (S : Sees) (c : Cfg) (m : Mem) (v : Option Val) : Prop :=
  Reach M S c (.fin m v)

/-! ## 5. The oracle is consulted in two instruction forms only -/

/-- The instruction forms whose step depends on the oracle. -/
def Instr.oracular : Instr → Bool
  | .aload .. => true
  | _ => false

/-- **A step that is not an atomic load does not depend on the oracle.** (This is the shape of
    machine GX: the presented memory matters only at the shared atomics.) -/
theorem step_indep (M : Modl) (O O' : Oracle) (c : Cfg)
    (h : ∀ i, Cfg.nextI M c = some i → i.oracular = false) : step M O c = step M O' c := by
  cases c with
  | fin m v => rfl
  | run m f ks =>
      simp only [step]
      cases hb : M.blk f.fn f.lbl with
      | none => rfl
      | some blk =>
          simp only
          cases hi : blk.body[f.pc]? with
          | none => rfl
          | some ins =>
              have hn : ins.oracular = false := h ins (by simp [Cfg.nextI, hb, hi])
              cases ins <;> simp_all [Instr.oracular]

end Gabbro.Code
