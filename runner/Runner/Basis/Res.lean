import Runner.Basis.Mem

/-! # Outcomes of one step, shared by `S0IR` and the x86-64 model

A step continues, faults (the process dies), asks the kernel (a system call: the request, and what follows from
each answer), or -- on the x86-64 side only -- reaches something the model does not describe (`unk`: an
undecodable instruction, an undefined flag read). The proofs show that the runner never reaches `unk`. -/

namespace Runner

/-- A Linux system call as the kernel sees it: the number and six arguments. -/
structure Req where
  nr : W
  a1 : W
  a2 : W
  a3 : W
  a4 : W
  a5 : W
  a6 : W

/-- The kernel's answer: the result, the memory after the call (the kernel may write into the process and change
    mappings), and the value it leaves in `r11` (the saved flags; only the x86-64 side sees it). -/
structure Resp where
  ret : W
  mem : Mem
  r11 : W

inductive Res (σ : Type) where
  | next (s : σ)
  | fault
  | sys (q : Req) (k : Resp → Option σ)
  | unk

/-- Continue with the value, or fault. -/
@[inline] def opt {σ α : Type} (o : Option α) (f : α → Res σ) : Res σ :=
  match o with
  | none => .fault
  | some a => f a

@[simp] theorem opt_none {σ α : Type} (f : α → Res σ) : opt none f = .fault := rfl
@[simp] theorem opt_some {σ α : Type} (a : α) (f : α → Res σ) : opt (some a) f = f a := rfl

end Runner
