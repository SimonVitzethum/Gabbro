import Runner.Basis.Mem

/-! # One step as a tree of requests to the memory and the kernel

A thread of `S0IR` and a thread of the x86-64 model both compute privately and ask the outside for everything
else: a read of `n` bytes, a write of a word, a compare-and-swap, or a system call. A step is therefore a tree:
it continues with a new thread state, faults (the process dies), is not described by the model (`unk`, x86 only),
or asks and continues with what follows from each answer. Who answers -- one memory, a memory with store buffers,
the kernel -- is the machine's business (`Runner/Mach/`), so a theorem about two trees holds under every memory
model the two machines share.

An answer is `none` when the access is refused (the process dies) and otherwise a pair: the value read (or the
old word of a `cas`, or the result of a system call), and for a system call the value the kernel leaves in `r11`
(seen only by the x86-64 side). -/

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
  deriving DecidableEq

inductive Op where
  /-- read `n` bytes (1, 4 or 8) at `a`, little-endian -/
  | rd (n : Nat) (a : W)
  /-- write the word `v` at `a` -/
  | wr (a v : W)
  /-- if the word at `a` is `e`, write `n`; answer the old word (a locked read-modify-write) -/
  | cas (a e n : W)
  | sys (q : Req)
  deriving DecidableEq

abbrev Ans := Option (W × W)

inductive Res (σ : Type) where
  | next (s : σ)
  | fault
  | unk
  | ask (o : Op) (k : Ans → Res σ)

/-- Continue with the value, or fault. -/
@[inline] def opt {σ α : Type} (o : Option α) (f : α → Res σ) : Res σ :=
  match o with
  | none => .fault
  | some a => f a

@[simp] theorem opt_none {σ α : Type} (f : α → Res σ) : opt none f = .fault := rfl
@[simp] theorem opt_some {σ α : Type} (a : α) (f : α → Res σ) : opt (some a) f = f a := rfl

/-! The requests both machines use, with the same conversion of the answer on both sides. -/

@[inline] def rd8 {σ : Type} (a : W) (f : W → Res σ) : Res σ :=
  .ask (.rd 1 a) fun r => opt r fun p => f (p.1.setWidth 8 |>.setWidth 64)
@[inline] def rd32 {σ : Type} (a : W) (f : BitVec 32 → Res σ) : Res σ :=
  .ask (.rd 4 a) fun r => opt r fun p => f (p.1.setWidth 32)
@[inline] def rd64 {σ : Type} (a : W) (f : W → Res σ) : Res σ :=
  .ask (.rd 8 a) fun r => opt r fun p => f p.1
@[inline] def wr64 {σ : Type} (a v : W) (s : σ) : Res σ :=
  .ask (.wr a v) fun r => opt r fun _ => .next s
@[inline] def cas {σ : Type} (a e n : W) (f : W → Res σ) : Res σ :=
  .ask (.cas a e n) fun r => opt r fun p => f p.1

/-- The thread numbers of the system calls the machines interpret themselves (fixed Linux numbers). -/
def NR_CLONE : Nat := 56
def NR_EXIT : Nat := 60
def NR_EXIT_GROUP : Nat := 231

/-- `clone` for a thread sharing everything: `CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD |
    CLONE_SYSVSEM`, no new stack (the runner never uses its stack), no tid pointers, no TLS. -/
def CLONE_FLAGS : Nat := 0x50F00

def cloneReq : Req := ⟨BitVec.ofNat 64 NR_CLONE, BitVec.ofNat 64 CLONE_FLAGS, 0, 0, 0, 0, 0⟩

end Runner
