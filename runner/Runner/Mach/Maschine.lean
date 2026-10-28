import Runner.Basis.Res

/-! # A process of threads over a memory model, with the fixed Linux thread calls

The same machine runs the threads of `S0IR` and the threads of the x86-64 model; only the threads' step `act`
differs. A memory model (`MemSys`) answers the threads' requests -- one memory, or a memory with a store buffer
per thread that drains on its own (`tau`) -- and the kernel's answers to system calls are part of it (any result,
any change of the memory the model allows).

The machine itself interprets three Linux calls (fixed numbers, `Runner/Basis/Res.lean`):
* `exit` (60): the thread ends;
* `exit_group` (231): the process ends with the code;
* `clone` with the fixed thread flags (`cloneReq`): the memory model answers; when the answer is a thread id
  (positive), a new thread starts with the same continuation answered 0 -- what Linux does for a thread that
  shares the memory. Any other `clone`-like call with other flags is not interpreted: the named assumption is
  that the program makes none.
Every other request goes to the memory model. A run is observed by its system calls (thread, request, answer)
and how it ends so far. -/

namespace Runner.Mach

structure MemSys where
  St : Type
  /-- Thread `i`'s request `o` gets the answer `a`; the memory goes to `s'`. -/
  ans : St → Nat → Op → Ans → St → Prop
  /-- The memory model's own steps (a store buffer drains). -/
  tau : St → St → Prop

structure Cfg (M : MemSys) (θ : Type) where
  ms : M.St
  ths : List (Option θ)

abbrev Ev := Nat × Req × Ans

inductive Ende
  | lauf
  | fault
  | unk
  | exit (code : W)
  deriving DecidableEq

/-- The requests the machine interprets itself. -/
def _root_.Runner.Op.special : Op → Bool
  | .sys q => q.nr.toNat == NR_EXIT || q.nr.toNat == NR_EXIT_GROUP || q == cloneReq
  | _ => false

/-- A request is observed when it is a system call. -/
def lbl (i : Nat) : Op → Ans → List Ev
  | .sys q, a => [(i, q, a)]
  | _, _ => []

/-- How a thread's step ends a run: a fault, or a step the model does not describe. -/
def Res.ende {θ : Type} : Res θ → Option Ende
  | .fault => some .fault
  | .unk => some .unk
  | _ => none

variable {M : MemSys} {θ : Type}

/-- Observations of the machine: from `c`, the system calls `l`, then the end `e`, in `n` steps. -/
inductive Tr (M : MemSys) (act : θ → Res θ) : Cfg M θ → List Ev → Ende → Nat → Prop
  | nil (c : Cfg M θ) : Tr M act c [] .lauf 0
  | tau {c : Cfg M θ} {ms : M.St} {l : List Ev} {e : Ende} {n : Nat} :
      M.tau c.ms ms → Tr M act ⟨ms, c.ths⟩ l e n → Tr M act c l e (n + 1)
  | priv {c : Cfg M θ} {i : Nat} {t t' : θ} {l : List Ev} {e : Ende} {n : Nat} :
      c.ths[i]? = some (some t) → act t = .next t' →
      Tr M act ⟨c.ms, c.ths.set i (some t')⟩ l e n → Tr M act c l e (n + 1)
  | stop {c : Cfg M θ} {i : Nat} {t : θ} {e : Ende} :
      c.ths[i]? = some (some t) → Res.ende (act t) = some e → Tr M act c [] e 1
  | ask {c : Cfg M θ} {i : Nat} {t t' : θ} {o : Op} {k : Ans → Res θ} {a : Ans} {ms : M.St} {l : List Ev}
      {e : Ende} {n : Nat} :
      c.ths[i]? = some (some t) → act t = .ask o k → o.special = false → M.ans c.ms i o a ms →
      k a = .next t' → Tr M act ⟨ms, c.ths.set i (some t')⟩ l e n → Tr M act c (lbl i o a ++ l) e (n + 1)
  | askStop {c : Cfg M θ} {i : Nat} {t : θ} {o : Op} {k : Ans → Res θ} {a : Ans} {ms : M.St} {e : Ende} :
      c.ths[i]? = some (some t) → act t = .ask o k → o.special = false → M.ans c.ms i o a ms →
      Res.ende (k a) = some e → Tr M act c (lbl i o a) e 1
  | exit {c : Cfg M θ} {i : Nat} {t : θ} {q : Req} {k : Ans → Res θ} {l : List Ev} {e : Ende} {n : Nat} :
      c.ths[i]? = some (some t) → act t = .ask (.sys q) k → q.nr.toNat = NR_EXIT →
      Tr M act ⟨c.ms, c.ths.set i none⟩ l e n → Tr M act c ((i, q, none) :: l) e (n + 1)
  | exitGroup {c : Cfg M θ} {i : Nat} {t : θ} {q : Req} {k : Ans → Res θ} :
      c.ths[i]? = some (some t) → act t = .ask (.sys q) k → q.nr.toNat = NR_EXIT_GROUP →
      Tr M act c [(i, q, none)] (.exit q.a1) 1
  /-- `clone` refused or answered with an error: no new thread. -/
  | cloneNo {c : Cfg M θ} {i : Nat} {t t' : θ} {k : Ans → Res θ} {a : Ans} {ms : M.St} {l : List Ev}
      {e : Ende} {n : Nat} :
      c.ths[i]? = some (some t) → act t = .ask (.sys cloneReq) k → M.ans c.ms i (.sys cloneReq) a ms →
      (∀ r w, a = some (r, w) → ¬ 0 < r.toInt) → k a = .next t' →
      Tr M act ⟨ms, c.ths.set i (some t')⟩ l e n → Tr M act c ((i, cloneReq, a) :: l) e (n + 1)
  | cloneNoStop {c : Cfg M θ} {i : Nat} {t : θ} {k : Ans → Res θ} {a : Ans} {ms : M.St} {e : Ende} :
      c.ths[i]? = some (some t) → act t = .ask (.sys cloneReq) k → M.ans c.ms i (.sys cloneReq) a ms →
      (∀ r w, a = some (r, w) → ¬ 0 < r.toInt) → Res.ende (k a) = some e → Tr M act c [(i, cloneReq, a)] e 1
  /-- `clone` answered with a thread id: the parent continues with it, the new thread with 0. -/
  | clone {c : Cfg M θ} {i : Nat} {t t' tc : θ} {k : Ans → Res θ} {r w : W} {ms : M.St} {l : List Ev}
      {e : Ende} {n : Nat} :
      c.ths[i]? = some (some t) → act t = .ask (.sys cloneReq) k →
      M.ans c.ms i (.sys cloneReq) (some (r, w)) ms → 0 < r.toInt → k (some (r, w)) = .next t' →
      k (some (0, w)) = .next tc →
      Tr M act ⟨ms, c.ths.set i (some t') ++ [some tc]⟩ l e n → Tr M act c ((i, cloneReq, some (r, w)) :: l) e (n + 1)

end Runner.Mach
