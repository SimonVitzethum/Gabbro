/-
  File:      Grammatik/SyscallPaarung.lean
  Subject:   SYSCALL PAIRING THEOREM (lane S4) -- the user-side contract
             follows from the kernel dispatch entry's proved contract.

  PLAN-SYSCALL.md section 2: a kernel dispatch entry for number `n` carries
  a proved contract (requires `Pk`, ensures `Qk`, effects `Ek`); the
   user-side `syscall` for `n` declares (`Pu`, `Qu`, `Eu`). With `Pu -> Pk`,
   `Qk -> Qu`, `Ek ⊆ Eu` with `Eu` coinciding with the declared axiom
   writes, the same register map, and the kernel recording the same
   `axiomSpur` events, the oracle premise for that `Ax` holds as the
   per-axiom instance of the recording `GutO` (frame + held locks +
   conditional recording) plus the decoded contract -- the syscall needs
   no named assumption.
-/
module

public import Grammatik.Kern.Semantik.Syscall.SyscallPaarung.Teil1
public import Grammatik.Kern.Semantik.Syscall.SyscallPaarung.Teil2
