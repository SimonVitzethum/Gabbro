# C memory model -- historical stub

**The C backend was removed on 2026-10-17.** LLVM (`crates/gabbro-check/src/llvm.rs`,
`llvm/`) is the only backend; see [LLVM-BACKEND](LLVM-BACKEND.md).

* The last tree with the C11 emitter, the generated C drivers and the C runtime carries the
  Git tag `archiv/c-emitter-2026-10-17`. Everything this file used to describe (the C11
  memory-model mapping, `_Atomic` lowering, the emitted forms) can be read there.
* The Lean proofs under `grammatik/Grammatik/CBackend` stay as **archived evidence**. They
  prove statements about the removed C lowering and are not part of the current trust chain;
  nothing new builds on them.
* The file keeps its name only because the document set is capped at 30 `.md` files and other
  documents link here.
