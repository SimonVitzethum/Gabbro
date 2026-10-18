# C memory model -- historical stub

**The C backend was removed on 2026-10-17.** LLVM (`crates/gabbro-check/src/llvm.rs`,
`llvm/`) is the only backend; see [LLVM-BACKEND](LLVM-BACKEND.md).

* The last tree with the C11 emitter, the generated C drivers and the C runtime carries the
  Git tag `archiv/c-emitter-2026-10-17`. Everything this file used to describe (the C11
  memory-model mapping, `_Atomic` lowering, the emitted forms) can be read there.
* The Lean line for the C backend (`grammatik/Grammatik/CBackend`, the C correspondence chain and
  its C memory model `CSpeicher`) was **deleted on 2026-10-18**; it lives in the same tag. Nothing
  in the current tree builds on it.
* The file keeps its name only because the document set is capped at 30 `.md` files and other
  documents link here.
