# Direct compiler detailed design: generic source-to-final-bytes compilation with fast validation

*Lane 323, 2026-10-01. Status: PROPOSED design, not an implementation or a proof.
Nothing here claims any source-to-x86 chain is closed. Central progress record:
[DIRECT-COMPILER.md](DIRECT-COMPILER.md). All source-to-executed-final-binary
claims remain OPEN.*

## 0. Reading guide and claim boundary

This document is a plan. Every section marked PROPOSED needs Lean modelling,
generic proofs and review before any Rust part is built. Existing helpers are
bounded foundations, not implemented native compilation. No new mini-model is
proposed; all names refer to the canonical vocabularies below.
<!-- APPEND-MARKER -->
