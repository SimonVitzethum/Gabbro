//! F2 (2026-10-07, legacy C backend): the page-return helper of `reset X at i count n;` must test
//! the ABSOLUTE rounded addresses (`lo < hi`) before it forms any offset. The first version formed
//! `bis = (a + bytes) / seite * seite - a` in `uint64_t` first, which wraps for a range inside one
//! page and zeroed far past the buffer (example 175 with `reset RING at 10 count 100;` exited 139).
//! Template `region.leeren`, `leeren_in_einer_seite` / `leeren_alt_bricht` in `SchablonenArena.lean`.
//! The run-time half (corrected helper exits 0, the first-version twin dies) is stage 4 of
//! `instrumente/pruefe-seiten-zurueck.sh`.

