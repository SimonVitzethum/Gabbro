/-
  File:      Grammatik/Speichermodell/Sicht.lean
  Subject:   THE VIEW DISCIPLINE of the weak memory model (Opus agent B, 2026-09-26), and the
             classic litmus shapes as Lean facts about it.

  WHICH MODEL, AND WHY THIS ONE. The emitter lowers every access to an `atomic` through an
  explicit `atomic_*_explicit` call (`emit.rs`, lane 152; `C-MEMORY-MODEL.md` §1c) with
  exactly these orders:
  * a declaration `release` or `acquire`: stores `memory_order_release`, loads
    `memory_order_acquire`, a fetch RMW `memory_order_acq_rel` (`holordnung`), a CAS loop
    release on success and acquire on the load;
  * a declaration `seq`: `memory_order_seq_cst` on both sides;
  * a declaration `relaxed` or NO ordering word: `memory_order_relaxed` on both sides.
  No `atomic_thread_fence`, no `consume` (measured in `C-MEMORY-MODEL.md` §1c). Plain carriers
  are ordinary C objects; the lock primitive `L_nimm`/`L_gib` is a `pthread_mutex`
  (`treiber.rs`), i.e. an acquire at the lock and a release at the unlock.

  For that fragment the model is the TIMESTAMP (view) machine of RC11 WITHOUT promises, as in
  Kang et al., "A promising semantics for relaxed-memory concurrency" (POPL 2017) restricted to
  its promise-free part, and Lahav, Giannarakis, Vafeiadis, "Taming release-acquire
  consistency" (POPL 2016) for the release/acquire half:
  * every location has a HISTORY of messages `⟨ts, wert, sicht⟩`; the timestamps of one
    location are its modification order;
  * every thread has a VIEW (a timestamp per location); a read of `x` may return ANY message of
    `x` at or above the reader's view of `x` -- that is the weakness -- and raises the view;
  * a write picks a FRESH timestamp strictly above the writer's view of `x` (not necessarily
    the largest: two writers may be ordered either way), so a later write may even be placed
    below an earlier one in modification order;
  * an ACQUIRE read joins the message's view into the reader's view; a RELEASE write stores
    the writer's whole view in its message; a relaxed read/write carries only its own
    location;
  * a lock carries a view: taking it joins the lock's view, releasing it joins the thread's.
  `seq_cst` is modelled as release/acquire. That is an OVER-approximation (the model admits
  every RC11 behaviour of a `seq_cst` access and more, e.g. store buffering, `sb_sc_modell`);
  every claim proved over the model therefore holds for the C, and no claim here uses the
  total order of `seq_cst`. What the model does NOT contain: promises, hence no load
  buffering (RC11 forbids it too: `po ∪ rf` is acyclic there), and no out-of-thin-air.

  THE LITMUS FACTS (below, over a small instruction machine built from exactly these
  primitives; the machine of Gabbro, `RufSchrittW`, MaschineW.lean, uses the same ones):
  * `mp_ra_verboten`   -- message passing with a release store and an acquire load: the
                          outcome "flag seen, data not" is FORBIDDEN;
  * `mp_rlx_erlaubt`   -- the same shape all relaxed: that outcome is REACHABLE (non-SC);
  * `sb_erlaubt`       -- store buffering, all release/acquire: both reads 0 is REACHABLE
                          (non-SC; RC11 allows it for release/acquire);
  * `sb_sc_verboten`   -- the same outcome is NOT reachable on the SC machine
                          (`LSchrittSC`: reads take the newest, writes append) -- the weak
                          machine is strictly weaker than SC;
  * `corr_verboten`    -- coherence read-read: after reading the second of two writes to one
                          location, a thread never reads the first.
-/
module

public import Grammatik.Speichermodell.Maschine.Sicht.Teil1
public import Grammatik.Speichermodell.Maschine.Sicht.Teil2
