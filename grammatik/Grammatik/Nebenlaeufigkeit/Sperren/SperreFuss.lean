/-
  File:      Grammatik/SperreFuss.lean
  Subject:   THE FOOTPRINT CHECK WITH LOCK INVARIANTS -- the carriers a frame
             may rely on at a given point, the decidable program fact that
             replaces `fussOrtGB`, the residue predicate of the replay, and
             the user obligation `KoerperGutS`.

  `fussOrtGB` (the check of `ziel_ort_ganz`) asks every footprint carrier of
  a function to be guarded by a lock the function holds BY SIGNATURE, or to
  be written by no function: a carrier a thread reads inside
  `locks L { … }` falls (verdict probes B, C). Here a footprint carrier may
  also be PROTECTED BY A LOCK INVARIANT: guarded by a lock `L` that lists it
  (`c ∈ S.orte L`). Such a carrier is stable for the frame only while `L` is
  held -- at the access, which the typing guarantees (`Expr.orte_darf`: every
  guard of a carrier an expression reads is in its static holdings, from the
  signature or from an enclosing `locks` block). Between two critical
  sections other threads may change it; the sequential semantics
  (`SperreSem.lean`) lets the environment move it at the next acquire.

  * `stabilS P S lok f Λ`: the carriers the replay keeps equal between the
    sequential and the machine world while the frame's static holdings are
    `Λ` -- the footprint carriers guarded by a signature lock or written by
    no function (`sicher`), and the protected carriers of every lock held in
    `Λ`.
  * `fussSperreB`: every footprint carrier is `sicher`, or protected by an
    invariant of one of its guards; the device carriers of the registers a
    body reads (read without a guard at the access) must be `sicher`.
  * `KoerperGutS`: the obligation of `ziel_ort_ganz` over the semantics with
    acquire moves and release checks, for every move in `HavocOk S`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss.Teil1
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss.Teil2
