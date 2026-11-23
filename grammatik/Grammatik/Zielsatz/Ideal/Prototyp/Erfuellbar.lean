/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Erfuellbar.lean
  Subject:   PROTOTYPE of S7: the premise `Disc` of the prototype's theorem is satisfiable by a program in which
             every form of the fragment occurs (AGENTS.md §3: one `_erfuellbar` lemma per premise bundle).

  The program: thread 0 runs a lock section (plain load and store of a lock location, a device read, a store to
  its own buffer), a masked section (a store to a mask location), a relaxed atomic store, `lend`/`takeBack` of its
  buffer and a local assignment; thread 1 runs a lock section on the same lock (a store to its own location) and
  `seq_cst` and relaxed atomics; the handler reads a device register and stores to and loads from a mask
  location.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Satz

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The protection of the instance: 1 the mask, 2 the buffer of thread 0, 3 owned by thread 1, else lock 0. -/
def protE (l : Nat) : Prot := if l = 1 then .irq else if l = 2 then .own 0 else if l = 3 then .own 1 else .lock 0

/-- The instance: every form of the fragment occurs. -/
def progE : Prog where
  prot := protE
  thread t := if t = 0 then
      [.lock 0 [.load 0 0, .store 0 (.add (.reg 0) (.lit 1)), .dev 1 7, .store 2 (.reg 1)],
       .masked [.store 1 (.lit 5)], .atom .rlx (.st 0 (.lit 1)), .lend 2, .takeBack 2, .set 3 (.reg 1)]
    else
      [.lock 0 [.load 0 0, .store 3 (.reg 0)], .atom .sc (.faa 0 0 (.lit 1)), .atom .sc (.ld 1 0),
       .atom .rlx (.ld 2 0)]
  handler := [.dev 0 9, .store 1 (.reg 0), .load 1 1]

/-- **`disc_erfuellbar`**: the premise of `s7_prototyp` holds for a program that uses every form of the fragment
    (both threads, lock and masked sections, every plain operation, relaxed and `seq_cst` atomics, `lend` and
    `takeBack`, a local assignment, and a handler). -/
theorem disc_erfuellbar : Disc progE := by
  refine ⟨fun t => ?_, ?_⟩
  · rcases t with ⟨_ | _ | n, hn⟩
    · simp [progE, ProgOk, BodyOk, OpOk, KLk, KMk, protE]
    · simp [progE, ProgOk, BodyOk, OpOk, KLk, protE]
    · omega
  · simp [progE, BodyOk, OpOk, KIrq, protE]

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
