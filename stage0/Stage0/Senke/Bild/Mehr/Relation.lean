/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Relation.lean
  Subject:   THE SIMULATION RELATION of the multi-thread image theorem (package MT1). `MTRel P O passes L c K S X mk`
             relates a configuration `c` of the IR process (shared memory, threads) to a thread machine `K` of
             machine G, through
             * `S i` -- per live runner thread its `Solo` (state, solo memory, footprint, write set),
             * `X i` -- per runner thread its G position (`MLage`: body frame, G thread, boundary, view machine),
             * `mk` -- the COMMITTED memory: the world of `K` in the layout `L`.
             Fields: the threads of `c` are exactly the threads with a `Solo`, at its state (`zustand`, `lebend`);
             the memory part (`mem`, `Verschmolzen`); every position satisfies the chain's premises (`lage`) on the
             same program, oracle, passes and layout (`prog`); every thread's state is where its solo run from its
             boundary stands (`solo`); its G thread is live in `K`, joins nothing, belongs to no other runner thread
             and stands in `K` at the thread's boundary (`lebtG`, `inj`, `amRand`); the committed memory holds `K`'s
             world (`welt`) and the shared memory equals it at every byte no thread may write in its current
             segment (`aussen`). Machine G moves only at segment ends (package MT2), so inside segments `K` stutters.
             `MTRel.nach`: the relation after a change of thread `i` alone that keeps its footprint and write set
             and changes the memory inside its write set only.
-/
module
public import Stage0.Senke.Bild.Mehr.Lage
public import Stage0.Senke.Bild.Mehr.Fuss
public import Stage0.Senke.Bild.Mehr.Prozess
public import Grammatik.Nebenlaeufigkeit.Allgemein.Threads.FadenMaschine
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner.IR

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- **The simulation relation** between the IR process and the thread machine of machine G. -/
structure MTRel (P : Programm D) (O : Orakel D) (passes : Nat) (L : Lay D) (c : PCfg) (K : FadenMaschine D)
    (S : Nat → Option Solo) (X : Nat → MLage D) (mk : Runner.Mem) : Prop where
  zustand : ∀ i s, S i = some s → c.ths[i]? = some (some s.r)
  lebend : ∀ i r, c.ths[i]? = some (some r) → ∃ s, S i = some s
  mem : Verschmolzen c.m S
  lage : ∀ i s, S i = some s → (X i).Ok
  prog : ∀ i s, S i = some s → (X i).B.P = P ∧ (X i).B.O = O ∧ (X i).B.passes = passes ∧ (X i).B.L = L
  solo : ∀ i s, S i = some s → SoloLauf (X i).start (X i).mb s.r s.m
  lebtG : ∀ i s, S i = some s → K.lebt (X i).thr = true ∧ K.wartet (X i).thr = []
  inj : ∀ i j s u, S i = some s → S j = some u → (X i).thr = (X j).thr → i = j
  amRand : ∀ i s, S i = some s → K.m.faeden (X i).thr = (X i).M.faeden (X i).thr
  welt : WeltAt mk L (K.m.speicher.welt [])
  aussen : ∀ y, (∀ i s, S i = some s → ¬ s.Wr y) → GleichAt c.m mk y

/-- Startup can have allocated root slots before any lowered body is
    registered. The committed view is already the exact source world. -/
theorem MTRel.no_registered_threads {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D}
    {c : PCfg} {state : FadenMaschine D} (positions : Nat → MLage D)
    (empty : ∀ (i : Nat) (r : Res T), c.ths[i]? ≠ some (some r))
    (world : WeltAt c.m L (state.m.speicher.welt [])) :
    MTRel P O passes L c state (fun _ => none) positions c.m where
  zustand := fun _ _ h => by cases h
  lebend := fun i r h => (empty i r h).elim
  mem := ⟨fun _ _ h => by cases h, fun _ _ h => by cases h, fun _ _ _ _ _ h => by cases h⟩
  lage := fun _ _ h => by cases h
  prog := fun _ _ h => by cases h
  solo := fun _ _ h => by cases h
  lebtG := fun _ _ h => by cases h
  inj := fun _ _ _ _ h => by cases h
  amRand := fun _ _ h => by cases h
  welt := world
  aussen := fun address _ => GleichAt.refl _ address

/-- Whatever a field asks of every thread with a `Solo`, it asks after a replacement too. -/
theorem setzeS_alt {S : Nat → Option Solo} {i j : Nat} {s s' u : Solo} (hi : S i = some s)
    (h : setzeS S i s' j = some u) : ∃ u0, S j = some u0 := by
  rcases setzeS_fall h with ⟨rfl, -⟩ | ⟨-, h⟩
  · exact ⟨s, hi⟩
  · exact ⟨u, h⟩

/-- **The relation after a change of thread `i` alone**: thread `i` has a new `Solo` with the same footprint and
    write set, whose state the new configuration holds and whose solo run continues the position; every other thread
    is unchanged; the memory part holds; the shared memory changed inside `i`'s write set only. `K`, the positions
    and the committed memory are kept: machine G stutters. -/
theorem MTRel.nach {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D} {c c' : PCfg}
    {K : FadenMaschine D} {S : Nat → Option Solo} {X : Nat → MLage D} {mk : Runner.Mem}
    (hR : MTRel P O passes L c K S X mk) {i : Nat} {s s' : Solo} (hi : S i = some s)
    (hW : s'.Wr = s.Wr) (hthi : c'.ths[i]? = some (some s'.r))
    (hthj : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?) (hmem : Verschmolzen c'.m (setzeS S i s'))
    (hsolo : SoloLauf (X i).start (X i).mb s'.r s'.m) (hau : ∀ y, ¬ s.Wr y → GleichAt c'.m c.m y) :
    MTRel P O passes L c' K (setzeS S i s') X mk where
  zustand := by
    intro j u hu
    rcases setzeS_fall hu with ⟨rfl, rfl⟩ | ⟨hj, hu⟩
    · exact hthi
    · rw [hthj j hj]
      exact hR.zustand j u hu
  lebend := by
    intro j r hr
    by_cases hj : j = i
    · exact ⟨s', by rw [hj]; exact setzeS_self S i s'⟩
    · rw [hthj j hj] at hr
      obtain ⟨u, hu⟩ := hR.lebend j r hr
      exact ⟨u, by rw [setzeS_ne S s' hj]; exact hu⟩
  mem := hmem
  lage := fun j _ hu => by
    obtain ⟨u0, hu0⟩ := setzeS_alt hi hu
    exact hR.lage j u0 hu0
  prog := fun j _ hu => by
    obtain ⟨u0, hu0⟩ := setzeS_alt hi hu
    exact hR.prog j u0 hu0
  solo := by
    intro j u hu
    rcases setzeS_fall hu with ⟨rfl, rfl⟩ | ⟨_, hu⟩
    · exact hsolo
    · exact hR.solo j u hu
  lebtG := fun j _ hu => by
    obtain ⟨u0, hu0⟩ := setzeS_alt hi hu
    exact hR.lebtG j u0 hu0
  inj := fun j1 j2 _ _ hu1 hu2 e => by
    obtain ⟨v1, hv1⟩ := setzeS_alt hi hu1
    obtain ⟨v2, hv2⟩ := setzeS_alt hi hu2
    exact hR.inj j1 j2 v1 v2 hv1 hv2 e
  amRand := fun j _ hu => by
    obtain ⟨u0, hu0⟩ := setzeS_alt hi hu
    exact hR.amRand j u0 hu0
  welt := hR.welt
  aussen := by
    intro y hy
    have hs : ¬ s.Wr y := by
      rw [← hW]
      exact hy i s' (setzeS_self S i s')
    refine (hau y hs).trans (hR.aussen y fun j u hu => ?_)
    by_cases hj : j = i
    · rw [hj, hi] at hu
      cases hu
      exact hs
    · exact hy j u (by rw [setzeS_ne S s' hj]; exact hu)

/-- A freshly activated root has no lowered body thread yet. Adding its
    empty body slot preserves the existing simulation and all snapshots. -/
theorem MTRel.append_pending_root {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D}
    {c : PCfg} {before after : FadenMaschine D} {S : Nat → Option Solo}
    {X : Nat → MLage D} {committed : Runner.Mem}
    (related : MTRel P O passes L c before S X committed)
    (machine : after.m = before.m) (waiting : after.wartet = before.wartet)
    (live : ∀ i, before.lebt i = true → after.lebt i = true) :
    MTRel P O passes L ⟨c.m, c.ths ++ [none]⟩ after S X committed := by
  refine {
    zustand := ?_
    lebend := ?_
    mem := related.mem
    lage := related.lage
    prog := related.prog
    solo := related.solo
    lebtG := ?_
    inj := related.inj
    amRand := ?_
    welt := ?_
    aussen := related.aussen }
  · intro i s known
    have found := related.zustand i s known
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · intro i r found
    change (c.ths ++ [none])[i]? = some (some r) at found
    by_cases inside : i < c.ths.length
    · rw [List.getElem?_append_left inside] at found
      exact related.lebend i r found
    · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at found
      cases offset : i - c.ths.length <;> rw [offset] at found <;> cases found
  · intro i s known
    obtain ⟨resident, ready⟩ := related.lebtG i s known
    exact ⟨live _ resident, waiting.symm ▸ ready⟩
  · rw [machine]
    exact related.amRand
  · rw [machine]
    exact related.welt

/-- Once startup enters a lowered body, replace its empty slot by the
    exact source position. Existing threads and the committed GX world
    retain their relation through the startup's private writes. -/
theorem MTRel.enter_pending_root {P : Programm D} {O : Orakel D} {passes : Nat} {L : Lay D}
    {c : PCfg} {state : FadenMaschine D} {S : Nat → Option Solo}
    {X : Nat → MLage D} {committed memory : Runner.Mem} {i : Nat} {entry : MLage D}
    (related : MTRel P O passes L c state S X committed)
    (empty : c.ths[i]? = some none)
    (entryOK : entry.Ok) (exactProgram : entry.B.P = P ∧ entry.B.O = O ∧ entry.B.passes = passes ∧ entry.B.L = L)
    (live : state.lebt entry.thr = true) (waiting : state.wartet entry.thr = [])
    (head : state.m.faeden entry.thr = entry.M.faeden entry.thr)
    (fresh : ∀ j s, S j = some s → (X j).thr ≠ entry.thr)
    (footprint writes : Runner.W → Prop)
    (inside : ∀ byte, writes byte → footprint byte)
    (agrees : GleichAuf footprint memory entry.mb)
    (outside : ∀ byte, ¬ writes byte → GleichAt memory c.m byte)
    (entryPrivate : ∀ j s, S j = some s → ∀ byte, writes byte → ¬ s.F byte)
    (existingPrivate : ∀ j s, S j = some s → ∀ byte, s.Wr byte → ¬ footprint byte) :
    MTRel P O passes L ⟨memory, c.ths.set i (some (.next entry.start))⟩ state
      (setzeS S i ⟨.next entry.start, entry.mb, footprint, writes⟩)
      (fun j => if j = i then entry else X j) committed := by
  let added : Solo := ⟨.next entry.start, entry.mb, footprint, writes⟩
  have slot := (List.getElem?_eq_some_iff.mp empty).1
  have ready (j : Nat) (s : Solo) (found : setzeS S i added j = some s) :
      j = i ∧ s = added ∨ j ≠ i ∧ S j = some s := setzeS_fall found
  refine {
    zustand := ?_
    lebend := ?_
    mem := ⟨?_, ?_, ?_⟩
    lage := ?_
    prog := ?_
    solo := ?_
    lebtG := ?_
    inj := ?_
    amRand := ?_
    welt := related.welt
    aussen := ?_ }
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · exact List.getElem?_set_self slot
    · exact (List.getElem?_set_ne other.symm).trans (related.zustand j s previous)
  · intro j r found
    by_cases same : j = i
    · subst j
      exact ⟨added, setzeS_self _ _ _⟩
    · change (c.ths.set i (some (.next entry.start)))[j]? = some (some r) at found
      rw [List.getElem?_set_ne (Ne.symm same)] at found
      obtain ⟨s, previous⟩ := related.lebend j r found
      exact ⟨s, (setzeS_ne S added same).trans previous⟩
  · intro j s known byte read
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨_, previous⟩
    · exact agrees byte read
    · exact (outside byte (fun written => entryPrivate j s previous byte written read)).trans
        (related.mem.gleich j s previous byte read)
  · intro j s known byte written
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨_, previous⟩
    · exact inside byte written
    · exact related.mem.wrF j s previous byte written
  · intro j k s u distinct left right byte written
    rcases ready j s left with ⟨rfl, rfl⟩ | ⟨_, leftOld⟩ <;>
      rcases ready k u right with ⟨rfl, rfl⟩ | ⟨_, rightOld⟩
    · exact (distinct rfl).elim
    · exact entryPrivate k u rightOld byte written
    · exact existingPrivate j s leftOld byte written
    · exact related.mem.getrennt j k s u distinct leftOld rightOld byte written
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · simpa only [ite_true] using entryOK
    · simpa only [ite_eq_right other] using related.lage j s previous
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · simpa only [ite_true] using exactProgram
    · simpa only [ite_eq_right other] using related.prog j s previous
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · simpa only [ite_true] using soloLauf_start entry.start entry.mb
    · simpa only [ite_eq_right other] using related.solo j s previous
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · simpa only [ite_true] using And.intro live waiting
    · simpa only [ite_eq_right other] using related.lebtG j s previous
  · intro j k s u left right same
    rcases ready j s left with ⟨rfl, rfl⟩ | ⟨otherJ, leftOld⟩ <;>
      rcases ready k u right with ⟨rfl, rfl⟩ | ⟨otherK, rightOld⟩
    · rfl
    · simp only [ite_true, ite_eq_right otherK] at same
      exact (fresh k u rightOld same.symm).elim
    · simp only [ite_eq_right otherJ, ite_true] at same
      exact (fresh j s leftOld same).elim
    · simp only [ite_eq_right otherJ, ite_eq_right otherK] at same
      exact related.inj j k s u leftOld rightOld same
  · intro j s known
    rcases ready j s known with ⟨rfl, rfl⟩ | ⟨other, previous⟩
    · simpa only [ite_true] using head
    · simpa only [ite_eq_right other] using related.amRand j s previous
  · intro byte unwritten
    refine (outside byte (unwritten i added (setzeS_self _ _ _))).trans (related.aussen byte ?_)
    intro j s previous
    have other : j ≠ i := by
      intro same
      subst j
      have present := related.zustand i s previous
      rw [empty] at present
      cases present
    exact unwritten j s ((setzeS_ne S added other).trans previous)

end Gabbro.Stage0.Senke.BildMehr
