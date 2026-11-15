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

end Gabbro.Stage0.Senke.BildMehr
