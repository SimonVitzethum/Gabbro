/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Start.lean
  Subject:   The simulation relation at the start of a process (multi-thread image theorem, base of package MT6).
             One runner thread stands at the boundary of a position `x` whose single-thread premises hold
             (`MLage.Ok`): the configuration with the boundary's memory and the one thread at the instruction there
             (`startCfg`) is related by `MTRel` to every thread machine `K` whose G thread `x.thr` is live, joins
             nothing, stands where the position's view machine stands and has the view machine's memory
             (`mtRel_start`). The thread's footprint and write set are all bytes (it is alone); the committed
             memory is the boundary's memory, which holds the world of `K` because the image side of the boundary
             holds the position's world (`MLage.Ok.welt`). So the relation is not empty whenever a single-thread
             boundary exists -- the joint premises of `MTRel` are those of the single-thread chain plus four facts
             about `K`.
-/
module
public import Stage0.Senke.Bild.Mehr.Relation
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner.IR

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- One thread with a `Solo`: thread `0`. -/
def startS (s : Solo) : Nat → Option Solo
  | 0 => some s
  | _ + 1 => none

theorem startS_eq {s u : Solo} {i : Nat} (h : startS s i = some u) : i = 0 ∧ u = s := by
  cases i with
  | zero => exact ⟨rfl, (Option.some.inj h).symm⟩
  | succ i => cases h

/-- The thread at the boundary of `x`, alone: every byte in its footprint and its write set. -/
def startSolo (x : MLage D) : Solo := ⟨.next x.start, x.mb, fun _ => True, fun _ => True⟩

/-- The process at the boundary of `x`: its memory, one thread at the instruction there. -/
def startCfg (x : MLage D) : PCfg := ⟨x.mb, [some (.next x.start)]⟩

/-- A memory that is the world's memory holds the world in the image (the trace is not in the image). -/
theorem weltAt_speicher {m : Runner.Mem} {L : Lay D} {σ : World D} {s : Speicher D} (hs : s = σ.speicher)
    (h : WeltAt m L σ) : WeltAt m L (s.welt []) := by
  subst hs
  unfold WeltAt at h ⊢
  exact h

/-- At the boundary of a position, the image memory holds the position's world, and the view machine's memory is
    the world's memory. -/
theorem MLage.Ok.welt {x : MLage D} (hx : x.Ok) : WeltAt x.mb x.B.L x.σ ∧ x.M.speicher = x.σ.speicher := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hW, _, _⟩ := hx.rand.1
  obtain ⟨⟨_, hZ⟩, _, _⟩ := hx.rand.2
  exact ⟨hW, hZ.2⟩

/-- **The relation at the start**: one runner thread at the boundary of a position whose single-thread premises
    hold, and a thread machine whose G thread stands there with the view machine's memory. -/
theorem mtRel_start {x : MLage D} (hx : x.Ok) {K : FadenMaschine D} (hl : K.lebt x.thr = true)
    (hw : K.wartet x.thr = []) (hf : K.m.faeden x.thr = x.M.faeden x.thr) (hs : K.m.speicher = x.M.speicher) :
    MTRel x.B.P x.B.O x.B.passes x.B.L (startCfg x) K (startS (startSolo x)) (fun _ => x) x.mb where
  zustand := by
    intro i s h
    obtain ⟨rfl, rfl⟩ := startS_eq h
    rfl
  lebend := by
    intro i r h
    cases i with
    | zero => exact ⟨_, rfl⟩
    | succ i => simp [startCfg] at h
  mem := by
    refine ⟨?_, ?_, ?_⟩
    · intro i s h y _
      obtain ⟨rfl, rfl⟩ := startS_eq h
      exact GleichAt.refl _ y
    · intro i s h y _
      obtain ⟨rfl, rfl⟩ := startS_eq h
      trivial
    · intro i j s u hij hi hj
      obtain ⟨rfl, -⟩ := startS_eq hi
      obtain ⟨rfl, -⟩ := startS_eq hj
      exact absurd rfl hij
  lage := fun _ _ _ => hx
  prog := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
  solo := by
    intro i s h
    obtain ⟨rfl, rfl⟩ := startS_eq h
    exact soloLauf_start _ _
  lebtG := fun _ _ _ => ⟨hl, hw⟩
  inj := by
    intro i j s u hi hj _
    obtain ⟨rfl, -⟩ := startS_eq hi
    obtain ⟨rfl, -⟩ := startS_eq hj
    rfl
  amRand := fun _ _ _ => hf
  welt := weltAt_speicher (hs.trans hx.welt.2) hx.welt.1
  aussen := fun y _ => GleichAt.refl _ y

/-- The thread machine of one live thread at the view machine of a position (the start of a process). -/
def startK (x : MLage D) : FadenMaschine D := ⟨x.M, fun t => t == x.thr, fun _ => [], fun _ => 0, 0⟩

/-- **The relation at the start, with its thread machine**: from the premises of the single-thread chain alone. -/
theorem mtRel_startK {x : MLage D} (hx : x.Ok) :
    MTRel x.B.P x.B.O x.B.passes x.B.L (startCfg x) (startK x) (startS (startSolo x)) (fun _ => x) x.mb :=
  mtRel_start hx (by simp [startK]) rfl rfl rfl

end Gabbro.Stage0.Senke.BildMehr
