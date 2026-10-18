import Grammatik.Code.Lower.Rep
import Grammatik.Speichermodell.Atomar.AtomarLauf

/-
  File:      Grammatik/Code/Conc/Present.lean
  Subject:   TRACK L, PHASE L3 -- THE REPRESENTATION AND MACHINE GX: the memory of a presented world, and of the
             successor, is represented by the IR memory whenever G's step on the presented world is.

  Machine GX (`RufSchrittGX`) runs a step of G on a PRESENTED memory `σ` that agrees with the machine's memory outside
  the shared atomics `Tg`; the successor takes the written carriers from the step and keeps the rest. `Rep` leaves
  the cells of the shared atomics (`lay.shared`) free, so:

    * `rep_agree`   -- worlds that agree outside the shared atomics are represented by the same memories;
    * `rep_presented` -- if the IR memory represents the machine's memory, it represents every presented one;
    * `rep_successor` -- if it represents the memory G's step produced on the presented memory, it represents the
      memory the GX step leaves (the carriers outside `Tg` are the step's, the shared atomics are free).

  So a refinement proof for G (a block that runs from a world that `Rep` represents and ends in a world that `Rep`
  represents) is, with these three, a refinement proof for GX with NO new memory reasoning: the IR memory is the
  shared one, G's presented world is read from it, and the successor is read back from it.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Speicher Wert TraegerGleich RufMaschineG Programm Orakel Faden
  RufSchrittGX mitSpeicher)

variable {D : Deklaration}

/-- **Worlds that agree outside the shared atomics are represented by the same memories.** -/
theorem rep_agree {lay : Layout D} {σ σ' : World D} {m : Mem}
    (hs : ∀ t k f, σ'.slots t k f = σ.slots t k f)
    (hg : ∀ g, lay.shared g = false → σ'.globs g = σ.globs g) (h : Rep lay σ m) : Rep lay σ' m := by
  refine ⟨fun t k f hs0 h0 h1 => ?_, fun g hs0 => ?_⟩
  · rw [hs t k f]; exact h.1 t k f hs0 h0 h1
  · obtain ⟨hx, hc⟩ := h.2 g hs0
    exact ⟨hx, fun hsh => by rw [hg g hsh]; exact hc hsh⟩

/-- The shared atomics `Tg` of machine GX are the globals the layout calls shared. -/
def TgShared (lay : Layout D) (Tg : D.Tab ⊕ D.Glob → Prop) : Prop :=
  ∀ c, Tg c → ∃ g, c = .inr g ∧ lay.shared g = true

/-- A memory that agrees with `sp` outside `Tg` agrees outside the shared globals, slots and globals. -/
theorem agree_outside {lay : Layout D} {Tg : D.Tab ⊕ D.Glob → Prop} (hT : TgShared lay Tg)
    {σ sp : Speicher D} (h : ∀ c, ¬ Tg c → TraegerGleich σ sp c) :
    (∀ t k f, σ.slots t k f = sp.slots t k f) ∧
      ∀ g, lay.shared g = false → σ.globs g = sp.globs g := by
  refine ⟨fun t k f => ?_, fun g hg => ?_⟩
  · have hn : ¬ Tg (.inl t) := fun ht => by
      obtain ⟨g, hg, _⟩ := hT _ ht
      exact absurd hg (by simp)
    have := h _ hn
    simp only [TraegerGleich] at this
    rw [this]
  · have hn : ¬ Tg (.inr g) := fun ht => by
      obtain ⟨g', hg', hs⟩ := hT _ ht
      have := Sum.inr.inj hg'
      subst this
      rw [hs] at hg
      exact Bool.noConfusion hg
    have := h _ hn
    simp only [TraegerGleich] at this
    rw [this]

/-- **A representation of the machine's memory is one of every presented memory.** -/
theorem rep_presented {lay : Layout D} {Tg : D.Tab ⊕ D.Glob → Prop} (hT : TgShared lay Tg)
    {σ sp : Speicher D} (h : ∀ c, ¬ Tg c → TraegerGleich σ sp c) {tr tr' : List (Gabbro.Grammatik.Ereignis D)}
    {m : Mem} (hR : Rep lay (sp.welt tr) m) : Rep lay (σ.welt tr') m := by
  obtain ⟨h1, h2⟩ := agree_outside hT h
  exact rep_agree (σ := sp.welt tr) (σ' := σ.welt tr') h1 h2 hR

/-- **A representation of the step's memory is one of the successor GX leaves**, for the memory the GX step takes
    from the step (`M''`) outside `Tg`. -/
theorem rep_successor {lay : Layout D} {Tg : D.Tab ⊕ D.Glob → Prop} (hT : TgShared lay Tg)
    {s' s'' : Speicher D} (h : ∀ c, ¬ Tg c → TraegerGleich s' s'' c) {tr tr' : List (Gabbro.Grammatik.Ereignis D)}
    {m : Mem} (hR : Rep lay (s''.welt tr) m) : Rep lay (s'.welt tr') m := by
  obtain ⟨h1, h2⟩ := agree_outside hT h
  exact rep_agree (σ := s''.welt tr) (σ' := s'.welt tr') h1 h2 hR

/-- **The memory half of the GX simulation**: a GX step is a G step on a presented memory; if the IR memory `m`
    represents the machine's memory, it represents the presented one (so the G step's refinement applies), and if
    the IR memory `m'` the run leaves represents the memory of G's step, it represents the memory the GX step
    leaves. -/
theorem rep_gx {lay : Layout D} {Tg : D.Tab ⊕ D.Glob → Prop} (hT : TgShared lay Tg)
    {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittGX P O passes Tg M u M') {m : Mem} (hR : Rep lay (M.speicher.welt []) m) :
    ∃ (σ : Speicher D) (M'' : RufMaschineG D),
      Gabbro.Grammatik.RufSchrittG P O passes (mitSpeicher M σ) u M'' ∧ Rep lay (σ.welt []) m ∧
      ∀ m' : Mem, Rep lay (M''.speicher.welt []) m' → Rep lay (M'.speicher.welt []) m' := by
  obtain ⟨σ, M'', hg, hσ, h1, h2, h3, h4, h5⟩ := hs
  refine ⟨σ, M'', hg, rep_presented hT hσ hR, fun m' hR' => ?_⟩
  exact rep_successor hT (Gabbro.Grammatik.gx_aussen hσ h1 h2) hR'

end Gabbro.Code.Lower
