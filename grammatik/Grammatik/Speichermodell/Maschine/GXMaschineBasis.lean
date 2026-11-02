/-
  File:      Grammatik/Speichermodell/GXMaschine.lean
  Subject:   THE THREAD MACHINE AND THE TIME SEGMENTS OVER MACHINE GX (Opus lane O25c, 2026-09-26,
             OFFEN O25). Definitions and machine-level lemmas; no program fact.

  Machine GX (`RufSchrittGX`, AtomarLauf.lean) is machine G whose reads of the shared atomics
  `Tg` are answered by the weak memory: a G step on a PRESENTED memory that agrees with G's
  outside `Tg`. Every W step of an accepted program is a GX step (`schwach_ist_gX`). The goal
  statement speaks, since lane O25c, about runs of GX with threads spawned at run time. This
  file builds that machine the way FadenMaschine.lean builds it over G:

  * `FadenSchrittX`, `FadenErreichbarX` -- the thread machine with GX in place of G in its `lauf`
    rule; `start`, `kind`, `join` are FadenMaschine.lean's word for word;
  * `fadenSchrittX_of`, `fadenErreichbarX_of` -- every thread-machine run over G is one over GX
    (a G step is a GX step presenting G's own memory, `gx_aus_g`): nothing is lost;
  * `fadenErreichbarX_GX`, `fadenErreichbarX_von_GX` -- the bridge to GX and back, as for G;
  * `FadenInvX` and its lemmas -- `FadenInv` with a GX run in its `lauf` field;
  * `gx_leer_g` -- with NO shared atomic (`Tg` empty) a GX step IS a G step, so GX over an empty
    `Tg` is G (used to derive the statement of before);
  * `SegLaufX`, `segZaehleX`, `aktivVorX`, `frame_schritte_beschraenktX` -- the time bound of
    KostenG.lean over GX segments: a thread's step count depends on its own frames only, which a
    GX step moves exactly as its inner G step does.
-/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.Threads.FadenMaschine
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Speichermodell.Atomar.AtomarLauf
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. GX steps: facts about threads -/

section GX

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- A thread other than the actor keeps its state over a GX step. -/
theorem gxSchritt_fremd {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') (t : Faden) (htu : t ≠ u) :
    M'.faeden t = M.faeden t := by
  obtain ⟨σ, M'', hs, _, _, _, hfa, _, _⟩ := h
  rw [hfa]
  exact rufSchrittG_fremd hs t htu

/-- **With no shared atomic a GX step is a G step**: the presented memory is G's, and the
    successor is the inner step's machine. -/
theorem gx_leer_g (hT : ∀ c, ¬ Tg c) {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') : RufSchrittG P O passes M u M' := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, hfa, hla, hst⟩ := h
  have eσ : σ = M.speicher := speicher_ext fun c => hσ c (hT c)
  subst eσ
  rw [mitSpeicher_selbst] at hs h1 h2
  have esp : M'.speicher = M''.speicher := speicher_ext fun c => by
    by_cases hw : SchreibG M M'' u c
    · exact h1 c hw
    · exact traegerGleich_trans (h2 c hw)
        (traegerGleich_symm (traegerGleich_of_nicht_schreib (M := M) (M' := M'') hw))
  have e : M' = M'' := by
    cases M' with
    | mk sp fa la st =>
      cases M'' with
      | mk sp' fa' la' st' =>
        simp only at esp hfa hla hst
        subst esp hfa hla hst
        rfl
  rw [e]
  exact hs

theorem gx_leer_g_lauf (hT : ∀ c, ¬ Tg c) {M0 M : RufMaschineG D}
    (h : RufErreichbarGX P O passes Tg M0 M) : RufErreichbarG P O passes M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ _ ih (gx_leer_g hT hs)

/-- GX is monotone in the shared atomics: a larger `Tg` admits more presented memories. -/
theorem gx_mono {Tg' : D.Tab ⊕ D.Glob → Prop} (hT : ∀ c, Tg c → Tg' c) {M M' : RufMaschineG D}
    {u : Faden} (h : RufSchrittGX P O passes Tg M u M') : RufSchrittGX P O passes Tg' M u M' := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨σ, M'', hs, fun c hc => hσ c fun ht => hc (hT c ht), h1, h2, h3, h4, h5⟩

end GX

end Gabbro.Grammatik
