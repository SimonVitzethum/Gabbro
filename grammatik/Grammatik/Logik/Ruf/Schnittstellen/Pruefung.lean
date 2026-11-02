module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- No pointer interface contract mentions `c`: neither pre nor post of any
    signature number. This is the pointer half of `VertragsFrei`; a shared
    atomic read cannot be hidden in a pointer predicate. -/
def PtrVertragsFrei (P : Programm D) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ n, c ∉ (P.ptrVertrag n).pre.orte ∧ c ∉ (P.ptrVertrag n).post.orte

/-- The pointer half, decided over an explicit finite signature inventory
    `ns`. Unchecked numbers must carry empty contracts (`htriv` in the
    soundness lemma); the exporter only lowers finitely many nontrivial
    interfaces, the rest stay `trivial` by default. -/
def ptrVertragsFreiB (P : Programm D) (ns : List Nat) (c : D.Tab ⊕ D.Glob) : Bool :=
  ns.all fun n => !(istIn (P.ptrVertrag n).pre.orte c) && !(istIn (P.ptrVertrag n).post.orte c)

theorem ptrVertragsFreiB_ok {P : Programm D} {ns : List Nat} {c : D.Tab ⊕ D.Glob}
    (htriv : ∀ n, n ∉ ns → (P.ptrVertrag n).pre.orte = [] ∧ (P.ptrVertrag n).post.orte = [])
    (h : ptrVertragsFreiB P ns c = true) : PtrVertragsFrei P c := by
  intro n
  by_cases hm : n ∈ ns
  · have h1 := (List.all_eq_true.mp h) n hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨h1, h2⟩ := h1
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [istIn_iff.mpr hc] at h1
      cases h1
    · rw [istIn_iff.mpr hc] at h2
      cases h2
  · obtain ⟨hpre, hpost⟩ := htriv n hm
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hpre] at hc
      exact absurd hc List.not_mem_nil
    · rw [hpost] at hc
      exact absurd hc List.not_mem_nil

/-- The guards of a pointer interface contract are its signature locks.
    This is the interface twin of `vertrag_darf`: `pre` lives under
    `Signatur.anfang`, `post` under `Vertrag.ende`, so every guard of a
    contract carrier is held by the interface signature. -/
theorem ptr_vertrag_darf (P : Programm D) (n : Nat) :
    ∀ o ∈ (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte, ∀ L, Bewacht o L →
      L ∈ (D.sigNr n).haelt := by
  intro o ho L hB
  rcases List.mem_append.mp ho with ho | ho
  · have h := bewacht_held ((P.ptrVertrag n).pre.orte_darf o ho) hB
    unfold Signatur.anfang at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨K, hK, e⟩ := List.mem_map.mp h
      cases e
      exact hK
    · obtain ⟨m, _, e⟩ := List.mem_map.mp h
      cases m
      cases e
  · have h := bewacht_held ((P.ptrVertrag n).post.orte_darf o ho) hB
    unfold Vertrag.ende at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨K, hK, e⟩ := List.mem_map.mp h
      cases e
      exact hK
    · obtain ⟨m, _, e⟩ := List.mem_map.mp h
      cases m
      cases e

/-- A pointer interface contract's carriers are stable at an indirect call.
    Their guards are the interface signature locks, which the caller holds
    at the call (`RufPasst.hh`); the footprint inclusion holds because the
    checker footprint `fussOrteG` carries the interface pre/post orte at
    every indirect site. -/
theorem ptr_vertrag_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
    {f : D.Fn} (hF : FussS P S lok f) {V : Vertrag D} {Λ : List (Res D)} {n : Nat}
    (hp : RufPasst D V (D.sigNr n) Λ)
    (h : (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte ⊆ fussOrteG P f) :
    (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte ⊆ stabilS P S lok f Λ :=
  fun _ ho => stabil_of_fuss hF (h ho) fun L hB =>
    hp.hh L (ptr_vertrag_darf P n _ ho L hB)

/-- Indirect call-graph closure is already in `AbgK`: a closed graph admits
    every admitted target of every indirect site. If `f` is in the closed
    set and its body passes the call-graph check, then every function that
    conforms to an indirect signature `n` used at a `callInd` site is in the
    set. The refinement duty for the pair stays user proof in
    `LogikPflicht`; this lemma only carries the structural closure the
    checker decides. -/
theorem abgK_indirekt_schliesst {P : Programm D} {fs : List D.Fn} {Z : D.Fn → Bool}
    (hAbg : AbgK P fs Z) {f : D.Fn} (hf : Z f = true) {n : Nat}
    (hsite : (rufM fs Z).ind n = true) {g : D.Fn} (hg : D.passt g n = true)
    (hvoll : ∀ g : D.Fn, g ∈ fs) : Z g = true := by
  unfold rufM at hsite
  simp only at hsite
  have h1 := (List.all_eq_true.mp hsite) g (hvoll g)
  rw [hg] at h1
  simpa using h1

end Gabbro.Grammatik
