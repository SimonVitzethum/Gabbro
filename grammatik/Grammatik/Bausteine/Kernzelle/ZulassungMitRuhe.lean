module

public import Grammatik.Bausteine.Kernzelle.Zulassung
public import Grammatik.Bausteine.Kernzelle.KernAbfrageBindung
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T3

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

variable {D : Deklaration}

variable [DecidableEq D.Fn]

variable [DecidableEq D.Ax]

/-! ## The idle-root transfer -/

/-- Signature facts ride `some` (types shift by `tyR`, which fixes `int`). -/
theorem params_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.params (some f) = (D.params f).map tyR := rfl

theorem erg_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.erg (some f) = (D.erg f).map tyR := rfl

theorem gruende_mitRuhe_some (f : D.Fn) :
    D.mitRuhe.gruende (some f) = D.gruende f := rfl

theorem gtyp_mitRuhe (g : D.Glob) : D.mitRuhe.gtyp g = tyR (D.gtyp g) := rfl

/-- The idle root writes nothing. -/
theorem traegerSchreibt_mitRuhe_ruhe (P : Programm D) (c : D.mitRuhe.Tab ⊕ D.mitRuhe.Glob) :
    TraegerSchreibt (D := D.mitRuhe) none c = false := by
  cases c <;> rfl

/-- Transfer of one declaration's admission to the idle-root program. -/
theorem akkuZulaessig_mitRuhe (P : Programm D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {a : AccumulatorDecl D} (h : akkuZulaessig P fs a) :
    akkuZulaessig P.mitRuhe (fsRuhe fs) (AccumulatorDecl.mitRuhe a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, fun i => ?_, fun f' hf1 hf2 i => ?_, ?_, ?_, ?_, ?_, h7⟩
  · obtain ⟨hN, hB, hG, hW, hT, hZ, hS, hUF⟩ := h0
    refine ⟨hN, hB, hG, hW, fun i => ?_, hZ, hS,
      fun hcon => hUF (Option.some.inj hcon)⟩
    show D.mitRuhe.gtyp (a.zellen i) = Ty.int a.lo a.hi
    exact congrArg tyR (hT i)
  · show D.mitRuhe.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)]
    exact h1 i
  · cases f' with
    | none =>
        refine ⟨traegerSchreibt_mitRuhe_ruhe P _, ?_⟩
        rw [fussOrteG_mitRuhe_ruhe P]
        exact fun h => List.not_mem_nil h
    | some f =>
        have hf1' : f ≠ a.aktualisiere := fun hcon => hf1 (congrArg some hcon)
        have hf2' : f ≠ a.falte := fun hcon => hf2 (congrArg some hcon)
        obtain ⟨hw, hf⟩ := h2 f hf1' hf2' i
        refine ⟨?_, ?_⟩
        · show TraegerSchreibt (D := D.mitRuhe) (some f) _ = false
          exact hw
        · show _ ∉ fussOrteG P.mitRuhe (some f)
          rw [fussOrteG_mitRuhe]
          exact hf
  · obtain ⟨h31, h32, h33, h34⟩ := h3
    refine ⟨?_, ?_, ?_, fun c => ?_⟩
    · show D.mitRuhe.params (some a.kernAbfrage) = []
      exact congrArg (List.map tyR) h31
    · show D.mitRuhe.erg (some a.kernAbfrage) = some (Ty.int 0 _)
      exact congrArg (Option.map tyR) h32
    · show D.mitRuhe.gruende (some a.kernAbfrage) = 0
      rw [gruende_mitRuhe_some, h33]
    · show TraegerSchreibt (D := D.mitRuhe) (some a.kernAbfrage) c = false
      have hw := h34 c
      cases c <;> exact hw
  · obtain ⟨h41, h42, h43, h44⟩ := h4
    refine ⟨?_, fun f' hf' => ?_, ?_, ?_⟩
    · show reachB P.mitRuhe (fsRuhe fs) (some a.aktualisiere) (some a.kernAbfrage) = true
      rw [reachB_mitRuhe P hvoll hAbg]
      exact h41
    · cases f' with
      | none =>
          have hf2 : reachB P.mitRuhe (fsRuhe fs) (some a.aktualisiere) none = true := hf'
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf2
          cases hf2
      | some f =>
          have hf2 : reachB P.mitRuhe (fsRuhe fs) (some a.aktualisiere) (some f) = true := hf'
          rw [reachB_mitRuhe P hvoll hAbg] at hf2
          obtain ⟨hcc, hm⟩ := h42 f hf2
          refine ⟨fun c hc => ?_, ?_⟩
          · have hc' : TraegerSchreibt f c = true := by
              cases c <;> exact hc
            obtain ⟨i, hi⟩ := hcc c hc'
            exact ⟨i, hi⟩
          · show mE (bodenM (some f)) (P.mitRuhe.rumpf (some f)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm
    · show D.mitRuhe.params (some a.aktualisiere) = _
      exact congrArg (List.map tyR) h43
    · show D.mitRuhe.erg (some a.aktualisiere) = _
      exact congrArg (Option.map tyR) h44
  · obtain ⟨h51, h52, h53⟩ := h5
    refine ⟨?_, ?_, fun f' hf' => ?_⟩
    · show D.mitRuhe.params (some a.falte) = []
      exact congrArg (List.map tyR) h51
    · show D.mitRuhe.erg (some a.falte) = _
      exact congrArg (Option.map tyR) h52
    · cases f' with
      | none =>
          have hf2 : reachB P.mitRuhe (fsRuhe fs) (some a.falte) none = true := hf'
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf2
          cases hf2
      | some f =>
          have hf2 : reachB P.mitRuhe (fsRuhe fs) (some a.falte) (some f) = true := hf'
          rw [reachB_mitRuhe P hvoll hAbg] at hf2
          obtain ⟨hcc, hm⟩ := h53 f hf2
          refine ⟨fun c => ?_, ?_⟩
          · have hw := hcc c
            cases c <;> exact hw
          · show mE (bodenM (some f)) (P.mitRuhe.rumpf (some f)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm
  · obtain ⟨q, hq⟩ := h6
    exact ⟨q, kernAbfrageVerbunden_mitRuhe P hq⟩

/-- Transfer of the admission to the idle-root program. -/
theorem accumulatorAdmission_mitRuhe (P : Programm D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {A : List (AccumulatorDecl D)} (h : AccumulatorAdmission P fs A) :
    AccumulatorAdmission P.mitRuhe (fsRuhe fs) (A.map AccumulatorDecl.mitRuhe) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact akkuZulaessig_mitRuhe P hvoll hAbg (h1 a ha)
  · -- cells ride the identity map
    have e : alleZellen (A.map AccumulatorDecl.mitRuhe) = alleZellen A := by
      simp only [alleZellen, List.flatMap_map, mitRuhe_kernZahl,
        mitRuhe_zellen]
    rw [e]
    exact h2
  · have e : alleSperren (A.map AccumulatorDecl.mitRuhe) = alleSperren A := by
      simp only [alleSperren, List.flatMap_map, mitRuhe_kernZahl,
        mitRuhe_sperren]
    rw [e]
    exact h3

#print axioms Gabbro.Grammatik.Kernzelle.akkuZulaessig_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorAdmission_mitRuhe

end Gabbro.Grammatik.Kernzelle
