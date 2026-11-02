module

public import Grammatik.Bausteine.Kernzelle.Zulassung

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

variable [DecidableEq D.Fn]

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
    TraegerSchreibt P.mitRuhe none c = false := by
  cases c <;> rfl

/-- Transfer of one declaration's admission to the idle-root program. -/
theorem akkuZulaessig_mitRuhe (P : Programm D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {a : AccumulatorDecl D} (h : akkuZulaessig P fs a) :
    akkuZulaessig P.mitRuhe (fsRuhe fs) (AccumulatorDecl.mitRuhe a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, fun i => ?_, fun f' hf1 hf2 i => ?_, ?_, ?_, ?_⟩
  · refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun i => ?_,
      fun i j hij => h0.2.2.2.2.2.1 hij, fun i j hij => h0.2.2.2.2.2.2.1 hij,
      fun hcon => h0.2.2.2.2.2.2.2 (Option.some_injective hcon)⟩
    show D.mitRuhe.gtyp (a.zellen i) = Ty.int a.lo a.hi
    rw [gtyp_mitRuhe, h0.2.2.2.2.1 i]
  · show D.mitRuhe.gbraucht (a.zellen i) = [Sum.inl (a.sperren i)]
    exact h1 i
  · cases f' with
    | none =>
        refine ⟨traegerSchreibt_mitRuhe_ruhe P _, ?_⟩
        rw [fussOrteG_mitRuhe_ruhe P]
        exact List.not_mem_nil _
    | some f =>
        have hf1' : f ≠ a.aktualisiere := fun hcon => hf1 (congrArg some hcon)
        have hf2' : f ≠ a.falte := fun hcon => hf2 (congrArg some hcon)
        obtain ⟨hw, hf⟩ := h2 f hf1' hf2' i
        refine ⟨?_, ?_⟩
        · show TraegerSchreibt P.mitRuhe (some f) _ = false
          simpa only [traegerSchreibt_mitRuhe] using hw
        · show _ ∉ fussOrteG P.mitRuhe (some f)
          rw [fussOrteG_mitRuhe]
          exact hf
  · obtain ⟨h31, h32, h33, h34⟩ := h3
    refine ⟨?_, ?_, ?_, fun c => ?_⟩
    · show D.mitRuhe.params (some a.kernAbfrage) = []
      rw [params_mitRuhe_some, h31]
    · show D.mitRuhe.erg (some a.kernAbfrage) = some (Ty.int 0 _)
      rw [erg_mitRuhe_some, h32]
    · show D.mitRuhe.gruende (some a.kernAbfrage) = 0
      rw [gruende_mitRuhe_some, h33]
    · show TraegerSchreibt P.mitRuhe (some a.kernAbfrage) c = false
      rw [traegerSchreibt_mitRuhe]
      exact h34 c
  · obtain ⟨h41, h42, h43, h44⟩ := h4
    refine ⟨?_, fun f' hf' => ?_, ?_, ?_⟩
    · show reachB P.mitRuhe (fsRuhe fs) (some a.aktualisiere) (some a.kernAbfrage) = true
      rw [reachB_mitRuhe P hvoll hAbg]
      exact h41
    · cases f' with
      | none =>
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf'
          cases hf'
      | some f =>
          obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
          obtain ⟨hcc, hm⟩ := h42 g hg
          refine ⟨fun c hc => ?_, ?_⟩
          · have hc' : TraegerSchreibt P g c = true := by
              simpa only [traegerSchreibt_mitRuhe] using hc
            obtain ⟨i, hi⟩ := hcc c hc'
            exact ⟨i, hi⟩
          · show mE (bodenM (some g)) (P.mitRuhe.rumpf (some g)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm
    · show D.mitRuhe.params (some a.aktualisiere) = _
      rw [params_mitRuhe_some, h43]
    · show D.mitRuhe.erg (some a.aktualisiere) = _
      rw [erg_mitRuhe_some, h44]
  · obtain ⟨h51, h52, h53⟩ := h5
    refine ⟨?_, ?_, fun f' hf' => ?_⟩
    · show D.mitRuhe.params (some a.falte) = []
      rw [params_mitRuhe_some, h51]
    · show D.mitRuhe.erg (some a.falte) = _
      rw [erg_mitRuhe_some, h52]
    · cases f' with
      | none =>
          rw [reachB_mitRuhe_nicht_ruhe P hAbg] at hf'
          cases hf'
      | some f =>
          obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
          obtain ⟨hcc, hm⟩ := h53 g hg
          refine ⟨fun c => ?_, ?_⟩
          · have hc' : TraegerSchreibt P g c = false := by
              simpa only [traegerSchreibt_mitRuhe] using hcc c
            exact hc'
          · show mE (bodenM (some g)) (P.mitRuhe.rumpf (some g)) = true
            rw [rumpf_mitRuhe_mE]
            exact hm

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
      simp only [alleZellen, List.flatMap_map, Function.comp_apply, mitRuhe_kernZahl,
        mitRuhe_zellen]
    rw [e]
    exact h2
  · have e : alleSperren (A.map AccumulatorDecl.mitRuhe) = alleSperren A := by
      simp only [alleSperren, List.flatMap_map, Function.comp_apply, mitRuhe_kernZahl,
        mitRuhe_sperren]
    rw [e]
    exact h3

#print axioms Gabbro.Grammatik.Kernzelle.akkuZulaessig_mitRuhe
#print axioms Gabbro.Grammatik.Kernzelle.accumulatorAdmission_mitRuhe

end Gabbro.Grammatik.Kernzelle
