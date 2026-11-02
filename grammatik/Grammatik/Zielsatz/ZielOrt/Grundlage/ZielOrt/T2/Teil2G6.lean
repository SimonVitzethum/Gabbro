module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Sperren
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for group-6 steps** (`RufSchrittG6`: the top-level foreign
    calls `endeBindAxiomElse*`). Same statement as `schritt_traeger`,
    specialised to group 6 so that `ZielOrt/T2/Teil2.lean` stays below the
    file-size limit. The C08 generalized fallible calls at the top level of a
    body (`endeBindAxiomOptElseOk`, `endeBindAxiomOptElseGrund`) are proved
    exactly like their twins (`endeBindAxiomElseOk`,
    `endeBindAxiomElseGrund`): the write footprint from `hd`/`hgd`, the frame
    from the oracle's answer (`hfr`), and the signature permission from
    `RufPasst` (`hp.hw`/`hp.hg`, whose signature is the axiom's declared
    shape `D.asignatur a`). -/
theorem schritt_traeger_g6 (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG6 P O passes M u M') (c : D.Tab ⊕ D.Glob)
    (hc : (∃ L, Bewacht c L ∧ L ∉ offen (M.faeden u).spur) ∨
      TraegerSchreibt (M.faeden u).kopf.f c = false) :
    TraegerGleich M'.speicher M.speicher c := by
  cases hs with
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
      rw [← e] at hfr
      cases c with
      | inl t =>
          show σ₂.slots t = M.speicher.slots t
          have ha : D.aschreibt a t = false := by
            cases hat : D.aschreibt a t with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hd t hat _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hw t hat
                  rw [hW] at this
                  exact Bool.false_ne_true this
          funext k fld
          rw [hfr.1 t ha k fld, hs₁]
          rfl
      | inr x =>
          show σ₂.globs x = M.speicher.globs x
          have ha : D.agschreibt a x = false := by
            cases hax' : D.agschreibt a x with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hgd x hax' _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hg x hax'
                  rw [hW] at this
                  exact Bool.false_ne_true this
          rw [hfr.2 x ha, hs₁]
          rfl
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
      rw [← e] at hfr
      cases c with
      | inl t =>
          show σ₂.slots t = M.speicher.slots t
          have ha : D.aschreibt a t = false := by
            cases hat : D.aschreibt a t with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hd t hat _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hw t hat
                  rw [hW] at this
                  exact Bool.false_ne_true this
          funext k fld
          rw [hfr.1 t ha k fld, hs₁]
          rfl
      | inr x =>
          show σ₂.globs x = M.speicher.globs x
          have ha : D.agschreibt a x = false := by
            cases hax' : D.agschreibt a x with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hgd x hax' _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hg x hax'
                  rw [hW] at this
                  exact Bool.false_ne_true this
          rw [hfr.2 x ha, hs₁]
          rfl
  | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
      rw [← e] at hfr
      cases c with
      | inl t =>
          show σ₂.slots t = M.speicher.slots t
          have ha : D.aschreibt a t = false := by
            cases hat : D.aschreibt a t with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hd t hat _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hp.hw t hat
                  rw [hW] at this
                  exact Bool.false_ne_true this
          funext k fld
          rw [hfr.1 t ha k fld, hs₁]
          rfl
      | inr x =>
          show σ₂.globs x = M.speicher.globs x
          have ha : D.agschreibt a x = false := by
            cases hax' : D.agschreibt a x with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hgd x hax' _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hp.hg x hax'
                  rw [hW] at this
                  exact Bool.false_ne_true this
          rw [hfr.2 x ha, hs₁]
          rfl
  | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      have e : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
      rw [← e] at hfr
      cases c with
      | inl t =>
          show σ₂.slots t = M.speicher.slots t
          have ha : D.aschreibt a t = false := by
            cases hat : D.aschreibt a t with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hd t hat _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hp.hw t hat
                  rw [hW] at this
                  exact Bool.false_ne_true this
          funext k fld
          rw [hfr.1 t ha k fld, hs₁]
          rfl
      | inr x =>
          show σ₂.globs x = M.speicher.globs x
          have ha : D.agschreibt a x = false := by
            cases hax' : D.agschreibt a x with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hgd x hax' _ hB
                    simpa [Res.von] using this
                  exact hfrei (hΛ L hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hp.hg x hax'
                  rw [hW] at this
                  exact Bool.false_ne_true this
          rw [hfr.2 x ha, hs₁]
          rfl

end Sperren

end Gabbro.Grammatik
