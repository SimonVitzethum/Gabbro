import Grammatik.Zielsatz.Projekte.Komposition

/-!
  File:      Grammatik/Zielsatz/Projekte/Ohne.lean
  Subject:   The user obligation of a program WITHOUT contracts and invariants, decided.

  A project whose functions carry no `requires`, no `ensures` and no table invariant, whose bodies
  pass the Bool `logikFrei` and whose declaration has no atomic global, owes nothing beyond what
  the checker decides: `nutzerTeilO_ohne` gives its `NutzerTeilO`, at every budget and for every
  project of the program. It is how a library of plain helpers is linked without a single
  hand-written proof.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **No contract, a `logik`-free body: the body triple holds.** The callees have no `requires`,
    so the caller never blames itself (`logikFrei_ok` with "no precondition failure"); the
    `ensures` is `true`. -/
theorem koerperGutR_ohne {P : Programm D} {passes : Nat} {f : D.Fn}
    (hreq : ∀ g, P.requires g = .tru) (hens : P.ensures f = .tru)
    (hfrei : (P.rumpf f).logikFrei = true) : KoerperGutR P passes f := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun σ' v _ => by unfold EnsAmRueck; rw [hens]; rfl, fun g h => ?_⟩
  have hT : ∀ g' σ' ρ' e, torRuf P R g' σ' ρ' = RufAusgang.logik e → ∀ g'', e ≠ .vorbedingung g'' := by
    intro g' σ' ρ' e he
    unfold torRuf at he
    rw [hreq g'] at he
    exact hOV g' σ' ρ' e he
  exact Endblock.logikFrei_ok O' passes (torRuf P R) hT (P.rumpf f) hfrei σ ρ _ h g rfl

/-- **The user's sequential logic of such a program.** -/
theorem logikPflicht_ohne {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hreq : ∀ g, P.requires g = .tru) (hens : ∀ g, P.ensures g = .tru) (hinv : D.invs = [])
    (hfrei : programmLogikFrei P fs = true) :
    LogikPflicht P (SperrInv.leer D) (axWahr D) :=
  ⟨fun passes f => ⟨koerperGutS_leer ⟨koerperGutRQ_of_R _ (koerperGutR_ohne hreq (hens f)
        ((List.all_eq_true.mp hfrei) f (hvoll f))), programmLogikFrei_ok hvoll hfrei passes _ f⟩,
      invGutS_leer hinv f, by
        unfold InvGutGrund
        intros
        unfold InvAmRueck
        intro i hi
        rw [hinv] at hi
        cases hi⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr⟩

/-- **Such a project owes nothing a human writes**: without an atomic global the open-world rely
    is empty, and the sequential logic is the logic with the rely. -/
theorem nutzerTeilO_ohne [DecidableEq D.Fn] {p : Projekt D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hat : ∀ g : D.Glob, D.atomar g = false)
    (hP : p.E.S = SperrInv.leer D) (hQ : p.E.Q = axWahr D)
    (hreq : ∀ g, p.E.P.requires g = .tru) (hens : ∀ g, p.E.P.ensures g = .tru) (hinv : D.invs = [])
    (hfrei : programmLogikFrei p.E.P fs = true)
    (hstart : ∀ a ∈ p.E.starts ++ p.E.gestartet, ReqAmEintritt p.E.P a.1 (p.E.sp0.welt []) a.2) :
    NutzerTeilO p := by
  have hL := logikPflichtA_of_frei (T := OffenA) (fun f c _ hc => by
      obtain ⟨g, _, hg⟩ := hc.1
      rw [hat g] at hg
      cases hg) (logikPflicht_ohne hvoll hreq hens hinv hfrei)
  rw [← hP, ← hQ] at hL
  refine ⟨⟨fun passes f _ => hL.1 passes f, hL.2⟩, ⟨fun L => ?_, hstart⟩⟩
  rw [hP]
  rfl

#print axioms koerperGutR_ohne
#print axioms nutzerTeilO_ohne

end Gabbro.Grammatik.Zielsatz
