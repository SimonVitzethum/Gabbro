module
public import Grammatik.Zielsatz.Projekte.Komposition
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Projekte/Ohne.lean
  Subject:   The user obligation of a program WITHOUT contracts and invariants, decided.

  A project whose functions carry no `requires`, no `ensures` and no table invariant, whose bodies
  pass the Bool `logikFrei` and whose declaration has no atomic global, owes nothing beyond what
  the checker decides: `nutzerTeilO_ohne` gives its `NutzerTeilO`, at every budget and for every
  project of the program. C06 pointer-interface refinement remains an explicit owner duty;
  trivial function bodies alone do not establish arbitrary interface posts.
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

/-- Body logic is independent of the separately owed pointer-interface refinement. -/
private theorem bodyLogic_ohne {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hreq : ∀ g, P.requires g = .tru) (hens : ∀ g, P.ensures g = .tru) (hinv : D.invs = [])
    (hfrei : programmLogikFrei P fs = true) (passes : Nat) (f : D.Fn) :
    KoerperGutS P passes (axWahr D) (SperrInv.leer D) f ∧
      InvGutS P passes (axWahr D) (SperrInv.leer D) f ∧
      InvGutGrund P passes (axWahr D) (SperrInv.leer D) f :=
  ⟨koerperGutS_leer ⟨koerperGutRQ_of_R _ (koerperGutR_ohne hreq (hens f)
        ((List.all_eq_true.mp hfrei) f (hvoll f))), programmLogikFrei_ok hvoll hfrei passes _ f⟩,
      invGutS_leer hinv f, by
        unfold InvGutGrund
        intros
        unfold InvAmRueck
        intro i hi
        rw [hinv] at hi
        cases hi⟩

/-- The full collection consumes the canonical C06 refinement rather than deriving it from bodies. -/
theorem logikPflicht_ohne {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hreq : ∀ g, P.requires g = .tru) (hens : ∀ g, P.ensures g = .tru) (hinv : D.invs = [])
    (hfrei : programmLogikFrei P fs = true) (hPtr : PtrVerfeinert P) :
    LogikPflicht P (SperrInv.leer D) (axWahr D) :=
  ⟨bodyLogic_ohne hvoll hreq hens hinv hfrei, fun _ _ _ _ => rfl, axEnsLokal_wahr, hPtr⟩

/-- Without an atomic global the body logic carries to the open-world rely;
    the project supplies refinement only for the targets it owns. -/
theorem nutzerTeilO_ohne [DecidableEq D.Fn] {p : Projekt D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hat : ∀ g : D.Glob, D.atomar g = false)
    (hP : p.E.S = SperrInv.leer D) (hQ : p.E.Q = axWahr D)
    (hreq : ∀ g, p.E.P.requires g = .tru) (hens : ∀ g, p.E.P.ensures g = .tru) (hinv : D.invs = [])
    (hfrei : programmLogikFrei p.E.P fs = true)
    (hPtr : ∀ f, p.eigen f = true → ∀ n (hf : D.passt f n = true),
      PtrZielVerfeinert p.E.P f n hf)
    (hstart : ∀ a ∈ p.E.starts ++ p.E.gestartet, ReqAmEintritt p.E.P a.1 (p.E.sp0.welt []) a.2) :
    NutzerTeilO p := by
  have free : ∀ f, LiestNicht p.E.P OffenA f := by
    intro f c _ hc
    obtain ⟨g, _, hg⟩ := hc.1
    rw [hat g] at hg
    cases hg
  refine ⟨⟨fun passes f _ => ?_, ?_, ?_, hPtr⟩, ⟨fun L _ => ?_, hstart⟩⟩
  · obtain ⟨k, i, g⟩ := bodyLogic_ohne hvoll hreq hens hinv hfrei passes f
    rw [← hP, ← hQ] at k i g
    exact ⟨koerperGutSA_of_frei (free f) k, invGutSA_of_frei (free f) i,
      invGutGrundA_of_frei (free f) g⟩
  · rw [hP]; exact fun _ _ _ _ => rfl
  · rw [hQ]; exact axEnsLokal_wahr
  · rw [hP]; rfl

#print axioms koerperGutR_ohne
#print axioms nutzerTeilO_ohne

end Gabbro.Grammatik.Zielsatz
