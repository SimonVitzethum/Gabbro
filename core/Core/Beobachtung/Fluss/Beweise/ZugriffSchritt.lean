/-
  File:      core/Core/Beobachtung/Fluss/Beweise/ZugriffSchritt.lean
  Subject:   THE STEP-LEVEL PART OF `ZugriffNIAussage` (MK-04, MK-13). The information flow of an
             access instruction splits into a step-level part, which `RegelFluss` carries for every
             form, and a run-level lifting, which is not a consequence of the premises.

             Proved here: two form steps of one access instruction from publicly equal source states
             end in publicly equal states with equal plan and output views (`zugriffSchrittNI`); the
             head of an access instruction respects public source-state equality together with the
             machine status equality carried by the coupling (`zugriffKopfGleich`); and, because the
             unit labels nothing, equal plan views already give equal public read labels
             (`zugriffPlanSicht_lesen`).

             Missing step: the coupling `Kopplung` does not carry the memory graph. Two coupled states
             can differ in `HatQuelle` for a cell and in the reads-from resolution, so two
             `FuehrtSchrittAus` steps with equal plan views can append different public memory events
             (a lazily materialised initial write on one side only). Closing this needs the graph-level
             coupling of MK-13: an inductive graph relation on the coupled states for public cells,
             maintained step by step, plus the one-label `Speicherfolge` determinism it enables.
-/
module

public import Core.Beobachtung.Fluss.Fragment
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.NISichtbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

/-- Two steps of one form from public-equal source states stay public-equal, with equal plan and
    output views. This is the whole step-level content of `RegelFluss`; it holds for access
    instructions as for every other form, independently of the head of a second run. -/
theorem zugriffSchrittNI (p : Fragment) (plattform : Plattform) (f : Befehl)
    (familie : f.familie = .zugriff) (fluss : RegelFluss (p.einheit plattform) f) :
    ∀ {c : Kontext} {v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂},
      QuellzustandGleich (p.einheit plattform) v₁ v₂ →
      FormSchritt (p.einheit plattform) f c v₁ w₁ p₁ u₁ →
      FormSchritt (p.einheit plattform) f c v₂ w₂ p₂ u₂ →
      QuellzustandGleich (p.einheit plattform) u₁ u₂ ∧
        PlanSicht (p.einheit plattform) p₁ = PlanSicht (p.einheit plattform) p₂ ∧
          AusgabeSicht (p.einheit plattform) c v₁ u₁ = AusgabeSicht (p.einheit plattform) c v₂ u₂ := by
  intro c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich s₁ s₂
  unfold RegelFluss at fluss
  by_cases pub : oeffentlich ((p.einheit plattform).fluss.kontrolle f) = true
  · exact fluss.2 pub c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich s₁ s₂
  · have pubf : oeffentlich ((p.einheit plattform).fluss.kontrolle f) = false := by
      cases hb : oeffentlich ((p.einheit plattform).fluss.kontrolle f) <;> simp_all
    have o₁ := (fluss.1 c v₁ w₁ p₁ u₁ s₁).2 pubf
    have o₂ := (fluss.1 c v₂ w₂ p₂ u₂ s₂).2 pubf
    have hquel : QuellzustandGleich (p.einheit plattform) u₁ u₂ :=
      Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans (v := u₁) (u := v₁) (n := u₂)
        (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.symm (v := v₁) (u := u₁) o₁.1)
        (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans (v := v₁) (u := v₂) (n := u₂)
          gleich o₂.1)
    exact ⟨hquel, o₁.2.1.trans o₂.2.1.symm, o₁.2.2.trans o₂.2.2.symm⟩

/-- An access instruction at the head transfers to a publicly equal source state with the same
    machine status. The frame part comes from the unit's empty local labels, the status part from
    the coupling (not from `QuellzustandGleich`, which compares only the public end view). -/
theorem zugriffKopfGleich (p : Fragment) (plattform : Plattform) {f : Befehl}
    {v w : Ast.Semantik.Zustand} {c : Kontext}
    (gleich : QuellzustandGleich (p.einheit plattform) v w)
    (statusEq : v.status = w.status)
    (kopf : (p.einheit plattform).system.kopf v c = some f) :
    (p.einheit plattform).system.kopf w c = some f := by
  have lokEqFun : v.lokal = w.lokal := by
    funext d
    exact gleich.1 d ⟨0, Nat.zero_lt_one⟩ rfl
  have sysKopf : ∀ s d, (p.einheit plattform).system.kopf s d = Ast.Semantik.kopf p.code s d :=
    fun s d => rfl
  have h : Ast.Semantik.kopf p.code w c = Ast.Semantik.kopf p.code v c := by
    rw [Ast.Semantik.kopf, Ast.Semantik.kopf]
    rw [← lokEqFun, ← congrFun statusEq]
  rw [sysKopf, h, ← sysKopf]
  exact kopf

/-- The unit labels nothing, so a public plan view records every read label. Equal plan views of
    two access steps therefore give equal read labels, including the value read. The remaining gap
    to equal observations is the graph-dependent initial write of `Speicherfolge`, not the plan. -/
theorem zugriffPlanSicht_lesen (p : Fragment) (plattform : Plattform)
    {p₁ p₂ : Ast.Semantik.Plan}
    (h : PlanSicht (p.einheit plattform) p₁ = PlanSicht (p.einheit plattform) p₂) :
    p₁.lesen = p₂.lesen := by
  have hfst := congrArg Prod.fst h
  simpa only [PlanSicht, Fragment.einheit, Einheit.etiketten, Etiketten.leer,
    oeffentlich, decide_true, List.filter_true] using hfst

end Gabbro.Core.Beobachtung
