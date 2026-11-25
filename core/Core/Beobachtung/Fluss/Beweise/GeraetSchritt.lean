module

public import Core.Beobachtung.Fluss.Beweise.GeraetFluss
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.NISichtbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device (Binding Denotation Rule RegisterAccess Frame State Plan)
open Gabbro.Core.Ast.LowLevel.Device (setFrame internal)

/-- Two steps of one public form from public-equal source states stay public-equal,
    with equal plan and output views. This is the whole content of `RegelFluss`
    for a pair of steps; unlike the run-level duty it does not determine the head
    of a second run. -/
private theorem schrittpaar_gleich_allein
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) {f : Form}
    (fl : RegelFluss E f) {c : Kontext} {v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂}
    (gleich : QuellzustandGleich E v₁ v₂)
    (s₁ : FormSchritt E f c v₁ w₁ p₁ u₁) (s₂ : FormSchritt E f c v₂ w₂ p₂ u₂) :
    QuellzustandGleich E u₁ u₂ ∧ PlanSicht E p₁ = PlanSicht E p₂ ∧
      AusgabeSicht E c v₁ u₁ = AusgabeSicht E c v₂ u₂ := by
  unfold RegelFluss at fl
  by_cases pub : oeffentlich (E.fluss.kontrolle f) = true
  · exact fl.2 pub c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich s₁ s₂
  · have pubf : oeffentlich (E.fluss.kontrolle f) = false := by
      cases hb : oeffentlich (E.fluss.kontrolle f) <;> simp_all
    have o₁ := (fl.1 c v₁ w₁ p₁ u₁ s₁).2 pubf
    have o₂ := (fl.1 c v₂ w₂ p₂ u₂ s₂).2 pubf
    have hquel : QuellzustandGleich E u₁ u₂ :=
      Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans (v := u₁) (u := v₁) (n := u₂)
        (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.symm (v := v₁) (u := u₁) o₁.1)
        (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans (v := v₁) (u := v₂) (n := u₂)
          gleich o₂.1)
    exact ⟨hquel, o₁.2.1.trans o₂.2.1.symm, o₁.2.2.trans o₂.2.2.symm⟩

/-- Step-level information flow of the device form: two form steps of the same
    elaborated device from public-equal source states end in public-equal states
    with equal plan and output views. This is the part of `GeraeteNIAussage` that
    `RegelFluss` alone carries; the run-level lifting is the open step. -/
theorem geraeteSchrittNI {k scope} (locals : Ast.Umgebung scope) (d : Denotation k scope) :
    ∀ (c : Kontext) (v₁ v₂ : State) (w : PUnit) (p₁ p₂ : Plan) (u₁ u₂ : State),
      QuellzustandGleich (d.unit locals) v₁ v₂ →
      FormSchritt (d.unit locals) () c v₁ w p₁ u₁ →
      FormSchritt (d.unit locals) () c v₂ w p₂ u₂ →
      QuellzustandGleich (d.unit locals) u₁ u₂ ∧
        PlanSicht (d.unit locals) p₁ = PlanSicht (d.unit locals) p₂ ∧
        AusgabeSicht (d.unit locals) c v₁ u₁ = AusgabeSicht (d.unit locals) c v₂ u₂ := by
  intro c v₁ v₂ w p₁ p₂ u₁ u₂ gleich s₁ s₂
  exact schrittpaar_gleich_allein (d.unit locals) (geraeteRegelFlussAussage locals d) gleich s₁ s₂

/-- The device unit's head respects the coupling: with empty labels a public
    source-state equality is full equality of the acting frame and the coupling
    already equates the machine statuses, so the head `some ()` transfers. -/
theorem geraeteKopfGleich {k scope} (locals : Ast.Umgebung scope) (d : Denotation k scope)
    {v w : State} {c : Kontext}
    (gleich : QuellzustandGleich (d.unit locals) v w)
    (statusEq : v.status = w.status)
    (kopf : (d.unit locals).system.kopf v c = some ()) :
    (d.unit locals).system.kopf w c = some () := by
  dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit] at kopf ⊢
  change (match w.status c with | .laeuft => some () | _ => none) = some ()
  rw [← congrFun statusEq c]
  exact kopf

end Gabbro.Core.Beobachtung
