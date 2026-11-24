module

public import Core.Ast.Variant.Obligations

/-!
# VariantMatch

- `Surface.VariantMatchInversionAussage`
- `Surface.VariantMatchSuffixAussage`
- `Surface.VariantMatchDerivationAussage`
- `VariantMatchParseAussage`
- `VariantMatchElaboriertAussage`
- `VariantMatchRealisiertAussage`
- `VariantMatchAnnahmeAussage`
- `VariantMatchIdealAussage`
- `VariantMatchEinheitAussage`
- `VariantMatchImplAussage`
- `VariantMatchErhaltungAussage`
- `VariantMatchRegelSicherAussage`
- `VariantMatchErfuellbarAmAussage`
- `VariantMatchExhaustiveAussage`
- `VariantMatchDispatchAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem vm_amOrt (ctx : Scope × Option (Ty .value)) : (variantMatchForm ctx).RegelAmOrt := by
  intro a
  let head := (.waehleVariante 0 a.name a.labels a.payloads (variantArms a.arms).branches : Befehl)
  let valueCode := (expr 0 a.value).code
  let bodyCode := (variantArms a.arms).body.code
  change (((valueCode ++ [head]) ++ bodyCode)[valueCode.length]?) = some head
  have hlt : valueCode.length < (valueCode ++ [head]).length := by simp
  rw [List.getElem?_append_left hlt]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem variantMatch_annahme : VariantMatchAnnahmeAussage := by
  intro ctx platform args
  let form := variantMatchForm ctx
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

private theorem vm_block_inv {result before after} (b : Block result before after) :
    (block b).klauseln.invariant = [] := by
  induction b with
  | done => rfl
  | step first rest ih => simp [block, stmt_keine_invarianten, ih]

private theorem vm_braced_inv {result before} (b : BracedBlock result before) :
    (bracedBlock b).klauseln.invariant = [] := by
  cases b with
  | braces body => simpa [bracedBlock] using vm_block_inv body

private theorem vm_arms_inv {result scope allowed labels payloads}
    (arms : VariantArms result scope allowed labels payloads) :
    (variantArms arms).body.klauseln.invariant = [] := by
  induction arms with
  | done => rfl
  | nullary label caseName body rest ih => simp [variantArms, MatchCode.prepend, vm_braced_inv, ih]
  | payload label binder ordinary body rest ih => simp [variantArms, MatchCode.prepend, vm_braced_inv, ih]
  | wildcard body nonempty shape => simp [variantArms, vm_braced_inv]

theorem variantMatch_erhaltung : VariantMatchErhaltungAussage := by
  intro ctx platform args
  let p := (variantMatchForm ctx).fragment args
  let b := (variantMatchForm ctx).befehl args
  have inv : p.klauseln.invariant = [] := by
    dsimp [p, Quellform.fragment, fragment]
    simp [expr_keine_invarianten, vm_arms_inv]
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicher p platform inv⟩

theorem variantMatch_regelSicher : VariantMatchRegelSicherAussage := by
  intro ctx platform args
  exact (variantMatch_erhaltung ctx platform args).2.2.2

theorem variantMatch_elaboriert : VariantMatchElaboriertAussage := by
  intro ctx platform args
  rfl

theorem variantMatch_realisiert : VariantMatchRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (variantMatchForm ctx).realisiert (vm_amOrt ctx) platform args s running active live atPc

theorem variantMatch_ideal : VariantMatchIdealAussage := by
  intro ctx
  constructor
  · exact vm_amOrt ctx
  · intro args
    constructor
    · exact ((variantMatchForm ctx).befehl args).bestimmt
    · intro c s w plans u
      rfl

theorem variantMatch_einheit : VariantMatchEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((variantMatchForm ctx).befehl args).kommutation⟩

theorem variantMatch_impl : VariantMatchImplAussage := by
  intro ctx args c s w plans u
  rfl

end Gabbro.Core.Ast.Semantik
