module

public import Core.Ast.Variant.Obligations

/-!
# VariantValue

- `Surface.VariantValueInversionAussage`
- `Surface.VariantValueSuffixAussage`
- `Surface.VariantValueDerivationAussage`
- `VariantValueParseAussage`
- `VariantValueElaboriertAussage`
- `VariantValueRealisiertAussage`
- `VariantValueAnnahmeAussage`
- `VariantValueIdealAussage`
- `VariantValueEinheitAussage`
- `VariantValueImplAussage`
- `VariantValueErhaltungAussage`
- `VariantValueRegelSicherAussage`
- `VariantValueErfuellbarAmAussage`
- `VariantValuePayloadAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem vv_amOrt (scope : Scope) : (variantValueForm scope).RegelAmOrt := by
  intro a
  change (((caseCode 0 a.payload).code ++
    [(Befehl.baueVariante 0 a.ref.name.val a.labels a.payloads a.index)]))[
      (caseCode 0 a.payload).code.length]? =
    some (Befehl.baueVariante 0 a.ref.name.val a.labels a.payloads a.index)
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem variantValue_annahme : VariantValueAnnahmeAussage := by
  intro scope platform args
  let form := variantValueForm scope
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

private theorem vv_caseCode_inv (slot : Nat) {ty : Option (Ty .value)}
    (payload : CasePayload scope ty) : (caseCode slot payload).klauseln.invariant = [] := by
  cases payload with
  | nullary paren => rfl
  | value e => simpa [caseCode] using expr_keine_invarianten slot e

theorem variantValue_erhaltung : VariantValueErhaltungAussage := by
  intro scope platform args
  let p := (variantValueForm scope).fragment args
  let b := (variantValueForm scope).befehl args
  have inv : p.klauseln.invariant = [] := by
    change ((caseCode 0 args.payload).klauseln.invariant ++
      (Fragment.einzel b).klauseln.invariant) = []
    rw [vv_caseCode_inv]
    rfl
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicher p platform inv⟩

theorem variantValue_regelSicher : VariantValueRegelSicherAussage := by
  intro scope platform args
  exact (variantValue_erhaltung scope platform args).2.2.2

theorem variantValue_elaboriert : VariantValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem variantValue_realisiert : VariantValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (variantValueForm scope).realisiert (vv_amOrt scope) platform args s running active live atPc

theorem variantValue_ideal : VariantValueIdealAussage := by
  intro scope
  constructor
  · exact vv_amOrt scope
  · intro args
    constructor
    · exact ((variantValueForm scope).befehl args).bestimmt
    · intro c s w plans u
      rfl

theorem variantValue_einheit : VariantValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((variantValueForm scope).befehl args).kommutation⟩

theorem variantValue_impl : VariantValueImplAussage := by
  intro scope args c s w plans u
  rfl

private theorem vv_case_inject (cases : List (Option (Ty .value))) (index : Fin cases.length)
    (payload : Wert ((cases.get index).getD .productEnd)) :
    (variantCase cases (variantInject cases index payload)).1 = index.val := by
  induction cases with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      cases index with
      | mk n bound =>
        cases n with
        | zero => rfl
        | succ n =>
            have h := ih ⟨n, Nat.lt_of_succ_lt_succ bound⟩ payload
            simpa [variantCase, variantInject, h]

theorem variantValue_payload : VariantValuePayloadAussage := by
  intro scope a frame payload h
  constructor
  · change ((variantActual (a.payloads.get a.index) (frame.temp 0)).bind
      (fun value => (some ⟨variantValueType a.ref.name.val a.labels a.payloads,
        variantInject a.payloads a.index value⟩ : Option Dynamisch))) =
      (some ⟨variantValueType a.ref.name.val a.labels a.payloads,
        variantInject a.payloads a.index payload⟩ : Option Dynamisch)
    rw [h]
    rfl
  · exact vv_case_inject a.payloads a.index payload

end Gabbro.Core.Ast.Semantik
