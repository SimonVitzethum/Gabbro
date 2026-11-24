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

private theorem vm_arms_inv (result : Option (Ty .value)) (scope : Scope) (allowed : Bool)
    (labels : List Identifier) (payloads : List (Option (Ty .value)))
    (arms : VariantArms result scope allowed labels payloads) :
    (variantArms arms).body.klauseln.invariant = [] := by
  refine @Gabbro.Core.Ast.VariantArms.rec result
    (fun _ _ _ => True)
    (fun _ _ blk => (block blk).klauseln.invariant = [])
    (fun _ br => (bracedBlock br).klauseln.invariant = [])
    (fun _ _ _ _ ar => (variantArms ar).body.klauseln.invariant = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    scope allowed labels payloads arms
  all_goals simp_all [stmt, block, bracedBlock, variantArms, MatchCode.prepend,
    Fragment.anhaengen, Fragment.einzel, Fragment.leer,
    Quellklauseln.anhaengen, Quellklauseln.leer]
  · intro before middle after a a_1 ih
    exact stmt_keine_invarianten a

theorem variantMatch_erhaltung : VariantMatchErhaltungAussage := by
  intro ctx platform args
  let p := (variantMatchForm ctx).fragment args
  let b := (variantMatchForm ctx).befehl args
  have inv : p.klauseln.invariant = [] := by
    change ((((expr 0 args.value).anhaengen
      (Fragment.einzel (Befehl.waehleVariante 0 args.name args.labels args.payloads
        (variantArms args.arms).branches))).anhaengen
        (variantArms args.arms).body).klauseln.invariant = [])
    simp [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer,
      expr_keine_invarianten, vm_arms_inv]
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

private theorem vm_arms_length (result : Option (Ty .value)) (scope : Scope) (allowed : Bool)
    (labels : List Identifier) (payloads : List (Option (Ty .value)))
    (arms : VariantArms result scope allowed labels payloads) :
    (variantArms arms).branches.length = payloads.length := by
  refine @Gabbro.Core.Ast.VariantArms.rec result
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ => True)
    (fun _ _ _ p ar => (variantArms ar).branches.length = p.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    scope allowed labels payloads arms
  all_goals simp_all [variantArms, MatchCode.prepend]

private theorem vm_case_lt (cases : List (Option (Ty .value))) :
    ∀ value : Wert (variantLayout cases), (variantCase cases value).1 < cases.length := by
  cases cases with
  | nil => intro value; exact Empty.elim value
  | cons head tail =>
      intro value
      cases hsum : (value : Sum (Wert (head.getD .productEnd)) (Wert (variantLayout tail))) with
      | inl payload => simp [variantCase, hsum]
      | inr rest =>
          simpa [variantCase, hsum, Nat.succ_eq_add_one] using
            Nat.succ_lt_succ (vm_case_lt tail rest)

theorem variantMatch_exhaustive : VariantMatchExhaustiveAussage := by
  intro ctx a
  constructor
  · exact vm_arms_length ctx.2 ctx.1 false a.labels a.payloads a.arms
  · intro value
    have h := vm_case_lt a.payloads value
    have hlen := vm_arms_length ctx.2 ctx.1 false a.labels a.payloads a.arms
    omega

private theorem vm_arms_bind (result : Option (Ty .value)) (scope : Scope) (allowed : Bool)
    (labels : List Identifier) (payloads : List (Option (Ty .value)))
    (arms : VariantArms result scope allowed labels payloads) :
    ∀ (i : Nat) (hib : i < (variantArms arms).branches.length),
      ((variantArms arms).branches[i]).2 = true →
      (payloads[i]?).join.isSome = true := by
  refine @Gabbro.Core.Ast.VariantArms.rec result
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ => True)
    (fun _ _ _ p ar => ∀ (i : Nat) (hib : i < (variantArms ar).branches.length),
      ((variantArms ar).branches[i]).2 = true → (p[i]?).join.isSome = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    scope allowed labels payloads arms
  all_goals simp_all [variantArms, MatchCode.prepend]
  · intro scope labels payloads label caseName body rest ih i hib hb
    cases i with
    | zero => simp at hb
    | succ j =>
        have hj : j < (variantArms rest).branches.length := by omega
        have hb' : ((variantArms rest).branches[j]).2 = true := by
          simpa using hb
        simpa using ih j hj hb'
  · intro type scope labels payloads label binder ordinary body rest ih i hib hb
    cases i with
    | zero => simp
    | succ j =>
        have hj : j < (variantArms rest).branches.length := by omega
        have hb' : ((variantArms rest).branches[j]).2 = true := by
          simpa using hb
        simpa using ih j hj hb'

private theorem vm_case_payload_some (cases : List (Option (Ty .value))) :
    ∀ (value : Wert (variantLayout cases)) (i : Nat),
      (variantCase cases value).1 = i →
      (cases[i]?).join.isSome = true →
      (variantCase cases value).2.isSome = true := by
  cases cases with
  | nil => intro value; exact Empty.elim value
  | cons head tail =>
      intro value i hidx hsome
      cases hsum : (value : Sum (Wert (head.getD .productEnd)) (Wert (variantLayout tail))) with
      | inl payload =>
          cases i with
          | zero =>
              cases head with
              | none => simp at hsome
              | some t => rfl
          | succ j => simp [variantCase, hsum] at hidx
      | inr rest =>
          cases i with
          | zero => simp [variantCase, hsum] at hidx
          | succ j =>
              have hh : (variantCase tail rest).1 + 1 = j + 1 := by
                simpa [variantCase, hsum] using hidx
              have hidx' : (variantCase tail rest).1 = j := Nat.add_right_cancel hh
              have hsome' : (tail[j]?).join.isSome = true := by simpa using hsome
              exact vm_case_payload_some tail rest j hidx' hsome'

theorem variantMatch_dispatch : VariantMatchDispatchAussage := by
  intro ctx a frame value hv
  let branches := (variantArms a.arms).branches
  let i := (variantCase a.payloads value).1
  let payload := (variantCase a.payloads value).2
  have hlen : branches.length = a.payloads.length := by
    simpa [branches] using vm_arms_length ctx.2 ctx.1 false a.labels a.payloads a.arms
  have hi : i < a.payloads.length := by
    simpa [i] using vm_case_lt a.payloads value
  have hibr : i < branches.length := by omega
  let entry := branches[i]
  have hget : branches[i]? = some entry := List.getElem?_eq_some_iff.mpr ⟨hibr, rfl⟩
  have hval : (frame.temp 0).bind
      (wertAls (variantValueType a.name a.labels a.payloads)) = some value := by
    simp [hv, wertAls, variantValueType]
  have hnext : ((variantMatchForm ctx).befehl a).auswerten frame =
      { frame with
        pc := frame.pc + entry.1
        lokale := if entry.2 = true then payload :: frame.lokale else frame.lokale } := by
    simp [Befehl.auswerten, variantMatchForm, hv, hval, i, payload, branches, entry, hget,
      wertAls, variantValueType]
  refine ⟨entry.1, entry.2, hget, ?_⟩
  dsimp
  rw [hnext]
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro hb
  have hsome : (a.payloads[i]?).join.isSome = true := by
    exact vm_arms_bind ctx.2 ctx.1 false a.labels a.payloads a.arms i hibr
      (by simpa [entry] using hb)
  exact vm_case_payload_some a.payloads value i rfl hsome

private theorem vm_read_suffix {result scope allowed labels payloads input arms rest}
    (read : Gabbro.Core.Ast.VariantArmsRead result scope allowed input arms rest) : rest <:+ input := by
  induction read with
  | done => exact List.suffix_cons _ _
  | nullary label caseName blockRead restRead ih =>
      exact ih.trans ((BlockReads.consumes blockRead).trans
        ((List.suffix_cons _ _).trans (List.suffix_cons _ _)))
  | payload label binder ordinary body blockRead restRead ih =>
      exact ih.trans ((BlockReads.consumes blockRead).trans
        ((List.suffix_cons _ _).trans ((List.suffix_cons _ _).trans
          ((List.suffix_cons _ _).trans ((List.suffix_cons _ _).trans (List.suffix_cons _ _))))))
  | wildcard nonempty shape blockRead =>
      exact (List.suffix_cons _ _).trans ((BlockReads.consumes blockRead).trans
        ((List.suffix_cons _ _).trans (List.suffix_cons _ _)))

theorem variantMatch_suffix : Gabbro.Core.Ast.Surface.VariantMatchSuffixAussage := by
  intro scope result allowed labels payloads input rest arms read
  exact vm_read_suffix read

end Gabbro.Core.Ast.Semantik
