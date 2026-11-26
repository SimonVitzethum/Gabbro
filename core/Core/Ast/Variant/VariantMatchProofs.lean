module

public import Core.Ast.Variant.Obligations
import Core.Ast.Semantik.Runtime.ValueCoercion

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
  have hlt : valueCode.length < (valueCode ++ [head]).length := by
    simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_self valueCode.length
  rw [List.getElem?_append_left hlt]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

theorem variantMatch_annahme : VariantMatchAnnahmeAussage := by
  intro ctx platform args
  let form := variantMatchForm ctx
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (h := Or.inl rfl) (w := w) step execute
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer,
      expr_keine_invarianten, vm_arms_inv, List.nil_append]
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicherheitsPflichten p platform [] (tabLeer _ inv) (fun b _ => rfl)⟩

theorem variantMatch_regelSicher : VariantMatchRegelSicherAussage := by
  intro ctx platform args
  exact (variantMatch_erhaltung ctx platform args).2.2.2.1

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
    · exact (variantMatchForm ctx).bestimmt args
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    scope allowed labels payloads arms
  all_goals simp_all [variantArms, MatchCode.prepend]

private theorem vm_case_lt (cases : List (Option (Ty .value))) :
    ∀ value : Wert (variantLayout cases), (variantCase cases value).1 < cases.length := by
  cases cases with
  | nil => intro value; exact Empty.elim value
  | cons head tail =>
      intro value
      cases hsum : (value : Sum (Wert (head.getD .productEnd)) (Wert (variantLayout tail))) with
      | inl payload => exact Nat.zero_lt_succ _
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    | zero => rfl
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
          | succ j =>
              have impossible : (0 : Nat) = j + 1 := by simpa only [variantCase, hsum] using hidx
              cases impossible
      | inr rest =>
          cases i with
          | zero =>
              have impossible : (variantCase tail rest).1 + 1 = 0 := by simpa only [variantCase, hsum] using hidx
              omega
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
    rw [hv, Option.bind_some]
    exact wertAls_selbst value
  have hnext : ((variantMatchForm ctx).befehl a).auswerten frame =
      { frame with
        pc := frame.pc + entry.1
        lokale := if entry.2 = true then payload :: frame.lokale else frame.lokale } := by
    simp only [Befehl.auswerten, variantMatchForm, hval, Id.run]
    rw [show (variantArms a.arms).branches[(variantCase a.payloads value).1]? = some entry from hget]
    rfl
  refine ⟨entry.1, entry.2, hget, ?_⟩
  dsimp
  rw [hnext]
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro hb
  have hsome : (a.payloads[i]?).join.isSome = true := by
    exact vm_arms_bind ctx.2 ctx.1 false a.labels a.payloads a.arms i hibr
      (by simpa [entry] using hb)
  exact vm_case_payload_some a.payloads value i rfl hsome

open Gabbro.Core.Text
open Surface

theorem variantMatch_inversion : VariantMatchInversionAussage := by
  intro scope result input tree rest starts read
  generalize tokens : keyword "match" :: input = ts at read
  cases read with
  | variantMatch valueRead armsRead =>
    cases (List.cons.inj tokens).2
    exact ⟨⟨_, _, _, _, _⟩, _, valueRead, armsRead, rfl⟩
  | assignVar _ _ _ _ _ => exact ((starts _).1 (List.cons.inj tokens).2).elim
  | assignField _ _ _ _ _ _ _ _ => exact ((starts _).2 (List.cons.inj tokens).2).elim
  | directCall callRead =>
    rename_i call
    have ordinary := call.ordinary
    cases callRead
    apply ordinary.2 |>.elim
    rw [← Token.word.inj (List.cons.inj tokens).1]
    have present : "match" ∈ ["let", "if", "return", "while", "for", "leave", "next", "match", "forever", "mem"] :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
    exact List.mem_map.mpr ⟨"match", present, rfl⟩
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable <;> cases (List.cons.inj tokens).1
  | _ => cases (List.cons.inj tokens).1

private theorem variantArmsPrints (arms : VariantArms result scope allowed labels payloads) :
    VariantArmsRead result scope allowed (arms.printPieces.map PrintedToken.value ++ closeBrace :: rest) arms rest := by
  have nameToken (name : Identifier) : name.print.value = .word name.val := rfl
  have arrowToken : printMatchArrow.value = matchArrow := rfl
  induction labels generalizing payloads allowed with
  | nil =>
    cases arms with
    | done => exact .done
    | wildcard _ nonempty _ => exact (nonempty rfl).elim
  | cons head tail ih =>
    cases arms with
    | nullary label ordinary body next =>
      have bodyRead := body.printReads (next.printPieces.map PrintedToken.value ++ closeBrace :: rest)
      simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.append_assoc, nameToken, arrowToken] using
        (VariantArmsRead.nullary (allowed := allowed) head ordinary bodyRead (ih next))
    | payload label binder ordinary body next =>
      have bodyRead := body.printReads (next.printPieces.map PrintedToken.value ++ closeBrace :: rest)
      simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.append_assoc, nameToken, arrowToken,
        show printOpen.value = openParen from rfl, show printClose.value = closeParen from rfl] using
        (VariantArmsRead.payload (allowed := allowed) head binder ordinary body bodyRead (ih next))
    | wildcard body nonempty shape =>
      simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, arrowToken, show discardName.print.value = Token.word ['_'] from rfl] using
        (VariantArmsRead.wildcard nonempty shape (body.printReads (closeBrace :: rest)))

private theorem variantMatchPrints (ctx : Scope × Option (Ty .value)) (args : VariantMatchArgs ctx) :
    (variantMatch ctx).production args
      (((Category.statement ctx.1 ctx.2).printPieces ((variantMatch ctx).tree args)).map PrintedToken.value) := by
  let armsInput := args.arms.printPieces.map PrintedToken.value ++ [closeBrace]
  let input := args.value.printTokens ++ openBrace :: armsInput
  refine ⟨input, armsInput, ?_, args.value.printReads noOperatorAtOpenBrace, variantArmsPrints args.arms⟩
  change ((Stmt.variantMatch args.value args.arms).printPieces.map PrintedToken.value) = _
  simp only [Stmt.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_assoc, input, armsInput, Expr.printTokens]
  rfl

theorem variantMatch_derivation : VariantMatchDerivationAussage := by
  rintro ctx ⟨witness⟩
  refine ⟨?_, variantMatchPrints ctx, Rule.satisfiableOfPrint witness (variantMatchPrints ctx witness)⟩
  rintro args tokens ⟨input, arms, rfl, valueRead, armsRead⟩
  exact .variantMatch valueRead armsRead

theorem variantMatch_suffix : Gabbro.Core.Ast.Surface.VariantMatchSuffixAussage := by
  intro scope result allowed labels payloads input rest arms read
  exact read.consumes

theorem variantMatch_parse : Gabbro.Core.Ast.Semantik.VariantMatchParseAussage := by
  intro ctx args text pieces lexed production
  apply (Gabbro.Core.Ast.Category.statement ctx.1 ctx.2).syntax.parse_iff.mpr
  refine ⟨pieces, lexed, ?_⟩
  rcases production with ⟨input, arms, same, valueRead, armsRead⟩
  rw [same]
  exact .variantMatch valueRead armsRead

theorem variantMatch_erfuellbarAm : VariantMatchErfuellbarAmAussage := by
  intro platform start
  let name : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'v' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let lbl : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'a' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let member : Gabbro.Core.Ast.VariantMember := ⟨lbl, none⟩
  let labels : List Gabbro.Core.Ast.Identifier := Gabbro.Core.Ast.variantLabels [member]
  let payloads : List (Option (Ty .value)) := Gabbro.Core.Ast.variantPayloads [member]
  let schemaType : Ty .value := variantSchemaType name.val labels payloads
  let binding : Gabbro.Core.Ast.Binding := ⟨name, schemaType, false, true⟩
  let scope : Scope := [binding]
  let refSchema : Local scope schemaType := .here
  let ref : Gabbro.Core.Ast.VariantRef scope labels payloads :=
    ⟨name, refSchema, trivial, rfl, rfl,
      by change [lbl.val].Nodup; exact List.nodup_singleton _⟩
  let index : Fin payloads.length := ⟨0, Nat.zero_lt_succ _⟩
  have written : labels[index.val]? = some lbl := rfl
  have ordinary : Gabbro.Core.Ast.ordinaryLocal lbl := by
    exact (directName_of_singleton (name := lbl) rfl).1
  have available : availableCase scope lbl := by
    constructor
    · exact List.count_singleton_self
    · intro b hb
      have same : b = binding := List.mem_singleton.mp hb
      subst b
      intro same
      cases same
  let payload : Gabbro.Core.Ast.CasePayload scope (payloads.get index) := .nullary false
  let valueArgs : Gabbro.Core.Ast.Surface.VariantValueArgs scope :=
    ⟨labels, payloads, ref, lbl, index, written, ordinary, available, payload⟩
  let arms : Gabbro.Core.Ast.VariantArms none scope false labels payloads :=
    .nullary lbl (by intro same; cases same) (.braces .done) .done
  let a : Gabbro.Core.Ast.Surface.VariantMatchArgs (scope, none) :=
    ⟨name.val, labels, payloads, valueArgs.expression, arms⟩
  refine ⟨(scope, none), a, ?_⟩
  let form := variantMatchForm (scope, none)
  let s₀ := (I.start (form.einheit platform a) start).2
  let vb : Befehl := .baueVariante 0 name.val labels payloads index
  let s₁ := vb.nach eintritt s₀
  have vbhead : kopf (form.fragment a).code s₀ eintritt = some vb := by
    rfl
  have step : (form.einheit platform a).system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨vb, vbhead, rfl, rfl⟩
  have reached : (form.einheit platform a).system.IErreichbar s₀ s₁ :=
    .schritt eintritt () [plan] .start step
  dsimp [Quellform.ErfuellbarAm]
  refine ⟨Ast.print (category := .statement scope none) (form.produktion.tree a), s₁,
    Ast.parse_print _, rfl, reached, ?_, ?_⟩
  · refine form.realisiert (vm_amOrt (scope, none)) platform a s₁ rfl rfl rfl ?_
    rfl
  · intro g guard; cases guard

end Gabbro.Core.Ast.Semantik
