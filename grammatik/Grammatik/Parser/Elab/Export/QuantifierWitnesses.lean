module
public import Grammatik.Parser.Elab.Export.ExportQuantifiers
import all Grammatik.Parser.Elab.Export.ExportRelations
import all Grammatik.Parser.Item.ElementTief.Defs1a
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- The source loop-header duties remain refusals rather than disappearing into a finite loop. -/
theorem traversal_header_refused_zeuge :
    let ctx : UCtx := {names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := none, fname := "sample", alias := [], lits := []}
    uLoopExport ctx "node" none "descendants" (.variable "root") "unvisited" "decreases node " none =
      .error "source export: traversal decreases/touches duties lack a checked source binding" ∧
    uLoopExport ctx "node" none "descendants" (.variable "root") "consuming" "" none =
      .error "consuming traversal requires decreases" := by
  exact ⟨rfl, rfl⟩

theorem tree_quantifier_export_zeuge :
    uSichert relationContext (.ext .all ["root", "descendants"]
      [.variable "root", .bin "<=" (.variable "root") (.lit 1)]) =
      .ok (.filtered true "T" "root" "next" false (.param "root")
        (.cmp "<=" (.param "root") (.lit 1))) := by
  have sameName : strEq "root" "root" = true := by decide +kernel
  apply tree_quantifier_export relationContext true false "root"
    (.variable "root") (.bin "<=" (.variable "root") (.lit 1))
    "T" "next" 0 (.param "root") (.cmp "<=" (.param "root") (.lit 1))
  · rfl
  · simp [uSichert, uIstVgl, uSeite, uRechne, uSeiteBlatt,
      uParamNr, uParamNrAux, uArtBei, relationContext, sameName]

theorem tree_quantifier_lower_zeuge :
    (lowEns relationUnit [.index 3, .index 3] [] relationFunction none
      (.filtered true "T" "root" "next" false (.param "root")
        (.cmp "<=" (.param "root") (.lit 1)))).toOption.isSome = true := by
  have outer : lowIdx relationUnit [.int 0 2, .int 0 2] [] relationFunction 0
      (⟨0, by decide⟩ : Fin relationUnit.tabs.length) (.param "root") = .ok (.var .here) := by
    simp [lowIdx, relationFunction, paramPos, Ty.index, declOf, tabAt, relationUnit,
      lowVar_same_head]
  have parameter : lowWertE relationUnit [.int 0 2, .int 0 2, .int 0 2] []
      (relationFunction.mitIndex "root" 0 3) none (.param "root") =
      .ok (⟨.int 0 2, .var .here⟩ : LowWert relationUnit [.int 0 2, .int 0 2, .int 0 2] []) := by
    simp [lowWertE, lowParamWert, lowParamSide, UFn.mitIndex, relationFunction,
      paramPos, Ty.index, lowVar_same_head, Except.map, LowSide.wert]
  have inner : lowEns relationUnit [.int 0 2, .int 0 2, .int 0 2] []
      (relationFunction.mitIndex "root" 0 3) none (.cmp "<=" (.param "root") (.lit 1)) =
      .ok (.le (.var .here) (.lit 1)) := by
    simp [lowEns, usideHatZaehle, lowCmp, parameter, lowWertE,
      LowSide.wert, zahlVon, LowWert.zahl]
  have ready : (selfEdge relationUnit (⟨0, by decide⟩ : Fin relationUnit.tabs.length)
      "next").toOption.isSome = true := rfl
  cases typed : selfEdge relationUnit (⟨0, by decide⟩ : Fin relationUnit.tabs.length) "next" with
  | error error =>
    rw [typed] at ready
    change false = true at ready
    cases ready
  | ok edge =>
    have emitted := tree_quantifier_lower relationUnit [.index 3, .index 3] []
      relationFunction relationFunction none true false "T" "root" "next"
      (.param "root") (.cmp "<=" (.param "root") (.lit 1)) ⟨0, by decide⟩ edge
      (.var .here) (.le (.var .here) (.lit 1)) rfl rfl typed outer rfl
      relation_table_guard inner
    rw [emitted]
    rfl

/-- The source adapter requires one genuine optional-self child edge. -/
theorem consuming_edge_zeuge :
    uConsumingEdge relationContext "T" = .ok "next" ∧
    uConsumingEdge {relationContext with tabs := [{name := "T", count := 3, cols := []}]} "T" =
      .error "consuming traversal requires one declared child edge" ∧
    uConsumingEdge {relationContext with tabs := [{name := "T", count := 3, cols := [], kanten := [("child", "a"), ("child", "b")]}]} "T" =
      .error "consuming traversal requires exactly one declared child edge" := by
  exact ⟨rfl, rfl, rfl⟩

private def consumingEffectTokens (take : Bool) : List Token :=
  [.wort (if take then "consumes" else "reads"), .ident "T", .zeichen ".", .wort "slots", .ende]

private theorem consuming_effect_lex (take : Bool) :
    lex (if take then "consumes T.slots" else "reads T.slots") = .ok (consumingEffectTokens take) := by
  cases take <;> rfl

-- The suffix remains symbolic here; the actual producer still uses exactly 10000.
private theorem consuming_effect_parse (take : Bool) (suffix : Nat) :
    parseEffektListe (suffix + 14) (consumingEffectTokens take) =
      .ok ([if take then .takes (.field (.variable "T") "slots")
        else .reads (.field (.variable "T") "slots")], [.ende]) := by
  cases take <;> rfl

private theorem consuming_effect_checked (functions : List UFn) (writes : List String) (take : Bool) :
    lowConsumingEffects {relationUnit with fns := functions} {relationFunction with puts := writes}
      "T" (if take then "consumes T.slots" else "reads T.slots") =
      if take then (if writes.any (strEq · "T") then .ok ()
        else .error "consuming traversal touches exceeds function writes")
      else .error "consuming traversal touches must consume its domain" := by
  rw [lowConsumingEffects, consuming_effect_lex]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [consuming_effect_parse take 9986]
  simp only [bind, Except.bind, pure, Except.pure]
  have sameTable : strEq "T" "T" = true := by decide +kernel
  cases take <;> cases allowed : writes.any (strEq · "T") <;>
    simp [relationUnit, relationFunction, uSchreibtOrt, uStelle, uArtBei, uEffekteAux,
      uIstGriffOrt, uIstGlobName, sameTable, allowed, bind, Except.bind, pure, Except.pure,
      MonadExceptOf.throw]

theorem consuming_effects_zeuge :
    lowConsumingEffects relationUnit {relationFunction with puts := ["T"]} "T" "consumes T.slots" =
      .ok () ∧
    lowConsumingEffects relationUnit relationFunction "T" "consumes T.slots" =
      .error "consuming traversal touches exceeds function writes" ∧
    lowConsumingEffects relationUnit relationFunction "T" "reads T.slots" =
      .error "consuming traversal touches must consume its domain" := by
  simpa [relationUnit, relationFunction, strEq] using
    And.intro (consuming_effect_checked [] ["T"] true)
      (And.intro (consuming_effect_checked [] [] true) (consuming_effect_checked [] [] false))

theorem consuming_negative_measure_zeuge :
    lowConsumingMass relationUnit [] [] relationFunction (.lit (-1)) =
      .error "consuming traversal decreases must have a nonnegative range" := by rfl

theorem consuming_exits_refused_zeuge :
    let context := {relationContext with loops := ["#consume:node"]}
    uEndeStmt context (some (.leave "node")) = .error "consuming traversal forbids leave" ∧
    uEndeStmt context (some (.next "node")) = .error "consuming traversal forbids next" := by
  exact ⟨rfl, rfl⟩

/-- Preserve the checked position, kind and canonical variable before constructing an index. -/
private theorem index_parameter_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (shift position : Nat) (name : String) (table : Fin u.tabs.length) (origin : Nat)
    (indexVar : Var Γ (.index ((declOf u).count table)))
    (found : paramPos fn.params name = .ok position)
    (kind : fn.kinds[position]? = some (.index origin))
    (lookup : lowVar Γ (shift + position) (.index ((declOf u).count table)) = .ok indexVar) :
    lowIdx u Γ Λ fn shift table (.param name) = .ok (.var indexVar) := by
  simp only [lowIdx, found, kind, lookup]

/-- Nonempty represented domain, two ordered index binders and a current-world count
    jointly reach the production consuming branch of the structured lowerer. -/
theorem consuming_traversal_lower_zeuge :
    let fn := {relationFunction with puts := ["T"]}
    let u := {relationUnit with fns := [fn]}
    let caller : Fin u.fns.length := ⟨0, by decide⟩
    let header := UStmt.consumeLoopBeg "node" "T" "#consume:predecessor"
      (.reach "T" "next" (.param "root") (.param "node"))
      (.reach "T" "next" (.param "#consume:predecessor") (.param "node")) .tru
      (.zaehleBaum "T" "j" "next" false (.param "root") .tru) "consumes T.slots"
    (lowStructL (l := false) u caller [.index 3, .index 3] fn 2 [] []
      header [.blkEnd]).toOption.isSome = true := by
  let fn : UFn := {relationFunction with puts := ["T"]}
  let u : UProg := {relationUnit with fns := [fn]}
  let caller : Fin u.fns.length := ⟨0, by decide⟩
  let t : Fin u.tabs.length := ⟨0, by decide⟩
  let Γ : Ctx := [.index 3, .index 3]
  let node := fn.mitIndex "node" 0 3
  let predecessor := node.mitIndex "#consume:predecessor" 0 3
  let mass := USide.zaehleBaum "T" "j" "next" false (.param "root") .tru
  change (lowStructL (l := false) u caller Γ fn 2 [] []
    (.consumeLoopBeg "node" "T" "#consume:predecessor"
      (.reach "T" "next" (.param "root") (.param "node"))
      (.reach "T" "next" (.param "#consume:predecessor") (.param "node")) .tru
      mass "consumes T.slots") [.blkEnd]).toOption.isSome = true
  have gate : u.exportGate = .ok () := rfl
  have found : tabIdx u.tabs "T" = .ok t := rfl
  have guard : darf (declOf u) t [] := by
    intro resource member
    have empty : (declOf u).braucht t = [] := rfl
    rw [empty] at member
    cases member
  have seed : lowIdx u Γ [] fn 0 t (.param "root") = .ok (.var .here) := by
    exact index_parameter_lower u Γ [] fn 0 0 "root" t 0 .here
      (by simp [paramPos, fn, relationFunction]) rfl (lowVar_same_head _ _)
  have ready : (selfEdge u t "next").toOption.isSome = true := rfl
  cases typed : selfEdge u t "next" with
  | error error =>
    rw [typed] at ready
    change false = true at ready
    cases ready
  | ok edge =>
    let selected : Expr (declOf u) (.index 3 :: Γ) [] .bool :=
      .reaches t edge.field edge.self (.var (.there .here)) (.var .here) guard
    let relation : Expr (declOf u) (.index 3 :: .index 3 :: Γ) [] .bool :=
      .reaches t edge.field edge.self (.var .here) (.var (.there .here)) guard
    have different : ("node" == "root") = false := by decide +kernel
    have privateName : ("#consume:predecessor" == "node") = false := by decide +kernel
    have members := reach_lower u (.index 3 :: Γ) [] node 0 "T" "next"
      (.param "root") (.param "node") t edge (.var (.there .here)) (.var .here) gate found typed
      (index_parameter_lower u (.index 3 :: Γ) [] node 0 1 "root" t 0 (.there .here)
        (by simp [paramPos, node, UFn.mitIndex, fn, relationFunction, different])
        rfl (lowVar_next_head _ _ _))
      (index_parameter_lower u (.index 3 :: Γ) [] node 0 0 "node" t 0 .here
        (by simp [paramPos, node, UFn.mitIndex]) rfl (lowVar_same_head _ _)) guard
    have edges := reach_lower u (.index 3 :: .index 3 :: Γ) [] predecessor 0 "T" "next"
      (.param "#consume:predecessor") (.param "node") t edge (.var .here) (.var (.there .here))
      gate found typed
      (index_parameter_lower u (.index 3 :: .index 3 :: Γ) [] predecessor 0 0
        "#consume:predecessor" t 0 .here
        (by simp [paramPos, predecessor, UFn.mitIndex]) rfl (lowVar_same_head _ _))
      (index_parameter_lower u (.index 3 :: .index 3 :: Γ) [] predecessor 0 1 "node" t 0 (.there .here)
        (by simp [paramPos, predecessor, node, UFn.mitIndex, privateName])
        rfl (lowVar_next_head _ _ _)) guard
    let count : Expr (declOf u) Γ [] (.int 0 3) := .count 3 (.and selected .tru)
    have finite : (declOf u).offen t = false := rfl
    have nonnegative : 0 ≤ (declOf u).count t := by decide
    have counted : lowSeiteZ u Γ [] fn none mass =
        .ok ({range := (0, 3), term := count} : LowSide u Γ []) := by
      simp only [mass, lowSeiteZ, gate, found, typed, seed, ergAlsParam, bind, Except.bind,
        finite, Bool.false_eq_true, ite_false]
      rw [dite_eq_left nonnegative, dite_eq_left guard]
      rfl
    have measured : lowConsumingMass u Γ [] fn mass =
        .ok ⟨3, Expr.widen (Int.le_refl 0) (Int.le_refl 3) count⟩ := by
      simp [lowConsumingMass, mass, seiteAltErg, ensAltErg, counted,
        bind, Except.bind, Except.mapError, pure, Except.pure]
    have inside : lowSeqL (l := true) u caller (.index 3 :: Γ) node 1 [] [] [.blkEnd] =
        .ok (⟨[], (Block.nil : Block (declOf u) (verOf u caller) true (.index 3 :: Γ) [] [])⟩,
          [.blkEnd]) := rfl
    have emitted := consuming_traversal_lower (loop := false) u caller Γ fn 1 [] []
      "node" "T" "#consume:predecessor"
      (.reach "T" "next" (.param "root") (.param "node"))
      (.reach "T" "next" (.param "#consume:predecessor") (.param "node")) .tru mass
      "consumes T.slots" [.blkEnd] [] t selected relation .tru 3
      (Expr.widen (Int.le_refl 0) (Int.le_refl 3) count) Block.nil found
      (by simpa [fn, strEq] using consuming_effect_checked [fn] ["T"] true) (by rfl) measured
      (by simpa only [lowEns] using members) (by simpa only [lowEns] using edges) inside
    rw [emitted]
    rfl

theorem index_scope_zeuge (entry state : World (declOf relationUnit))
    (root other binder : Zahl 0 2) :
    eval entry (Expr.weaken (Expr.var (D := declOf relationUnit) (Λ := [])
      (Γ := [.index 3, .index 3]) (τ := .index 3) .here)) state
        (.cons (τ := .index 3) binder (.cons root (.cons other .nil))) = root := by
  exact index_scope relationUnit [.index 3, .index 3] [] relationFunction 0
    ⟨0, by decide⟩ (.param "root") (.var .here) rfl (binderTy := .index 3) binder entry state (.cons root (.cons other .nil))

end Gabbro.Grammatik.Parser.ExportPreservation
