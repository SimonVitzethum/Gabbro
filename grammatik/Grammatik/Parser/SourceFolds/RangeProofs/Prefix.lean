module

public import Grammatik.Parser.SourceFolds.Range

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

theorem matchFoldNode_some {e : SExpr} (h : isRangeFold e = true) :
    ∃ k b a, matchFoldNode e = some (k, b, a) := by
  unfold isRangeFold at h
  cases hm : matchFoldNode e with
  | none => simp [hm] at h
  | some t =>
    obtain ⟨k, b, a⟩ := t
    exact ⟨k, b, a, rfl⟩

theorem except_ok_inj {ε α : Type} {a b : α} (h : (Except.ok a : Except ε α) = Except.ok b) :
    a = b := by
  cases h
  rfl

theorem hasRangeFoldAnwList_append (a b : List SAnw)
    (ha : hasRangeFoldAnwList a = false) (hb : hasRangeFoldAnwList b = false) :
    hasRangeFoldAnwList (a ++ b) = false := by
  revert ha
  induction a with
  | nil => intro _; simpa using hb
  | cons x xs tail =>
    intro ha
    cases hxx : hasRangeFoldAnw x with
    | true => simp [hasRangeFoldAnwList, hxx] at ha
    | false =>
      have hxs : hasRangeFoldAnwList xs = false := by simp [hasRangeFoldAnwList, hxx] at ha; exact ha
      simp [hasRangeFoldAnwList, hxx, tail hxs]

theorem combineStmts_free (d : FoldDesc) (acc element : String) :
    hasRangeFoldAnwList (combineStmts d acc element) = false := by
  cases hK : d.kind <;>
    simp [combineStmts, hK, hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold]

theorem foldInit_free (kind : XKind) (empty' : Option SExpr)
    (h : (empty'.map hasRangeFold).getD false = false) :
    hasRangeFold (foldInit kind empty') = false := by
  cases kind <;> cases empty' <;> simp_all [foldInit, hasRangeFold]

theorem boundTests_free {lo hi count : SExpr} {binder : String}
    (hlo : hasRangeFold lo = false) (hhi : hasRangeFold hi = false) :
    hasRangeFoldList (boundTests lo hi count binder) = false := by
  unfold boundTests
  cases h1 : beqSExpr lo (.lit 0) <;> cases h2 : beqSExpr hi count <;>
    simp [h1, h2, beqSExpr, hasRangeFoldList, hasRangeFold, hlo, hhi]

theorem effFilter_free {tests : List SExpr} {filter' : SExpr}
    (ht : hasRangeFoldList tests = false) (hf : hasRangeFold filter' = false) :
    hasRangeFold (effFilter tests filter') = false := by
  unfold effFilter
  revert filter'
  induction tests with
  | nil =>
    intro filter' hf
    simpa using hf
  | cons t ts tail =>
    intro filter' hf
    cases htt : hasRangeFold t with
    | true => simp [hasRangeFoldList, htt] at ht
    | false =>
      have hts : hasRangeFoldList ts = false := by
        simp [hasRangeFoldList, htt] at ht
        exact ht
      cases hcur : beqSExpr filter' .tru with
      | true =>
        have hstep : hasRangeFold (if beqSExpr filter' .tru then t else .bin "&&" filter' t) = false := by
          simp [hcur, htt]
        exact tail hts hstep
      | false =>
        have hstep : hasRangeFold (if beqSExpr filter' .tru then t else .bin "&&" filter' t) = false := by
          simp [hcur, hf, htt, hasRangeFold]
        exact tail hts hstep

theorem buildLoopStmts_free (d : FoldDesc) (acc element : String) (filter' value' : SExpr)
    (preF preV : List SAnw) (tests : List SExpr)
    (hF : hasRangeFoldAnwList preF = false) (hV : hasRangeFoldAnwList preV = false)
    (hf : hasRangeFold filter' = false) (hv : hasRangeFold value' = false)
    (ht : hasRangeFoldList tests = false) :
    hasRangeFoldAnwList (buildLoopStmts d acc element filter' value' preF preV tests) = false := by
  unfold buildLoopStmts
  have heff := effFilter_free ht hf
  cases hE : beqSExpr (effFilter tests filter') .tru with
  | true =>
    simp [hE, hF, hV, hf, hv, heff, combineStmts_free,
      hasRangeFoldAnwList_append, hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold]
  | false =>
    simp [hE, hF, hV, hf, hv, heff, combineStmts_free,
      hasRangeFoldAnwList_append, hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold]

theorem buildFoldPrefix_free (d : FoldDesc) (idx : Nat) (filter' value' : SExpr)
    (sF sV sE : List SAnw) (empty' : Option SExpr) (tests : List SExpr)
    (hF : hasRangeFoldAnwList sF = false) (hV : hasRangeFoldAnwList sV = false)
    (hE : hasRangeFoldAnwList sE = false)
    (hf : hasRangeFold filter' = false) (hv : hasRangeFold value' = false)
    (he : (empty'.map hasRangeFold).getD false = false)
    (ht : hasRangeFoldList tests = false) :
    hasRangeFoldAnwList (buildFoldPrefix d idx filter' value' sF sV sE empty' tests) = false := by
  unfold buildFoldPrefix
  have hLoop := buildLoopStmts_free d (accName idx) (valueName idx) filter' value' sF sV tests
    hF hV hf hv ht
  have hInit := foldInit_free d.kind empty' he
  simp [hLoop, hE, hasRangeFoldAnwList_append, hasRangeFoldAnwList,
    hasRangeFoldAnw, hasRangeFold, hInit]

/-- The bound tests from a successful validation are fold-free. -/
theorem parseAndCheck_tests_free (source : List SItemTief) (locals : Spec.Locals)
    (chain : List String) (tags : List (SExpr × Nat)) (expected : Option STyp)
    (node : SExpr) (d : FoldDesc) (idx : Nat) (tests : List SExpr)
    (h : parseAndCheck source locals chain tags expected node = .ok (d, idx, tests)) :
    hasRangeFoldList tests = false := by
  unfold parseAndCheck at h
  cases hB : boundArgs node with
  | none =>
    simp [hB, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    cases hP : parseFoldNode source locals expected chain node with
    | error e => simp [hP, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    | ok dd =>
      simp [hP, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases hL : lookupTag tags node with
      | none => simp [hL, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | some ii =>
        simp [hL, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
  | some p =>
    obtain ⟨lo, hi⟩ := p
    simp [hB, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    cases hC : checkBoundsFree lo hi with
    | error e => simp [hC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    | ok _ =>
      simp [hC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      obtain ⟨hLo, hHi⟩ := checkBoundsFree_ok hC
      cases hP : parseFoldNode source locals expected chain node with
      | error e => simp [hP, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok dd =>
        simp [hP, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hL : lookupTag tags node with
        | none => simp [hL, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | some ii =>
          simp [hL, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact boundTests_free hLo hHi

/-- Rewriting an extension's arguments preserves its canonical range-fold classification. -/
theorem isRangeFold_ext_args (kind : XKind) (names : List String) (args rewritten : List SExpr) :
    isRangeFold (.ext kind names args) = isRangeFold (.ext kind names rewritten) := by
  cases names with
  | nil => rfl
  | cons binder rest =>
    cases rest with
    | nil => rfl
    | cons marker tail =>
      by_cases hMarker : marker = "range"
      · subst marker
        by_cases hKind : isFoldKind kind = true <;> simp [isRangeFold, matchFoldNode, hKind]
      · simp [isRangeFold, matchFoldNode, hMarker]

end Gabbro.Grammatik.Parser.SourceFolds
