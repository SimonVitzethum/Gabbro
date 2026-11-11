module

public import Grammatik.Parser.SourceFolds.Hoist
public import Grammatik.Parser.SourceFolds.RangeProofs

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- Expanding a list hoists every element in order: the rewritten expressions
    and the flattened prefixes are fold-free. -/
theorem hoistList_map_free (source : List SItemTief) (locals : Spec.Locals)
    (tags : List (SExpr × Nat)) (es : List SExpr) (pairs : List (SExpr × List SAnw))
    (h : es.mapM (expandNested 32 source locals [] tags) = .ok pairs) :
    hasRangeFoldList (pairs.map Prod.fst) = false ∧
      hasRangeFoldAnwList ((pairs.map Prod.snd).flatten) = false := by
  induction es generalizing pairs with
  | nil =>
    have h2 : (Except.ok [] : Except String (List (SExpr × List SAnw))) = .ok pairs := h
    obtain rfl := except_ok_inj h2
    exact ⟨by simp only [List.map_nil, hasRangeFoldList],
      by simp only [List.map_nil, List.flatten_nil, hasRangeFoldAnwList]⟩
  | cons x xs tail =>
    rw [List.mapM_cons] at h
    cases h1 : expandNested 32 source locals [] tags x with
    | error e => rw [h1] at h; cases h
    | ok p =>
      obtain ⟨x', sx⟩ := p
      cases h2 : xs.mapM (expandNested 32 source locals [] tags) with
      | error e => rw [h1, h2] at h; cases h
      | ok q =>
        rw [h1, h2] at h
        obtain rfl := except_ok_inj (a := (x', sx) :: q) h
        obtain ⟨ihFst, ihSnd⟩ := expandNested_ok source locals [] tags 32 _ _ _ h1
        obtain ⟨tailFst, tailSnd⟩ := tail _ h2
        exact ⟨by simp only [List.map_cons, hasRangeFoldList, ihFst, tailFst, Bool.or_self],
          by
            simp only [List.map_cons, List.flatten_cons]
            exact hasRangeFoldAnwList_append _ _ ihSnd tailSnd⟩

/-- A successful hoist leaves no fold in the rewritten expressions or the
    emitted prefix. -/
theorem hoistList_free (source : List SItemTief) (locals : Spec.Locals)
    (es es' : List SExpr) (s : List SAnw)
    (h : hoistList source locals es = .ok (es', s)) :
    hasRangeFoldList es' = false ∧ hasRangeFoldAnwList s = false := by
  unfold hoistList at h
  cases hR : hasRangeFoldList es with
  | true =>
    simp only [hR, ite_true] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hM : es.mapM (expandNested 32 source locals [] (tagFoldNodesList es 0).1) with
        | error e => rw [hM] at h; cases h
        | ok pairs =>
          rw [hM] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj
            (except_ok_inj (a := (pairs.map Prod.fst, (pairs.map Prod.snd).flatten)) h)
          exact hoistList_map_free source locals _ _ _ hM
  | false =>
    rw [hR] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (except_ok_inj (a := (es, ([] : List SAnw))) h)
    exact ⟨hR, by simp only [hasRangeFoldAnwList]⟩

/-- A successful single-expression hoist leaves no fold behind. -/
theorem hoistOne_free (source : List SItemTief) (locals : Spec.Locals)
    (e e' : SExpr) (s : List SAnw)
    (h : hoistOne source locals e = .ok (e', s)) :
    hasRangeFold e' = false ∧ hasRangeFoldAnwList s = false := by
  unfold hoistOne at h
  cases hM : hoistList source locals [e] with
  | error err => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨es, pre⟩ := pr
    rw [hM] at h
    match es, hM, h with
    | [], _, h => cases h
    | _ :: _ :: _, _, h => cases h
    | [x], hM, h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (except_ok_inj (a := (x, pre)) h)
      obtain ⟨hFst, hSnd⟩ := hoistList_free source locals [e] [x] pre hM
      simp only [hasRangeFoldList, Bool.or_false] at hFst
      exact ⟨hFst, hSnd⟩

/-- A successful pair hoist leaves no fold in either rewritten operand. -/
theorem hoistPair_free (source : List SItemTief) (locals : Spec.Locals)
    (a b a' b' : SExpr) (s : List SAnw)
    (h : hoistPair source locals a b = .ok (a', b', s)) :
    hasRangeFold a' = false ∧ hasRangeFold b' = false ∧
      hasRangeFoldAnwList s = false := by
  unfold hoistPair at h
  cases hM : hoistList source locals [a, b] with
  | error err => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨es, pre⟩ := pr
    rw [hM] at h
    match es, hM, h with
    | [], _, h => cases h
    | [_], _, h => cases h
    | _ :: _ :: _ :: _, _, h => cases h
    | [x, y], hM, h =>
      have hp := except_ok_inj (a := (x, y, pre)) h
      obtain ⟨rfl, hq⟩ := Prod.mk.inj hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      obtain ⟨hFst, hSnd⟩ := hoistList_free source locals [a, b] [x, y] pre hM
      simp only [hasRangeFoldList, Bool.or_false, Bool.or_eq_false_iff] at hFst
      exact ⟨hFst.1, hFst.2, hSnd⟩

/-- A successful hoist over a fold-carrying expression passed the freshness
    gate: no generated accumulator, element or result name occurs among the
    surrounding names, so no other read observes the accumulator. -/
theorem hoistList_gate (source : List SItemTief) (locals : Spec.Locals)
    (es es' : List SExpr) (s : List SAnw)
    (hR : hasRangeFoldList es = true)
    (h : hoistList source locals es = .ok (es', s)) :
    (reservedNames (tagFoldNodesList es 0).1.length).any
      ((locals.map Prod.fst ++ es.flatMap (Oeffentlich.namenA []) ++
        tagBinders (tagFoldNodesList es 0).1 ++
        (Spec.functionHeads source).map (·.name)).contains ·) = false := by
  unfold hoistList at h
  simp only [hR, ite_true] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hG
      exact (Bool.not_eq_true _).mp hG

/-- A returned range fold that becomes a block carries a fold-free prefix. The
    elimination theorem gives the whole block; the prefix is its head. -/
theorem returnFold_block_free (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (e : SExpr) (pre : List SAnw) (ending : Option SEnde)
    (hM : (matchFoldNode e).isSome = true)
    (h : returnFold source locals result (.ret (some e)) = .ok (.block pre ending)) :
    hasRangeFoldAnwList pre = false := by
  have hI : isRangeFold e = true := by simp [isRangeFold, hM]
  have hnf := returnFold_noFold source locals result e (.block pre ending) hI h
  cases hP : hasRangeFoldAnwList pre with
  | true => simp [hasRangeFoldAnw, hP] at hnf
  | false => rfl

end Gabbro.Grammatik.Parser.SourceFolds
