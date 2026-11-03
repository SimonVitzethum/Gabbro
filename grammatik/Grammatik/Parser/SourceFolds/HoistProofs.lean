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
    exact ⟨rfl, rfl⟩
  | cons x xs tail =>
    simp [List.mapM] at h
    cases h1 : expandNested 32 source locals [] tags x with
    | error e => simp [h1] at h
    | ok p =>
      obtain ⟨x', sx⟩ := p
      simp [h1] at h
      cases h2 : xs.mapM (expandNested 32 source locals [] tags) with
      | error e => simp [h2] at h
      | ok q =>
        simp [h2] at h
        obtain ⟨rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := expandNested_ok source locals [] tags 32 _ _ _ h1
        obtain ⟨tailFst, tailSnd⟩ := tail _ h2
        exact ⟨by simp [hasRangeFoldList, ihFst, tailFst],
          by simp [List.flatten, hasRangeFoldAnwList_append, ihSnd, tailSnd]⟩

/-- A successful hoist leaves no fold in the rewritten expressions or the
    emitted prefix. -/
theorem hoistList_free (source : List SItemTief) (locals : Spec.Locals)
    (es es' : List SExpr) (s : List SAnw)
    (h : hoistList source locals es = .ok (es', s)) :
    hasRangeFoldList es' = false ∧ hasRangeFoldAnwList s = false := by
  unfold hoistList at h
  cases hR : hasRangeFoldList es with
  | true =>
    simp [hR] at h
    cases hD : hasDuplicateTags (tagFoldNodesList es 0).1 with
    | true => simp [hD] at h
    | false =>
      simp [hD] at h
      cases hG : (reservedNames (tagFoldNodesList es 0).1.length).any
          ((locals.map Prod.fst ++ es.flatMap (Oeffentlich.namenA []) ++
            tagBinders (tagFoldNodesList es 0).1 ++
            (Spec.functionHeads source).map (·.name)).contains ·) with
      | true => simp [hG] at h
      | false =>
        simp [hG] at h
        cases hM : es.mapM (expandNested 32 source locals [] (tagFoldNodesList es 0).1) with
        | error e => simp [hM] at h
        | ok pairs =>
          simp [hM] at h
          obtain ⟨rfl⟩ := h
          exact hoistList_map_free source locals _ _ _ hM
  | false =>
    simp [hR] at h
    obtain ⟨rfl⟩ := h
    exact ⟨hR, rfl⟩

/-- A successful single-expression hoist leaves no fold behind. -/
theorem hoistOne_free (source : List SItemTief) (locals : Spec.Locals)
    (e e' : SExpr) (s : List SAnw)
    (h : hoistOne source locals e = .ok (e', s)) :
    hasRangeFold e' = false ∧ hasRangeFoldAnwList s = false := by
  unfold hoistOne at h
  cases hM : hoistList source locals [e] with
  | error err => simp [hM] at h
  | ok pr =>
    obtain ⟨es, prefix⟩ := pr
    simp [hM] at h
    cases hE : es with
    | nil => simp [hE] at h
    | cons x xs =>
      cases hX : xs with
      | cons _ _ => simp [hE, hX] at h
      | nil =>
        simp [hE, hX] at h
        obtain ⟨rfl⟩ := h
        rw [hE, hX] at hM
        obtain ⟨hFst, hSnd⟩ := hoistList_free source locals [e] [x] prefix hM
        cases hx : hasRangeFold x with
        | true => simp [hasRangeFoldList, hx] at hFst
        | false => exact ⟨hx, hSnd⟩

/-- A successful pair hoist leaves no fold in either rewritten operand. -/
theorem hoistPair_free (source : List SItemTief) (locals : Spec.Locals)
    (a b a' b' : SExpr) (s : List SAnw)
    (h : hoistPair source locals a b = .ok (a', b', s)) :
    hasRangeFold a' = false ∧ hasRangeFold b' = false ∧
      hasRangeFoldAnwList s = false := by
  unfold hoistPair at h
  cases hM : hoistList source locals [a, b] with
  | error err => simp [hM] at h
  | ok pr =>
    obtain ⟨es, prefix⟩ := pr
    simp [hM] at h
    cases hE : es with
    | nil => simp [hE] at h
    | cons x xs =>
      cases hX : xs with
      | nil => simp [hE, hX] at h
      | cons y ys =>
        cases hY : ys with
        | cons _ _ => simp [hE, hX, hY] at h
        | nil =>
          simp [hE, hX, hY] at h
          obtain ⟨rfl⟩ := h
          rw [hE, hX, hY] at hM
          obtain ⟨hFst, hSnd⟩ := hoistList_free source locals [a, b] [x, y] prefix hM
          cases hx : hasRangeFold x with
          | true => simp [hasRangeFoldList, hx] at hFst
          | false =>
            cases hy : hasRangeFold y with
            | true => simp [hasRangeFoldList, hx, hy] at hFst
            | false => exact ⟨hx, hy, hSnd⟩

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
  rw [hR] at h
  simp at h
  cases hD : hasDuplicateTags (tagFoldNodesList es 0).1 with
  | true => simp [hD] at h
  | false =>
    simp [hD] at h
    cases hG : (reservedNames (tagFoldNodesList es 0).1.length).any
        ((locals.map Prod.fst ++ es.flatMap (Oeffentlich.namenA []) ++
          tagBinders (tagFoldNodesList es 0).1 ++
          (Spec.functionHeads source).map (·.name)).contains ·) with
    | true => simp [hG] at h
    | false => exact hG

/-- A returned range fold that becomes a block carries a fold-free prefix. The
    elimination theorem gives the whole block; the prefix is its head. -/
theorem returnFold_block_free (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (e : SExpr) (prefix : List SAnw) (ending : Option SEnde)
    (hM : (matchFoldNode e).isSome = true)
    (h : returnFold source locals result (.ret (some e)) = .ok (.block prefix ending)) :
    hasRangeFoldAnwList prefix = false := by
  have hI : isRangeFold e = true := by simp [isRangeFold, hM]
  have hnf := returnFold_noFold source locals result e (.block prefix ending) hI h
  cases hP : hasRangeFoldAnwList prefix with
  | true => simp [hasRangeFoldAnw, hP] at hnf
  | false => exact hP

/-- A `let` binding a range fold hoists the loop before the binding. The
    accumulator uses the nested derivation, since the hoist carries no
    ascription; the ordinary elaborator checks the annotation afterwards. -/
theorem hoistAnw_let_zeuge :
    hoistAnw [] [("xs", .array (.atom "u8") (.lit 2))] none
      (.bind false "t" none
        (.ext .foldAdd ["i", "range"]
          [.lit 0, .lit 2, .tru, .index (.variable "xs") (.variable "i")])) =
    .ok (.block
      [.bind true "$rangeFold$acc$0" (some (.atom "u64")) (.lit 0),
       .each "i" none "elems" (.variable "xs") "unvisited" "" none
         (.block
           [.bind false "$rangeFold$value$0" none
              (.index (.variable "xs") (.variable "i")),
            .set (.variable "$rangeFold$acc$0") "+=" (.variable "$rangeFold$value$0")] none),
       .bind false "$rangeFold$result$0" none (.variable "$rangeFold$acc$0"),
       .bind false "t" none (.variable "$rangeFold$result$0")] none) := rfl

end Gabbro.Grammatik.Parser.SourceFolds
