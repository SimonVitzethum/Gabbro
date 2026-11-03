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
    exact ⟨k, b, a, hm⟩

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
  cases hK : d.kind with
  | foldAdd => simp [combineStmts, hK, hasRangeFold]
  | foldMin => simp [combineStmts, hK, hasRangeFold]
  | foldMax => simp [combineStmts, hK, hasRangeFold]
  | foldAnd => simp [combineStmts, hK, hasRangeFold]
  | foldOr => simp [combineStmts, hK, hasRangeFold]
  | all => simp [combineStmts, hK, hasRangeFold]
  | any => simp [combineStmts, hK, hasRangeFold]
  | count => simp [combineStmts, hK, hasRangeFold]
  | mem => simp [combineStmts, hK, hasRangeFold]
  | reach => simp [combineStmts, hK, hasRangeFold]
  | imp => simp [combineStmts, hK, hasRangeFold]
  | text => simp [combineStmts, hK, hasRangeFold]
  | call => simp [combineStmts, hK, hasRangeFold]
  | label => simp [combineStmts, hK, hasRangeFold]
  | dyn => simp [combineStmts, hK, hasRangeFold]
  | instantiate => simp [combineStmts, hK, hasRangeFold]

theorem foldInit_free (kind : XKind) (empty' : Option SExpr)
    (h : (empty'.map hasRangeFold).getD false = false) :
    hasRangeFold (foldInit kind empty') = false := by
  cases kind with
  | foldAdd => simp [foldInit]
  | foldAnd => simp [foldInit]
  | foldOr => simp [foldInit]
  | foldMin =>
    cases empty' with
    | none => simp [foldInit]
    | some emp' => simp [foldInit, h]
  | foldMax =>
    cases empty' with
    | none => simp [foldInit]
    | some emp' => simp [foldInit, h]
  | all => simp [foldInit, h]
  | any => simp [foldInit, h]
  | count => simp [foldInit, h]
  | mem => simp [foldInit, h]
  | reach => simp [foldInit, h]
  | imp => simp [foldInit, h]
  | text => simp [foldInit, h]
  | call => simp [foldInit, h]
  | label => simp [foldInit, h]
  | dyn => simp [foldInit, h]
  | instantiate => simp [foldInit, h]

theorem boundTests_free {lo hi count : SExpr} {binder : String}
    (hlo : hasRangeFold lo = false) (hhi : hasRangeFold hi = false) :
    hasRangeFoldList (boundTests lo hi count binder) = false := by
  unfold boundTests
  cases h1 : beqSExpr lo (.lit 0) with
  | true =>
    cases h2 : beqSExpr hi count with
    | true => simp [h1, h2]
    | false => simp [h1, h2, hhi, hasRangeFold, hasRangeFoldList]
  | false =>
    cases h2 : beqSExpr hi count with
    | true => simp [h1, h2, hlo, hasRangeFold, hasRangeFoldList]
    | false => simp [h1, h2, hlo, hhi, hasRangeFold, hasRangeFoldList]

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
        exact tail _ hstep
      | false =>
        have hstep : hasRangeFold (if beqSExpr filter' .tru then t else .bin "&&" filter' t) = false := by
          simp [hcur, hf, htt, hasRangeFold]
        exact tail _ hstep

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
      hasRangeFoldAnwList_append, hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFold]
  | false =>
    simp [hE, hF, hV, hf, hv, heff, combineStmts_free,
      hasRangeFoldAnwList_append, hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFold]

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
    simp [hB] at h
    cases hP : parseFoldNode source locals expected chain node with
    | error e => simp [hP] at h
    | ok dd =>
      simp [hP] at h
      cases hL : lookupTag tags node with
      | none => simp [hL] at h
      | some ii =>
        simp [hL] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
  | some p =>
    obtain ⟨lo, hi⟩ := p
    simp [hB] at h
    cases hC : checkBoundsFree lo hi with
    | error e => simp [hC] at h
    | ok _ =>
      simp [hC] at h
      obtain ⟨hLo, hHi⟩ := checkBoundsFree_ok hC
      cases hP : parseFoldNode source locals expected chain node with
      | error e => simp [hP] at h
      | ok dd =>
        simp [hP] at h
        cases hL : lookupTag tags node with
        | none => simp [hL] at h
        | some ii =>
          simp [hL] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact boundTests_free hLo hHi

/-- Expansion eliminates every range fold node from an expression. -/
theorem expandNested_ok (source : List SItemTief) (locals : Spec.Locals)
    (chain : List String) (tags : List (SExpr × Nat)) :
    ∀ (fuel : Nat) (e e' : SExpr) (s : List SAnw),
    expandNested fuel source locals chain tags e = .ok (e', s) →
    hasRangeFold e' = false ∧ hasRangeFoldAnwList s = false := by
  intro fuel
  induction fuel generalizing chain with
  | zero =>
    intro e e' s h
    cases hh : hasRangeFold e with
    | true => simp [expandNested, hh] at h
    | false =>
      simp [expandNested, hh] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh, rfl⟩
  | succ f ih =>
    have argsOk : ∀ (xs : List SExpr) (pairs : List (SExpr × List SAnw)),
      xs.mapM (expandNested f source locals chain tags) = .ok pairs →
      hasRangeFoldList (pairs.map Prod.fst) = false ∧
        hasRangeFoldAnwList ((pairs.map Prod.snd).flatten) = false := by
      intro xs
      induction xs with
      | nil =>
        intro pairs h
        have h2 : (Except.ok [] : Except String (List (SExpr × List SAnw))) = .ok pairs := h
        obtain rfl := except_ok_inj h2
        exact ⟨rfl, rfl⟩
      | cons x xs tail =>
        intro pairs h
        simp [List.mapM] at h
        cases h1 : expandNested f source locals chain tags x with
        | error e => simp [h1] at h
        | ok p =>
          obtain ⟨x', sx⟩ := p
          simp [h1] at h
          cases h2 : xs.mapM (expandNested f source locals chain tags) with
          | error e => simp [h2] at h
          | ok q =>
            simp [h2] at h
            obtain ⟨rfl⟩ := h
            obtain ⟨ihFst, ihSnd⟩ := ih _ _ _ _ h1
            obtain ⟨tailFst, tailSnd⟩ := tail _ _ h2
            exact ⟨by simp [hasRangeFoldList, ihFst, tailFst],
              by simp [List.flatten, hasRangeFoldAnwList_append, ihSnd, tailSnd]⟩
    intro e e' s h
    cases e with
    | lit n => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | float t => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | tru => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | fls => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | «variable» v => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | fnref f => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | res => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | why g r => simp [expandNested, matchFoldNode] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | field x fieldName =>
      simp [expandNested, matchFoldNode] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih _ _ _ _ h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | arrow x fieldName =>
      simp [expandNested, matchFoldNode] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih _ _ _ _ h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | un o x =>
      simp [expandNested, matchFoldNode] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih _ _ _ _ h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | old x =>
      simp [expandNested, matchFoldNode] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih _ _ _ _ h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | index a b =>
      simp [expandNested, matchFoldNode] at h
      cases ha : expandNested f source locals chain tags a with
      | error e => simp [ha] at h
      | ok pa =>
        obtain ⟨a', sa⟩ := pa
        simp [ha] at h
        cases hb : expandNested f source locals chain tags b with
        | error e => simp [hb] at h
        | ok pb =>
          obtain ⟨b', sb⟩ := pb
          simp [hb] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ihaF, ihaS⟩ := ih _ _ _ _ ha
          obtain ⟨ihbF, ihbS⟩ := ih _ _ _ _ hb
          exact ⟨by simp [hasRangeFold, ihaF, ihbF],
            by simp [hasRangeFoldAnwList_append, ihaS, ihbS]⟩
    | bin o a b =>
      simp [expandNested, matchFoldNode] at h
      cases ha : expandNested f source locals chain tags a with
      | error e => simp [ha] at h
      | ok pa =>
        obtain ⟨a', sa⟩ := pa
        simp [ha] at h
        cases hb : expandNested f source locals chain tags b with
        | error e => simp [hb] at h
        | ok pb =>
          obtain ⟨b', sb⟩ := pb
          simp [hb] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ihaF, ihaS⟩ := ih _ _ _ _ ha
          obtain ⟨ihbF, ihbS⟩ := ih _ _ _ _ hb
          exact ⟨by simp [hasRangeFold, ihaF, ihbF],
            by simp [hasRangeFoldAnwList_append, ihaS, ihbS]⟩
    | call g args =>
      simp [expandNested, matchFoldNode] at h
      cases hM : args.mapM (expandNested f source locals chain tags) with
      | error e => simp [hM] at h
      | ok pairs =>
        simp [hM] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hM
        exact ⟨by simp [hasRangeFold, mapFst],
          by simp [hasRangeFoldAnwList_append, mapSnd]⟩
    | built g args =>
      simp [expandNested, matchFoldNode] at h
      cases hM : args.mapM (expandNested f source locals chain tags) with
      | error e => simp [hM] at h
      | ok pairs =>
        simp [hM] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hM
        exact ⟨by simp [hasRangeFold, mapFst],
          by simp [hasRangeFoldAnwList_append, mapSnd]⟩
    | ext k ns args =>
      cases hM : matchFoldNode (.ext k ns args) with
      | none =>
        simp [expandNested, hM] at h
        cases hA : args.mapM (expandNested f source locals chain tags) with
        | error e => simp [hA] at h
        | ok pairs =>
          simp [hA] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hA
          exact ⟨by simp [hasRangeFold, mapFst],
            by simp [hasRangeFoldAnwList_append, mapSnd]⟩
      | some _ =>
        simp [expandNested, hM] at h
        cases hPC : parseAndCheck source locals chain tags none (.ext k ns args) with
        | error e => simp [hPC] at h
        | ok p =>
          obtain ⟨d, idx, tests⟩ := p
          have hT := parseAndCheck_tests_free _ _ _ _ _ _ _ _ _ hPC
          simp [hPC] at h
          cases hF : expandNested f source locals (d.binder :: chain) tags d.filter with
          | error e => simp [hF] at h
          | ok pF =>
            obtain ⟨filter', sF⟩ := pF
            simp [hF] at h
            cases hV : expandNested f source locals (d.binder :: chain) tags d.value with
            | error e => simp [hV] at h
            | ok pV =>
              obtain ⟨value', sV⟩ := pV
              simp [hV] at h
              cases hEm : d.empty with
              | none =>
                simp [hEm] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨ihFF, ihFS⟩ := ih _ _ _ _ hF
                obtain ⟨ihVF, ihVS⟩ := ih _ _ _ _ hV
                have he : ((none : Option SExpr).map hasRangeFold).getD false = false := rfl
                have hPre := buildFoldPrefix_free d idx filter' value' sF sV [] none tests
                  ihFS ihVS rfl ihFF ihVF he hT
                have hTmp : hasRangeFoldAnwList
                    [SAnw.bind false (resultName idx) none
                      (.variable (accName idx))] = false := by
                  simp [hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFold]
                exact ⟨rfl, hasRangeFoldAnwList_append _ _ hPre hTmp⟩
              | some emp =>
                simp [hEm] at h
                cases hE : expandNested f source locals (d.binder :: chain) tags emp with
                | error e => simp [hE] at h
                | ok pE =>
                  obtain ⟨emp', sE⟩ := pE
                  simp [hE] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨ihFF, ihFS⟩ := ih _ _ _ _ hF
                  obtain ⟨ihVF, ihVS⟩ := ih _ _ _ _ hV
                  obtain ⟨ihEF, ihES⟩ := ih _ _ _ _ hE
                  have he : ((some emp').map hasRangeFold).getD false = false := by
                    simpa using ihEF
                  have hPre := buildFoldPrefix_free d idx filter' value' sF sV sE (some emp') tests
                    ihFS ihVS ihES ihFF ihVF he hT
                  have hTmp : hasRangeFoldAnwList
                      [SAnw.bind false (resultName idx) none
                        (.variable (accName idx))] = false := by
                    simp [hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFold]
                  exact ⟨rfl, hasRangeFoldAnwList_append _ _ hPre hTmp⟩


/-- A returned range fold expands to ordinary traversal with no fold left. -/
theorem returnFold_noFold (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (f : SExpr) (out : SAnw) :
    isRangeFold f = true →
    returnFold source locals result (.ret (some f)) = .ok out →
    hasRangeFoldAnw out = false := by
  intro hf h
  simp [returnFold] at h
  cases hM : matchFoldNode f with
  | none =>
    have hZ : isRangeFold f = false := by simp [isRangeFold, hM]
    simp [hZ] at hf
  | some _ =>
    simp [hM] at h
    cases hR : result with
    | none => simp [hR] at h
    | some ty =>
      simp [hR] at h
      cases hDup : hasDuplicateTags (tagFoldNodes f 0).1 with
      | true => simp [hDup] at h
      | false =>
        simp [hDup] at h
        cases hPC : parseAndCheck source locals [] (tagFoldNodes f 0).1 result f with
        | error e => simp [hPC] at h
        | ok p =>
          obtain ⟨d, idx, tests⟩ := p
          have hT := parseAndCheck_tests_free _ _ _ _ _ _ _ _ _ hPC
          simp [hPC] at h
          cases hCol : (reservedNames ((tagFoldNodes f 0).1.length)).any
              ((d.binder :: locals.map Prod.fst ++
                Oeffentlich.namenA [] d.value ++ Oeffentlich.namenA [] d.filter ++
                (match d.empty with | none => [] | some emp => Oeffentlich.namenA [] emp) ++
                (Spec.functionHeads source).map (·.name)).contains ·) with
          | true => simp [hCol] at h
          | false =>
            simp [hCol] at h
            cases hF : expandNested 32 source locals [d.binder]
                (tagFoldNodes f 0).1 d.filter with
            | error e => simp [hF] at h
            | ok pF =>
              obtain ⟨filter', sF⟩ := pF
              simp [hF] at h
              cases hV : expandNested 32 source locals [d.binder]
                  (tagFoldNodes f 0).1 d.value with
              | error e => simp [hV] at h
              | ok pV =>
                obtain ⟨value', sV⟩ := pV
                simp [hV] at h
                cases hEm : d.empty with
                | none =>
                  simp [hEm] at h
                  obtain ⟨rfl⟩ := h
                  obtain ⟨hFF, hFS⟩ := expandNested_ok source locals [d.binder]
                    ((tagFoldNodes f 0).1) 32 d.filter filter' sF hF
                  obtain ⟨hVF, hVS⟩ := expandNested_ok source locals [d.binder]
                    ((tagFoldNodes f 0).1) 32 d.value value' sV hV
                  have hPre := buildFoldPrefix_free d idx filter' value' sF sV [] none tests
                    hFS hVS rfl hFF hVF rfl hT
                  simp [hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold, hPre]
                | some emp =>
                  simp [hEm] at h
                  cases hE : expandNested 32 source locals [d.binder]
                      (tagFoldNodes f 0).1 emp with
                  | error e => simp [hE] at h
                  | ok pE =>
                    obtain ⟨emp', se⟩ := pE
                    simp [hE] at h
                    obtain ⟨rfl⟩ := h
                    obtain ⟨hFF, hFS⟩ := expandNested_ok source locals [d.binder]
                      ((tagFoldNodes f 0).1) 32 d.filter filter' sF hF
                    obtain ⟨hVF, hVS⟩ := expandNested_ok source locals [d.binder]
                      ((tagFoldNodes f 0).1) 32 d.value value' sV hV
                    obtain ⟨hEF, hES⟩ := expandNested_ok source locals [d.binder]
                      ((tagFoldNodes f 0).1) 32 emp emp' se hE
                    have he : ((some emp').map hasRangeFold).getD false = false := by
                      simpa using hEF
                    have hPre := buildFoldPrefix_free d idx filter' value' sF sV se
                      (some emp') tests hFS hVS hES hFF hVF he hT
                    simp [hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold, hPre]


end Gabbro.Grammatik.Parser.SourceFolds
