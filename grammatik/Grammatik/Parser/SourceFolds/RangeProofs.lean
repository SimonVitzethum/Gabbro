module

public import Grammatik.Parser.SourceFolds.RangeProofs.Prefix

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

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
    | true => simp [expandNested, hh, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    | false =>
      simp [expandNested, hh, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh, by simp [hasRangeFoldAnwList]⟩
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
        exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
      | cons x xs tail =>
        intro pairs h
        simp only [List.mapM_cons] at h
        cases h1 : expandNested f source locals chain tags x with
        | error e => simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok p =>
          obtain ⟨x', sx⟩ := p
          simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          cases h2 : xs.mapM (expandNested f source locals chain tags) with
          | error e => simp [h2, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          | ok q =>
            simp [h2, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
            obtain ⟨rfl⟩ := h
            obtain ⟨ihFst, ihSnd⟩ := ih chain x x' sx h1
            obtain ⟨tailFst, tailSnd⟩ := tail q h2
            exact ⟨by simp [hasRangeFoldList, ihFst, tailFst],
              by simpa only [List.map_cons, List.flatten_cons] using
                (hasRangeFoldAnwList_append sx ((q.map Prod.snd).flatten) ihSnd tailSnd)⟩
    intro e e' s h
    cases e with
    | lit n => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | float t => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | tru => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | fls => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | «variable» v => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | fnref f => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | res => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | why g r => simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by simp [hasRangeFoldAnwList]⟩
    | field x fieldName =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih chain x x' sx h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | arrow x fieldName =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih chain x x' sx h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | un o x =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih chain x x' sx h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | old x =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases h1 : expandNested f source locals chain tags x with
      | error e => simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok p =>
        obtain ⟨x', sx⟩ := p
        simp [h1, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihFst, ihSnd⟩ := ih chain x x' sx h1
        exact ⟨by simp [hasRangeFold, ihFst],
          by simp [hasRangeFoldAnwList_append, ihSnd]⟩
    | index a b =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases ha : expandNested f source locals chain tags a with
      | error e => simp [ha, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok pa =>
        obtain ⟨a', sa⟩ := pa
        simp [ha, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hb : expandNested f source locals chain tags b with
        | error e => simp [hb, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok pb =>
          obtain ⟨b', sb⟩ := pb
          simp [hb, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ihaF, ihaS⟩ := ih chain a a' sa ha
          obtain ⟨ihbF, ihbS⟩ := ih chain b b' sb hb
          exact ⟨by simp [hasRangeFold, ihaF, ihbF],
            by simp [hasRangeFoldAnwList_append, ihaS, ihbS]⟩
    | bin o a b =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases ha : expandNested f source locals chain tags a with
      | error e => simp [ha, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok pa =>
        obtain ⟨a', sa⟩ := pa
        simp [ha, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hb : expandNested f source locals chain tags b with
        | error e => simp [hb, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok pb =>
          obtain ⟨b', sb⟩ := pb
          simp [hb, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ihaF, ihaS⟩ := ih chain a a' sa ha
          obtain ⟨ihbF, ihbS⟩ := ih chain b b' sb hb
          exact ⟨by simp [hasRangeFold, ihaF, ihbF],
            by simp [hasRangeFoldAnwList_append, ihaS, ihbS]⟩
    | call g args =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases hM : args.mapM (expandNested f source locals chain tags) with
      | error e => simp [hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok pairs =>
        simp [hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hM
        exact ⟨by simp [hasRangeFold, mapFst],
          by simp [hasRangeFoldAnwList_append, mapSnd]⟩
    | built g args =>
      simp [expandNested, matchFoldNode, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases hM : args.mapM (expandNested f source locals chain tags) with
      | error e => simp [hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | ok pairs =>
        simp [hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hM
        exact ⟨by simp [hasRangeFold, mapFst],
          by simp [hasRangeFoldAnwList_append, mapSnd]⟩
    | ext k ns args =>
      cases hM : matchFoldNode (.ext k ns args) with
      | none =>
        simp [expandNested, hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hA : args.mapM (expandNested f source locals chain tags) with
        | error e => simp [hA, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok pairs =>
          simp [hA, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨mapFst, mapSnd⟩ := argsOk _ _ hA
          have hRoot : isRangeFold (.ext k ns (pairs.map Prod.fst)) = false := by
            rw [← isRangeFold_ext_args k ns args (pairs.map Prod.fst)]
            simp [isRangeFold, hM]
          exact ⟨by simp [hasRangeFold, hRoot, mapFst],
            by simp [hasRangeFoldAnwList_append, mapSnd]⟩
      | some _ =>
        simp [expandNested, hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hPC : parseAndCheck source locals chain tags none (.ext k ns args) with
        | error e => simp [hPC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok p =>
          obtain ⟨d, idx, tests⟩ := p
          have hT := parseAndCheck_tests_free _ _ _ _ _ _ _ _ _ hPC
          simp [hPC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          cases hF : expandNested f source locals (d.binder :: chain) tags d.filter with
          | error e => simp [hF, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          | ok pF =>
            obtain ⟨filter', sF⟩ := pF
            simp [hF, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
            cases hV : expandNested f source locals (d.binder :: chain) tags d.value with
            | error e => simp [hV, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
            | ok pV =>
              obtain ⟨value', sV⟩ := pV
              simp [hV, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
              cases hEm : d.empty with
              | none =>
                simp [hEm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨ihFF, ihFS⟩ := ih (d.binder :: chain) d.filter filter' sF hF
                obtain ⟨ihVF, ihVS⟩ := ih (d.binder :: chain) d.value value' sV hV
                have he : ((none : Option SExpr).map hasRangeFold).getD false = false := rfl
                have hPre := buildFoldPrefix_free d idx filter' value' sF sV [] none tests
                  ihFS ihVS (by simp [hasRangeFoldAnwList]) ihFF ihVF he hT
                have hTmp : hasRangeFoldAnwList
                    [SAnw.bind false (resultName idx) none
                      (.variable (accName idx))] = false := by
                  simp [hasRangeFoldAnwList, hasRangeFoldAnw, hasRangeFold]
                exact ⟨rfl, hasRangeFoldAnwList_append _ _ hPre hTmp⟩
              | some emp =>
                simp [hEm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                cases hE : expandNested f source locals (d.binder :: chain) tags emp with
                | error e => simp [hE, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                | ok pE =>
                  obtain ⟨emp', sE⟩ := pE
                  simp [hE, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨ihFF, ihFS⟩ := ih (d.binder :: chain) d.filter filter' sF hF
                  obtain ⟨ihVF, ihVS⟩ := ih (d.binder :: chain) d.value value' sV hV
                  obtain ⟨ihEF, ihES⟩ := ih (d.binder :: chain) emp emp' sE hE
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
  simp [returnFold, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
  cases hM : matchFoldNode f with
  | none =>
    have hZ : isRangeFold f = false := by simp [isRangeFold, hM]
    simp [hZ] at hf
  | some _ =>
    simp [hM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    cases hR : result with
    | none => simp [hR, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
    | some ty =>
      simp [hR, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      cases hDup : hasDuplicateTags (tagFoldNodes f 0).1 with
      | true => simp [hDup, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      | false =>
        simp [hDup, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        cases hPC : parseAndCheck source locals [] (tagFoldNodes f 0).1 (some ty) f with
        | error e => simp [hPC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        | ok p =>
          obtain ⟨d, idx, tests⟩ := p
          have hT := parseAndCheck_tests_free _ _ _ _ _ _ _ _ _ hPC
          simp [hPC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          cases hCol : (reservedNames ((tagFoldNodes f 0).1.length)).any
              ((d.binder :: locals.map Prod.fst ++
                Oeffentlich.namenA [] d.value ++ Oeffentlich.namenA [] d.filter ++
                (match d.empty with | none => [] | some emp => Oeffentlich.namenA [] emp) ++
                (Spec.functionHeads source).map (·.name)).contains ·) with
          | true => simp [hCol, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
          | false =>
            simp [hCol, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
            cases hF : expandNested 32 source locals [d.binder]
                (tagFoldNodes f 0).1 d.filter with
            | error e => simp [hF, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
            | ok pF =>
              obtain ⟨filter', sF⟩ := pF
              simp [hF, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
              cases hV : expandNested 32 source locals [d.binder]
                  (tagFoldNodes f 0).1 d.value with
              | error e => simp [hV, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
              | ok pV =>
                obtain ⟨value', sV⟩ := pV
                simp [hV, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                cases hEm : d.empty with
                | none =>
                  simp [hEm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                  obtain ⟨rfl⟩ := h
                  obtain ⟨hFF, hFS⟩ := expandNested_ok source locals [d.binder]
                    ((tagFoldNodes f 0).1) 32 d.filter filter' sF hF
                  obtain ⟨hVF, hVS⟩ := expandNested_ok source locals [d.binder]
                    ((tagFoldNodes f 0).1) 32 d.value value' sV hV
                  have hPre := buildFoldPrefix_free d idx filter' value' sF sV [] none tests
                    hFS hVS (by simp [hasRangeFoldAnwList]) hFF hVF rfl hT
                  simp [hasRangeFoldAnw, hasRangeFoldEnde, hasRangeFold, hPre]
                | some emp =>
                  simp [hEm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                  cases hE : expandNested 32 source locals [d.binder]
                      (tagFoldNodes f 0).1 emp with
                  | error e => simp [hE, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
                  | ok pE =>
                    obtain ⟨emp', se⟩ := pE
                    simp [hE, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
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
