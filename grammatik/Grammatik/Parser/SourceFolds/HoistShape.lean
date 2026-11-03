module

public import Grammatik.Parser.SourceFolds.HoistProofs

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- A directly returned fold becomes a block: the statement head is fixed, only
    the prefix and the ending vary. -/
theorem returnFold_direct_shape (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (e : SExpr) (out : SAnw)
    (hM : (matchFoldNode e).isSome = true)
    (h : returnFold source locals result (.ret (some e)) = .ok out) :
    ∃ prefix ending, out = .block prefix ending := by
  unfold returnFold at h
  cases hN : matchFoldNode e with
  | none => simp [hN] at hM
  | some _ =>
    simp [hN] at h
    cases hR : result with
    | none => simp [hR] at h
    | some _ =>
      simp [hR] at h
      cases hD : hasDuplicateTags (tagFoldNodes e 0).1 with
      | true => simp [hD] at h
      | false =>
        simp [hD] at h
        cases hP : parseAndCheck source locals [] (tagFoldNodes e 0).1 result e with
        | error err => simp [hP] at h
        | ok pr =>
          obtain ⟨d, idx, tests⟩ := pr
          simp [hP] at h
          cases hC : (reservedNames (tagFoldNodes e 0).1.length).any
              ((d.binder :: locals.map Prod.fst ++
                Oeffentlich.namenA [] d.value ++ Oeffentlich.namenA [] d.filter ++
                (match d.empty with | none => [] | some emp => Oeffentlich.namenA [] emp) ++
                (Spec.functionHeads source).map (·.name)).contains ·) with
          | true => simp [hC] at h
          | false =>
            simp [hC] at h
            cases hF : expandNested 32 source locals [d.binder] (tagFoldNodes e 0).1 d.filter with
            | error err => simp [hF] at h
            | ok pF =>
              obtain ⟨filter', sF⟩ := pF
              simp [hF] at h
              cases hV : expandNested 32 source locals [d.binder] (tagFoldNodes e 0).1 d.value with
              | error err => simp [hV] at h
              | ok pV =>
                obtain ⟨value', sV⟩ := pV
                simp [hV] at h
                cases hEm : d.empty with
                | none =>
                  simp [hEm] at h
                  obtain ⟨rfl⟩ := h
                  exact ⟨_, _, rfl⟩
                | some emp =>
                  simp [hEm] at h
                  cases hE : expandNested 32 source locals [d.binder] (tagFoldNodes e 0).1 emp with
                  | error err => simp [hE] at h
                  | ok pE =>
                    obtain ⟨emp', se⟩ := pE
                    simp [hE] at h
                    obtain ⟨rfl⟩ := h
                    exact ⟨_, _, rfl⟩

/-- Every hoisted statement keeps its head: the output is either the input with
    its immediate folds replaced after a fold-free prefix, or the direct-return
    block with a fold-free prefix. The prefix runs before the statement, in
    source order, and the rewritten statement reads only fresh result
    variables. -/
theorem hoistAnw_shape (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (s out : SAnw)
    (h : hoistAnw source locals result s = .ok out) :
    (∃ s' prefix, out = afterPrefix s' prefix ∧ hasRangeFoldAnwList prefix = false) ∨
    (∃ prefix ending, out = .block prefix ending ∧
      hasRangeFoldAnwList prefix = false) := by
  cases s with
  | ret e =>
    cases hE : e with
    | none =>
      simp only [hoistAnw, hE] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, [], rfl, rfl⟩
    | some e =>
      simp only [hoistAnw, hE] at h
      cases hM : matchFoldNode e with
      | none =>
        simp only [hM] at h
        cases hH : hoistOne source locals e with
        | error err => simp [hH] at h
        | ok pr =>
          obtain ⟨e', prefix⟩ := pr
          simp [hH] at h
          obtain ⟨rfl⟩ := h
          exact Or.inl ⟨_, _, rfl,
            (hoistOne_free source locals e _ prefix hH).2⟩
      | some _ =>
        simp only [hM] at h
        cases hR : returnFold source locals result (.ret (some e)) with
        | error err => simp [hR] at h
        | ok o =>
          simp [hR] at h
          obtain ⟨rfl⟩ := h
          obtain ⟨prefix, ending, rfl⟩ :=
            returnFold_direct_shape source locals result e o (by simp [hM]) hR
          exact Or.inr ⟨prefix, ending, rfl,
            returnFold_block_free source locals result e prefix ending
              (by simp [hM]) hR⟩
  | bind b n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | bindQ b n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | bindElse n t e why body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | bindAxiomOpt n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | bindAxiomOptElse n t e why body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | await n t e p =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | swap n t e p =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | set a op b =>
    simp only [hoistAnw] at h
    cases hH : hoistPair source locals a b with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨a', b', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistPair_free source locals a b _ _ prefix hH).2.2⟩
  | shift e a b =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | trim e n body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | trimReq e n =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | free e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | call name args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' prefix hH).2⟩
  | callQ name args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' prefix hH).2⟩
  | callElse name args reason body =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' prefix hH).2⟩
  | genericCall name words args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' prefix hH).2⟩
  | cond c body arms other =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals c with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨c', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals c _ prefix hH).2⟩
  | elsif c body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals c with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨c', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals c _ prefix hH).2⟩
  | cases g arms =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals g with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨g', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals g _ prefix hH).2⟩
  | alloc b n t a e body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | reset n r =>
    simp only [hoistAnw] at h
    cases hM : hoistList source locals
        (r.toList.flatMap fun p => [p.1, p.2]) with
    | error err => simp [hM] at h
    | ok pr =>
      obtain ⟨es, prefix⟩ := pr
      simp [hM] at h
      cases hE : es with
      | nil =>
        simp [hE] at h
        obtain ⟨rfl⟩ := h
        rw [hE] at hM
        exact Or.inl ⟨_, _, rfl,
          (hoistList_free source locals _ _ prefix hM).2⟩
      | cons a l =>
        cases hL : l with
        | nil => simp [hE, hL] at h
        | cons b l2 =>
          cases l2 with
          | cons _ _ => simp [hE, hL] at h
          | nil =>
            simp [hE, hL] at h
            obtain ⟨rfl⟩ := h
            rw [hE, hL] at hM
            exact Or.inl ⟨_, _, rfl,
              (hoistList_free source locals _ _ prefix hM).2⟩
  | grow n e body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ prefix hH).2⟩
  | emit a b p =>
    simp only [hoistAnw] at h
    cases hH : hoistPair source locals a b with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨a', b', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistPair_free source locals a b _ _ prefix hH).2.2⟩
  | bindLib b n t c =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals c.args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals c.args args' prefix hH).2⟩
  | lcall c =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals c.args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', prefix⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals c.args args' prefix hH).2⟩
  | block ss ending =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | each n start kind subject mode raw inv body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | retry raw body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | loop raw body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | waive ns body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | watch n body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | leave n =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | next n =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | child body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | start ns =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | other raw =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | arm c n body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | step a b =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | allocVon b n t a =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩
  | locks b e body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, rfl⟩

end Gabbro.Grammatik.Parser.SourceFolds
