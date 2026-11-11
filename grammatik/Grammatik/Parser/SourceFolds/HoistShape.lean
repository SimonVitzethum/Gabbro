module

public import Grammatik.Parser.SourceFolds.HoistProofs

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- The `Except` monad computes on its constructors; `simp` needs these stated. -/
private theorem exceptBindOk {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a >>= k) = k a := rfl
private theorem exceptBindError {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e >>= k) = Except.error e := rfl
private theorem exceptMapOk {ε α β : Type} (a : α) (k : α → β) :
    k <$> (Except.ok a : Except ε α) = Except.ok (k a) := rfl
private theorem exceptMapError {ε α β : Type} (e : ε) (k : α → β) :
    k <$> (Except.error e : Except ε α) = Except.error e := rfl
private theorem exceptThrow {ε α : Type} (e : ε) : (throw e : Except ε α) = Except.error e := rfl
private theorem exceptPure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
private theorem nilFree : hasRangeFoldAnwList [] = false := by simp only [hasRangeFoldAnwList]
attribute [local simp] exceptBindOk exceptBindError exceptMapOk exceptMapError exceptThrow exceptPure

/-- A directly returned fold becomes a block: the statement head is fixed, only
    the pre and the ending vary. -/
theorem returnFold_direct_shape (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (e : SExpr) (out : SAnw)
    (hM : (matchFoldNode e).isSome = true)
    (h : returnFold source locals result (.ret (some e)) = .ok out) :
    ∃ pre ending, out = .block pre ending := by
  unfold returnFold at h
  cases hN : matchFoldNode e with
  | none => simp [hN] at hM
  | some _ =>
    simp [hN] at h
    cases result with
    | none => simp at h
    | some rt =>
      simp at h
      cases hD : hasDuplicateTags (tagFoldNodes e 0).1 with
      | true => simp [hD] at h
      | false =>
        simp [hD] at h
        cases hP : parseAndCheck source locals [] (tagFoldNodes e 0).1 (some rt) e with
        | error err => simp [hP] at h
        | ok pr =>
          obtain ⟨d, idx, tests⟩ := pr
          simp [hP] at h
          have gate : ∀ {c : Prop} [Decidable c] {a b o : Except String SAnw},
              (if c then a else b) = o → (c ∧ a = o) ∨ (¬c ∧ b = o) := by
            intro c _ a b o hi
            by_cases hc : c <;> simp_all
          rcases gate h with ⟨_, h⟩ | ⟨_, h⟩
          · simp at h
          · skip
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
    its immediate folds replaced after a fold-free pre, or the direct-return
    block with a fold-free pre. The pre runs before the statement, in
    source order, and the rewritten statement reads only fresh result
    variables. -/
theorem hoistAnw_shape (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) (s out : SAnw)
    (h : hoistAnw source locals result s = .ok out) :
    (∃ s' pre, out = afterPrefix s' pre ∧ hasRangeFoldAnwList pre = false) ∨
    (∃ pre ending, out = .block pre ending ∧
      hasRangeFoldAnwList pre = false) := by
  cases s with
  | ret e =>
    cases hE : e with
    | none =>
      simp only [hoistAnw, hE] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, [], rfl, nilFree⟩
    | some e =>
      simp only [hoistAnw, hE] at h
      cases hM : matchFoldNode e with
      | none =>
        simp only [hM] at h
        cases hH : hoistOne source locals e with
        | error err => simp [hH] at h
        | ok pr =>
          obtain ⟨e', pre⟩ := pr
          simp [hH] at h
          obtain ⟨rfl⟩ := h
          exact Or.inl ⟨_, _, rfl,
            (hoistOne_free source locals e _ pre hH).2⟩
      | some _ =>
        simp only [hM] at h
        cases hR : returnFold source locals result (.ret (some e)) with
        | error err => simp [hR] at h
        | ok o =>
          simp [hR] at h
          obtain ⟨rfl⟩ := h
          obtain ⟨pre, ending, rfl⟩ :=
            returnFold_direct_shape source locals result e _ (by simp [hM]) hR
          exact Or.inr ⟨pre, ending, rfl,
            returnFold_block_free source locals result e pre ending
              (by simp [hM]) hR⟩
  | bind b n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | bindQ b n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | bindElse n t e why body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | bindAxiomOpt n t e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | bindAxiomOptElse n t e why body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | await n t e p =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | swap n t e p =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | set a op b =>
    simp only [hoistAnw] at h
    cases hH : hoistPair source locals a b with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨a', b', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistPair_free source locals a b _ _ pre hH).2.2⟩
  | shift e a b =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | trim e n body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | trimReq e n =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | free e =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | call name args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' pre hH).2⟩
  | callQ name args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' pre hH).2⟩
  | callIndElse pointer args reason body =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals (pointer :: args) with
    | error err => simp [hH] at h
    | ok pair =>
      obtain ⟨operands, pre⟩ := pair
      simp [hH] at h
      cases hO : operands with
      | nil => simp [hO] at h
      | cons pointer' args' =>
        simp [hO] at h
        obtain ⟨rfl⟩ := h
        exact Or.inl ⟨_, _, rfl,
          (hoistList_free source locals (pointer :: args) operands pre hH).2⟩
  | callElse name args reason body =>

    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' pre hH).2⟩
  | genericCall name words args =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals args args' pre hH).2⟩
  | cond c body arms other =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals c with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨c', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals c _ pre hH).2⟩
  | elsif c body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals c with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨c', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals c _ pre hH).2⟩
  | cases g arms =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals g with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨g', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals g _ pre hH).2⟩
  | alloc b n t a e body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | reset n r =>
    simp only [hoistAnw] at h
    cases hM : hoistList source locals
        (r.toList.flatMap fun p => [p.1, p.2]) with
    | error err => simp [hM] at h
    | ok pr =>
      obtain ⟨es, pre⟩ := pr
      simp [hM] at h
      cases hE : es with
      | nil =>
        simp [hE] at h
        obtain ⟨rfl⟩ := h
        rw [hE] at hM
        exact Or.inl ⟨_, _, rfl,
          (hoistList_free source locals _ _ pre hM).2⟩
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
              (hoistList_free source locals _ _ pre hM).2⟩
  | grow n e body =>
    simp only [hoistAnw] at h
    cases hH : hoistOne source locals e with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨e', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistOne_free source locals e _ pre hH).2⟩
  | emit a b p =>
    simp only [hoistAnw] at h
    cases hH : hoistPair source locals a b with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨a', b', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistPair_free source locals a b _ _ pre hH).2.2⟩
  | bindLib b n t c =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals c.args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals c.args args' pre hH).2⟩
  | lcall c =>
    simp only [hoistAnw] at h
    cases hH : hoistList source locals c.args with
    | error err => simp [hH] at h
    | ok pr =>
      obtain ⟨args', pre⟩ := pr
      simp [hH] at h
      obtain ⟨rfl⟩ := h
      exact Or.inl ⟨_, _, rfl,
        (hoistList_free source locals c.args args' pre hH).2⟩
  | block ss ending =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | each n start kind subject mode raw inv body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | retry raw body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | loop raw body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | waive ns body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | watch n body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | leave n =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | next n =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | child body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | start ns =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | retires ns =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | other raw =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | arm c n body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | step a b =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | allocVon b n t a =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩
  | locks b e body =>
    simp only [hoistAnw] at h
    obtain ⟨rfl⟩ := h
    exact Or.inl ⟨_, [], rfl, nilFree⟩

end Gabbro.Grammatik.Parser.SourceFolds
