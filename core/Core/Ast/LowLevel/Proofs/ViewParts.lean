module

public import Core.Ast.LowLevel.Obligations
public import Core.Ast.Program.WrittenTypes

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter

private lemma viewProductionUnique {tokens : List Token} {a b : Tree .view}
    (ha : a.production tokens) (hb : b.production tokens) : a = b := by
  cases a with
  | view ra ta =>
      cases b with
      | view rb tb =>
          simp only [Tree.production] at ha hb
          rcases ha with ⟨inputa, rfl, readsA⟩
          rcases hb with ⟨inputb, eqB, readsB⟩
          simp at eqB
          rcases eqB with ⟨hval, hinput⟩
          have hra : ra = rb := Subtype.ext hval
          have htype : ta = tb := (TypeReads.deterministic readsA (hinput.symm ▸ readsB)).1
          exact congrArg₂ Tree.view hra htype

lemma viewParseOfPrint (tree : Tree .view)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) :
    Parse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 (tree.printPieces)
  refine ⟨True.intro, pieces, lexical, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (t : Tree .view) => t.production tokens))
        (ts.map Symbol.terminal) ts := by
    intro ts
    induction ts with
    | nil => exact .nil
    | cons t ts ih => exact .terminal ih
  exact .production ⟨semanticTokens pieces, rfl, by
    have hp : tree.production (canonicalTokens pieces) := by
      rw [align]
      exact prints
    simpa [canonicalTokens] using hp⟩ (symbols (semanticTokens pieces))

lemma viewParseAussage : ParseAussage .view := by
  intro tree text pieces lex prod
  refine ⟨True.intro, pieces, lex, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (t : Tree .view) => t.production tokens))
        (ts.map Symbol.terminal) ts := by
    intro ts
    induction ts with
    | nil => exact .nil
    | cons t ts ih => exact .terminal ih
  exact .production ⟨semanticTokens pieces, rfl, by
    have hp : tree.production (canonicalTokens pieces) := prod
    simpa [canonicalTokens] using hp⟩ (symbols (semanticTokens pieces))

lemma viewInversionAussage : InversionAussage .view := by
  intro tree text parsed
  rcases parsed with ⟨root, pieces, lex, derives⟩
  refine ⟨pieces, lex, ?_⟩
  cases derives with
  | production production children =>
      obtain ⟨expected, rfl, reads⟩ := production
      simpa [canonicalTokens, children.terminalTokens] using reads

lemma viewEindeutigAussage : EindeutigAussage .view := by
  intro a b text pa pb
  rcases pa with ⟨root, pieces, lex, derivesA⟩
  rcases pb with ⟨root', pieces', lex', derivesB⟩
  have same : pieces = pieces' := LexedAt.deterministic lex lex'
  subst pieces'
  have readsA : a.production (canonicalTokens pieces) := by
    cases derivesA with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  have readsB : b.production (canonicalTokens pieces) := by
    cases derivesB with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  exact viewProductionUnique readsA readsB

lemma viewPrints (region : Identifier) (type : WrittenType) (valid : type.valid []) :
    (Tree.view region type).production
      ((Tree.view region type).printPieces.map PrintedToken.value) := by
  refine ⟨type.printPieces.map PrintedToken.value, ?_, ?_⟩
  · simpa only [Tree.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, keyword, word, Identifier.print,
      PrintedToken.unquoted, printPunctuation, printDot, dot, String.reduceToList]
  · simpa only [List.append_nil] using
      (WrittenType.printReads (tree := type) (scope := []) (rest := []) valid
        (by intro more h; cases h))

lemma viewDruckAussage : DruckAussage .view := by
  intro tree printable
  cases tree with
  | view region type =>
      change type.valid [] at printable
      exact ⟨viewPrints region type printable, viewParseOfPrint _ (viewPrints region type printable)⟩

lemma viewElaboriertAussage : ElaboriertAussage .view := by
  intro k scope tree E
  constructor <;> intro h <;> exact h

lemma viewRealisiertAussage : RealisiertAussage .view := by
  intro k scope tree op start _ heval
  let s := (I.start (unit op) start).2
  have hs : s.status entryContext = .laeuft := by
    simp only [s, I.start, unit, bootData, entryContext, Zustand.start, ↓reduceIte]
  have hp : (s.lokal entryContext).pc = 0 := by
    simp only [s, I.start, unit, bootData, entryContext, Zustand.start, ↓reduceIte]
  have heval' : (op.evaluate s entryContext).isSome := by
    simpa [s] using heval
  have hhead : head op s entryContext = some op := by
    unfold head
    rw [hs]
    have hcond : entryContext = entryContext ∧ (s.lokal entryContext).pc = 0 ∧
        (op.evaluate s entryContext).isSome := ⟨rfl, hp, heval'⟩
    rw [if_pos hcond]
  simpa only [unit, system, s] using hhead

lemma viewAnnahmeAussage : AnnahmeAussage .view := by
  intro k scope tree op _
  constructor
  · intro c s u w P hideal
    simp only [unit, system, Instruction.rule, Instruction.ideal] at hideal
    rcases hideal with ⟨transfer, heval, hP, hu⟩
    have hP' : P = plan := by simpa using hP
    subst P
    have hfuss : plan.fuss = [] := rfl
    have hlesen : plan.lesen = [] := rfl
    rw [Annahme.Befugt, hfuss, hlesen]
    constructor
    · intro x hx
      cases hx
    · intro l hl
      cases hl
  · intro s c w plans next hideal
    rcases hideal with ⟨transfer, heval, hplans, hnext⟩
    exact hplans

lemma viewIdealAussage : IdealAussage .view := by
  intro k scope tree op hElab
  constructor
  · intro c s w es es' s1 s2 h1 h2
    change ∃ t, op.evaluate s c = some t ∧ es = [plan] ∧ s1 = t.apply c s at h1
    change ∃ t, op.evaluate s c = some t ∧ es' = [plan] ∧ s2 = t.apply c s at h2
    rcases h1 with ⟨t1, he1, hes1, hs1⟩
    rcases h2 with ⟨t2, he2, hes2, hs2⟩
    constructor
    · rw [hes1, hes2]
    · have ht : t1 = t2 := by
        rw [he1] at he2
        cases he2
        rfl
      rw [hs1, hs2, ht]
  · intro c s w plans next
    rfl

lemma viewEinheitAussage : EinheitAussage .view := by
  intro k scope tree op hElab
  constructor
  · rfl
  constructor
  · rfl
  · intro other
    exact ⟨fun s s1 s2 h _ => False.elim h,
           fun s s1 s2 _ h => False.elim h⟩

lemma viewImplAussage : ImplAussage .view := by
  intro k scope tree op hElab c s w plans next
  change (match op.evaluate s c with
      | none => False
      | some t => plans = [plan] ∧ next = t.apply c s) ↔
    (∃ t, op.evaluate s c = some t ∧ plans = [plan] ∧ next = t.apply c s)
  cases hEval : op.evaluate s c with
  | none =>
      simp only [hEval]
      constructor
      · intro h
        exact False.elim h
      · intro h
        rcases h with ⟨t, ht, hp, hn⟩
        cases ht
  | some t =>
      simp only [hEval]
      constructor
      · intro h
        exact ⟨t, rfl, h.1, h.2⟩
      · intro h
        rcases h with ⟨u, hu, hp, hn⟩
        cases hu
        exact ⟨hp, hn⟩

lemma viewFortschrittAussage : FortschrittAussage .view := by
  intro k scope tree op hElab s c hhead
  cases hEval : op.evaluate s c with
  | none =>
      exfalso
      change head op s c = some op at hhead
      cases hs : s.status c with
      | laeuft =>
          simp only [head, hs] at hhead
          split at hhead
          next hcond =>
            have hisSome : (op.evaluate s c).isSome := hcond.2.2
            rw [hEval] at hisSome
            cases hisSome
          next _ => cases hhead
      | ruht =>
          simp only [head, hs] at hhead
          cases hhead
      | beendet e =>
          simp only [head, hs] at hhead
          cases hhead
  | some transfer =>
      left
      refine ⟨(), [plan], transfer.apply c s, ?_⟩
      change ∃ t, op.evaluate s c = some t ∧ [plan] = [plan] ∧
        transfer.apply c s = t.apply c s
      exact ⟨transfer, hEval, rfl, rfl⟩

end Gabbro.Core.Ast.LowLevel
