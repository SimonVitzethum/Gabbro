module

public import Grammatik.Parser.Item.ElementTief.Sequence
import Lean.Elab.Tactic.Conv

@[expose] public section

namespace Gabbro.Grammatik.Parser

private theorem punctuation_read {mark : String} {tokens rest : List Token}
    (read : fordereZeichen mark tokens = .ok rest) : tokens = .zeichen mark :: rest := by
  cases tokens with
  | nil => cases read
  | cons token tail =>
    cases token <;> simp only [fordereZeichen, reduceCtorEq] at read
    split at read
    · rename_i exactMark
      rw [(strEq_eq _ _).mp exactMark, Except.ok.inj read]
    · cases read

private theorem moduleBody_read {fuel : Nat} {header rest : List Token} {node : SItemTief}
    (make : List SItemTief → SItemTief)
    (parsed : (do
      let inside ← fordereZeichen "{" header
      let (nodes, ending) ← parseItemsTief fuel inside
      let rest ← fordereZeichen "}" ending
      pure (make nodes, rest)) = .ok (node, rest)) :
    ∃ inside nodes, header = .zeichen "{" :: inside ∧
      ItemSequence fuel inside nodes (.zeichen "}" :: rest) ∧ node = make nodes := by
  cases opening : fordereZeichen "{" header with
  | error e => simp only [opening, bind, Except.bind, reduceCtorEq] at parsed
  | ok inside =>
    cases body : parseItemsTief fuel inside with
    | error e => simp only [opening, body, bind, Except.bind, reduceCtorEq] at parsed
    | ok result =>
      obtain ⟨nodes, ending⟩ := result
      cases closing : fordereZeichen "}" ending with
      | error e => simp only [opening, body, closing, bind, Except.bind, reduceCtorEq] at parsed
      | ok remaining =>
        simp only [opening, body, closing, bind, Except.bind, pure, Except.pure] at parsed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj parsed)
        exact ⟨inside, nodes, punctuation_read opening,
          punctuation_read closing ▸ parseItemsTief_iff.mp body, rfl⟩

/-- Every parsed ordinary or generic module contains exactly the ordered
    children read between its braces. The closing brace is consumed by the
    module and the outer reader receives exactly the following tokens. -/
theorem parseModulTief_body {fuel : Nat} {tokens rest : List Token} {node : SItemTief}
    (parsed : parseModulTief (fuel + 1) tokens = .ok (node, rest)) :
    ∃ afterModule path afterPath,
      nimmWort "module" tokens = .ok afterModule ∧ nimmPfad afterModule = .ok (path, afterPath) ∧
      ∃ header inside nodes,
        header = .zeichen "{" :: inside ∧ ItemSequence fuel inside nodes (.zeichen "}" :: rest) ∧
        ((header = afterPath ∧ node = .modT ("::".intercalate path) nodes) ∨
          ∃ params, parseGenericParams fuel afterPath = .ok (params, header) ∧
            node = .moduleTemplateT ("::".intercalate path) params nodes) := by
  conv at parsed => lhs; unfold parseModulTief
  cases keyword : nimmWort "module" tokens with
  | error error => simp only [keyword, reduceCtorEq] at parsed
  | ok afterModule =>
    cases name : nimmPfad afterModule with
    | error error => simp only [keyword, name, reduceCtorEq] at parsed
    | ok nameResult =>
      obtain ⟨path, afterPath⟩ := nameResult
      simp only [keyword, name] at parsed
      refine ⟨afterModule, path, afterPath, keyword, name, ?_⟩
      split at parsed
      · rename_i tail
        cases parameters : parseGenericParams fuel (.zeichen "[" :: tail) with
        | error error => simp only [parameters, bind, Except.bind, reduceCtorEq] at parsed
        | ok generic =>
          obtain ⟨params, header⟩ := generic
          simp only [parameters, bind, Except.bind] at parsed
          obtain ⟨inside, nodes, opening, body, nodeEq⟩ :=
            moduleBody_read (fun nodes => .moduleTemplateT ("::".intercalate path) params nodes) (by
              simpa only [bind, Except.bind, pure, Except.pure] using parsed)
          exact ⟨header, inside, nodes, opening, body, .inr ⟨params, parameters, nodeEq⟩⟩
      · obtain ⟨inside, nodes, opening, body, nodeEq⟩ :=
          moduleBody_read (fun nodes => .modT ("::".intercalate path) nodes) (by
            simpa only [bind, Except.bind, pure, Except.pure] using parsed)
        exact ⟨afterPath, inside, nodes, opening, body, .inl ⟨rfl, nodeEq⟩⟩

end Gabbro.Grammatik.Parser
