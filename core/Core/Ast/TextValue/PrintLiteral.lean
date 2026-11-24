module

public import Core.Text.Printing

@[expose] public section

namespace Gabbro.Core.Text

def escapeStringChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else [c]

def escapeString (text : List Char) : List Char := text.flatMap escapeStringChar

theorem escapeString_reads (text : List Char) : StringContent (escapeString text) text := by
  induction text with
  | nil => exact .nil
  | cons c rest ih =>
    change StringContent (escapeStringChar c ++ escapeString rest) (c :: rest)
    unfold escapeStringChar
    split
    · rename_i eq
      subst c
      exact .escaped .quote ih
    · rename_i notQuote
      split
      · rename_i eq
        subst c
        exact .escaped .backslash ih
      · rename_i notBackslash
        split
        · rename_i eq
          subst c
          exact .escaped .newline ih
        · rename_i notNewline
          exact .plain notQuote notBackslash notNewline ih

/-- When scanning from the opening quote, the first unescaped closing quote
    fixes the extent of the token independently of the following source. -/
theorem StringContent.closed_length {left right a b : List Char}
    (lhs : StringContent left a) (rhs : StringContent right b)
    (same : left ++ '"' :: tail = right ++ '"' :: other) : left.length = right.length := by
  induction lhs generalizing right b other with
  | nil =>
    cases rhs with
    | nil => rfl
    | plain different _ _ _ => exact (different (List.cons.inj same).1.symm).elim
    | escaped _ _ => cases (List.cons.inj same).1
  | plain noQuote noSlash noNewline body ih =>
    cases rhs with
    | nil => simp_all only [List.nil_append, List.cons_append, List.cons.injEq, false_and]
    | plain _ _ _ rhs =>
      exact congrArg (· + 1) (ih rhs (List.cons.inj same).2)
    | escaped _ _ => simp_all only [List.cons_append, List.cons.injEq, false_and]
  | escaped code body ih =>
    cases rhs with
    | nil => simp_all only [List.nil_append, List.cons_append, List.cons.injEq, Char.reduceEq, false_and]
    | plain _ _ _ _ => simp_all only [List.cons_append, List.cons.injEq, ne_eq, eq_comm, false_and]
    | escaped _ rhs =>
      exact congrArg (fun n => n + 1 + 1) (ih rhs (List.cons.inj (List.cons.inj same).2).2)

def PrintedToken.textLiteral (decoded : List Char) : PrintedToken where
  value := .string decoded
  spelling := ['"'] ++ escapeString decoded ++ ['"']
  reads := .string (escapeString_reads decoded)
  headNotSpace := by
    intro c head
    obtain rfl := Option.some.inj head
    simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true]
  separated := by
    intro rest
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro other suffix kind same read
      have tag := read.decodes
      have start : lexicalTag other = .string := by
        cases other with
        | nil => exact (read.nonempty rfl).elim
        | cons first more =>
          have isQuote : '"' = first := (List.cons.inj same).1
          subst first
          exact lexicalTag_string
      rw [start] at tag
      obtain ⟨raw, value, spelling, content, _⟩ := tag
      subst other
      have closed : escapeString decoded ++ '"' :: ' ' :: rest = raw ++ '"' :: suffix := by
        have tails := (List.cons.inj same).2
        change (escapeString decoded ++ ['"']) ++ (' ' :: rest) = (raw ++ ['"']) ++ suffix at tails
        simpa only [List.append_assoc, List.singleton_append] using tails
      have length := (escapeString_reads decoded).closed_length content closed
      simp only [List.length_append, List.length_cons, List.length_nil, length]
      exact Nat.le_refl _
    · intro _ bad
      cases bad
    · intro _ _ _ bad
      cases bad
    · intro _ _ bad
      cases bad

end Gabbro.Core.Text
