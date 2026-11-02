/-
  File:      Grammatik/Parser/Round/RundlaufTyp.lean
  Subject:   Layer L2b, part one: the pieces under the statements -- raw header texts, bare names that
             the printer re-lexes, and surface types (`druckTyp` read back by `parseTyp`).

  Raw texts. The reader keeps several headers as text (`retry`/`forever` headers, `traverse`
  `decreases`/`touches` words, `narrow` ranges, `publishes`/`awaits` payloads, `exchange` tails); the
  printer re-lexes the text (`rohToks`). A text read back is the rendered token list (L1's
  `renderText`), so the round-trip class of a raw field is: the field IS `renderText ts` for a
  lexically clean `ts` that holds none of the collector's stop tokens (`roh_*` below). Each
  collector (`traverseRest`, `schleifenKopf`, `nimmBisWort`, `nimmBisZeichen`) returns exactly that
  text (`renderText_cons`: one token, one space).

  Bare names. A call head and a `start` root ride as text (`rohToks f`); `rohToks_name`: a
  name-shaped `f` re-lexes to the one token the lexer reads for it (`nameTok f`).

  Types (`TypGut`): atoms (not one of the type-head words), paths of two or more segments,
  `range`/`wrapping` suffix chains over them, `ptr<space, right> T` with a single right,
  `[option] index into t`, arrays, `string max e`. `parse_druckTyp`: every `TypGut` type reads back
  before a type follow (`TypFolge`: no suffix word, no `::`, benign for expressions), with fuel
  `fbT t = 8 * #tokens + 30`. Excluded (recorded): `embeds` fields, raw brace groups and `fn(..)`
  types (`.raw`), `entry fn(..)` types, rights lists `rw+own`/`own@h`, suffix chains over a
  non-chain base (`[T; n] wrapping` reads `[T; n]` and leaves `wrapping`).

  Names print as `nameTok`, the token the lexer reads (`u32`, `bool`, `dma` are table words); the
  reader takes both. A path type's head is no type-head word (`typKopf`), as an atom.
-/
module

public import Grammatik.Parser.Round.RundlaufTok.Teil4
public import Grammatik.Parser.Round.Statements.RundlaufAnw3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Rendered text, token by token -/

theorem zeigeTok_spell (t : Token) (h : TokGut t) : zeigeTok t = String.ofList (spell t) := by
  cases t with
  | ident s => simp only [zeigeTok, spell, String.ofList_toList]
  | wort s => simp only [zeigeTok, spell, String.ofList_toList]
  | num n => rfl
  | float s => simp only [zeigeTok, spell, String.ofList_toList]
  | text s =>
    simp only [zeigeTok, spell]
    rw [show ('"' :: (s.toList ++ ['"'])) = ['"'] ++ s.toList ++ ['"'] by simp only [↓Char.isValue, List.cons_append, List.nil_append],
      String.ofList_append, String.ofList_append, String.ofList_toList]
  | zeichen s => simp only [zeigeTok, spell, String.ofList_toList]
  | doku _ => exact absurd h id
  | ende => exact absurd h id

theorem renderText_nil : renderText [] = "" := by rfl

theorem renderText_cons (t : Token) (ts : List Token) (h : TokGut t) :
    renderText (t :: ts) = zeigeTok t ++ " " ++ renderText ts := by
  unfold renderText
  rw [zeigeTok_spell t h]
  simp only [render]
  rw [show spell t ++ ' ' :: render ts = spell t ++ [' '] ++ render ts by simp only [↓Char.isValue, List.append_assoc, List.cons_append, List.nil_append],
    String.ofList_append, String.ofList_append]

/-- The re-lexed rendered text is the token list. -/
theorem filter_ende : ∀ (ts : List Token), (∀ t ∈ ts, TokGut t) →
    (ts ++ [Token.ende]).filter (fun t => match t with | .ende => false | _ => true) = ts := by
  intro ts h
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    cases t <;> simp_all [TokGut]

theorem rohToks_render (ts : List Token) (h : ∀ t ∈ ts, TokGut t) :
    rohToks (renderText ts) = ts := by
  unfold rohToks
  rw [lex_render ts h]
  exact filter_ende ts h

/-! ### The collectors return the rendered text -/

theorem traverseRest_roh : ∀ (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant") →
    traverseRest (ts ++ .zeichen "{" :: rest) = .ok (renderText ts, .zeichen "{" :: rest) := by
  intro ts rest
  induction ts with
  | nil => intro _; simp only [List.nil_append, traverseRest, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s "invariant" = false := by
        cases e : strEq s "invariant"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
      simp only [List.cons_append, traverseRest, hs, Bool.false_eq_true, ↓reduceIte, ih', zeigeTok]
    | zeichen s =>
      have hs : s ≠ "{" := fun e => h1 (by rw [e])
      simp only [List.cons_append, traverseRest, ih', zeigeTok]
    | _ => simp only [List.cons_append, traverseRest, ih']

theorem schleifenKopf_schritt (t : Token) (rest : List Token) (n : Nat)
    (h1 : t ≠ .zeichen "{") (h2 : ∀ s r, t = .wort s → rest ≠ .zeichen "{" :: r) :
    schleifenKopf (t :: rest) (n + 1) = match schleifenKopf rest n with
      | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
      | .error e => .error e := by
  rw [schleifenKopf.eq_5 t rest n (fun s r e1 e2 => h2 s r e1 e2) h1]
  rfl

theorem schleifenKopf_roh : ∀ (ts rest : List Token) (n : Nat),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "effects") → ts.length < n →
    schleifenKopf (ts ++ .zeichen "{" :: rest) n = .ok (renderText ts, .zeichen "{" :: rest) := by
  intro ts rest
  induction ts with
  | nil =>
    intro n _ hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_nil] at hn; omega⟩
    simp only [List.nil_append, schleifenKopf, renderText_nil]
  | cons t ts ih =>
    intro n h hn
    obtain ⟨hg, h1, h2⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (n - 1) (fun x hx => h x (by simp only [List.mem_cons, hx, or_true])) (by simp only [List.length_cons] at hn; omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    simp only [Nat.add_sub_cancel] at ih'
    rw [renderText_cons t ts hg]
    cases ts with
    | nil =>
      cases t with
      | wort s =>
        have hs : strEq s "effects" = false := by
          cases e : strEq s "effects"
          · rfl
          · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
        simp only [List.cons_append, List.nil_append, schleifenKopf, hs, Bool.false_eq_true, ↓reduceIte, zeigeTok,
  renderText_nil, String.append_empty]
      | _ =>
        simp only [List.nil_append, List.cons_append] at ih' ⊢
        rw [schleifenKopf_schritt _ _ _ h1 (by intro s r e; cases e), ih']
    | cons t2 ts2 =>
      have h3 : t2 ≠ .zeichen "{" := (h t2 (by simp only [List.mem_cons, true_or, or_true])).2.1
      simp only [List.cons_append] at ih' ⊢
      rw [schleifenKopf_schritt _ _ _ h1 (by intro s r _ e; injection e with e1; exact h3 e1), ih']

theorem nimmBisWort_roh : ∀ (w : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .wort w) →
    nimmBisWort w (ts ++ .wort w :: rest) 0 = .ok (renderText ts, .wort w :: rest) := by
  intro w ts rest
  induction ts with
  | nil => intro _; simp only [List.nil_append, nimmBisWort, strEq_self, BEq.rfl, Bool.and_self, ↓reduceIte, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    rw [renderText_cons t ts hg]
    cases t with
    | wort s =>
      have hs : strEq s w = false := by
        cases e : strEq s w
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h3
      simp only [List.cons_append, nimmBisWort, hs, BEq.rfl, Bool.and_true, Bool.false_eq_true, ↓reduceIte, ih',
  zeigeTok]
    | zeichen s =>
      have hs1 : s ≠ "{" := fun e => h1 (by rw [e])
      have hs2 : s ≠ "}" := fun e => h2 (by rw [e])
      simp only [List.cons_append, nimmBisWort, ih', zeigeTok]
    | _ => simp only [List.cons_append, nimmBisWort, ih']

theorem nimmBisZeichen_roh : ∀ (z : String) (ts rest : List Token),
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .zeichen "}" ∧ t ≠ .zeichen z) →
    nimmBisZeichen z (ts ++ .zeichen z :: rest) 0 = .ok (renderText ts, .zeichen z :: rest) := by
  intro z ts rest
  induction ts with
  | nil => intro _; simp only [List.nil_append, nimmBisZeichen, BEq.rfl, strEq_self, Bool.and_self, ↓reduceIte, renderText_nil]
  | cons t ts ih =>
    intro h
    obtain ⟨hg, h1, h2, h3⟩ := h t (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
    rw [renderText_cons t ts hg]
    cases t with
    | zeichen s =>
      have hs : strEq s z = false := by
        cases e : strEq s z
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h3
      have hs1 : strEq s "{" = false := by
        cases e : strEq s "{"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h1
      have hs2 : strEq s "}" = false := by
        cases e : strEq s "}"
        · rfl
        · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
      simp only [List.cons_append, nimmBisZeichen, BEq.rfl, hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hs1,
  hs2, ih', zeigeTok]
    | _ => simp only [List.cons_append, nimmBisZeichen, ih']


end Gabbro.Grammatik.Parser
