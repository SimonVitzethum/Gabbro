module
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil4

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil3

import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- What the induction carries per position. -/
def Bein : Rolle → SAnw → Prop
  | .anw, s => AnwBein s ∧ AnwKopf s
  | .block, b => BlockBein b ∧ BlockKopf b
  | .elsif, x => ElsifBein x
  | .arm, x => ArmBein x

theorem anwKopf_wort (s : SAnw) (w : String) (hw : w ≠ "else") (h : ∃ ts, druckAnw s = .wort w :: ts) :
    AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  exact ⟨_, ts, h, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by intro e; injection e with e; exact hw e, by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

theorem nameTok_ne_else {a : String} (h : a ≠ "else") : nameTok a ≠ .wort "else" := by
  unfold nameTok; split
  · intro e; injection e with e; exact h e
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem anwKopf_ident (s : SAnw) (a : String) (ha : a ≠ "else")
    (h : ∃ ts, druckAnw s = nameTok a :: ts) : AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  exact ⟨_, ts, h, by simp only [ne_eq, nameTok_ne_zeichen, not_false_eq_true], nameTok_ne_else ha, by simp only [ne_eq, nameTok_ne_ende, not_false_eq_true]⟩

theorem anwKopf_platz (s : SAnw) (z : SExpr) (hz : gutPlatz z = true)
    (h : ∃ ts, druckAnw s = druckToks z ++ ts) : AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  obtain ⟨a, us, hu, ak⟩ := platz_kopf z hz
  exact anwKopf_ident s a (by intro e; subst e; revert ak; decide) ⟨us ++ ts, by rw [h, hu]; simp only [List.cons_append]⟩

theorem ende_bein (e : Option SEnde) (he : EndeOk e) : ∀ s ∈ endeAnw e, AnwBein s ∧ AnwKopf s := by
  intro s hs
  cases e with
  | none => simp only [endeAnw, List.not_mem_nil] at hs
  | some e' =>
    cases e' with
    | ret x =>
      cases x with
      | none =>
        simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
        exact ⟨anw_ret_leer, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
      | some y =>
        simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
        exact ⟨anw_ret y he, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
    | leave l =>
      simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact ⟨anw_leave l, anwKopf_wort _ "leave" (by decide) ⟨_, rfl⟩⟩
    | next l =>
      simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact ⟨anw_next l, anwKopf_wort _ "next" (by decide) ⟨_, rfl⟩⟩

/-- **The induction**: every printable tree has the legs of its position. -/
theorem bein_gut : ∀ (r : Rolle) (s : SAnw), AnwGut r s → Bein r s := by
  intro r s h
  induction h with
  | bind m x ty e hx hty he =>
    exact ⟨anw_bind m x hx ty e hty he, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | bindElse x ty e f b hx hty he _ ihb =>
    exact ⟨anw_bindElse x hx ty e f b hty he ihb.1, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | bindLib m x ty c hx hty hc =>
    exact ⟨anw_bindLib m x hx ty c hty hc, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | set z o w hz ho hw =>
    exact ⟨anw_set z o w hz ho hw, anwKopf_platz _ z hz ⟨_, by simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq] <;> rfl⟩⟩
  | shift z a b hz =>
    exact ⟨anw_shift z a b hz, anwKopf_wort _ "transition" (by decide) ⟨_, rfl⟩⟩
  | call f xs hf hw hxs =>
    exact ⟨anw_call f xs hf hw hxs, anwKopf_ident _ f (by intro e; subst e; revert hw; decide)
      ⟨_, by simp only [druckAnw, rohToks_nameGut f hf, List.cons_append, List.nil_append, List.cons.injEq, true_and] <;> rfl⟩⟩
  | lcall c hc =>
    exact ⟨anw_lcall c hc, ⟨.zeichen "@", _, rfl, by simp only [ne_eq, Token.zeichen.injEq, String.reduceEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩⟩
  | cond c t eis s hc _ _ _ iht iheis ihs =>
    exact ⟨anw_cond c t eis s hc iht.1 iht.2 iheis ihs, anwKopf_wort _ "if" (by decide)
      (by cases s <;> exact ⟨_, rfl⟩)⟩
  | elsif c b hc _ ihb => exact ⟨c, b, rfl, hc, ihb.1, ihb.2⟩
  | cases g arms hg _ iha =>
    exact ⟨anw_cases g arms hg iha, anwKopf_wort _ "match" (by decide) ⟨_, rfl⟩⟩
  | arm v bi b _ ihb => exact ⟨v, bi, b, rfl, ihb.1, ihb.2⟩
  | each b o k s m r i body ho hs hr hi _ ihb =>
    exact ⟨anw_each b o k s m r i body ho hs hr hi ihb.1 ihb.2,
      anwKopf_wort _ "traverse" (by decide) ⟨_, rfl⟩⟩
  | retry h b hh _ ihb =>
    exact ⟨by simpa using anw_schleife 1 h b (Or.inl rfl) hh ihb.1 ihb.2,
      anwKopf_wort _ "retry" (by decide) ⟨_, rfl⟩⟩
  | loop h b hh _ ihb =>
    exact ⟨by simpa using anw_schleife 2 h b (Or.inr rfl) hh ihb.1 ihb.2,
      anwKopf_wort _ "forever" (by decide) ⟨_, rfl⟩⟩
  | waive ns b hne _ ihb =>
    exact ⟨anw_waive ns b hne ihb.1 ihb.2, anwKopf_wort _ "breaking" (by decide) ⟨_, rfl⟩⟩
  | trim o t b ho ht _ ihb =>
    exact ⟨anw_trim o t b ho ht ihb.1 ihb.2, anwKopf_wort _ "narrow" (by decide) ⟨_, rfl⟩⟩
  | locks g o b ho hsh _ ihb =>
    exact ⟨anw_locks g o b ho hsh ihb.1 ihb.2, anwKopf_wort _ "locks" (by decide) ⟨_, rfl⟩⟩
  | watch d b _ ihb =>
    exact ⟨anw_watch d b ihb.1 ihb.2, anwKopf_wort _ "observes" (by decide) ⟨_, rfl⟩⟩
  | leave l => exact ⟨anw_leave l, anwKopf_wort _ "leave" (by decide) ⟨_, rfl⟩⟩
  | next l => exact ⟨anw_next l, anwKopf_wort _ "next" (by decide) ⟨_, rfl⟩⟩
  | emit z w p hz hw hp =>
    exact ⟨anw_emit z w p hz hw hp, anwKopf_platz _ z hz ⟨_, by simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq] <;> rfl⟩⟩
  | await n ty q p hx hty hq hp =>
    exact ⟨anw_await n hx ty q p hty hq hp, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | swap n ty o k hx hty ho hk =>
    exact ⟨anw_swap n hx ty o k hty ho hk, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | step a b => exact ⟨anw_step a b, anwKopf_wort _ "advances" (by decide) ⟨_, rfl⟩⟩
  | retLeer => exact ⟨anw_ret_leer, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
  | ret e he => exact ⟨anw_ret e he, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
  | alloc m n ty t w s hx hty hw _ ihs =>
    exact ⟨anw_alloc m n hx ty t w s hty hw (fun b hb => (ihs b hb).1),
      anwKopf_wort _ "let" (by decide) (by cases s <;> exact ⟨_, rfl⟩)⟩
  | allocVon m n ty t hx hty =>
    exact ⟨anw_allocVon m n hx ty t hty, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | reset a rg hrg => exact ⟨anw_reset a rg hrg, anwKopf_wort _ "reset" (by decide) ⟨_, rfl⟩⟩
  | grow a e b he _ ihb =>
    exact ⟨anw_grow a e b he ihb.1 ihb.2, anwKopf_wort _ "grow" (by decide) ⟨_, rfl⟩⟩
  | free z hz => exact ⟨anw_free z hz, anwKopf_wort _ "free" (by decide) ⟨_, rfl⟩⟩
  | child b _ ihb =>
    exact ⟨anw_child b ihb.1 ihb.2, anwKopf_wort _ "child" (by decide) ⟨_, rfl⟩⟩
  | start ps hne hp => exact ⟨anw_start ps hne hp, anwKopf_ident _ "start" (by decide) ⟨_, rfl⟩⟩
  | block ss e _ he hw ihss =>
    refine ⟨block_rund ss e ?_ hw, blockKopf_block ss e⟩
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact ihss s h
    · exact ende_bein e he s h

/-- **L2b: every printable statement reads back** before an `else`-free follow. -/
theorem rundlauf_anw (s : SAnw) (h : AnwGut .anw s) (rest : List Token) (F : Nat) (hK : KE rest)
    (hF : fbA s ≤ F) : parseStmt F (druckAnw s ++ rest) = .ok (s, rest) :=
  (bein_gut .anw s h).1 rest F hK hF

/-- **L2b: every printable block reads back**, whatever follows. -/
theorem rundlauf_block (b : SAnw) (h : AnwGut .block b) (rest : List Token) (F : Nat)
    (hF : fbA b ≤ F) : parseBlock F (druckAnw b ++ rest) = .ok (b, rest) :=
  (bein_gut .block b h).1 rest F hF

/-- The whole block reader (`parseTopBlock`, fuel `8 * length + 32`). -/
theorem parseTopBlock_druck (b : SAnw) (h : AnwGut .block b) :
    parseTopBlock (druckAnw b ++ [.ende]) = .ok b := by
  unfold parseTopBlock
  rw [rundlauf_block b h [.ende] _ (by simp only [fbA, List.length_append, List.length_singleton]; omega)]

/-- **Composition with L1**: a printable block whose print is lexically clean reads back from its
    rendered source text. -/
theorem rundlauf_block_text (b : SAnw) (h : AnwGut .block b) (ht : ∀ t ∈ druckAnw b, TokGut t) :
    (match lex (renderText (druckAnw b)) with
      | .ok toks => parseTopBlock toks
      | .error _ => .error "lex") = .ok b := by
  rw [lex_render _ ht]
  exact parseTopBlock_druck b h


/-! ### Witnesses -/

/-- A block with a typed `let`, an indexed compound assignment, an `if` with an `else if` branch and
    an `else` block (holding a `child`), a `retry` with a raw header, a shared `locks`, a call, and a
    valued `return` as the ender. The binder `x`, the variable `x` and the call head `max` are table
    words: they print as `wort` and read back as names. -/
def zeugeBlock : SAnw :=
  .block [
    .bind false "x" (some (.atom "u32")) (.bin "+" (.variable "a") (.lit 1)),
    .set (.index (.variable "t") (.variable "x")) "+=" (.lit 2),
    .cond (.bin "<" (.variable "x") (.lit 10)) (.block [.call "max" [.variable "x"]] none)
      [.elsif (.bin "==" (.variable "x") (.lit 10)) (.block [] (some (.leave "l")))]
      (some (.block [.child (.block [] none)] none)),
    .retry (renderText [.wort "until", .ident "fertig"]) (.block [] none),
    .locks true (.variable "L") (.block [] none)]
    (some (.ret (some (.variable "x"))))

theorem zeugeBlock_gut : AnwGut .block zeugeBlock := by
  have leer : AnwGut .block (.block [] none) :=
    .block [] none (by simp only [List.not_mem_nil, false_implies, implies_true]) trivial (by intro _ s h; simp only [List.getLast?_nil, reduceCtorEq] at h)
  apply AnwGut.block _ _ _ (by show gut (.variable "x") = true; decide) (by intro h; cases h)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact .bind _ _ _ _ (by decide) (.kette (.atom "u32") [] (.atom _ (by decide)) (by simp only [TsGut, List.not_mem_nil, false_implies, implies_true]))
      (by decide)
  · exact .set _ _ _ (by decide) (by decide) (by decide)
  · refine .cond _ _ _ _ (by decide) ?_ ?_ ?_
    · refine .block _ _ ?_ trivial (by intro _ s h; simp only [List.getLast?_singleton, Option.some.injEq] at h; subst h; rfl)
      intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact .call _ _ (show nameForm _ = true by decide) (by decide) (by decide)
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
      exact .elsif _ _ (by decide) (.block [] _ (by simp only [List.not_mem_nil, false_implies, implies_true]) trivial (by intro h; cases h))
    · intro b hb; cases hb
      refine .block _ _ ?_ trivial (by intro _ s h; simp only [List.getLast?_singleton, Option.some.injEq] at h; subst h; rfl)
      intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact .child _ leer
  · refine .retry _ _ ⟨[.wort "until", .ident "fertig"], rfl, ?_, ?_⟩ leer
    · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨⟨by decide, by decide⟩, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, Token.wort.injEq, String.reduceEq, not_false_eq_true]⟩
      · exact ⟨⟨by decide, by decide⟩, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
    · intro R; rfl
  · exact .locks _ _ _ (by decide) (by intro h; cases h) leer

/-- The witness reads back through the whole block reader. -/
theorem zeugeBlock_rund : parseTopBlock (druckAnw zeugeBlock ++ [.ende]) = .ok zeugeBlock :=
  parseTopBlock_druck zeugeBlock zeugeBlock_gut

/-- The witness from its rendered source text (lexer, then the block reader). -/
theorem zeugeBlock_text :
    (match lex (renderText (druckAnw zeugeBlock)) with
      | .ok toks => parseTopBlock toks
      | .error _ => .error "lex") = .ok zeugeBlock :=
  rundlauf_block_text zeugeBlock zeugeBlock_gut (tokGut_of_all _ (by decide))

/-- **Planted defect** (the `EndeGut` hypothesis is needed): a block without an ender whose last
    statement is a `return` reads back with that statement as its ender. -/
theorem endeGut_noetig : ¬ EndeGut [.ret none] none := by
  intro h; exact absurd (h rfl (.ret none) rfl) (by decide)


end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.rundlauf_anw
#print axioms Gabbro.Grammatik.Parser.rundlauf_block
#print axioms Gabbro.Grammatik.Parser.parseTopBlock_druck
#print axioms Gabbro.Grammatik.Parser.rundlauf_block_text
#print axioms Gabbro.Grammatik.Parser.zeugeBlock_rund
#print axioms Gabbro.Grammatik.Parser.zeugeBlock_text
