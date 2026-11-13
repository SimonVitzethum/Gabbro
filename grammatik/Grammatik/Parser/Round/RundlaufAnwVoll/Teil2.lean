module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil1

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

/-- A place head never opens `start {`. -/
theorem platz_nicht_start (z : SExpr) (hz : gutPlatz z = true) (X : List Token)
    (hX : ∀ r', X ≠ .zeichen "{" :: r') (hXo : istOrtsFort X = true) :
    ∃ a r, druckToks z ++ X = nameTok a :: r ∧ (∀ r', r ≠ .zeichen "{" :: r') ∧
      istOrtsFort r = true ∧ a ≠ "transition" := by
  obtain ⟨a, suff, rfl, hka, _, _⟩ := zerlege (groesse z) z (Nat.le_refl _) hz
  rw [druckToks_applySuff]
  refine ⟨a, suffToks suff ++ X, by simp only [druckToks, List.cons_append, List.nil_append], ?_, ?_, ?_⟩
  · intro r' e
    cases suff with
    | nil => exact hX r' (by simpa [suffToks] using e)
    | cons s _ => cases s <;> simp only [suffToks, List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.append_assoc, List.nil_append] at e
  · cases suff with
    | nil => simpa [suffToks] using hXo
    | cons s _ => cases s <;> rfl
  · intro e; subst e; revert hka; decide

/-- An assignment operator cannot open an ordinary or generic call. -/
theorem zuweis_keineRufOeffnung (o : String) (ho : istZuweis o = true)
    (R : List Token) :
    (∀ tail, Token.zeichen o :: R ≠ .zeichen "(" :: tail) ∧
    (∀ tail, Token.zeichen o :: R ≠ .zeichen "::" :: .zeichen "[" :: tail) := by
  have hnparen : o ≠ "(" := by
    intro h
    subst h
    simp only [istZuweis, strEq_paren_gleich, strEq_paren_plusgleich,
      strEq_paren_minusgleich, strEq_paren_undgleich, strEq_paren_odergleich,
      Bool.false_or, Bool.false_eq_true] at ho
  have hngeneric : o ≠ "::" := by
    intro h
    subst h
    simp only [istZuweis, strEq_doppelpunkt_gleich, strEq_doppelpunkt_plusgleich,
      strEq_doppelpunkt_minusgleich, strEq_doppelpunkt_undgleich,
      strEq_doppelpunkt_odergleich, Bool.false_or, Bool.false_eq_true] at ho
  constructor
  · intro tail h
    exact hnparen (Token.zeichen.inj (List.cons.inj h).1)
  · intro tail h
    exact hngeneric (Token.zeichen.inj (List.cons.inj h).1)

theorem anw_set (z : SExpr) (o : String) (w : SExpr) (hz : gutPlatz z = true)
    (ho : istZuweis o = true) (hw : gut w = true) : AnwBein (.set z o w) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton] at hF
  have hd : druckAnw (.set z o w) ++ rest = druckToks z ++ .zeichen o :: (druckToks w ++ .zeichen ";" :: rest) := by
    simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨a, r, hzr, hr, hro, hrt⟩ := platz_nicht_start z hz
    (.zeichen o :: (druckToks w ++ .zeichen ";" :: rest))
    (by intro r' e; injection e with e1; injection e1 with e1; subst e1
        rcases zuweis_is "{" ho with h | h | h | h | h <;> exact absurd h (by decide))
    (by rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;> rfl)
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have placed : parsePlatzStmt (F' + 2) (nameTok a :: r) = .ok (.set z o w, rest) := by
    rw [parsePlatzStmt_ident _ _ _ hrt, ← hzr]
    have hK := kopfP z hz (.zeichen o :: (druckToks w ++ .zeichen ";" :: rest)) F'
      (by rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;> rfl) (by omega)
    have hO := ausdruck w hw (.zeichen ";" :: rest) F' rfl rfl rfl (by omega)
    obtain ⟨hmiss, hgeneric⟩ := zuweis_keineRufOeffnung o ho
      (druckToks w ++ .zeichen ";" :: rest)
    simp only [parseKopfStmt, hK]
    split
    · simp only [gutPlatz, Bool.false_eq_true] at hz
    · simp only [gutPlatz, Bool.false_eq_true] at hz
    · simp only [gutPlatz, Bool.false_eq_true] at hz
    · rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;> split <;>
        simp_all [hO, fordereZeichen, strEq_self]
  rw [hd, hzr]
  exact parseStmt_ident (F' + 2) a r hr (Or.inl hro) placed

theorem anw_shift (z : SExpr) (a b : String) (hz : gutPlatz z = true) : AnwBein (.shift z a b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨c, ts, hc, ck⟩ := platz_kopf z hz
  have hd : druckAnw (.shift z a b) ++ rest = .wort "transition" :: (druckToks z ++
      (.zeichen ":" :: nameTok a :: .zeichen "->" :: nameTok b :: .zeichen ";" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_transition _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
  have hO := ortP z hz (.zeichen ":" :: nameTok a :: .zeichen "->" :: nameTok b :: .zeichen ";" :: rest)
    F' rfl (by omega)
  simp only [parseUebergang, hO, fordereZeichen, strEq_self, ↓reduceIte, nimmName, nameText_nameTok]

theorem anw_free (z : SExpr) (hz : gutPlatz z = true) : AnwBein (.free z) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨c, ts, hc, ck⟩ := platz_kopf z hz
  have hd : druckAnw (.free z) ++ rest = .wort "free" :: (druckToks z ++ .zeichen ";" :: rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_free _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
  have hO := ortP z hz (.zeichen ";" :: rest) F' rfl (by omega)
  simp only [parseFree, bind, Except.bind, hO, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

/-- A name-shaped call head (or `start` root) re-lexes to its name token. -/
def NameGut (f : String) : Prop := nameForm f = true

theorem rohToks_nameGut (f : String) (h : NameGut f) : rohToks f = [nameTok f] :=
  rohToks_name f h

/-- Argument legs from printability. -/
theorem args_gut (xs : List SExpr) (h : gutListe xs = true) :
    ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true := by
  intro x hx
  have := gutListe_mem xs x hx h
  exact ⟨legs_tok x this, this⟩

theorem anw_call (f : String) (xs : List SExpr) (hf : NameGut f) (hw : istAnwWort f = false)
    (hxs : gutListe xs = true) : AnwBein (.call f xs) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, rohToks_nameGut f hf, List.length_append, List.length_singleton,
    List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.call f xs) ++ rest = nameTok f :: .zeichen "(" ::
      (druckToksListe xs ++ [.zeichen ")"] ++ (.zeichen ";" :: rest)) := by
    simp only [druckAnw, rohToks_nameGut f hf, List.cons_append, List.nil_append, List.append_assoc]
  have ht : f ≠ "transition" := by intro e; subst e; revert hw; decide
  have placed : parsePlatzStmt (F' + 3) (nameTok f :: .zeichen "(" ::
      (druckToksListe xs ++ [.zeichen ")"] ++ (.zeichen ";" :: rest))) = .ok (.call f xs, rest) := by
    rw [parsePlatzStmt_ident _ _ _ ht]
    have hA := argsM xs (.zeichen ";" :: rest) F' (args_gut xs hxs) (by omega)
    simp only [parseKopfStmt]
    rw [show F' + 1 = F' + 1 from rfl, kopf_ruf_head, hA]
    dsimp only
    rw [awaitSuffix_stop _ _ (show ruhigSuff (.zeichen ";" :: rest) = true from rfl)]
    simp only [parseRufMitElse, parseRufSchwanz, strEq_semi_frage, Bool.false_eq_true, fordereZeichen, strEq_self, ↓reduceIte]
  rw [hd]
  exact parseStmt_ident (F' + 3) f _ (by
    intro r e
    simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (Or.inr hw) placed

/-! ### Statements with a block -/

/-- A block prints with its opening brace first. -/
def BlockKopf (b : SAnw) : Prop := ∃ ts, druckAnw b = .zeichen "{" :: ts

theorem blockKopf_block (ss : List SAnw) (e : Option SEnde) : BlockKopf (.block ss e) :=
  ⟨druckAnwListe ss ++ druckEnde e ++ [.zeichen "}"], by simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]⟩

theorem ortsfort_block (b : SAnw) (hk : BlockKopf b) (rest : List Token) :
    istOrtsFort (druckAnw b ++ rest) = false := by
  obtain ⟨ts, h⟩ := hk; rw [h]; rfl

theorem block_len (b : SAnw) (hk : BlockKopf b) : 1 ≤ (druckAnw b).length := by
  obtain ⟨ts, h⟩ := hk; rw [h]; simp only [List.length_cons, Nat.le_add_left]

theorem anw_child (b : SAnw) (hb : BlockBein b) (hk : BlockKopf b) : AnwBein (.child b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.child b) ++ rest = .wort "child" :: (druckAnw b ++ rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append]
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  rw [hd, parseStmt_child _ _ (ortsfort_block b hk rest)]
  simp only [parseChild, bind, Except.bind, hB, pure, Except.pure]

theorem anw_watch (d : String) (b : SAnw) (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (.watch d b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.watch d b) ++ rest = .wort "observes" :: nameTok d :: (druckAnw b ++ rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append]
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  rw [hd, parseStmt_observes _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseBeobachtet, nimmName, nameText_nameTok, hB]

/-- `locks` before a place whose head is no `shared`: the place reader sees the head name. -/
theorem parseSperrt_nameTok (f : Nat) (c : String) (hc : c ≠ "shared") (R : List Token) :
    parseSperrt (f + 1) (nameTok c :: R) = (match parseOrt f (nameTok c :: R) with
      | .error e => .error e
      | .ok (o, rest) => match parseBlock f rest with
        | .error e => .error e
        | .ok (b, rest') => .ok (.locks false o b, rest')) := by
  have hs : strEq c "shared" = false := by
    cases h : strEq c "shared"
    · rfl
    · exact absurd ((strEq_eq _ _).mp h) hc
  unfold nameTok; split
  · simp only [parseSperrt, hs, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · rfl

theorem anw_locks (g : Bool) (o : SExpr) (b : SAnw) (ho : gutPlatz o = true)
    (hsh : g = false → kopfName o ≠ "shared") (hb : BlockBein b)
    (hk : BlockKopf b) : AnwBein (.locks g o b) := by
  intro rest F _ hF
  obtain ⟨ts, hts⟩ := hk
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero] at hF <;> omega⟩
  obtain ⟨c, cs, hc, ck⟩ := platz_kopf o ho
  have hO := ortP o ho (druckAnw b ++ rest) (F' + 1) (by rw [hts]; rfl)
    (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  cases g
  · have hd : druckAnw (.locks false o b) ++ rest = .wort "locks" :: (druckToks o ++ (druckAnw b ++ rest)) := by
      simp only [druckAnw, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append,
  List.append_assoc]
    rw [hd, parseStmt_locks _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    have hcn : c = kopfName o := by
      obtain ⟨us, hu⟩ := platz_kopfName o ho
      rw [hc] at hu; injection hu with hu; exact nameTok_inj hu
    simp only [hc, List.cons_append] at hO ⊢
    rw [show F' + 2 = (F' + 1) + 1 from rfl, parseSperrt_nameTok _ c (hcn ▸ hsh rfl)]
    simp only [hO, hB]
  · have hd : druckAnw (.locks true o b) ++ rest =
        .wort "locks" :: .wort "shared" :: (druckToks o ++ (druckAnw b ++ rest)) := by
      simp only [druckAnw, ↓reduceIte, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd, parseStmt_locks _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseSperrt, strEq_self, ↓reduceIte, hO, hB]

theorem anw_grow (a : String) (e : SExpr) (b : SAnw) (he : gut e = true) (hb : BlockBein b)
    (hk : BlockKopf b) : AnwBein (.grow a e b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil,
    List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckAnw (.grow a e b) ++ rest = .wort "grow" :: nameTok a :: .wort "by" ::
      (druckToks e ++ .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hB := hb (.zeichen ";" :: rest) F' (by simp only [fbA]; omega)
  have hE := ausdruck e he (.wort "else" :: (druckAnw b ++ .zeichen ";" :: rest)) F' rfl rfl rfl
    (by omega)
  rw [hd, parseStmt_grow _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseGrow, bind, Except.bind, nimmName, nameText_nameTok, nimmWort, strEq_self, ↓reduceIte, hE, hB,
  fordereZeichen, pure, Except.pure]


/-! ### More statement forms -/

theorem anw_reset (a : String) (rg : Option (SExpr × SExpr))
    (hrg : ∀ i n, rg = some (i, n) → gut i = true ∧ gut n = true) : AnwBein (.reset a rg) := by
  intro rest F _ hF
  cases rg with
  | none =>
    simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.reset a none) ++ rest = .wort "reset" :: nameTok a :: .zeichen ";" :: rest := by
      simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append]
    rw [hd, parseStmt_reset _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseReset, bind, Except.bind, nimmName, nameText_nameTok, pure, Except.pure, fordereZeichen,
  strEq_self, ↓reduceIte]
  | some p =>
    obtain ⟨i, n⟩ := p
    obtain ⟨hi, hn⟩ := hrg i n rfl
    simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.reset a (some (i, n))) ++ rest = .wort "reset" :: nameTok a :: .wort "at" ::
        (druckToks i ++ .wort "count" :: (druckToks n ++ .zeichen ";" :: rest)) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    have hI := ausdruck i hi (.wort "count" :: (druckToks n ++ .zeichen ";" :: rest)) F' rfl rfl rfl
      (by omega)
    have hN := ausdruck n hn (.zeichen ";" :: rest) F' rfl rfl rfl (by omega)
    rw [hd, parseStmt_reset _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseReset, bind, Except.bind, nimmName, nameText_nameTok, hI, nimmWort, strEq_self, ↓reduceIte,
  hN, pure, Except.pure, fordereZeichen]


end Gabbro.Grammatik.Parser
