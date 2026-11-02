module
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2

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

theorem parseStmt_at (f : Nat) (r : List Token) :
    parseStmt (f + 1) (.zeichen "@" :: r) = parseLibStmt f (.zeichen "@" :: r) := by
  simp only [parseStmt]

/-- A printable library region closes exactly once, before any following tokens. -/
def LibraryRegionGut (tokens : List Token) : Prop :=
  ∀ rest, libraryRegion (tokens ++ .zeichen "}" :: rest) 1 = .ok (tokens, rest)

/-- Empty input is a printable region. -/
theorem libraryRegionGut_nil : LibraryRegionGut [] := by intro rest; rfl

/-- A library call is printable when its paths are non-empty (the reader never produces an
    empty path), its expressions have their ordinary round-trip legs and its retained region is
    balanced. No argument or input token is replaced by a placeholder. -/
def LibraryCallGut (c : SLibraryCall) : Prop :=
  c.library ≠ [] ∧ c.function ≠ [] ∧
    (∀ x ∈ c.args, LegsB (fb x) x ∧ gut x = true) ∧ LibraryRegionGut c.region

/-- `nimmPfad` reads a printed path and stops before a non-`::` follow (the path twin of
    `nimmPfad_pfad`, proved here because the item round trip may not be imported). -/
theorem nimmPfad_pfadToks (p : List String) (R : List Token) (hp : p ≠ [])
    (hR : ∀ r, R ≠ .zeichen "::" :: r) :
    nimmPfad (pfadToks p ++ R) = .ok (p, R) := by
  match p, hp with
  | [a], _ => simp only [nimmPfad, pfadToks, List.cons_append, List.nil_append, nameText_nameTok, sammleSeg_stop2 [a] R hR]
  | a :: b :: cs, _ =>
    have := sammleSeg_pfad (b :: cs) [a] R (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hR
    simp only [pfadToks, List.cons_append, List.nil_append, List.singleton_append] at this ⊢
    simp only [nimmPfad, nameText_nameTok, this]

theorem libRuf_rund (c : SLibraryCall) (hc : LibraryCallGut c)
    (rest : List Token) (F : Nat) (hF : 6 * (druckToksListe c.args).length + 37 ≤ F) :
    parseLibRuf F (druckLibraryCall c ++ rest) = .ok (c, rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨hlne, hfnne, hargs, hreg⟩ := hc
  cases c with
  | mk library function args region =>
    have hA := argsM args (.zeichen "{" :: (region ++ .zeichen "}" :: rest)) F' hargs (by simp only at hF; omega)
    simp only [List.append_assoc, List.singleton_append] at hA
    have hR := hreg rest
    have hL := nimmPfad_pfadToks library (.zeichen "#" :: (pfadToks function ++ .zeichen "(" ::
      (druckToksListe args ++ .zeichen ")" :: .zeichen "{" :: (region ++ .zeichen "}" :: rest)))) hlne
      (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    have hFn := nimmPfad_pfadToks function (.zeichen "(" :: (druckToksListe args ++ .zeichen ")" ::
      .zeichen "{" :: (region ++ .zeichen "}" :: rest))) hfnne
      (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    simp only [druckLibraryCall, parseLibRuf, List.append_assoc, List.cons_append, List.nil_append,
      fordereZeichen, strEq_self, ↓reduceIte, hL, hFn, hA, hR]

theorem anw_lcall (c : SLibraryCall) (hc : LibraryCallGut c) : AnwBein (.lcall c) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, druckLibraryCall, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hL := libRuf_rund c hc (.zeichen ";" :: rest) F' (by omega)
  rw [show druckAnw (.lcall c) ++ rest = druckLibraryCall c ++ .zeichen ";" :: rest by
    simp only [druckAnw, List.append_assoc, List.singleton_append]]
  have hHead : druckLibraryCall c ++ .zeichen ";" :: rest = .zeichen "@" :: (pfadToks c.library ++
      [.zeichen "#"] ++ pfadToks c.function ++ [.zeichen "("] ++ druckToksListe c.args ++
      [.zeichen ")", .zeichen "{"] ++ c.region ++ [.zeichen "}"] ++ .zeichen ";" :: rest) := by
    simp only [druckLibraryCall, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  rw [hHead, parseStmt_at, ← hHead]
  simp only [parseLibStmt, hL, fordereZeichen, strEq_self, ↓reduceIte]

theorem anw_bindLib (m : Bool) (x : String) (hx : x ≠ "mut") (ty : Option STyp) (c : SLibraryCall)
    (hty : TypOptGut ty) (hc : LibraryCallGut c) :
    AnwBein (.bindLib m x ty c) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, druckLibraryCall, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.bindLib m x ty c) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
      nameTok x :: (druckTypOpt ty ++ .zeichen "=" :: (druckLibraryCall c ++ .zeichen ";" :: rest))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
  rw [parseLet_kopf (F' + 1) m x hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
  obtain ⟨F'', hF''⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega⟩
  have hL := libRuf_rund c hc (.zeichen ";" :: rest) F' (by split at hF <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;> omega)
  subst hF''
  simp only [druckLibraryCall, List.append_assoc, List.cons_append, List.nil_append] at hL ⊢
  simp only [parseLetNach, List.append_assoc, List.cons_append, List.nil_append, parseLetLib, bind, Except.bind,
    hL, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]


/-! ### `let` forms with a tail -/

theorem anw_alloc (m : Bool) (n : String) (hx : n ≠ "mut") (ty : Option STyp) (t : String) (w : SExpr) (s : Option SAnw)
    (hty : TypOptGut ty) (hw : gut w = true) (hs : ∀ b, s = some b → BlockBein b) :
    AnwBein (.alloc m n ty t w s) := by
  intro rest F _ hF
  have he : strEq "alloc" "alloc" = true := by decide
  cases s with
  | none =>
    simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
    have hd : druckAnw (.alloc m n ty t w none) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
        nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen "(" ::
          (druckToks w ++ .zeichen ")" :: .zeichen ";" :: rest)))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil]
    rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
    rw [show F' + 3 = (F' + 2) + 1 from rfl,
      parseLet_kopf (F' + 2) m n hx ty _ hty (by
        intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero, Nat.reduceLeDiff] at hF <;> omega)]
    have hW := ausdruck w hw (.zeichen ")" :: .zeichen ";" :: rest) (F' + 1) rfl rfl rfl
      (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero, Nat.reduceLeDiff] at hF <;> omega)
    simp only [parseLetNach, he, ite_true, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
    simp only [parseLetAlloc, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hW, pure, Except.pure]
  | some b =>
    simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
    have hd : druckAnw (.alloc m n ty t w (some b)) ++ rest = .wort "let" ::
        ((if m then [.wort "mut"] else []) ++
        nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen "(" ::
          (druckToks w ++ .zeichen ")" :: .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest))))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
    rw [show F' + 3 = (F' + 2) + 1 from rfl,
      parseLet_kopf (F' + 2) m n hx ty _ hty (by
        intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
    have hW := ausdruck w hw (.zeichen ")" :: .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest))
      (F' + 1) rfl rfl rfl (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    have hB := hs b rfl (.zeichen ";" :: rest) (F' + 1) (by
      simp only [fbA]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    simp only [parseLetNach, he, ite_true, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
    simp only [parseLetAlloc, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hW, hB, pure, Except.pure]

theorem anw_allocVon (m : Bool) (n : String) (hx : n ≠ "mut") (ty : Option STyp) (t : String)
    (hty : TypOptGut ty) : AnwBein (.allocVon m n ty t) := by
  intro rest F _ hF
  have he : strEq "alloc" "alloc" = true := by decide
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.allocVon m n ty t) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen ";" :: rest))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) m n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
  simp only [parseLetNach, he, ite_true, nameText_nameTok]

theorem anw_bindElse (x : String) (hx : x ≠ "mut") (ty : Option STyp) (e : SExpr) (f : String) (b : SAnw)
    (hty : TypOptGut ty) (he : gut e = true) (hb : BlockBein b) :
    AnwBein (.bindElse x ty e f b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.bindElse x ty e f b) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok x :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks e ++ .wort "else" :: .zeichen "(" ::
        nameTok f :: .zeichen ")" :: (druckAnw b ++ rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, Bool.false_eq_true, ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false x hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ e he]
  have hE := ausdruck e he (.wort "else" :: .zeichen "(" :: nameTok f :: .zeichen ")" :: (druckAnw b ++ rest))
    (F' + 1) rfl rfl rfl (by omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  simp only [parseLetExpr, bind, Except.bind, hE, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hB, pure, Except.pure]

/-- A raw text inside braces (`awaits`/`publishes` payloads). -/
def RohZu (s : String) : Prop :=
  RohText (fun t => t = .zeichen "{" ∨ t = .zeichen "}") s

/-- A raw text up to `;` (the `exchange` tail). -/
def RohSemi (s : String) : Prop :=
  RohText (fun t => t = .zeichen "{" ∨ t = .zeichen "}" ∨ t = .zeichen ";") s

theorem anw_await (n : String) (hx : n ≠ "mut") (ty : Option STyp) (q : SExpr) (p : String) (hty : TypOptGut ty)
    (hq : gut q = true) (hp : RohZu p) :
    AnwBein (.await n ty q p) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hp
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  simp only [fbA, druckAnw, hroh, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.await n ty q (renderText ts)) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks q ++ .wort "awaits" :: .zeichen "{" ::
        (ts ++ .zeichen "}" :: .zeichen ";" :: rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, Bool.false_eq_true,
  ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ q hq]
  have hQ := ausdruck q hq (.wort "awaits" :: .zeichen "{" :: (ts ++ .zeichen "}" :: .zeichen ";" :: rest))
    (F' + 1) rfl rfl rfl (by omega)
  have hN := nimmBisZeichen_roh "}" ts (.zeichen ";" :: rest)
    (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e), fun e => (hts t ht).2 (Or.inr e),
      fun e => (hts t ht).2 (Or.inr e)⟩)
  simp only [parseLetExpr, bind, Except.bind, hQ, hN, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

end Gabbro.Grammatik.Parser
