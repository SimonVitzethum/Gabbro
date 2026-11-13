module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.CallElse
public import Grammatik.Parser.Round.RundlaufAnwVoll.IndirectElse
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

theorem elseIfs_rund : ∀ (eis : List SAnw) (s : Option SAnw) (acc : List SAnw) (rest : List Token) (F : Nat),
    (∀ x ∈ eis, ElsifBein x) → (∀ b, s = some b → BlockBein b ∧ BlockKopf b) →
    (s = none → KE rest) → 8 * (druckAnwListe eis ++ druckSonst s).length + 31 ≤ F →
    parseElseIfs F (druckAnwListe eis ++ druckSonst s ++ rest) acc = .ok ((acc ++ eis, s), rest) := by
  intro eis
  induction eis with
  | nil =>
    intro s acc rest F _ hs hK hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases s with
    | none =>
      have hk := hK rfl
      simp only [druckAnwListe, druckSonst, List.nil_append, List.append_nil]
      rcases rest with _ | ⟨t, r⟩
      · simp only [parseElseIfs]
      · cases t with
        | wort w =>
          have : strEq w "else" = false := by
            cases h : strEq w "else"
            · rfl
            · exact absurd (by rw [(strEq_eq _ _).mp h]) (hk r)
          simp only [parseElseIfs, this, Bool.false_eq_true, ↓reduceIte]
        | _ => simp only [parseElseIfs]
    | some b =>
      obtain ⟨hb, us, hus⟩ := hs b rfl
      simp only [druckAnwListe, druckSonst, List.nil_append, List.length_append, List.length_cons,
        List.length_nil] at hF ⊢
      have hB := hb rest F' (by simp only [fbA]; omega)
      rw [hus] at hB ⊢
      simp only [List.cons_append, List.append_assoc] at hB ⊢
      simp only [parseElseIfs, strEq_self, ↓reduceIte, List.nil_append, hB, List.append_nil]
  | cons x eis ih =>
    intro s acc rest F hx hs hK hF
    obtain ⟨c, b, rfl, hc, hb, us, hus⟩ := hx x (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    have hR := ih s (acc ++ [.elsif c b]) rest F' (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hs hK
      (by simp only [List.length_append]; omega)
    have hB := hb (druckAnwListe eis ++ druckSonst s ++ rest) F' (by simp only [fbA]; omega)
    have hC := ausdruck c hc (druckAnw b ++ (druckAnwListe eis ++ druckSonst s ++ rest)) F'
      (by rw [hus]; rfl) (by rw [hus]; rfl) (by rw [hus]; rfl) (by omega)
    have hd : druckAnwListe (.elsif c b :: eis) ++ druckSonst s ++ rest = .wort "else" :: .wort "if" ::
        (druckToks c ++ (druckAnw b ++ (druckAnwListe eis ++ druckSonst s ++ rest))) := by
      simp only [druckAnwListe, druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd]
    simp only [List.append_assoc] at hR hB hC ⊢
    simp only [parseElseIfs, strEq_self, ↓reduceIte, List.tail_cons, hC, hB, hR, List.cons_append,
  List.nil_append]

theorem anw_cond (c : SExpr) (t : SAnw) (eis : List SAnw) (s : Option SAnw) (hc : gut c = true)
    (ht : BlockBein t) (htk : BlockKopf t) (heis : ∀ x ∈ eis, ElsifBein x)
    (hs : ∀ b, s = some b → BlockBein b ∧ BlockKopf b) : AnwBein (.cond c t eis s) := by
  intro rest F hK hF
  obtain ⟨us, hus⟩ := htk
  have hd : druckAnw (.cond c t eis s) ++ rest = .wort "if" :: (druckToks c ++ (druckAnw t ++
      (druckAnwListe eis ++ druckSonst s ++ rest))) := by
    cases s <;> simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, druckSonst]
  have hlen : (druckAnw (.cond c t eis s)).length = 1 + (druckToks c).length + (druckAnw t).length +
      (druckAnwListe eis ++ druckSonst s).length := by
    cases s <;> simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, druckSonst] <;> omega
  simp only [fbA, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨k, ks, hk, hkg⟩ := druck_kopf c hc
  have hE := elseIfs_rund eis s [] rest F' heis hs (fun _ => hK) (by omega)
  have hT := ht (druckAnwListe eis ++ druckSonst s ++ rest) F' (by simp only [fbA]; omega)
  have hC := ausdruck c hc (druckAnw t ++ (druckAnwListe eis ++ druckSonst s ++ rest)) F'
    (by rw [hus]; rfl) (by rw [hus]; rfl) (by rw [hus]; rfl) (by omega)
  rw [hd, parseStmt_if _ _ (by rw [hk]; exact kopf_nicht_ortsfort k hkg _)]
  simp only [List.append_assoc] at hE hT hC ⊢
  simp only [parseWenn, hC, hT, hE, List.nil_append]

/-- Name patterns still use exactly the previous token reader path. -/
theorem nimmArmMuster_nameTok (s : String) (rest : List Token) :
    nimmArmMuster (nameTok s :: rest) = .ok (s, rest) := by
  unfold nameTok
  split <;> rfl

/-- The numeric token case preserves the arm-name representation as well. -/
theorem nimmArmMuster_armMusterTok (s : String) (rest : List Token) :
    nimmArmMuster (armMusterTok s :: rest) = .ok (s, rest) := by
  cases h : armZahl? s with
  | none => simpa only [armMusterTok, h] using nimmArmMuster_nameTok s rest
  | some n =>
    simp only [armMusterTok, h]
    by_cases hq : strEq s (toString n) = true
    · rw [if_pos hq]
      have he : s = toString n := strKlingt _ _ hq
      simp only [nimmArmMuster, he]
    · simpa only [if_neg hq] using nimmArmMuster_nameTok s rest

theorem armMusterTok_ne_zeichen (s z : String) : armMusterTok s ≠ .zeichen z := by
  cases h : armZahl? s with
  | none => simpa only [armMusterTok, h] using nameTok_ne_zeichen s z
  | some n =>
    simp only [armMusterTok, h]
    by_cases hq : strEq s (toString n) = true
    · simp only [if_pos hq, ne_eq, reduceCtorEq, not_false_eq_true]
    · simpa only [if_neg hq] using nameTok_ne_zeichen s z

/-- The legs of a `match` arm. -/
def ArmBein (x : SAnw) : Prop :=
  ∃ v bi b, x = .arm v bi b ∧ BlockBein b ∧ BlockKopf b

theorem arme_rund : ∀ (arms : List SAnw) (rest : List Token) (F : Nat),
    (∀ x ∈ arms, ArmBein x) → 8 * (druckAnwListe arms).length + 31 ≤ F →
    parseArme F (druckAnwListe arms ++ .zeichen "}" :: rest) = .ok (arms, .zeichen "}" :: rest) := by
  intro arms
  induction arms with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArme, druckAnwListe, List.nil_append]
  | cons x arms ih =>
    intro rest F hx hF
    obtain ⟨v, bi, b, rfl, hb, us, hus⟩ := hx x (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hR := ih rest F' (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have hB := hb (druckAnwListe arms ++ .zeichen "}" :: rest) F'
    cases bi with
    | none =>
      simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
      have hd : druckAnwListe (.arm v none b :: arms) ++ .zeichen "}" :: rest = armMusterTok v :: .zeichen "=>" ::
          (druckAnw b ++ (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
        simp only [druckAnwListe, druckAnw, List.append_nil, List.cons_append, List.nil_append, List.append_assoc]
      rw [hd]
      rw [hus] at hB ⊢
      simp only [List.cons_append] at hB
      simp only [parseArme, List.cons_append, List.cons.injEq, armMusterTok_ne_zeichen, nameTok_ne_zeichen, false_and, imp_self,
  implies_true, nimmArmMuster_armMusterTok, nimmName, nameText_nameTok, fordereZeichen, Token.zeichen.injEq, String.reduceEq, strEq_self,
  ↓reduceIte, hB (by simp only [fbA]; omega), hR (by omega)]
    | some y =>
      simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
      have hd : druckAnwListe (.arm v (some y) b :: arms) ++ .zeichen "}" :: rest = armMusterTok v ::
          .zeichen "(" :: nameTok y :: .zeichen ")" :: .zeichen "=>" ::
          (druckAnw b ++ (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
        simp only [druckAnwListe, druckAnw, List.cons_append, List.nil_append, List.append_assoc]
      rw [hd]
      rw [hus] at hB ⊢
      simp only [List.cons_append] at hB
      simp only [parseArme, List.cons_append, List.cons.injEq, armMusterTok_ne_zeichen, nameTok_ne_zeichen, false_and, imp_self,
  implies_true, nimmArmMuster_armMusterTok, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hB (by simp only [fbA]; omega),
  hR (by omega)]

theorem anw_cases (g : SExpr) (arms : List SAnw) (hg : gut g = true) (ha : ∀ x ∈ arms, ArmBein x) :
    AnwBein (.cases g arms) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨k, ks, hk, hkg⟩ := druck_kopf g hg
  have hd : druckAnw (.cases g arms) ++ rest = .wort "match" :: (druckToks g ++ .zeichen "{" ::
      (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hG := ausdruck g hg (.zeichen "{" :: (druckAnwListe arms ++ .zeichen "}" :: rest)) F' rfl rfl rfl
    (by omega)
  have hA := arme_rund arms rest F' ha (by omega)
  rw [hd, parseStmt_match _ _ (by rw [hk]; exact kopf_nicht_ortsfort k hkg _)]
  simp only [parseMatchS, hG, fordereZeichen, strEq_self, ↓reduceIte, hA]


/-! ### The printability class and the induction -/

/-- The position of a statement tree: a statement, a block, an `else if` branch, a `match` arm. -/
inductive Rolle
  | anw | block | elsif | arm

/-- A printable ender: a valued `return` has a printable value. -/
def EndeOk : Option SEnde → Prop
  | some (.ret (some x)) => gut x = true
  | _ => True

/-- **The printability class of statements and blocks** (see the header). -/
inductive AnwGut : Rolle → SAnw → Prop
  | bind (m : Bool) (x : String) (ty : Option STyp) (e : SExpr) : x ≠ "mut" →
      TypOptGut ty → gut e = true → AnwGut .anw (.bind m x ty e)
  | bindElse (x : String) (ty : Option STyp) (e : SExpr) (f : String) (b : SAnw) : x ≠ "mut" →
      TypOptGut ty → gut e = true → AnwGut .block b → AnwGut .anw (.bindElse x ty e f b)
  | bindLib (m : Bool) (x : String) (ty : Option STyp) (c : SLibraryCall) : x ≠ "mut" →
      TypOptGut ty → LibraryCallGut c → AnwGut .anw (.bindLib m x ty c)
  | set (z : SExpr) (o : String) (w : SExpr) :
      gutPlatz z = true → istZuweis o = true → gut w = true → AnwGut .anw (.set z o w)
  | shift (z : SExpr) (a b : String) : gutPlatz z = true → AnwGut .anw (.shift z a b)
  | call (f : String) (xs : List SExpr) : NameGut f → istAnwWort f = false → gutListe xs = true →
      AnwGut .anw (.call f xs)
  | lcall (c : SLibraryCall) : LibraryCallGut c → AnwGut .anw (.lcall c)
  | cond (c : SExpr) (t : SAnw) (eis : List SAnw) (s : Option SAnw) :
      gut c = true → AnwGut .block t → (∀ x ∈ eis, AnwGut .elsif x) →
      (∀ b, s = some b → AnwGut .block b) → AnwGut .anw (.cond c t eis s)
  | elsif (c : SExpr) (b : SAnw) : gut c = true → AnwGut .block b → AnwGut .elsif (.elsif c b)
  | cases (g : SExpr) (arms : List SAnw) :
      gut g = true → (∀ x ∈ arms, AnwGut .arm x) → AnwGut .anw (.cases g arms)
  | arm (v : String) (bi : Option String) (b : SAnw) : AnwGut .block b → AnwGut .arm (.arm v bi b)
  | each (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m r : String) (i : Option SExpr)
      (body : SAnw) : (∀ e, o = some e → gut e = true) → gut s = true → RohTrav r →
      (∀ e, i = some e → PredGut e) → AnwGut .block body → AnwGut .anw (.each b o k s m r i body)
  | retry (h : String) (b : SAnw) : RohKopf h → AnwGut .block b → AnwGut .anw (.retry h b)
  | loop (h : String) (b : SAnw) : RohKopf h → AnwGut .block b → AnwGut .anw (.loop h b)
  | waive (ns : List String) (b : SAnw) : ns ≠ [] → AnwGut .block b → AnwGut .anw (.waive ns b)
  | trim (o : SExpr) (t : String) (b : SAnw) :
      gutPlatz o = true → TrimGut t → AnwGut .block b → AnwGut .anw (.trim o t b)
  | locks (g : Bool) (o : SExpr) (b : SAnw) :
      gutPlatz o = true → (g = false → kopfName o ≠ "shared") → AnwGut .block b →
      AnwGut .anw (.locks g o b)
  | watch (d : String) (b : SAnw) : AnwGut .block b → AnwGut .anw (.watch d b)
  | leave (l : String) : AnwGut .anw (.leave l)
  | next (l : String) : AnwGut .anw (.next l)
  | emit (z w : SExpr) (p : String) :
      gutPlatz z = true → gut w = true → PubGut p → AnwGut .anw (.emit z w p)
  | await (n : String) (ty : Option STyp) (q : SExpr) (p : String) : n ≠ "mut" → TypOptGut ty → gut q = true →
      RohZu p → AnwGut .anw (.await n ty q p)
  | swap (n : String) (ty : Option STyp) (o : SExpr) (k : String) : n ≠ "mut" → TypOptGut ty → gut o = true →
      RohSemi k → AnwGut .anw (.swap n ty o k)
  | step (a b : String) : AnwGut .anw (.step a b)
  | retLeer : AnwGut .anw (.ret none)
  | ret (e : SExpr) : gut e = true → AnwGut .anw (.ret (some e))
  | alloc (m : Bool) (n : String) (ty : Option STyp) (t : String) (w : SExpr) (s : Option SAnw) :
      n ≠ "mut" → TypOptGut ty → gut w = true → (∀ b, s = some b → AnwGut .block b) →
      AnwGut .anw (.alloc m n ty t w s)
  | reset (a : String) (rg : Option (SExpr × SExpr)) :
      (∀ i n, rg = some (i, n) → gut i = true ∧ gut n = true) → AnwGut .anw (.reset a rg)
  | grow (a : String) (e : SExpr) (b : SAnw) : gut e = true → AnwGut .block b → AnwGut .anw (.grow a e b)
  | free (z : SExpr) : gutPlatz z = true → AnwGut .anw (.free z)
  | child (b : SAnw) : AnwGut .block b → AnwGut .anw (.child b)
  | start (ps : List String) : ps ≠ [] → (∀ p ∈ ps, NameGut p) → AnwGut .anw (.start ps)
  | block (ss : List SAnw) (e : Option SEnde) :
      (∀ s ∈ ss, AnwGut .anw s) → EndeOk e → EndeGut ss e → AnwGut .block (.block ss e)
  | allocVon (m : Bool) (n : String) (ty : Option STyp) (t : String) :
      n ≠ "mut" → TypOptGut ty → AnwGut .anw (.allocVon m n ty t)

  | callElse (name : String) (args : List SExpr) (reason : String) (body : SAnw) :
      NameGut name → istAnwWort name = false → gutListe args = true → AnwGut .block body →
      AnwGut .anw (.callElse name args reason body)
  | callIndElse (pointer : SExpr) (args : List SExpr) (reason : String) (body : SAnw) :
      gut pointer = true → gutListe args = true → AnwGut .block body →
      AnwGut .anw (.callIndElse pointer args reason body)


end Gabbro.Grammatik.Parser
