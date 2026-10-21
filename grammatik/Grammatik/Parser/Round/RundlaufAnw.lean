/-
  File:      Grammatik/Parser/Round/RundlaufAnw.lean
  Subject:   Track P: the first round-trip THEOREM at statement level.

  Over the `gutPrim` expressions (the class `parse_druck_prim` proves), a block of the simple statements
  `return;`, `return e;`, `leave l;`, `next l;` and `let x = e;` prints (`Print/Stmt`) and reads back through
  `parseBlock` as the same tree, whatever follows the closing brace. The expression leg is the eight-leg
  record `Legs` of `Rundlauf3`; this file adds the statement dispatch (`parseStmt` -> `parseRueck`,
  `parseLet`, `parseVerlasse`, `parseWeiter`) and the fuel of the statement list.

  The class is small on purpose (no calls, no assignments, no nested blocks): each further statement form
  is one more case of `parseStmt_einfach` with its own head-token fact. Everything else is MEASURED
  (`Print/Proben`, the census columns `rt=` and `ri=`).
-/
import Grammatik.Parser.Round.Rundlauf4
import Grammatik.Parser.Print.Stmt

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ## The name reader on concrete tokens

`nameText` is reduced by these lemmas (and `nameText_nameTok`) instead of being unfolded, so a printed
name `nameTok s` meets its lemma before an unfolded `match`. -/

@[simp] theorem nameText_ident (s : String) : nameText (.ident s) = some s := rfl
@[simp] theorem nameText_wort (s : String) : nameText (.wort s) = some s := rfl
@[simp] theorem nameText_zeichen (s : String) : nameText (.zeichen s) = none := rfl
@[simp] theorem nameText_num (n : Nat) : nameText (.num n) = none := rfl
@[simp] theorem nameText_float (s : String) : nameText (.float s) = none := rfl
@[simp] theorem nameText_text (s : String) : nameText (.text s) = none := rfl
@[simp] theorem nameText_ende : nameText .ende = none := rfl

/-! ## The first token of a printed expression -/

/-- A token that opens no place continuation, no `;` and no `@`, and no `alloc` head. -/
def KopfGut : Token → Prop
  | .zeichen s => s = "(" ∨ s = "!" ∨ s = "-" ∨ s = "~" ∨ s = "&"
  | .wort s => s ≠ "alloc"
  | _ => True

theorem kopfGut_nameTok {s : String} (h : istKopfWort s = false) : KopfGut (nameTok s) := by
  unfold nameTok; split
  · show s ≠ "alloc"
    intro e; subst e; revert h; decide
  · trivial

theorem platz_kopf_aux : ∀ (n : Nat) (x : SExpr), groesse x ≤ n → gutPlatz x = true →
    ∃ s ts, druckToks x = nameTok s :: ts ∧ istKopfWort s = false := by
  intro n
  induction n with
  | zero =>
    intro x hs _
    have := groesse_pos x
    omega
  | succ n ih =>
    intro x hs hg
    cases x with
    | «variable» s =>
      exact ⟨s, [], by simp [druckToks], by simpa [gutPlatz] using hg⟩
    | field y f =>
      have hy : gutPlatz y = true := by simpa [gutPlatz] using hg
      have hs' : groesse y ≤ n := by simp only [groesse] at hs; omega
      obtain ⟨s, ts, h, hk⟩ := ih y hs' hy
      exact ⟨s, ts ++ [.zeichen ".", nameTok f], by simp [druckToks, h], hk⟩
    | index y i =>
      have hy : gutPlatz y = true := by
        simp only [gutPlatz, Bool.and_eq_true] at hg
        exact hg.1
      have hs' : groesse y ≤ n := by simp only [groesse] at hs; omega
      obtain ⟨s, ts, h, hk⟩ := ih y hs' hy
      exact ⟨s, ts ++ ([.zeichen "["] ++ druckToks i ++ [.zeichen "]"]), by simp [druckToks, h], hk⟩
    | arrow y f =>
      have hy : gutPlatz y = true := by simpa [gutPlatz] using hg
      have hs' : groesse y ≤ n := by simp only [groesse] at hs; omega
      obtain ⟨s, ts, h, hk⟩ := ih y hs' hy
      exact ⟨s, ts ++ [.zeichen "->", nameTok f], by simp [druckToks, h], hk⟩
    | lit _ => simp [gutPlatz] at hg
    | float _ => simp [gutPlatz] at hg
    | tru => simp [gutPlatz] at hg
    | fls => simp [gutPlatz] at hg
    | un _ _ => simp [gutPlatz] at hg
    | bin _ _ _ => simp [gutPlatz] at hg
    | call _ _ => simp [gutPlatz] at hg
    | fnref _ => simp [gutPlatz] at hg
    | built _ _ => simp [gutPlatz] at hg
    | old _ => simp [gutPlatz] at hg
    | res => simp [gutPlatz] at hg
    | why _ _ => simp [gutPlatz] at hg
    | ext _ _ _ => simp [gutPlatz] at hg

/-- Every printable expression starts with a good head token. -/
theorem druck_kopf : ∀ (e : SExpr), gut e = true →
    ∃ t ts, druckToks e = t :: ts ∧ KopfGut t := by
  intro e hg
  cases e with
  | lit n => exact ⟨.num n, [], by simp [druckToks], trivial⟩
  | float s => exact ⟨.float s, [], by simp [druckToks], trivial⟩
  | tru => exact ⟨.wort "true", [], by simp [druckToks], by simp [KopfGut]⟩
  | fls => exact ⟨.wort "false", [], by simp [druckToks], by simp [KopfGut]⟩
  | «variable» s =>
    exact ⟨nameTok s, [], by simp [druckToks], kopfGut_nameTok (by simpa [gut] using hg)⟩
  | field y f =>
    have hy : gutPlatz y = true := by simpa [gut] using hg
    obtain ⟨s, ts, h, hk⟩ := platz_kopf_aux (groesse y) y (Nat.le_refl _) hy
    exact ⟨nameTok s, ts ++ [.zeichen ".", nameTok f], by simp [druckToks, h], kopfGut_nameTok hk⟩
  | index y i =>
    have hy : gutPlatz y = true := by
      simp only [gut, Bool.and_eq_true] at hg
      exact hg.1
    obtain ⟨s, ts, h, hk⟩ := platz_kopf_aux (groesse y) y (Nat.le_refl _) hy
    exact ⟨nameTok s, ts ++ ([.zeichen "["] ++ druckToks i ++ [.zeichen "]"]), by simp [druckToks, h],
      kopfGut_nameTok hk⟩
  | arrow y f =>
    have hy : gutPlatz y = true := by simpa [gut] using hg
    obtain ⟨s, ts, h, hk⟩ := platz_kopf_aux (groesse y) y (Nat.le_refl _) hy
    exact ⟨nameTok s, ts ++ [.zeichen "->", nameTok f], by simp [druckToks, h], kopfGut_nameTok hk⟩
  | un o x =>
    have ho : gutOpUn o = true := by
      simp only [gut, Bool.and_eq_true] at hg
      exact hg.1
    refine ⟨.zeichen o, _, rfl, ?_⟩
    simp only [gutOpUn, Bool.or_eq_true, strEq_eq] at ho
    simp only [KopfGut]
    rcases ho with (h | h) | h <;> simp [h]
  | bin o l r => exact ⟨.zeichen "(", _, rfl, by simp [KopfGut]⟩
  | call f xs =>
    exact ⟨nameTok f, _, rfl, kopfGut_nameTok (by simp only [gut, Bool.and_eq_true] at hg; simpa using hg.1)⟩
  | fnref p => exact ⟨.zeichen "&", _, rfl, by simp [KopfGut]⟩
  | built f xs =>
    cases xs with
    | nil => simp [gut] at hg
    | cons a rest =>
      cases rest with
      | nil =>
        by_cases h1 : f = "sizeof"
        · subst h1; exact ⟨.wort "sizeof", _, rfl, by simp [KopfGut]⟩
        · by_cases h2 : f = "lenof"
          · subst h2; exact ⟨.wort "lenof", _, rfl, by simp [KopfGut]⟩
          · simp [gut, h1, h2] at hg
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          by_cases h1 : f = "aligned"
          · subst h1; exact ⟨.wort "aligned", _, rfl, by simp [KopfGut]⟩
          · simp [gut, h1] at hg
        | cons _ _ => simp [gut] at hg
  | old x => exact ⟨.wort "old", _, rfl, by simp [KopfGut]⟩
  | res => exact ⟨.wort "result", [], by simp [druckToks], by simp [KopfGut]⟩
  | why g f =>
    exact ⟨nameTok g, _, rfl, kopfGut_nameTok (by simp only [gut, Bool.and_eq_true] at hg; simpa using hg.1.1.1)⟩
  | ext _ _ _ => simp [gut] at hg

end Gabbro.Grammatik.Parser
