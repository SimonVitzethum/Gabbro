module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil6

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Printed places split into head variable plus fragments.
theorem druckToks_applySuff : ∀ (base : SExpr) (suff : List SuffFrag),
    druckToks (applySuff base suff) =
      druckToks base ++ suffToks suff := by
  intro base suff
  induction suff generalizing base with
  | nil => simp only [applySuff, suffToks, List.append_nil]
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      simp only [applySuff, suffToks] at ⊢
      rw [ih]
      simp only [druckToks, List.append_assoc, List.cons_append,
        List.nil_append]
    | arrow f =>
      simp only [applySuff, suffToks] at ⊢
      rw [ih]
      simp only [druckToks, List.append_assoc, List.cons_append,
        List.nil_append]
    | idx i =>
      simp only [applySuff, suffToks] at ⊢
      rw [ih]
      simp only [druckToks, List.append_assoc, List.cons_append,
        List.nil_append]

-- The generic-call head precedes ordinary calls in `parseKopf`.
-- Neither a printed suffix nor its benign follow can start it.
theorem suffToks_nogeneric (suff : List SuffFrag) (rest : List Token)
    (hr : ruhigSuff rest = true) :
    ∀ R, suffToks suff ++ rest ≠ .zeichen "::" :: .zeichen "[" :: R := by
  intro R hcon
  cases suff with
  | nil =>
    simp only [suffToks, List.nil_append] at hcon
    rw [hcon] at hr
    change false = true at hr
    cases hr
  | cons frag suff =>
    cases frag <;>
      simp only [suffToks, List.cons_append, List.cons.injEq,
        Token.zeichen.injEq, String.reduceEq, false_and] at hcon

-- Places through `parseOrt`: decompose, read the head, run the
-- chain. The head gate uses `!istKeinPlatz`; the chain is
-- `suff_rund`.
theorem ort_platz_all : ∀ (n : Nat) (Rn : R n)
    (p : SExpr) (rest : List Token) (F : Nat),
    groesse p ≤ n → gutPlatz p = true → ruhigSuff rest = true →
    12 * (groesse p + 1) + groesse p ≤ F →
    parseOrt F (druckToks p ++ rest) = .ok (p, rest) := by
  intro n Rn p rest F hs hg hr hF
  obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege n p hs hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [druckToks_applySuff] at ⊢
  have hkaf : istKeinPlatz a = false := kopf_kp (nichtWahr_falsch _ hka)
  simp only [parseOrt, druckToks, nameText_nameTok, hkaf, List.cons_append] at ⊢
  -- ⊢ : parseSuffixe F' (variable a) (suffToks suff ++ rest) = ...
  have hs2 : suffGroesse suff + groesse (.variable a) ≤ n + 1 := by
    simp only [groesse] at ⊢
    omega
  have hF2 : 12 * (suffGroesse suff + groesse (.variable a) + 1) +
      suffGroesse suff ≤ F' := by
    simp only [groesse, groesse_applySuff] at hs hF ⊢
    omega
  exact suff_rund n Rn suff (.variable a) rest F' hs2 hgs hr hF2
-- Places through `parsePrimary`: decompose, read the head,
-- run the chain. The `(` call arm misses by `suffToks_nopar`;
-- the `([a], …)` arm runs `suff_rund`.
theorem prim_platz : ∀ (n : Nat) (Rn : R n)
    (p : SExpr) (rest : List Token) (F : Nat),
    groesse p ≤ n + 1 → gutPlatz p = true → ruhigSuff rest = true →
    12 * (groesse p + 1) + groesse p + 1 ≤ F →
    parsePrimary F (druckToks p ++ rest) = .ok (p, rest) := by
  intro n Rn p rest F hs hg hr hF
  obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) p hs hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druckToks_applySuff] at ⊢
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  simp only [parseKopf, nameText_nameTok] at ⊢
  simp only [List.nil_append] at ⊢
  simp only [sammleSeg_suffToks, hr] at ⊢
  have hmiss : ∀ (R : List Token),
      suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  simp only [rufKopf_ohne, suffToks_nogeneric suff rest hr, hmiss] at ⊢
  have hs2 : suffGroesse suff + groesse (.variable a) ≤ n + 1 := by
    simp only [groesse] at ⊢
    omega
  have hF3 : 12 * (suffGroesse suff + groesse (.variable a) + 1) +
      suffGroesse suff ≤ F'' := by
    simp only [groesse, groesse_applySuff] at hs hF ⊢
    omega
  exact suff_rund n Rn suff (.variable a) rest F'' hs2 hgs hr hF3

-- Atomic `parsePrimary` outcomes (no children, no loops, no
-- follows inspected): unfold with successor fuel and let the
-- concrete head select its arm. (`fnref` is absent: it lives at
-- the unary level.)
theorem prim_lit : ∀ (m : Nat) (rest : List Token) (F : Nat),
    12 * (groesse (.lit m) + 1) + groesse (.lit m) ≤ F + 7 →
    parsePrimary F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
  intro m rest F hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary] at ⊢
theorem prim_gleit : ∀ (s : String) (rest : List Token) (F : Nat),
    ruhigGleit rest = true →
    12 * (groesse (.float s) + 1) + groesse (.float s) ≤ F + 7 →
    parsePrimary F (druckToks (.float s) ++ rest) = .ok (.float s, rest) := by
  intro s rest F hg hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary] at ⊢
  -- ⊢ : gleit arm selected (concrete head); inner match on `rest`
  -- (rounded or catch-all). Cases close it.
  cases rest with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | wort w =>
      simp only [ruhigGleit] at hg
      have hf := nichtWahr_falsch _ hg
      have ne := strNe_of w "rounded" hf
      simp only [List.cons.injEq, Token.wort.injEq, ne, false_and, imp_self, implies_true]
    | ident v => rfl
    | num n => rfl
    | float g => rfl
    | text t => rfl
    | doku t => rfl
    | zeichen z => rfl
    | ende => rfl
theorem prim_wahr : ∀ (rest : List Token) (F : Nat),
    12 * (groesse .tru + 1) + groesse .tru ≤ F + 7 →
    parsePrimary F (druckToks .tru ++ rest) = .ok (.tru, rest) := by
  intro rest F hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary] at ⊢
theorem prim_falsch : ∀ (rest : List Token) (F : Nat),
    12 * (groesse .fls + 1) + groesse .fls ≤ F + 7 →
    parsePrimary F (druckToks .fls ++ rest) = .ok (.fls, rest) := by
  intro rest F hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary] at ⊢
theorem prim_ergebnis : ∀ (rest : List Token) (F : Nat),
    12 * (groesse .res + 1) + groesse .res ≤ F + 7 →
    parsePrimary F (druckToks .res ++ rest) = .ok (.res, rest) := by
  intro rest F hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary] at ⊢
theorem prim_grund : ∀ (g f : String) (rest : List Token) (F : Nat),
    (!istKopfWort g) = true → (!istIntWort g) = true →
    (!istZuckerBreite g) = true → (!(strEq g "Self")) = true →
    ruhigSuff rest = true →
    12 * (groesse (.why g f) + 1) + groesse (.why g f) ≤ F + 7 →
    parsePrimary F (druckToks (.why g f) ++ rest) =
      .ok (.why g f, rest) := by
  intro g f rest F hkp hit hzuk hself hr hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hkp)]
  -- ⊢ : `parseKopf` on the head name.
  have hint : istIntWort g = false := nichtWahr_falsch _ hit
  have hzukf : istZuckerBreite g = false := nichtWahr_falsch _ hzuk
  have hselff : strEq g "Self" = false := nichtWahr_falsch _ hself
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseKopf, List.cons_append, nameText_nameTok] at ⊢
  -- ⊢ : `sammleSegmente` on `["::", name f]`, then the `[g, f]` arm.
  -- The `::` step is concrete; the tail stops by `ruhigSuff`.
  simp only [sammleSegmente, List.cons_append, nameText_nameTok] at ⊢
  simp only [List.nil_append] at ⊢
  rw [sammleSeg_stop [g, f] rest hr] at ⊢
  have hmiss : ∀ (R : List Token), rest ≠ .zeichen "(" :: R :=
    ruhigSuff_nopar rest hr
  have hgeneric : ∀ R, rest ≠ .zeichen "::" :: .zeichen "[" :: R := by
    simpa only [suffToks, List.nil_append] using suffToks_nogeneric [] rest hr
  simp only [rufKopf_ohne, hgeneric, hmiss, hint, hzukf, hselff,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte] at ⊢

-- `old` through `parsePrimary`: head word, place, close paren.
theorem prim_alt : ∀ (n : Nat) (Rn : R n)
    (x : SExpr) (rest : List Token) (F : Nat),
    groesse (.old x) ≤ n + 1 → gut (.old x) = true →
    ruhigSuff rest = true →
    12 * (groesse (.old x) + 1) + groesse (.old x) + 1 ≤ F →
    parsePrimary F (druckToks (.old x) ++ rest) = .ok (.old x, rest) := by
  intro n Rn x rest F hs hg hr hF
  simp only [gut] at hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary] at ⊢
  -- ⊢ : old arm → `parseOrt` → `)` close.
  have hx : groesse x ≤ n := by
    simp only [groesse] at hs
    omega
  have hxp : gutPlatz x = true := hg
  have hrp : ruhigSuff ([.zeichen ")"] ++ rest) = true := rfl
  have hFp : 12 * (groesse x + 1) + groesse x ≤ F' := by
    simp only [groesse] at hs hF ⊢
    omega
  have hO := ort_platz_all n Rn x ([.zeichen ")"] ++ rest) F' hx hxp hrp hFp
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
  simp only [hO, List.cons_append] at ⊢

-- `built` through `parsePrimary`: head word, then place or
-- pair arguments. `sizeof`/`lenof` take places (`parseOrt`);
-- `aligned` takes two whole expressions.
-- `sizeof`/`lenof` refuse bare type-word variables and accept
-- everything else (`_`-arm). From `gutPlatz` plus the exclusion.
theorem eingebaut_ein_ok : ∀ (w : String) (x : SExpr) (rest : List Token),
    gutPlatz x = true → (!istTypWortVar x) = true →
    (match x with
      | .variable s =>
        if istTypWort s = true then Except.error (w ++ " over a type")
        else .ok (SExpr.built w [x], rest)
      | _ => .ok (SExpr.built w [x], rest)) =
      .ok (SExpr.built w [x], rest) := by
  intro w x rest hpx htw
  have htwf : istTypWortVar x = false := nichtWahr_falsch _ htw
  cases x with
  | lit m => rfl
  | float s => rfl
  | tru => rfl
  | fls => rfl
  | «variable» s =>
    simp only [istTypWortVar] at htwf
    simp only [htwf, Bool.false_eq_true, ↓reduceIte]
  | field x f => rfl
  | index x i => rfl
  | arrow x f => rfl
  | un o x => rfl
  | bin o l r => rfl
  | call f xs => rfl
  | fnref f => rfl
  | built f xs => rfl
  | old x => rfl
  | res => rfl
  | why g f => rfl
  | ext xk xn xs => rfl
-- `built` through `parsePrimary`: head word, then place or
-- pair arguments. `sizeof`/`lenof` take places (`parseOrt`);
-- `aligned` takes two whole expressions. Singleton argument lists
-- unfold to the element (`args_einzeln`) before the place/expression
-- lemmas apply.

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here (filled in as the file grows).
-/

#print axioms Gabbro.Grammatik.Parser.strKlingt
