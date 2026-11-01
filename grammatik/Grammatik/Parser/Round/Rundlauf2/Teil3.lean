module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem turm_falsch : ∀ (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 1 ≤ G →
      parsePrimary G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 2 ≤ G →
      parseUnary G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 3 ≤ G →
      parseMul G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 4 ≤ G →
      parseAdd G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 5 ≤ G →
      parseBit G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 6 ≤ G →
      parseCmp G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 7 ≤ G →
      parseAnd G (druckToks .fls ++ rest) = .ok (.fls, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .fls + 1) + groesse .fls + 8 ≤ G →
      parseOr G (druckToks .fls ++ rest) = .ok (.fls, rest)) := by
  intro rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse .fls + 1) + groesse .fls + 1 ≤ G →
      parsePrimary G (druckToks .fls ++ rest) = .ok (.fls, rest) := by
    intro G hG
    exact prim_falsch rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse .fls + 1) + groesse .fls + 2 ≤ G →
      parseUnary G (druckToks .fls ++ rest) = .ok (.fls, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up .fls rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_var : ∀ (a : String) (rest : List Token),
    (!istKopfWort a) = true → ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
      parsePrimary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 2 ≤ G →
      parseUnary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 3 ≤ G →
      parseMul G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 4 ≤ G →
      parseAdd G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 5 ≤ G →
      parseBit G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 6 ≤ G →
      parseCmp G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 7 ≤ G →
      parseAnd G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 8 ≤ G →
      parseOr G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest)) := by
  intro a rest hka hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
      parsePrimary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest) := by
    intro G hG
    exact kern_prim_var a rest G hka hrs (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.variable a) + 1) + groesse (.variable a) + 2 ≤ G →
      parseUnary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    first | rw [parseUnary_nameTok] | simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up (.variable a) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- Standalone arm lemmas with WHOLE-SUBTERM middles (`M`)
-- and tails (`R`): callers align by canonicalising with
-- `append_assoc` (confluent), unification assigns whole
-- subterms, so association never enters unification. This
-- isolates all match-reduction risk in three tiny probes.
-- The prefix-operator arm generalised over the spelling:
-- `!`, `-` and `~` all run `parsePrimary` identically.
theorem bang_arm_gen : ∀ (G' : Nat) (M R : List Token) (o : String) (v : SExpr),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    parsePrimary G' M = .ok (v, R) →
    ((∀ T, M ≠ .zeichen "(" :: T) ∨ istLit v = false) →
    parseUnary (G' + 1) ([.zeichen o] ++ M) = .ok (.un o v, R) := by
  intro G' M R o v hop h hl
  obtain rfl | rfl | rfl := un_is_pre o hop
  · simp only [List.cons_append, List.nil_append] at h ⊢
    simp only [parseUnary, h] at ⊢
  · simp only [List.cons_append, List.nil_append] at h ⊢
    cases M with
    | nil => cases G' <;> simp only [parsePrimary, reduceCtorEq] at h
    | cons t T =>
      by_cases ht : t = .zeichen "("
      · subst ht
        have hl' : istLit v = false := by
          rcases hl with hl | hl
          · exact absurd rfl (hl T)
          · exact hl
        simp only [parseUnary, h, hl', Bool.false_eq_true, ite_false]
      · simp only [parseUnary]
        split <;> simp_all
  · simp only [List.cons_append, List.nil_append] at h ⊢
    simp only [parseUnary, h] at ⊢

/-- `-(n)`: the negation of a numeral (`.un "-()"`), the parenthesised arm of `-`. -/
theorem negklammer_arm : ∀ (G' : Nat) (M R : List Token) (n : Nat),
    parsePrimary G' ([.zeichen "("] ++ M) = .ok (.lit n, R) →
    parseUnary (G' + 1) ([.zeichen "-", .zeichen "("] ++ M) = .ok (.un "-()" (.lit n), R) := by
  intro G' M R n h
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp only [parseUnary, h, istLit, ite_true]

theorem paren_arm : ∀ (G'' : Nat) (M R : List Token) (v : SExpr),
    parseOr G'' M = .ok (v, [.zeichen ")"] ++ R) →
    parsePrimary (G'' + 1) ([.zeichen "("] ++ M) =
      .ok (v, R) := by
  intro G'' M R v h
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp only [parsePrimary, h] at ⊢

-- A parenthesised tree falls through `parseUnary` to
-- `parsePrimary` (`(` is no prefix operator). The catch-all arm
-- needs the four string inequalities spelled out (same pattern
-- as lane 161's `stopSuffix`: `simp` prunes the match arms from
-- the `≠` facts).
theorem un_paren_fall : ∀ (G' : Nat) (M R : List Token) (v : SExpr),
    parsePrimary G' ([.zeichen "("] ++ M) = .ok (v, R) →
    parseUnary (G' + 1) ([.zeichen "("] ++ M) = .ok (v, R) := by
  intro G' M R v h
  have n1 : ("(" : String) ≠ "!" := by decide
  have n2 : ("(" : String) ≠ "-" := by decide
  have n3 : ("(" : String) ≠ "~" := by decide
  have n4 : ("(" : String) ≠ "&" := by decide
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp only [parseUnary, List.cons.injEq, Token.zeichen.injEq, n1, false_and, imp_self, implies_true, n2, n3,
  n4, h] at ⊢

-- The `un` tower for ATOM children, generalised over the
-- prefix spelling: the `parsePrimary` leg (same follow)
-- through the prefix arm, then `tower_up`. Split from the
-- joint tower because the primary leg is provable only for
-- atoms (`parsePrimary` fails on operator heads). No
-- `parsePrimary` component (`primFrei` is false for `un`).
theorem kern_un_atom_turm : ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    istAtom x = true → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
      parsePrimary G (druckToks x ++ rest) = .ok (x, rest)) →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro o x rest hop hat hr hPx
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) =
        .ok (.un o x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un o x) =
        [.zeichen o] ++ druckToks x := by
      simp only [druckToks, un_ne_klammer _ hop, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
    have hP' := hPx G' (by omega)
    simp only [hd, List.append_assoc] at ⊢
    exact bang_arm_gen _ _ _ _ _ hop hP' (atom_bed x rest)
  have hup := tower_up (.un o x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `un` tower for PARENTHESISED (non-atom) children: the
-- `parseOr` leg (`)` follow) through the prefix arm into the
-- `(` arm, then `tower_up`.
theorem kern_un_paren_turm : ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    istAtom x = false → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
      parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
        .ok (x, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro o x rest hop hat hr hOx
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) =
        .ok (.un o x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un o x) = [.zeichen o] ++
        (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
      simp only [druckToks, un_ne_klammer _ hop, Bool.false_eq_true, ↓reduceIte, hat, List.cons_append,
  List.nil_append]
    have hF2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hO' := hOx G'' (by omega)
    have hPar := paren_arm _ _ _ _ hO'
    have hBang := bang_arm_gen _ _ _ _ _ hop hPar (Or.inr (nonatom_bed x hat))
    simp only [hd, List.append_assoc] at ⊢
    exact hBang
  have hup := tower_up (.un o x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "+"` tower from a binary-inner leg: the
-- `parsePrimary` leg runs the `(` arm over the inner parse, the
-- `parseUnary` leg falls through on `(`, then `tower_up`. Every
-- leg generalised over its own fuel.
theorem kern_bin_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    -- Inner token shape for `paren_arm`: `(` head, `l + r`
    -- body, `)` tail, all left-nested exactly as printed.
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    -- `hPar` and the goal differ by association only:
    -- canonicalise both, then they coincide.
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    -- Canonicalise both sides; the underscores let unification
    -- infer the middle and tail (the lemma holds for any tail).
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "+" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "*"` tower from a binary-inner leg: word for word
-- the `+` tower with the spelling swapped (no proof step
-- inspects the spelling -- the printer, the paren arm and the
-- fall-through are all spelling-blind).
theorem kern_bin_star_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
    simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "*" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

end Gabbro.Grammatik.Parser
