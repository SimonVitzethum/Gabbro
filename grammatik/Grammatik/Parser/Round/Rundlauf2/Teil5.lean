module

public import Grammatik.Parser.Round.Rundlauf2.Teil5a
public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- The `un` legs from the induction hypothesis, generalised
-- over the prefix spelling: atoms take the primary leg (via
-- `primFrei_of_atom`), parenthesised children the `parseOr` leg
-- with `)` follow. Returns the seven generalised legs (no
-- primary: `primFrei` is false for `un`).
theorem turm_un : ∀ (n : Nat), RKern n →
    ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    groesse (.un o x) ≤ n + 1 → gutKern x = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
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
  intro n rkn o x rest hop hs hgx hr hrs hrg
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hxn : groesse x ≤ n := by omega
  cases hat : istAtom x with
  | true =>
    have hpf : primFrei x = true := primFrei_of_atom x hat hgx
    have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
        parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
      intro G hG
      exact rPr x rest G hxn hgx hpf hrs hrg hG
    exact kern_un_atom_turm o x rest hop hat hr hPx
  | false =>
    have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
        parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
          .ok (x, [.zeichen ")"] ++ rest) := by
      intro G hG
      exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
        (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
    exact kern_un_paren_turm o x rest hop hat hr hOx

-- The `bin "+"` legs from the binary-inner invariant: a thin
-- wrapper adapting `BKern n` to the leg shape `kern_bin_turm`
-- takes. Returns the eight generalised legs.
theorem turm_bin : ∀ (n : Nat), BKern n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "+" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
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
  intro n bkn l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bkn l r rest G hsum hl hr2 hG
  exact kern_bin_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "*"` legs from the star invariant: word for word
-- the `+` wrapper with the spelling swapped.
theorem turm_bin_star : ∀ (n : Nat), BKernStar n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "*" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
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
  intro n bStar l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bStar l r rest G hsum hl hr2 hG
  exact kern_bin_star_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "||"` legs from the or invariant: word for word
-- the `*` wrapper with the spelling swapped.
theorem turm_bin_or : ∀ (n : Nat), BKernOr n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "||" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest)) := by
  intro n bOr l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bOr l r rest G hsum hl hr2 hG
  exact kern_bin_or_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "&&"` legs from the and invariant: word for word
-- the `||` wrapper with the spelling swapped.
theorem turm_bin_and : ∀ (n : Nat), BKernAnd n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "&&" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest)) := by
  intro n bAnd l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bAnd l r rest G hsum hl hr2 hG
  exact kern_bin_and_turm l r rest hl hr2 hrr hrs hrg hB

end Gabbro.Grammatik.Parser
