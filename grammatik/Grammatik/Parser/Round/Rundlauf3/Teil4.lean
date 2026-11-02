module

public import Grammatik.Parser.Round.Rundlauf3.Teil4a

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- Whole argument lists through `parseArgs`: mirror of lane
-- 161's `args_rund` (head by `toksKopf` at the tree's own
-- size, element by `arg_legs`, tail by list induction).
theorem args_legs : ∀ (xs : List SExpr) (rest : List Token) (F : Nat),
    gutListeAM xs = true →
    12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) =
      .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro rest F hs hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append,
      List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hF
    cases zs with
    | nil =>
      have hx : gutAM x = true := gutListeAM_Kopf x [] hs
      have hxg : gut x = true := gut_of_gutAM x hx
      have hLx : Legs x := legsAM x hx
      have hkop : ∀ (a : Token) (R : List Token),
          druckToks x = a :: R → a ≠ .zeichen ")" :=
        toksKopf (groesse x) x (Nat.le_refl _) hxg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_einzeln] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_legs x (.zeichen ")") rest F' hLx hxg
        (Or.inr rfl) (by simp only [groesseListe] at hF ⊢; omega)
      simp only [harg, List.cons_append] at ⊢
      rfl
    | cons y ys =>
      have hx : gutAM x = true := gutListeAM_Kopf x (y :: ys) hs
      have hxg : gut x = true := gut_of_gutAM x hx
      have hLx : Legs x := legsAM x hx
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_cons] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hkop : ∀ (a : Token) (R : List Token),
            druckToks x = a :: R → a ≠ .zeichen ")" :=
          toksKopf (groesse x) x (Nat.le_refl _) hxg
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_legs x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hLx hxg (Or.inl rfl) (by simp only [groesseListe] at hF ⊢; omega)
      have hzs : gutListeAM (y :: ys) =
          true := gutListeAM_Schwanz x (y :: ys) hs
      have hxp := groesse_pos x
      have htail := ihzs rest F' hzs
        (by simp only [groesseListe] at hF ⊢; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append] at ⊢

-- Calls through `parsePrimary`: mirror of lane 161's
-- `prim_ruf` (head word, `parseKopf` ruf arm, arguments via
-- `args_legs`).
theorem prim_ruf_legs : ∀ (f : String) (xs : List SExpr)
    (rest : List Token) (F : Nat),
    (!istKopfWort f) = true → gutListeAM xs = true →
    ruhigSuff rest = true →
    12 * (groesse (.call f xs) + 1) + groesse (.call f xs) + 1 ≤ F →
    parsePrimary F (druckToks (.call f xs) ++ rest) =
      .ok (.call f xs, rest) := by
  intro f xs rest F hf hxs hrs hF
  have hkaf : istKeinPlatz f = false := kopf_kp (nichtWahr_falsch _ hf)
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hf)]
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [kopf_ruf_head] at ⊢
  have hgl : 12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F'' := by
    have hs : groesse (.call f xs) = groesseListe xs + 1 := rfl
    omega
  have hA := args_legs xs rest F'' hxs hgl
  simp only [List.append_assoc] at hA ⊢
  simp only [List.nil_append, hA] at ⊢

-- Call legs from head lawfulness and argument legs: the
-- `parsePrimary` leg above, the `parseUnary` fall-through on
-- the `ident` head (no prefix arm fires), then `tower_up`.
-- (`ruf` is an atom, so no parenthesised case.)
theorem rufLegs : ∀ (f : String) (xs : List SExpr),
    (!istKopfWort f) = true → gutListeAM xs = true →
    Legs (.call f xs) := by
  intro f xs hf hxs
  have hsize : groesse (.call f xs) = groesseListe xs + 1 := rfl
  have hP : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.call f xs) + 1) + groesse (.call f xs) + 1 ≤ G →
      parsePrimary G (druckToks (.call f xs) ++ rest') =
        .ok (.call f xs, rest') := by
    intro rest' G hrs hrg hG
    exact prim_ruf_legs f xs rest' G hf hxs hrs hG
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.call f xs) + 1) + groesse (.call f xs) + 2 ≤ G →
      parseUnary G (druckToks (.call f xs) ++ rest') =
        .ok (.call f xs, rest') := by
    intro rest' G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' hrs hrg (by omega)
    have hd : druckToks (.call f xs) =
        [nameTok f] ++ (([.zeichen "("] ++ druckToksListe xs) ++
          [.zeichen ")"]) := by
      simp only [druckToks, List.cons_append, List.nil_append]
    simp only [hd, List.append_assoc] at hP' ⊢
    -- The name head fires no prefix arm: fall through to
    -- `parsePrimary`.
    have hU' : parseUnary (G' + 1) ([nameTok f] ++
        (([.zeichen "("] ++ druckToksListe xs) ++
          ([.zeichen ")"] ++ rest'))) =
        .ok (.call f xs, rest') := by
      simp only [List.cons_append, List.nil_append] at hP' ⊢
      rw [parseUnary_nameTok, hP']
    exact hU'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hrs hrg hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.call f xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- The new call layer: calls over level-3 argument lists.
def rufNeu : SExpr → Bool
  | .call f xs => !istKopfWort f && gutListeAM xs
  | _ => false

-- Level-4 predicate: level 3 plus one call layer.
def gutRuf (e : SExpr) : Bool := gutAM e || rufNeu e

-- Every level-4 tree has legs: level-3 trees by `legsAM`, new
-- calls by `rufLegs` over level-3 argument legs.
theorem legsRuf : ∀ (e : SExpr), gutRuf e = true → Legs e := by
  intro e hg
  simp only [gutRuf, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact legsAM e hold
  · cases e with
    | lit m => simp only [rufNeu, Bool.false_eq_true] at hnew
    | float s => simp only [rufNeu, Bool.false_eq_true] at hnew
    | tru => simp only [rufNeu, Bool.false_eq_true] at hnew
    | fls => simp only [rufNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [rufNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [rufNeu, Bool.false_eq_true] at hnew
    | bin o l r => simp only [rufNeu, Bool.false_eq_true] at hnew
    | field x f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [rufNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | call f xs =>
      simp only [rufNeu, Bool.and_eq_true] at hnew
      obtain ⟨hf, hxs⟩ := hnew
      exact rufLegs f xs hf hxs
    | fnref f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [rufNeu, Bool.false_eq_true] at hnew
    | old x => simp only [rufNeu, Bool.false_eq_true] at hnew
    | res => simp only [rufNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [rufNeu, Bool.false_eq_true] at hnew

end Gabbro.Grammatik.Parser
