module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem gut_of_gutCmp : ∀ (e : SExpr), gutCmp e = true → gut e = true := by
  intro e hg
  simp only [gutCmp, Bool.or_eq_true] at hg
  obtain hker | hnew := hg
  · exact gut_of_gutKern e hker
  · cases e with
    | lit m => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | float s => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | tru => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | fls => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | bin o l r =>
      simp only [cmpNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_cmp o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutKern l hl, gut_of_gutKern r hr2⟩
    | field x f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | old x => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | res => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [cmpNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [cmpNeu, Bool.false_eq_true] at hnew

theorem gut_of_gutBit : ∀ (e : SExpr), gutBit e = true → gut e = true := by
  intro e hg
  simp only [gutBit, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact gut_of_gutCmp e hold
  · cases e with
    | lit m => simp only [bitNeu, Bool.false_eq_true] at hnew
    | float s => simp only [bitNeu, Bool.false_eq_true] at hnew
    | tru => simp only [bitNeu, Bool.false_eq_true] at hnew
    | fls => simp only [bitNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [bitNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [bitNeu, Bool.false_eq_true] at hnew
    | bin o l r =>
      simp only [bitNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_bit o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutCmp l hl, gut_of_gutCmp r hr2⟩
    | field x f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [bitNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [bitNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [bitNeu, Bool.false_eq_true] at hnew
    | old x => simp only [bitNeu, Bool.false_eq_true] at hnew
    | res => simp only [bitNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [bitNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [bitNeu, Bool.false_eq_true] at hnew

theorem gut_of_gutAM : ∀ (e : SExpr), gutAM e = true → gut e = true := by
  intro e hg
  simp only [gutAM, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · obtain hold2 | hadd := hold
    · exact gut_of_gutBit e hold2
    · cases e with
      | lit m => simp only [addNeu, Bool.false_eq_true] at hadd
      | float s => simp only [addNeu, Bool.false_eq_true] at hadd
      | tru => simp only [addNeu, Bool.false_eq_true] at hadd
      | fls => simp only [addNeu, Bool.false_eq_true] at hadd
      | «variable» s => simp only [addNeu, Bool.false_eq_true] at hadd
      | un o x => simp only [addNeu, Bool.false_eq_true] at hadd
      | bin o l r =>
        simp only [addNeu, Bool.and_eq_true, and_assoc] at hadd
        obtain ⟨hop, hl, hr2⟩ := hadd
        have hbin := gutOpBin_of_add o hop
        simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
        exact ⟨hbin, gut_of_gutBit l hl, gut_of_gutBit r hr2⟩
      | field x f => simp only [addNeu, Bool.false_eq_true] at hadd
      | index x i => simp only [addNeu, Bool.false_eq_true] at hadd
      | arrow x f => simp only [addNeu, Bool.false_eq_true] at hadd
      | call f xs => simp only [addNeu, Bool.false_eq_true] at hadd
      | fnref f => simp only [addNeu, Bool.false_eq_true] at hadd
      | built f xs => simp only [addNeu, Bool.false_eq_true] at hadd
      | old x => simp only [addNeu, Bool.false_eq_true] at hadd
      | res => simp only [addNeu, Bool.false_eq_true] at hadd
      | why g f => simp only [addNeu, Bool.false_eq_true] at hadd
      | ext xk xn xs => simp only [addNeu, Bool.false_eq_true] at hadd
  · cases e with
    | lit m => simp only [mulNeu, Bool.false_eq_true] at hnew
    | float s => simp only [mulNeu, Bool.false_eq_true] at hnew
    | tru => simp only [mulNeu, Bool.false_eq_true] at hnew
    | fls => simp only [mulNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [mulNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [mulNeu, Bool.false_eq_true] at hnew
    | bin o l r =>
      simp only [mulNeu, Bool.and_eq_true, and_assoc] at hnew
      obtain ⟨hop, hl, hr2⟩ := hnew
      have hbin := gutOpBin_of_mul o hop
      simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      exact ⟨hbin, gut_of_gutBit l hl, gut_of_gutBit r hr2⟩
    | field x f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [mulNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [mulNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [mulNeu, Bool.false_eq_true] at hnew
    | old x => simp only [mulNeu, Bool.false_eq_true] at hnew
    | res => simp only [mulNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [mulNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [mulNeu, Bool.false_eq_true] at hnew

-- LEVEL CALLS (calls with argument lists).
--
-- Lists of level-3 trees (computable, so `decide` witnesses
-- keep working).
def gutListeAM : List SExpr → Bool
  | [] => true
  | x :: xs => gutAM x && gutListeAM xs
theorem gutListeAM_Kopf : ∀ (x : SExpr) (xs : List SExpr),
    gutListeAM (x :: xs) = true → gutAM x = true := by
  intro x xs h
  simp only [gutListeAM, Bool.and_eq_true] at h
  exact h.1
theorem gutListeAM_Schwanz : ∀ (x : SExpr) (xs : List SExpr),
    gutListeAM (x :: xs) = true → gutListeAM xs = true := by
  intro x xs h
  simp only [gutListeAM, Bool.and_eq_true] at h
  exact h.2
-- A `gutListeAM` list is a `gutListe` (via the bridge) and
-- every element has legs.
theorem gutListe_of_gutListeAM : ∀ (xs : List SExpr),
    gutListeAM xs = true → gutListe xs = true := by
  intro xs h
  induction xs with
  | nil => rfl
  | cons x zs ih =>
    simp only [gutListeAM, Bool.and_eq_true] at h
    obtain ⟨hx, hzs⟩ := h
    simp only [gutListe, Bool.and_eq_true]
    exact ⟨gut_of_gutAM x hx, ih hzs⟩
theorem legsListeAM : ∀ (xs : List SExpr),
    gutListeAM xs = true → ∀ (x : SExpr), x ∈ xs → Legs x := by
  intro xs h x hm
  induction xs with
  | nil => simp only [List.not_mem_nil] at hm
  | cons y ys ih =>
    simp only [gutListeAM, Bool.and_eq_true] at h
    obtain ⟨hy, hys⟩ := h
    simp only [List.mem_cons] at hm
    obtain rfl | hm2 := hm
    · exact legsAM x hy
    · exact ih hys hm2

-- One argument through `parseArg`: mirror of lane 161's
-- `arg_einzeln`, with the `Legs` Or-leg instead of `R n` and
-- `keinDP_tree` instantiated at the tree's own size (no size
-- bound needed anywhere).
theorem arg_legs : ∀ (x : SExpr) (sep : Token) (S : List Token) (F : Nat),
    Legs x → gut x = true →
    (sep = .zeichen "," ∨ sep = .zeichen ")") →
    12 * (groesse x + 1) + groesse x + 9 ≤ F →
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  intro x sep S F hL hxg hsep hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
    obtain ⟨a, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
    rw [hxb] at hcon
    simp only [List.cons_append] at hcon
    injection hcon with _ ht
    cases hR : R2 with
    | nil =>
      rw [hR] at ht
      simp only [List.nil_append, List.cons_append] at ht
      injection ht with hsep2 _
      cases hsep with
      | inl h =>
        subst h
        simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
      | inr h =>
        subst h
        simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp only [hxb, hR, List.mem_cons, true_or, or_true]
      have hne2 := keinDP_tree (groesse x) x (Nat.le_refl _) hxg b hbmem
      exact hne2 hb
  simp only [parseArg] at ⊢
  have hr1 : ruhig ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr2 : ruhigSuff ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr3 : ruhigGleit ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hFr : 12 * (groesse x + 1) + groesse x + 8 ≤ F' := by omega
  have hOr := hL.2.2.2.2.2.2.2 ([sep] ++ S) F' hr1 hr2 hr3 hFr
  simpa only [List.append_assoc] using hOr

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
