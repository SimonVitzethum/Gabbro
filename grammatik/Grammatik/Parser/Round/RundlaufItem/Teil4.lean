module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem item_atom (n : String) (t : STyp) (pub : Option (List SExpr)) (ord obs : Option String)
    (ht : TypGut t) (hg : AtomGut pub ord) : ItemBein (.atomT n t pub ord obs) := by
  intro rest F hF
  obtain ⟨hpub, hord⟩ := hg
  have hd : druckItem (.atomT n t pub ord obs) ++ rest = .wort "atomic" :: nameTok n :: .zeichen ":" ::
      (druckTyp t ++ (atomTail pub ord obs ++ rest)) := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp only [List.cons_append, List.nil_append, List.append_nil, List.append_assoc]
  have hlen : (druckItem (.atomT n t pub ord obs)).length = 3 + (druckTyp t).length +
      (atomTail pub ord obs).length := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp only [List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_right_cancel_iff, List.append_assoc, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hTF : TypFolge (atomTail pub ord obs ++ rest) := by
    have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" →
        w ≠ "rounded" → TypFolge (.wort w :: X) := by
      intro w X h1 h2 h3 h4
      have : strEq w "rounded" = false := by
        cases h : strEq w "rounded"
        · rfl
        · exact absurd ((strEq_eq _ _).mp h) h4
      refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
    rcases pub with _ | _ | ⟨p, ps⟩
    · rcases ord with _ | o
      · cases obs
        · exact ⟨(by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e),
            (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
        · exact gen "observed" _ (by decide) (by decide) (by decide) (by decide)
      · have ho := hord o rfl
        simp only [istOrdnung, Bool.or_eq_true, strEq_eq] at ho
        simp only [atomTail, List.nil_append, List.singleton_append, List.cons_append]
        rcases ho with ((h | h) | h) | h <;> subst h <;>
          exact gen _ _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "publishes" _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "publishes" _ (by decide) (by decide) (by decide) (by decide)
  have hT := parse_druckTyp t ht _ F' hTF (by simp only [fbT]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_atomic]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseAtomarTief, nimmWort, strEq_self, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, hT]
  have hR : parseAtomarRest (F'' + 1) (n, t, none, none, none) (atomTail pub ord obs ++ rest) =
      .ok ((n, t, pub, ord, obs), rest) := by
    have stepE : ∀ (G : Nat) acc, 1 ≤ G → parseAtomarRest G acc (.zeichen ";" :: rest) = .ok (acc, rest) := by
      intro G acc hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩; exact atomRest_ende G' acc rest
    have stepO : ∀ (G : Nat) (c : Option (List SExpr)) (d : Option String) (o : String) (R : List Token),
        1 ≤ G → parseAtomarRest G (n, t, c, d, none) (.wort "observed" :: .wort "by" :: nameTok o :: R) =
          parseAtomarRest (G - 1) (n, t, c, d, some o) R := by
      intro G c d o R hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      exact atomRest_obs G' n t c d none o R
    have stepD : ∀ (G : Nat) (c : Option (List SExpr)) (o : String) (R : List Token), istOrdnung o = true →
        1 ≤ G → parseAtomarRest G (n, t, c, none, none) (.wort o :: R) =
          parseAtomarRest (G - 1) (n, t, c, some o, none) R := by
      intro G c o R ho hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      exact atomRest_ord G' n t c none none o ho R
    have hlenT := hlen
    rcases pub with _ | _ | ⟨p, ps⟩
    · rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append]
        exact stepE _ _ (by omega)
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepO _ _ _ _ _ (by omega), stepE _ _ (by omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepD _ _ _ _ (hord o rfl) (by omega), stepE _ _ (by omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepD _ _ _ _ (hord o rfl) (by omega), stepO _ _ _ _ _ (by omega), stepE _ _ (by omega)]
    · rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepE _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepO _ _ _ _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
    · have hps := hpub (p :: ps) rfl
      rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
  simp only [hR]

/-! ### `lock` -/

/-- The clauses of a lock behind its rank. -/
def lockTail (h sh : Option SExpr) (m : Option String) (inv : Option SExpr) : List Token :=
  (match h with
    | some e => [.wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
    | none => []) ++
  (match sh with
    | some e => [.wort "shared", .wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
    | none => []) ++
  (match m with
    | some w => [.wort "masks", nameTok w]
    | none => []) ++
  (match inv with
    | some p => [.wort "invariant"] ++ druckToks p
    | none => []) ++ [.zeichen ";"]

theorem lockTail_ruhig (h sh : Option SExpr) (m : Option String) (inv : Option SExpr) (rest : List Token) :
    ruhig (lockTail h sh m inv ++ rest) = true ∧ ruhigSuff (lockTail h sh m inv ++ rest) = true ∧
      ruhigGleit (lockTail h sh m inv ++ rest) = true := by
  cases h <;> cases sh <;> cases m <;> cases inv <;> exact ⟨rfl, rfl, rfl⟩

theorem item_lock (n : String) (ps : List SExpr) (rk : SExpr) (h sh : Option SExpr) (m : Option String)
    (inv : Option SExpr) (hps : ∀ p ∈ ps, gut p = true) (hrk : gut rk = true)
    (hh : ∀ e, h = some e → gut e = true) (hs : ∀ e, sh = some e → gut e = true)
    (hi : ∀ e, inv = some e → gut e = true) : ItemBein (.lockT n ps rk h sh m inv) := by
  intro rest F hF
  have hd : druckItem (.lockT n ps rk h sh m inv) ++ rest = .wort "lock" :: nameTok n :: .wort "protects" ::
      .zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: .wort "rank" ::
        (druckToks rk ++ (lockTail h sh m inv ++ rest))) := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, lockTail]
  have hlen : (druckItem (.lockT n ps rk h sh m inv)).length = 6 + (druckPlaetze ps).length +
      (druckToks rk).length + (lockTail h sh m inv).length := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, lockTail, Nat.add_right_cancel_iff, Nat.reduceAdd] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  obtain ⟨h1, h2, h3⟩ := lockTail_ruhig h sh m inv rest
  have hRk := ausdruck rk hrk (lockTail h sh m inv ++ rest) F' h1 h2 h3 (by omega)
  have hPL := platzListe_rund ps hps (.wort "rank" :: (druckToks rk ++ (lockTail h sh m inv ++ rest))) F'
    (by omega)
  have hE : ∀ e, gut e = true → (druckToks e).length ≤ (lockTail h sh m inv).length →
      ∀ X, parseOr F' (druckToks e ++ .wort "ops" :: X) = .ok (e, .wort "ops" :: X) :=
    fun e he hl X => ausdruck e he _ F' rfl rfl rfl (by omega)
  have hI : ∀ p, gut p = true → (druckToks p).length ≤ (lockTail h sh m inv).length →
      parsePred F' (druckToks p ++ .zeichen ";" :: rest) = .ok (p, .zeichen ";" :: rest) :=
    fun p hp hl => pred_druck p hp _ ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [fb]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_lock]
  rcases h with _ | eh <;> rcases sh with _ | es <;> rcases m with _ | w <;> rcases inv with _ | ip
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, pure, Except.pure, fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, (hI ip (hi ip rfl) (by simp [lockTail]; omega)), fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, (hI ip (hi ip rfl) (by simp [lockTail]; omega)), fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega)), List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]

/-! ### `table`: numbers as text, fields, edges, group invariants, parts -/

theorem lex_zahl_allein (n : Nat) : lex (toString n) = .ok [.num n, .ende] := by
  unfold lex
  rw [show (toString n).toList = Nat.toDigits 10 n by rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]]
  have hd := toDigits_ziffern n
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, Nat.toDigits 10 n = c :: cs := by
    cases h : Nat.toDigits 10 n with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc : istZiffer c = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.1
  have hlen : (toString n).length = cs.length + 1 := by
    rw [← String.length_toList, Nat.toString_eq_ofList_toDigits, String.toList_ofList, hcs]; rfl
  rw [hlen, hcs, scan_ziffer_kopf false c cs _ hc]
  have hk : scanZahlKopf (c :: cs) = zahlBasis 10 (c :: cs) := by
    cases cs with
    | nil => exact scanZahlKopf_eins c
    | cons d ds =>
      have : istZiffer d = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.2.1
      exact scanZahlKopf_dez c d ds (ziffer_kein_praefix this)
  rw [hk]
  have hz : nimmZiffern (c :: cs) 10 = (n, true, []) := by
    unfold nimmZiffern
    have := nimmZiffern_go (c :: cs) [] 0 false (by rw [← hcs]; exact hd)
    simp only [List.append_nil] at this
    rw [this, ← hcs, Nat.ofDigitChars_ten_toDigits]
    simp only [nimmZiffern.go, Bool.false_or, Prod.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, Nat.toDigits_ne_nil, not_false_eq_true, and_self]
  simp only [zahlBasis, hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BEq.rfl, zahlWeiter, Except.map, scan]

theorem rohToks_zahl (n : Nat) : rohToks (toString n) = [.num n] := by
  unfold rohToks; rw [lex_zahl_allein]; rfl

/-- A bit position as the printer writes it: one number or one name. -/
def PosGut (s : String) : Prop := (∃ n : Nat, s = toString n) ∨ nameForm s = true

theorem bitpos_rund (p : String) (h : PosGut p) (R : List Token) :
    parseBitpos (rohToks p ++ R) = .ok (p, R) := by
  rcases h with ⟨n, rfl⟩ | h
  · rw [rohToks_zahl]; rfl
  · rw [rohToks_name p h]
    unfold nameTok
    split <;> simp only [parseBitpos, List.cons_append, List.nil_append, nameText_wort, zeigeTok, nameText_ident]

/-- A printable field. -/
def FeldGut (f : SFeld) : Prop :=
  TypGut f.ftyp ∧ (∀ p, f.pos = some p → PosGut p) ∧ (∀ e, f.wo = some e → gut e = true)

/-- The options of a field behind its type. -/
def feldRestToks (f : SFeld) : List Token :=
  (match f.pos with
    | some p => [.zeichen "@"] ++ rohToks p
    | none => []) ++
  (match f.bezug with
    | some n => [.wort "offset_into", nameTok n]
    | none => []) ++
  (match f.wo with
    | some p => [.wort "where"] ++ druckToks p
    | none => []) ++
  (if f.reserviert then [.wort "reserved"] else []) ++
  (if f.byOps then [.wort "by", .wort "ops"] else [])

theorem druckFeld_eq (f : SFeld) :
    druckFeld f = [nameTok f.fname, .zeichen ":"] ++ druckTyp f.ftyp ++ feldRestToks f := by
  simp only [druckFeld, List.cons_append, List.nil_append, List.append_assoc, feldRestToks, List.cons.injEq, List.append_cancel_left_eq, true_and]; rfl


/-- What follows a field: `,` or `}`. -/
def FeldEnde (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem feldRest_ende (f : Nat) (R : List Token) (hR : FeldEnde R) :
    parseFeldRest (f + 1) R = .ok ((none, none, none, false, false), R) := by
  rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseFeldRest, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]

theorem feldRest_by (f : Nat) (R X : List Token) (p b : Option String) (w : Option SExpr) (r y : Bool)
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "by" :: .wort "ops" :: R) = .ok ((p, b, w, r, true), X) := by
  simp [parseFeldRest, h, strEq_self, (by decide : strEq "by" "offset_into" = false),
    (by decide : strEq "by" "where" = false), (by decide : strEq "by" "reserved" = false),
    (by decide : strEq "ops" "ops" = true)]

theorem feldRest_res (f : Nat) (R X : List Token) (p b : Option String) (w : Option SExpr) (r y : Bool)
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "reserved" :: R) = .ok ((p, b, w, true, y), X) := by
  simp [parseFeldRest, h, strEq_self, (by decide : strEq "reserved" "offset_into" = false),
    (by decide : strEq "reserved" "where" = false)]

theorem feldRest_wo (f : Nat) (e : SExpr) (R X : List Token) (p b : Option String) (w : Option SExpr)
    (r y : Bool) (hP : parsePred f (druckToks e ++ R) = .ok (e, R))
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "where" :: (druckToks e ++ R)) = .ok ((p, b, some e, r, y), X) := by
  simp [parseFeldRest, h, hP, strEq_self, (by decide : strEq "where" "offset_into" = false)]

theorem feldRest_bezug (f : Nat) (n : String) (R X : List Token) (p b : Option String) (w : Option SExpr)
    (r y : Bool) (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "offset_into" :: nameTok n :: R) = .ok ((p, some n, w, r, y), X) := by
  by_cases hn : n = "Self"
  · subst hn
    have e : nameTok "Self" = .wort "Self" := by decide
    rw [e]; simp only [parseFeldRest, strEq_self, ↓reduceIte, zeigeTok, h]
  · have : strEq n "Self" = false := strEq_ne hn
    rcases nameTok_cases n with hh | hh <;> rw [hh] <;> simp only [parseFeldRest, strEq_self, ↓reduceIte, zeigeTok, this, Bool.false_eq_true, nameText_wort, h, nameText_ident]

theorem feldRest_pos (f : Nat) (q : String) (hq : PosGut q) (R X : List Token) (p b : Option String)
    (w : Option SExpr) (r y : Bool) (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.zeichen "@" :: (rohToks q ++ R)) = .ok ((some q, b, w, r, y), X) := by
  simp only [parseFeldRest, bitpos_rund q hq R, h]

theorem feldRest_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (feldRestToks fd).length + 60 ≤ F) :
    parseFeldRest F (feldRestToks fd ++ R) = .ok ((fd.pos, fd.bezug, fd.wo, fd.reserviert, fd.byOps), R) := by
  obtain ⟨-, hpos, hwo⟩ := hfd
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  simp only at hpos hwo ⊢
  have hPF : PredFolge R ∧ (∀ r, R ≠ .zeichen "," :: r → True) := by
    refine ⟨?_, fun _ _ => trivial⟩
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
  -- layer by layer, from the end
  have L5 : ∀ G, 2 ≤ G → parseFeldRest G ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R) =
      .ok ((none, none, none, false, byo), R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases byo
    · simpa using feldRest_ende (G' + 1) R hR
    · simpa using feldRest_by (G' + 1) R R none none none false false (feldRest_ende G' R hR)
  have L4 : ∀ G, 3 ≤ G → parseFeldRest G ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)) = .ok ((none, none, none, res, byo), R) := by
    intro G hG
    cases res
    · simpa using L5 G (by omega)
    · obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa using feldRest_res G' _ R none none none false byo (L5 G' (by omega))
  have hPF4 : PredFolge ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)) := by
    cases res <;> cases byo <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.nil_append,
      List.singleton_append, List.cons_append]
    · exact hPF.1
    all_goals exact ⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at e)⟩
  have hlen45 : ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)).length ≤ 3 + R.length := by
    cases res <;> cases byo <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Nat.le_add_left, List.cons_append, List.length_cons] <;> omega
  rcases pos with _ | q <;> rcases bezug with _ | n <;> rcases wo with _ | e
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    have := L4 F (by omega)
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have := feldRest_bezug (G + 0) n _ _ none none none res byo (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_bezug (G + 1) n _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have := feldRest_pos (G + 0) q (hpos q rfl) _ _ none none none res byo (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_pos (G + 1) q (hpos q rfl) _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have := feldRest_pos (G + 1) q (hpos q rfl) _ _ none (some n) none res byo (feldRest_bezug (G + 0) n _ _ none none none res byo (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 3 := ⟨F - 3, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_pos (G + 2) q (hpos q rfl) _ _ none (some n) (some e) res byo (feldRest_bezug (G + 1) n _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega))))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this


theorem feldRest_typFolge (fd : SFeld) (R : List Token) (hR : FeldEnde R) :
    TypFolge (feldRestToks fd ++ R) := by
  have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" →
      w ≠ "rounded" → TypFolge (.wort w :: X) := by
    intro w X h1 h2 h3 h4
    have : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) h4
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  rcases pos with _ | q
  · rcases bezug with _ | n
    · rcases wo with _ | e
      · cases res
        · cases byo
          · simp only [feldRestToks, ite_false, Bool.false_eq_true, List.nil_append]
            rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
              exact ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
                (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
          · exact gen "by" _ (by decide) (by decide) (by decide) (by decide)
        · exact gen "reserved" _ (by decide) (by decide) (by decide) (by decide)
      · exact gen "where" _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "offset_into" _ (by decide) (by decide) (by decide) (by decide)
  · exact ⟨(by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e),
      (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩

theorem feld_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (druckFeld fd).length + 61 ≤ F) : parseFeld F (druckFeld fd ++ R) = .ok (fd, R) := by
  rw [druckFeld_eq] at hF ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hT := parse_druckTyp fd.ftyp hfd.1 (feldRestToks fd ++ R) F' (feldRest_typFolge fd R hR)
    (by simp only [fbT]; omega)
  have hRe := feldRest_rund fd hfd R hR F' (by omega)
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  simp only [parseFeld, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hRe]

theorem feldKopf (fd : SFeld) (X : List Token) : ∃ ts, druckFeld fd ++ X = nameTok fd.fname :: ts := by
  rw [druckFeld_eq]; exact ⟨_, rfl⟩

end Gabbro.Grammatik.Parser
