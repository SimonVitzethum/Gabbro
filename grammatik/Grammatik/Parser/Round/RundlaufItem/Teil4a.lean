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


end Gabbro.Grammatik.Parser
