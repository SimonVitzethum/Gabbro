module

public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem sammleSeg_kette (suff : List SuffFrag) (hne : suff ≠ []) (segs : List String) (R : List Token) :
    sammleSegmente (suffToks suff ++ R) segs = (segs, suffToks suff ++ R) := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> rfl

theorem kette_nopar (suff : List SuffFrag) (hne : suff ≠ []) (R R2 : List Token) :
    suffToks suff ++ R ≠ .zeichen "(" :: R2 := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> simp only [suffToks, List.cons_append, ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, List.append_assoc, List.nil_append]

/-- Calls through a place through `parsePrimary` at token fuel. -/
theorem prim_methM (a : String) (suff : List SuffFrag) (xs : List SExpr) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hne : suff ≠ [])
    (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 6 * (druckToksListe xs).length + 40 ≤ F) :
    parsePrimary F (druckToks (.ext .call [] (applySuff (.variable a) suff :: xs)) ++ rest) =
      .ok (.ext .call [] (applySuff (.variable a) suff :: xs), rest) := by
  have hle := suffLen_le suff
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druck_ruf, druckToks_applySuff]
  simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  simp only [parseKopf, nameText_nameTok]
  rw [sammleSeg_kette suff hne]
  have hmiss : ∀ (R2 : List Token), suffToks suff ++ (.zeichen "(" :: (druckToksListe xs ++
      (.zeichen ")" :: rest))) ≠ .zeichen "(" :: R2 := kette_nopar suff hne _
  simp only [hmiss]
  rw [suffWeiterM suff (.variable a) _ F'' hs (by omega)]
  obtain ⟨G, hG⟩ : ∃ G, F'' - suff.length = G + 1 := ⟨F'' - suff.length - 1, by omega⟩
  rw [hG, suff_ruf G _ _ (istVar_kette a suff hne)]
  have hA := argsM xs rest G hxs (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hA
  rw [hA]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  exact stopSuffix G' _ rest hr

/-! ### `old`, `sizeof`, `lenof`, `aligned` -/

theorem prim_altM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 31 ≤ F) :
    parsePrimary F (druckToks (.old (applySuff (.variable a) suff)) ++ rest) =
      .ok (.old (applySuff (.variable a) suff), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary]
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F' hka hs (hrs_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
  simp only [hO, List.cons_append]

theorem prim_emb1M (w : String) (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hw : w = "sizeof" ∨ w = "lenof") (hka : (!istKopfWort a) = true) (hs : SuffLegs suff)
    (hp : gutPlatz (applySuff (.variable a) suff) = true)
    (htw : (!istTypWortVar (applySuff (.variable a) suff)) = true)
    (hr : ruhigSuff rest = true) (hF : 6 * (suffToks suff).length + 32 ≤ F) :
    parsePrimary F (druckToks (.built w [applySuff (.variable a) suff]) ++ rest) =
      .ok (.built w [applySuff (.variable a) suff], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F'' hka hs (hrs_paren rest) (by omega)
  obtain rfl | rfl := hw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "sizeof" _ rest hp htw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "lenof" _ rest hp htw

theorem prim_alignedM (m : Nat) (a b : SExpr) (rest : List Token) (F : Nat)
    (hLa : LegsB m a) (hLb : LegsB m b)
    (hF : m + 10 ≤ F) :
    parsePrimary F (druckToks (.built "aligned" [a, b]) ++ rest) =
      .ok (.built "aligned" [a, b], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, args_cons, args_einzeln, List.cons_append, parsePrimary]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseEingebaut_zwei]
  have hkomma : ruhig ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true := rfl
  have hskomma : ruhigSuff ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hgkomma : ruhigGleit ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hOa := hLa.2.2.2.2.2.2.2 ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) F''
    hkomma hskomma hgkomma (by omega)
  have hOb := hLb.2.2.2.2.2.2.2 ([.zeichen ")"] ++ rest) F''
    (hr_paren rest) (hrs_paren rest) (hrg_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOa hOb
  simp only [hOa, hOb]

/-! ### The joint induction at token fuel -/

theorem legs_tok_n : ∀ (n : Nat) (e : SExpr), groesse e ≤ n → gut e = true → LegsB (fb e) e := by
  intro n
  induction n with
  | zero =>
    intro e hs _
    have := groesse_pos e
    omega
  | succ n ih =>
    intro e hs hg
    -- Leaves: the size-bound legs (`Legs`, bound 25) raised to the token bound.
    have blatt : Legs e → groesse e = 1 → LegsB (fb e) e := by
      intro hL h1
      apply LegsB_mono _ (legsB_of_legs e hL)
      simp only [fb, h1]
      omega
    -- Places: decompose, payload legs from the hypothesis, the primary leg by `prim_platzM`.
    have platz : gutPlatz e = true → LegsB (fb e) e := by
      intro hp
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) e hs hp
      have hsl : SuffLegs suff := by
        intro i hi
        obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
        exact ih i (by omega) hi'
      have hd : druckToks (applySuff (.variable a) suff) = [nameTok a] ++ suffToks suff := by
        rw [druckToks_applySuff]; rfl
      apply legsB_kopf _ (nameTok a) _ (nameTok_form a) hd
      intro rest' G hrs _ hG
      apply prim_platzM a suff rest' G hka hsl hrs
      simp only [fb, hd, List.length_append, List.length_singleton] at hG
      omega
    cases e with
    | lit m => exact blatt (legsKern _ rfl) rfl
    | float s => exact blatt (legsKern _ rfl) rfl
    | tru => exact blatt (legsKern _ rfl) rfl
    | fls => exact blatt (legsKern _ rfl) rfl
    | «variable» s => exact blatt (legsKern _ hg) rfl
    | field x f => exact platz hg
    | index x i => exact platz hg
    | arrow x f => exact platz hg
    | un o x =>
      simp only [gut, Bool.or_eq_true, Bool.and_eq_true] at hg
      rcases hg with hg | ⟨ho, hl⟩
      · have hx : groesse x ≤ n := by simp only [groesse] at hs; omega
        have Hx := ih x hx hg.2
        have hne := un_ne_klammer o hg.1
        cases hat : istAtom x with
        | true =>
          apply LegsB_mono _ (unLegsM_atom _ o x hg.1 hat Hx)
          simp only [fb, druckToks, hne, hat, ite_true, Bool.false_eq_true, ite_false, List.length_append,
            List.length_singleton]
          omega
        | false =>
          apply LegsB_mono _ (unLegsM_klammer _ o x hg.1 hat Hx)
          simp only [fb, druckToks, hne, hat, Bool.false_eq_true, ite_false, List.length_append,
            List.length_singleton]
          omega
      · have := strKlingt o "-()" ho
        subst this
        cases x with
        | lit k =>
          have hk : groesse (SExpr.lit k) ≤ n := by simp only [groesse] at hs ⊢; omega
          apply LegsB_mono _ (negLitLegsM _ k (ih (.lit k) hk rfl))
          simp only [fb, druckToks, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, Nat.reduceAdd, ho,
  ↓reduceIte, List.cons_append, List.nil_append, Nat.reduceMul, Nat.reduceLeDiff]
        | _ => simp only [istLit, Bool.false_eq_true] at hl
    | bin o l r =>
      simp only [gut, Bool.and_eq_true] at hg
      have hl : groesse l ≤ n := by simp only [groesse] at hs; omega
      have hr : groesse r ≤ n := by simp only [groesse] at hs; omega
      have Hl := LegsB_mono (Nat.le_max_left (fb l) (fb r)) (ih l hl hg.1.2)
      have Hr := LegsB_mono (Nat.le_max_right (fb l) (fb r)) (ih r hr hg.2)
      apply LegsB_mono _ (binLegsM _ o l r hg.1.1 Hl Hr)
      simp only [fb, druckToks, List.length_append, List.length_singleton]
      omega
    | call f xs =>
      simp only [gut, Bool.and_eq_true] at hg
      have hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true := by
        intro x hx
        have hgx := gutListe_mem xs x hx hg.2
        have hsx : groesse x ≤ n := by
          have := groesse_mem_le xs x hx
          simp only [groesse] at hs; omega
        exact ⟨ih x hsx hgx, hgx⟩
      have hd : druckToks (.call f xs) = [nameTok f] ++
          ([.zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]) := by
        simp only [druckToks, List.cons_append, List.nil_append]
      apply legsB_kopf _ (nameTok f) _ (nameTok_form f) hd
      intro rest' G _ _ hG
      apply prim_rufM f xs rest' G hg.1 hxs
      simp only [fb, hd, List.length_append, List.length_singleton] at hG
      omega
    | fnref p => exact blatt (fnwertLegs p) rfl
    | built w xs =>
      rcases gut_built_faelle w xs hg with ⟨x, hw, rfl, hp, htw⟩ | ⟨a, b, rfl, rfl, ha, hb⟩
      · obtain ⟨c, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) x
          (by simp only [groesse, groesseListe] at hs; omega) hp
        have hsl : SuffLegs suff := by
          intro i hi
          obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
          have : groesse (applySuff (.variable c) suff) ≤ n := by
            simp only [groesse, groesseListe] at hs; omega
          rw [groesse_applySuff] at this
          exact ih i (by simp only [groesse] at this; omega) hi'
        have hd : druckToks (.built w [applySuff (.variable c) suff]) = [.wort w] ++
            ([.zeichen "("] ++ druckToksListe [applySuff (.variable c) suff] ++
              [.zeichen ")"]) := by
          simp only [druckToks, List.cons_append, List.nil_append]
        apply legsB_kopf _ (.wort w) _ (Or.inr ⟨w, rfl⟩) hd
        intro rest' G hrs _ hG
        apply prim_emb1M w c suff rest' G hw hka hsl hp htw hrs
        simp only [fb, hd, args_einzeln, druckToks_applySuff, List.length_append,
          List.length_singleton] at hG
        simp only [druckToks, List.length_singleton] at hG
        omega
      · have ha' : groesse a ≤ n := by simp only [groesse, groesseListe] at hs; omega
        have hb' : groesse b ≤ n := by simp only [groesse, groesseListe] at hs; omega
        have hd : druckToks (.built "aligned" [a, b]) = [.wort "aligned"] ++
            ([.zeichen "("] ++ druckToksListe [a, b] ++ [.zeichen ")"]) := by
          simp only [druckToks, List.cons_append, List.nil_append]
        apply legsB_kopf _ (.wort "aligned") _ (Or.inr ⟨_, rfl⟩) hd
        intro rest' G _ _ hG
        apply prim_alignedM (max (fb a) (fb b)) a b rest' G
          (LegsB_mono (Nat.le_max_left _ _) (ih a ha' ha))
          (LegsB_mono (Nat.le_max_right _ _) (ih b hb' hb))
        simp only [fb, hd, args_cons, args_einzeln, List.length_append,
          List.length_singleton] at hG ⊢
        omega
    | old x =>
      simp only [gut] at hg
      obtain ⟨c, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) x
        (by simp only [groesse] at hs; omega) hg
      have hsl : SuffLegs suff := by
        intro i hi
        obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
        exact ih i (by omega) hi'
      have hd : druckToks (.old (applySuff (.variable c) suff)) = [.wort "old"] ++
          ([.zeichen "("] ++ druckToks (applySuff (.variable c) suff) ++ [.zeichen ")"]) := by
        simp only [druckToks, List.cons_append, List.nil_append]
      apply legsB_kopf _ (.wort "old") _ (Or.inr ⟨_, rfl⟩) hd
      intro rest' G hrs _ hG
      apply prim_altM c suff rest' G hka hsl hrs
      simp only [fb, hd, druckToks_applySuff, List.length_append,
        List.length_singleton] at hG
      simp only [druckToks, List.length_singleton] at hG
      omega
    | res => exact blatt ergebnisLegs rfl
    | why g f =>
      simp only [gut, Bool.and_eq_true] at hg
      exact blatt (grundLegs g f hg.1.1.1 hg.1.1.2 hg.1.2 hg.2) rfl
    | ext k ns xs =>
      obtain ⟨rfl, rfl, c, ys, rfl, hp, hv, hys⟩ := gut_ruf_faelle k ns xs hg
      have hcs : groesse c ≤ n + 1 := by simp only [groesse, groesseListe] at hs; omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) c hcs hp
      have hne : suff ≠ [] := by rintro rfl; simp only [istVar, applySuff, Bool.true_eq_false] at hv
      have hsl : SuffLegs suff := by
        intro i hi
        obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
        have : groesse (applySuff (.variable a) suff) ≤ n := by
          simp only [groesse, groesseListe] at hs; omega
        rw [groesse_applySuff] at this
        exact ih i (by simp only [groesse] at this; omega) hi'
      have hxs : ∀ x ∈ ys, LegsB (fb x) x ∧ gut x = true := by
        intro x hx
        have hgx := gutListe_mem ys x hx hys
        have hsx : groesse x ≤ n := by
          have := groesse_mem_le ys x hx
          have := groesse_pos (applySuff (.variable a) suff)
          simp only [groesse, groesseListe] at hs; omega
        exact ⟨ih x hsx hgx, hgx⟩
      have hd : druckToks (.ext .call [] (applySuff (.variable a) suff :: ys)) = [nameTok a] ++
          (suffToks suff ++ ([.zeichen "("] ++ druckToksListe ys ++ [.zeichen ")"])) := by
        rw [druck_ruf, druckToks_applySuff]
        simp only [druckToks, List.append_assoc]
      apply legsB_kopf _ (nameTok a) _ (nameTok_form a) hd
      intro rest' G hrs _ hG
      apply prim_methM a suff ys rest' G hka hsl hne hxs hrs
      simp only [fb, hd, List.length_append, List.length_singleton] at hG
      omega

/-- **Every printable expression has its legs at the token bound.** -/
theorem legs_tok : ∀ (e : SExpr), gut e = true → LegsB (fb e) e :=
  fun e hg => legs_tok_n (groesse e) e (Nat.le_refl _) hg

/-- **L2a at token fuel**: a printable expression parses back through `parseOr` before any benign
    follow, with any fuel from `fb e + 8` up. -/
theorem parse_druck_tok : ∀ (e : SExpr) (rest : List Token) (F : Nat), gut e = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    fb e + 8 ≤ F → parseOr F (druckToks e ++ rest) = .ok (e, rest) :=
  fun e rest F hg hr hrs hrg hF => (legs_tok e hg).2.2.2.2.2.2.2 rest F hr hrs hrg hF

/-- **The whole expression reader** (`parseTop`, fuel `8 * length + 32`) returns every printable
    expression from its tokens. -/
theorem parseTop_druck_gut : ∀ (e : SExpr), gut e = true →
    parseTop (druckToks e ++ [.ende]) = .ok e := by
  intro e hg
  unfold parseTop
  rw [parse_druck_tok e [.ende] _ hg rfl rfl rfl (by
    simp only [fb, List.length_append, List.length_cons, List.length_nil]; omega)]

/-- **Composition with L1: from source text.** A printable expression whose print is lexically
    clean is read back from its rendered text by the front end (lexer, then `parseTop`). -/
theorem rundlauf_text_gut : ∀ (e : SExpr), gut e = true → (∀ t ∈ druckToks e, TokGut t) →
    parseTopAusText (renderText (druckToks e)) = .ok e := by
  intro e hg ht
  unfold parseTopAusText
  rw [lex_render _ ht]
  exact parseTop_druck_gut e hg

/-! ### Witnesses -/

/-- The many-small-nodes shape the size bound cannot reach (`a[!x][!y][!z]` -- three nodes per
    four tokens), through the whole reader. -/
theorem parseTop_druck_gut_zeuge :
    parseTop (druckToks (.index (.index (.index (.variable "a") (.un "!" (.variable "x")))
      (.un "!" (.variable "y"))) (.un "!" (.variable "z"))) ++ [.ende]) =
      .ok (.index (.index (.index (.variable "a") (.un "!" (.variable "x")))
      (.un "!" (.variable "y"))) (.un "!" (.variable "z"))) :=
  parseTop_druck_gut _ (by decide)

/-- A call through a place (`o.is_some()`) and one with arguments through a pointer chain
    (`p->q[i].f(x, 1)`), through the whole reader. -/
theorem parseTop_druck_ruf_zeuge :
    parseTop (druckToks (.ext .call [] [.field (.variable "o") "is_some"]) ++ [.ende]) =
      .ok (.ext .call [] [.field (.variable "o") "is_some"]) :=
  parseTop_druck_gut _ (by decide)

theorem parseTop_druck_ruf_zeuge2 :
    parseTop (druckToks (.ext .call [] [.field (.index (.arrow (.variable "p") "q") (.variable "i")) "f",
      .variable "x", .lit 1]) ++ [.ende]) =
      .ok (.ext .call [] [.field (.index (.arrow (.variable "p") "q") (.variable "i")) "f",
        .variable "x", .lit 1]) :=
  parseTop_druck_gut _ (by decide)

/-- The deep witness of `RundlaufVoll` from its rendered source text. -/
theorem rundlauf_text_gut_zeuge :
    parseTopAusText (renderText (druckToks zeugeTief)) = .ok zeugeTief :=
  rundlauf_text_gut zeugeTief zeugeTief_gut (tokGut_of_all _ (by decide))

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.legs_tok
#print axioms Gabbro.Grammatik.Parser.parse_druck_tok
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_gut
#print axioms Gabbro.Grammatik.Parser.rundlauf_text_gut
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_gut_zeuge
#print axioms Gabbro.Grammatik.Parser.rundlauf_text_gut_zeuge
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_ruf_zeuge
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_ruf_zeuge2
