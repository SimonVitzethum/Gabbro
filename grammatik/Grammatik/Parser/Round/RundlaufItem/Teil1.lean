/-
  File:      Grammatik/Parser/Round/RundlaufItem.lean
  Subject:   Layer L2c, the item pieces: each item form the item printer prints (`druckItem`,
             Print/Item.lean) reads back through `parseItemTief` -- `item_use`, `item_const`,
             `item_static`, `item_fn`, `item_proto`, `item_why`, `item_conc`, `item_mod`, `item_atom`,
             `item_lock`, `item_table`, `item_entry` -- with the readers of their parts (constant
             values, effects, clauses, parameters, paths, table fields and parts, register bindings).

  The printability class `ItemGut`, the induction over it and the composition with the lexer are in
  `RundlaufProgramm`; devices are in `RundlaufGeraet`.
-/
module

public import Grammatik.Parser.Round.RundlaufItem.Teil1a

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- Constant values and their rows read back before a benign follow. -/
theorem konst_rund : ∀ (v : SKonstWert), KonstGut v → ∀ (R : List Token) (F : Nat),
    ruhig R = true → ruhigSuff R = true → ruhigGleit R = true → fbK v ≤ F →
    parseKonstWert F (druckKonstWert v ++ R) = .ok (v, R) := by
  intro v hv
  induction hv with
  | one e he =>
    intro R F h1 h2 h3 hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbK] at hF; omega⟩
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf e he
    have hO := ausdruck e he R F' h1 h2 h3 (by simp only [fbK, druckKonstWert] at hF; omega)
    have hnb : ∀ r, druckToks e ++ R ≠ .zeichen "[" :: r := by
      rw [hd]; intro r e'; injection e' with e1; subst e1
      simp only [KopfGut, String.reduceEq, or_self] at hk
    simp only [druckKonstWert]
    rw [parseKonstWert.eq_def]
    simp only [hnb]
    simp only [bind, Except.bind, hO, pure, Except.pure]
  | rows xs hxs ih =>
    intro R F h1 h2 h3 hF
    have hrows : ∀ (ys : List SKonstWert), (∀ y ∈ ys, y ∈ xs) → ∀ (G : Nat),
        8 * (druckKonstWert.druckKonstWerte ys).length + 41 ≤ G →
        parseConstRows G (druckKonstWert.druckKonstWerte ys ++ .zeichen "]" :: R) = .ok (ys, R) := by
      intro ys
      induction ys with
      | nil =>
        intro _ G hG
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
        simp only [parseConstRows, druckKonstWert.druckKonstWerte, List.nil_append]
      | cons y ys ihy =>
        intro hsub G hG
        have hyx := hsub y (by simp only [List.mem_cons, true_or])
        have hy := hxs y hyx
        obtain ⟨t, ts, hd, ht1, -⟩ := konst_kopf y hy
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
        cases ys with
        | nil =>
          simp only [druckKonstWert.druckKonstWerte] at hG ⊢
          have hV := ih y hyx (.zeichen "]" :: R) G' rfl rfl rfl (by simp only [fbK]; omega)
          have hne : ∀ r, druckKonstWert y ++ .zeichen "]" :: R ≠ .zeichen "]" :: r := by
            rw [hd]; intro r e; injection e with e; exact ht1 e
          rw [parseConstRows.eq_def]
          simp only [hne]
          simp only [bind, Except.bind, hV, pure, Except.pure]
        | cons z zs =>
          rw [druckKonstWerte_cons y (z :: zs) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])] at hG ⊢
          simp only [List.length_append, List.length_cons] at hG
          have hV := ih y hyx (.zeichen "," :: (druckKonstWert.druckKonstWerte (z :: zs) ++ .zeichen "]" :: R))
            G' rfl rfl rfl (by simp only [fbK]; omega)
          have hR := ihy (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) G' (by omega)
          have hne : ∀ r, druckKonstWert y ++ .zeichen "," :: (druckKonstWert.druckKonstWerte (z :: zs) ++
              .zeichen "]" :: R) ≠ .zeichen "]" :: r := by
            rw [hd]; intro r e; injection e with e; exact ht1 e
          simp only [List.append_assoc, List.cons_append]
          rw [parseConstRows.eq_def]
          simp only [hne]
          simp only [bind, Except.bind, hV, hR, pure, Except.pure]
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbK] at hF; omega⟩
    have hH := hrows xs (fun x hx => hx) F' (by simp only [fbK, druckKonstWert] at hF; simp only [List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceLeDiff] at hF; omega)
    simp only [druckKonstWert, List.cons_append, List.append_assoc, List.singleton_append]
    simp only [parseKonstWert, List.nil_append, bind, Except.bind, hH, pure, Except.pure]

/-! ### Effects -/

/-- A printable effect arm. -/
def EffGut : SEffekt → Prop
  | .reads p => gut p = true
  | .writes p => gut p = true
  | .locks sh p => gut p = true ∧ (sh = false → ∀ ts, druckToks p ≠ .wort "shared" :: ts)
  | .takes p => gut p = true
  | .posts p => gut p = true
  | _ => True

/-- What follows an effect arm: `,` or `}`. -/
def EffFolge (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem effFolge_ruhig (R : List Token) (h : EffFolge R) :
    ruhig R = true ∧ ruhigSuff R = true ∧ ruhigGleit R = true := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

theorem effekt_rund (e : SEffekt) (he : EffGut e) (R : List Token) (hR : EffFolge R) (F : Nat)
    (hF : 6 * (druckEffekt e).length + 36 ≤ F) :
    parseEffekt F (druckEffekt e ++ R) = .ok (e, R) := by
  obtain ⟨h1, h2, h3⟩ := effFolge_ruhig R hR
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases e with
  | reads p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "reads" "reads" = true), ite_true, List.nil_append, hO]
  | writes p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "writes" "reads" = false), (by decide : strEq "writes" "writes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | locks sh p =>
    obtain ⟨he, hsh⟩ := he
    have hO := ausdruck p he R F' h1 h2 h3 (by
      simp only [druckEffekt, List.length_append, List.length_singleton] at hF; split at hF <;> simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf p he
    cases sh
    · simp only [druckEffekt, Bool.false_eq_true, ite_false, List.nil_append, List.singleton_append,
        List.cons_append]
      rw [hd] at hO ⊢
      simp only [List.cons_append] at hO ⊢
      cases t with
      | wort w =>
        have hw : strEq w "shared" = false := by
          cases h : strEq w "shared"
          · rfl
          · have := (strEq_eq _ _).mp h; subst this
            exact absurd hd (hsh rfl _)
        simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, hw, hO]
      | _ => simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
    · simp only [druckEffekt, ite_true, List.singleton_append, List.cons_append, List.append_assoc,
        List.nil_append]
      simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true,
        (by decide : strEq "shared" "shared" = true), hO]
  | masks n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "masks" "reads" = false), (by decide : strEq "masks" "writes" = false), (by decide : strEq "masks" "locks" = false), (by decide : strEq "masks" "masks" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | allocs n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "allocs" "reads" = false), (by decide : strEq "allocs" "writes" = false), (by decide : strEq "allocs" "locks" = false), (by decide : strEq "allocs" "masks" = false), (by decide : strEq "allocs" "allocs" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | takes p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "consumes" "reads" = false), (by decide : strEq "consumes" "writes" = false), (by decide : strEq "consumes" "locks" = false), (by decide : strEq "consumes" "masks" = false), (by decide : strEq "consumes" "allocs" = false), (by decide : strEq "consumes" "consumes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | posts p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "publishes" "reads" = false), (by decide : strEq "publishes" "writes" = false), (by decide : strEq "publishes" "locks" = false), (by decide : strEq "publishes" "masks" = false), (by decide : strEq "publishes" "allocs" = false), (by decide : strEq "publishes" "consumes" = false), (by decide : strEq "publishes" "publishes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | loops =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "diverges" "reads" = false), (by decide : strEq "diverges" "writes" = false), (by decide : strEq "diverges" "locks" = false), (by decide : strEq "diverges" "masks" = false), (by decide : strEq "diverges" "allocs" = false), (by decide : strEq "diverges" "consumes" = false), (by decide : strEq "diverges" "publishes" = false), (by decide : strEq "diverges" "diverges" = true), Bool.false_eq_true, ite_false, ite_true]
  | pure =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "pure" "reads" = false), (by decide : strEq "pure" "writes" = false), (by decide : strEq "pure" "locks" = false), (by decide : strEq "pure" "masks" = false), (by decide : strEq "pure" "allocs" = false), (by decide : strEq "pure" "consumes" = false), (by decide : strEq "pure" "publishes" = false), (by decide : strEq "pure" "diverges" = false), (by decide : strEq "pure" "pure" = true), Bool.false_eq_true, ite_false, ite_true]

theorem effekte_rund : ∀ (es : List SEffekt) (R : List Token) (F : Nat), es ≠ [] → (∀ e ∈ es, EffGut e) →
    8 * (druckEffekte es).length + 41 ≤ F →
    parseEffektListe F (druckEffekte es ++ .zeichen "}" :: R) = .ok (es, .zeichen "}" :: R) := by
  intro es
  induction es with
  | nil => intro _ _ h; exact absurd rfl h
  | cons e es ih =>
    intro R F _ hg hF
    have he := hg e (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases es with
    | nil =>
      simp only [druckEffekte] at hF ⊢
      have hE := effekt_rund e he (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp only [parseEffektListe, hE, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons e2 es2 =>
      have hd : druckEffekte (e :: e2 :: es2) = druckEffekt e ++ .zeichen "," :: druckEffekte (e2 :: es2) := by
        simp only [druckEffekte, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hE := effekt_rund e he (.zeichen "," :: (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      have hk : istZeichenZ "}" (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R) = false := by
        cases e2 <;> cases es2 <;> simp only [istZeichenZ, druckEffekte, druckEffekt, List.cons_append, List.nil_append, List.append_assoc] <;> (try split) <;> rfl
      simp only [List.append_assoc, List.cons_append] at hE ⊢
      simp only [parseEffektListe, hE, hk, Bool.false_eq_true, ite_false, hR]

theorem namen_rund : ∀ (ns : List String) (R : List Token) (F : Nat), ns ≠ [] →
    (∀ r, R ≠ .zeichen "," :: r) → ns.length ≤ F →
    parseNamenListe F (druckNamen ns ++ R) = .ok (ns, R) := by
  intro ns
  induction ns with
  | nil => intro _ _ h; exact absurd rfl h
  | cons n ns ih =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ns with
    | nil =>
      simp only [druckNamen, List.cons_append, List.nil_append]
      simp only [parseNamenListe, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, hR]
    | cons m ms =>
      have hq := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hR (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hlook : ∃ v, nimmName (druckNamen (m :: ms) ++ R) = .ok v := by
        cases ms <;> simp only [nimmName, druckNamen, List.cons_append, List.nil_append, nameText_nameTok, Except.ok.injEq, exists_eq']
      obtain ⟨v, hv⟩ := hlook
      have hd : druckNamen (n :: m :: ms) ++ R = nameTok n :: .zeichen "," :: (druckNamen (m :: ms) ++ R) := by
        simp only [druckNamen, List.cons_append, List.nil_append]
      rw [hd]
      have h0 : nimmName (nameTok n :: .zeichen "," :: (druckNamen (m :: ms) ++ R)) =
          .ok (n, .zeichen "," :: (druckNamen (m :: ms) ++ R)) := by simp only [nimmName, nameText_nameTok]
      simp only [parseNamenListe, h0, hv, hq]

/-! ### Clauses -/

/-- The printable clauses (`by`, `retires`, `deadline` ride as reconstructed text: excluded). -/
def KlauselGut : SKlausel → Prop
  | .needs p => PredGut p
  | .gives p => PredGut p
  | .keeps ns => ns ≠ []
  | .refs p => p ≠ []
  | .cost e => gut e = true
  | .drops e => gut e = true
  | .load p => p ≠ []
  | .part _ => True
  | .arch _ => True
  | .moves _ _ => True
  | .effs es => ∀ e ∈ es, EffGut e
  | _ => False

/-- What follows a clause: the next clause word, or the body (`{`, `;`). -/
def KlauselFolge (R : List Token) : Prop :=
  (∃ r, R = .zeichen "{" :: r) ∨ (∃ r, R = .zeichen ";" :: r) ∨
    (∃ w r, R = .wort w :: r ∧ istKlauselKopf w = true)

theorem klauselFolge_pred (R : List Token) (h : KlauselFolge R) :
    PredFolge R ∧ (∀ r, R ≠ .zeichen "," :: r) ∧ (∀ r, R ≠ .zeichen "::" :: r) := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨w, r, rfl, hw⟩
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩,
      (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)⟩
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩,
      (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)⟩
  · have hr : w ≠ "rounded" := by intro e; subst e; exact absurd hw (by decide)
    have hi : w ≠ "in" := by intro e; subst e; exact absurd hw (by decide)
    have hre : w ≠ "reaches" := by intro e; subst e; exact absurd hw (by decide)
    have hrs : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hr
    refine ⟨⟨rfl, rfl, by simp only [ruhigGleit, hrs, Bool.not_false], (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), ?_, ?_⟩,
      (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
    · intro x e; simp only [List.cons.injEq, Token.wort.injEq] at e; exact hi e.1
    · intro x e; simp only [List.cons.injEq, Token.wort.injEq] at e; exact hre e.1

end Gabbro.Grammatik.Parser
