module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem klausel_rund (k : SKlausel) (hk : KlauselGut k) (R : List Token) (hR : KlauselFolge R) (F : Nat)
    (hF : 8 * (druckKlausel k).length + 41 ≤ F) :
    parseKlausel F (druckKlausel k ++ R) = .ok ([k], R) := by
  obtain ⟨hp, hkomma, hdd⟩ := klauselFolge_pred R hR
  obtain ⟨h1, h2, h3, -⟩ := id hp
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases k with
  | needs p =>
    simp only [druckKlausel, druckPredListe, List.length_append, List.length_singleton] at hF ⊢
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hP := pred_voll p hk R hp F'' (by simp only [bP]; omega)
    have hL : parsePredListe (F'' + 1) (druckToks p ++ R) = .ok ([p], R) := by
      simp only [parsePredListe, hP]
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "requires" "requires" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | gives p =>
    simp only [druckKlausel, druckPredListe, List.length_append, List.length_singleton] at hF ⊢
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hP := pred_voll p hk R hp F'' (by simp only [bP]; omega)
    have hL : parsePredListe (F'' + 1) (druckToks p ++ R) = .ok ([p], R) := by
      simp only [parsePredListe, hP]
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "ensures" "requires" = false), (by decide : strEq "ensures" "ensures" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | keeps ns =>
    have hlen : ns.length ≤ (druckNamen ns).length := by
      clear hF hk
      induction ns with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons n ns ih => cases ns with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
        | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hN := namen_rund ns R F' hk hkomma (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "maintains" "requires" = false), (by decide : strEq "maintains" "ensures" = false), (by decide : strEq "maintains" "maintains" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hN]
  | refs p =>
    have hP := nimmPfad_pfad p R hk hdd
    simp only [druckKlausel, List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "refines" "requires" = false), (by decide : strEq "refines" "ensures" = false), (by decide : strEq "refines" "maintains" = false), (by decide : strEq "refines" "refines" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hP]
  | effs es =>
    cases es with
    | nil =>
      simp only [druckKlausel, druckEffekte, List.cons_append, List.nil_append]
      simp only [parseKlausel, (by decide : strEq "effects" "requires" = false), (by decide : strEq "effects" "ensures" = false), (by decide : strEq "effects" "maintains" = false), (by decide : strEq "effects" "refines" = false), (by decide : strEq "effects" "effects" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self]
    | cons e es' =>
      simp only [druckKlausel, List.length_append, List.length_cons, List.length_singleton] at hF ⊢
      have hE := effekte_rund (e :: es') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hk (by omega)
      have hne : ∀ r, druckEffekte (e :: es') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
        intro r e'
        have hke : EffGut e := hk e (by simp only [List.mem_cons, true_or])
        cases e <;> (try exact (hke : False).elim) <;> cases es' <;> simp only [druckEffekte, druckEffekt, List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq, false_and, List.append_assoc] at e' <;> (try split at e') <;> simp_all
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
      simp only [parseKlausel, (by decide : strEq "effects" "requires" = false), (by decide : strEq "effects" "ensures" = false), (by decide : strEq "effects" "maintains" = false), (by decide : strEq "effects" "refines" = false), (by decide : strEq "effects" "effects" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self]
      simp only [hne, hE, fordereZeichen, strEq_self, ite_true]
  | cost e =>
    simp only [druckKlausel, List.length_append, List.length_cons, List.length_singleton] at hF ⊢
    have hO := ausdruck e hk (.wort "ops" :: R) F' rfl rfl rfl (by omega)
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseKlausel, (by decide : strEq "costs" "requires" = false), (by decide : strEq "costs" "ensures" = false), (by decide : strEq "costs" "maintains" = false), (by decide : strEq "costs" "refines" = false), (by decide : strEq "costs" "effects" = false), (by decide : strEq "costs" "costs" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self, hO, nimmWort]
  | drops e =>
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck e hk R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "decreases" "requires" = false), (by decide : strEq "decreases" "ensures" = false), (by decide : strEq "decreases" "maintains" = false), (by decide : strEq "decreases" "refines" = false), (by decide : strEq "decreases" "effects" = false), (by decide : strEq "decreases" "costs" = false), (by decide : strEq "decreases" "deadline" = false), (by decide : strEq "decreases" "decreases" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | load p =>
    have hP := nimmPfad_pfad p R hk hdd
    simp only [druckKlausel, List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "payload" "requires" = false), (by decide : strEq "payload" "ensures" = false), (by decide : strEq "payload" "maintains" = false), (by decide : strEq "payload" "refines" = false), (by decide : strEq "payload" "effects" = false), (by decide : strEq "payload" "costs" = false), (by decide : strEq "payload" "deadline" = false), (by decide : strEq "payload" "decreases" = false), (by decide : strEq "payload" "by" = false), (by decide : strEq "payload" "section" = false), (by decide : strEq "payload" "arch" = false), (by decide : strEq "payload" "payload" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hP]
  | part s =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "section" "requires" = false), (by decide : strEq "section" "ensures" = false), (by decide : strEq "section" "maintains" = false), (by decide : strEq "section" "refines" = false), (by decide : strEq "section" "effects" = false), (by decide : strEq "section" "costs" = false), (by decide : strEq "section" "deadline" = false), (by decide : strEq "section" "decreases" = false), (by decide : strEq "section" "by" = false), (by decide : strEq "section" "section" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmTextTok]
  | arch n =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "arch" "requires" = false), (by decide : strEq "arch" "ensures" = false), (by decide : strEq "arch" "maintains" = false), (by decide : strEq "arch" "refines" = false), (by decide : strEq "arch" "effects" = false), (by decide : strEq "arch" "costs" = false), (by decide : strEq "arch" "deadline" = false), (by decide : strEq "arch" "decreases" = false), (by decide : strEq "arch" "by" = false), (by decide : strEq "arch" "section" = false), (by decide : strEq "arch" "arch" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | moves a b =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "advances" "requires" = false), (by decide : strEq "advances" "ensures" = false), (by decide : strEq "advances" "maintains" = false), (by decide : strEq "advances" "refines" = false), (by decide : strEq "advances" "effects" = false), (by decide : strEq "advances" "costs" = false), (by decide : strEq "advances" "deadline" = false), (by decide : strEq "advances" "decreases" = false), (by decide : strEq "advances" "by" = false), (by decide : strEq "advances" "section" = false), (by decide : strEq "advances" "arch" = false), (by decide : strEq "advances" "payload" = false), (by decide : strEq "advances" "advances" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, strEq_self]
  | induc h => simp only [KlauselGut] at hk
  | quits s => simp only [KlauselGut] at hk
  | limit s => simp only [KlauselGut] at hk

theorem klausel_kopf (k : SKlausel) (hk : KlauselGut k) :
    ∃ w ts, druckKlausel k = .wort w :: ts ∧ istKlauselKopf w = true := by
  cases k <;> (try simp only [KlauselGut, ne_eq] at hk) <;> exact ⟨_, _, rfl, by decide⟩

/-- The body behind a function head: a block or `;`. -/
def KlauselEnde (R : List Token) : Prop := (∃ r, R = .zeichen "{" :: r) ∨ (∃ r, R = .zeichen ";" :: r)

theorem klauseln_rund : ∀ (ks : List SKlausel) (R : List Token) (F : Nat), (∀ k ∈ ks, KlauselGut k) →
    KlauselEnde R → 8 * (druckKlauseln ks).length + 42 ≤ F →
    parseKlauseln F (druckKlauseln ks ++ R) = .ok (ks, R) := by
  intro ks
  induction ks with
  | nil =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseKlauseln, druckKlauseln, List.nil_append]
  | cons k ks ih =>
    intro R F hg hR hF
    have hk := hg k (by simp only [List.mem_cons, true_or])
    obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k hk
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckKlauseln, List.length_append] at hF ⊢
    have hfolge : KlauselFolge (druckKlauseln ks ++ R) := by
      cases ks with
      | nil => rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩
               · exact Or.inl ⟨r, by simp only [druckKlauseln, List.nil_append]⟩
               · exact Or.inr (Or.inl ⟨r, by simp only [druckKlauseln, List.nil_append]⟩)
      | cons k2 ks2 =>
        obtain ⟨w2, ts2, hd2, hw2⟩ := klausel_kopf k2 (hg k2 (by simp only [List.mem_cons, true_or, or_true]))
        exact Or.inr (Or.inr ⟨w2, ts2 ++ druckKlauseln ks2 ++ R, by simp only [druckKlauseln, hd2, List.cons_append, List.append_assoc], hw2⟩)
    have hl1 : 1 ≤ (druckKlausel k).length := by rw [hd]; simp only [List.length_cons, Nat.le_add_left]
    have hK := klausel_rund k hk (druckKlauseln ks ++ R) hfolge F' (by omega)
    have hR' := ih R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hR (by omega)
    rw [List.append_assoc, hd]
    rw [hd] at hK
    simp only [List.cons_append] at hK ⊢
    simp only [parseKlauseln, hw, ite_true, hK, hR', List.singleton_append]

/-! ### Parameters and the function head -/

theorem paramListe_rund : ∀ (ps : List (String × STyp)) (R : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, TypGut p.2) → (∃ r, R = .zeichen ")" :: r) → 8 * (druckParams ps).length + 31 ≤ F →
    parseParamListe F (druckParams ps ++ R) = .ok (ps, R) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hR hF
    obtain ⟨n, t⟩ := p
    have ht : TypGut t := hg (n, t) (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ps with
    | nil =>
      obtain ⟨r, rfl⟩ := hR
      simp only [druckParams, druckParam, List.length_append, List.length_cons, List.length_nil] at hF ⊢
      have hT := parse_druckTyp t ht (.zeichen ")" :: r) F'
        ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (by simp only [fbT]; omega)
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      simp only [parseParamListe, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons q qs =>
      obtain ⟨m, u⟩ := q
      obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((m, u) :: qs) = nameTok m :: Z := by
        cases qs <;> exact ⟨_, rfl⟩
      have hd : druckParams ((n, t) :: (m, u) :: qs) ++ R = nameTok n :: .zeichen ":" ::
          (druckTyp t ++ .zeichen "," :: nameTok m :: (Z ++ R)) := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this, hZ]; simp only [druckParam, List.cons_append, List.nil_append, List.append_assoc]
      have hlen : (druckParams ((n, t) :: (m, u) :: qs)).length =
          (druckTyp t).length + 3 + (druckParams ((m, u) :: qs)).length := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this]; simp only [druckParam, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append]; omega
      rw [hlen] at hF
      have hR' := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hR (by omega)
      rw [hZ] at hR' hF
      have hT := parse_druckTyp t ht (.zeichen "," :: nameTok m :: (Z ++ R)) F'
        ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (by simp only [fbT]; simp only [List.length_cons, Nat.reduceLeDiff] at hF; omega)
      rw [hd]
      simp only [List.cons_append] at hR'
      simp only [parseParamListe, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hR']

theorem params_rund (ps : List (String × STyp)) (hg : ∀ p ∈ ps, TypGut p.2) (R : List Token) (F : Nat)
    (hF : 8 * (druckParams ps).length + 32 ≤ F) :
    parseParams F (.zeichen "(" :: (druckParams ps ++ .zeichen ")" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp only [parseParams, fordereZeichen, strEq_self, ↓reduceIte, druckParams, List.nil_append]
  | cons p ps =>
    obtain ⟨n, t⟩ := p
    obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((n, t) :: ps) = nameTok n :: Z := by
      cases ps <;> exact ⟨_, rfl⟩
    have hL := paramListe_rund ((n, t) :: ps) (.zeichen ")" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hg ⟨R, rfl⟩ (by omega)
    rw [hZ] at hL ⊢
    simp only [List.cons_append] at hL ⊢
    simp only [parseParams, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hL]


end Gabbro.Grammatik.Parser
