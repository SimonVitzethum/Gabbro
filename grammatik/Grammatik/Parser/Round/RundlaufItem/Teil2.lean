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
        cases e <;> cases es' <;> simp only [druckEffekte, druckEffekt, List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq, false_and, List.append_assoc] at e' <;> (try split at e') <;> simp_all
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

/-- A printable function head. -/
def SigGut (s : FnSig) : Prop :=
  (s.art = "" ∨ s.art = "const" ∨ istMod s.art = true) ∧ (∀ p ∈ s.params, TypGut p.2) ∧
    TypOptGut s.res ∧ (∀ k ∈ s.klauseln, KlauselGut k)

/-- The function head behind its modifier, up to the body. -/
def sigToks (s : FnSig) : List Token :=
  [.wort "fn", nameTok s.name, .zeichen "("] ++ druckParams s.params ++ [.zeichen ")"] ++
    (match s.res with
      | some t => [.zeichen "->"] ++ druckTyp t
      | none => []) ++
    (match s.fehler with
      | some n => [.wort "or", nameTok n]
      | none => []) ++
    druckKlauseln s.klauseln

theorem druckFnSig_eq (s : FnSig) :
    druckFnSig s = (if strEq s.art "" then [] else [.wort s.art]) ++ sigToks s := by
  simp only [druckFnSig, List.append_assoc, List.cons_append, List.nil_append, sigToks, List.append_cancel_left_eq, List.cons.injEq, true_and]; rfl

/-- The result tokens of a head. -/
def resToks : Option STyp → List Token
  | some t => [.zeichen "->"] ++ druckTyp t
  | none => []

/-- The `or` channel tokens of a head. -/
def fehlerToks : Option String → List Token
  | some n => [.wort "or", nameTok n]
  | none => []

theorem sigToks_eq (s : FnSig) : sigToks s = [.wort "fn", nameTok s.name, .zeichen "("] ++
    druckParams s.params ++ [.zeichen ")"] ++ resToks s.res ++ fehlerToks s.fehler ++ druckKlauseln s.klauseln := by
  simp only [sigToks]
  cases s.res <;> cases s.fehler <;> rfl

/-- The tail of a function head (the `or` channel, clauses) is a type follow. -/
theorem kopfRest_typFolge (fehler : Option String) (ks : List SKlausel) (hk : ∀ k ∈ ks, KlauselGut k)
    (R : List Token) (hR : KlauselEnde R) :
    TypFolge (fehlerToks fehler ++ druckKlauseln ks ++ R) := by
  have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" → w ≠ "rounded" →
      TypFolge (.wort w :: X) := by
    intro w X h1 h2 h3 h4
    have : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) h4
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
  cases fehler with
  | some n => exact gen "or" _ (by decide) (by decide) (by decide) (by decide)
  | none =>
    simp only [fehlerToks, List.nil_append]
    cases ks with
    | nil =>
      rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        exact ⟨(by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
    | cons k ks' =>
      obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
      have : druckKlauseln (k :: ks') ++ R = .wort w :: (ts ++ druckKlauseln ks' ++ R) := by
        simp only [druckKlauseln, hd, List.cons_append, List.append_assoc]
      rw [this]
      apply gen w _ <;> intro e <;> subst e <;> exact absurd hw (by decide)

theorem fnSig_rund (s : FnSig) (hs : SigGut s) (R : List Token) (hR : KlauselEnde R) (F : Nat)
    (hF : 8 * (sigToks s).length + 42 ≤ F) :
    parseFnSig F s.art (sigToks s ++ R) = .ok (s, R) := by
  obtain ⟨-, hp, hres, hk⟩ := hs
  rw [sigToks_eq] at hF ⊢
  obtain ⟨art, name, params, res, fehler, klauseln⟩ := s
  simp only at hp hres hk hF ⊢
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hlenF : (fehlerToks fehler).length ≤ 2 := by cases fehler <;> simp only [fehlerToks, List.length_nil, Nat.zero_le, List.length_cons, Nat.zero_add, Nat.reduceAdd, Std.le_refl]
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  have hK := klauseln_rund klauseln R F' hk hR (by omega)
  have hFe : parseFehler (fehlerToks fehler ++ druckKlauseln klauseln ++ R) =
      .ok (fehler, druckKlauseln klauseln ++ R) := by
    cases fehler with
    | some n => simp only [parseFehler, fehlerToks, List.cons_append, List.nil_append, strEq_self, ↓reduceIte, nimmName, nameText_nameTok]
    | none =>
      simp only [fehlerToks, List.nil_append]
      cases klauseln with
      | nil =>
        rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseFehler, druckKlauseln, List.nil_append]
      | cons k ks =>
        obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
        have hwo : strEq w "or" = false := by
          cases h : strEq w "or"
          · rfl
          · have := (strEq_eq _ _).mp h; subst this; exact absurd hw (by decide)
        simp only [parseFehler, druckKlauseln, hd, List.cons_append, List.append_assoc, hwo, Bool.false_eq_true, ↓reduceIte]
  have hTF := kopfRest_typFolge fehler klauseln hk R hR
  have hErg : parseErgebnis F' (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) =
      .ok (res, fehler, druckKlauseln klauseln ++ R) := by
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    cases res with
    | some t =>
      have hT := parse_druckTyp t hres _ F'' hTF (by simp only [fbT]; simp only [Nat.zero_add, Nat.reduceAdd, resToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega)
      simp only [resToks, List.singleton_append, List.cons_append, List.append_assoc] at hT hFe ⊢
      simp only [parseErgebnis, List.nil_append, hT, hFe]
    | none =>
      simp only [resToks, List.nil_append]
      have hne : ∀ r, fehlerToks fehler ++ druckKlauseln klauseln ++ R ≠ .zeichen "->" :: r := by
        intro r e
        cases fehler with
        | some n => simp only [fehlerToks, List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e
        | none =>
          cases klauseln with
          | nil => rcases hR with ⟨r', rfl⟩ | ⟨r', rfl⟩ <;> simp only [fehlerToks, druckKlauseln, List.append_nil, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e
          | cons k ks =>
            obtain ⟨w, ts, hd, -⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
            simp only [fehlerToks, druckKlauseln, hd, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e
      rw [parseErgebnis.eq_def]
      simp only [hne]
      simp only [List.append_assoc] at hFe
      simp only [List.append_assoc, hFe]
  have hP := params_rund params hp (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) F'
    (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hP hErg hK ⊢
  simp only [parseFnSig, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hP, hErg, hK]

/-! ### Items -/

/-- The fuel bound of an item: eight per printed token, thirty-eight spare. -/
def fbI (it : SItemTief) : Nat := 8 * (druckItem it).length + 38

/-- An item reads back before every follow. -/
def ItemBein (it : SItemTief) : Prop :=
  ∀ (rest : List Token) (F : Nat), fbI it ≤ F → parseItemTief F (druckItem it ++ rest) = .ok (it, rest)

/-- An item prints with a head word other than `when` and `pub`. -/
def ItemKopf (it : SItemTief) : Prop :=
  ∃ w ts, druckItem it = .wort w :: ts ∧ w ≠ "when" ∧ w ≠ "pub"

/-- What may follow an item list: nothing, `}` or the end marker. -/
def ItemsEnde (R : List Token) : Prop := R = [] ∨ (∃ r, R = .zeichen "}" :: r) ∨ (∃ r, R = .ende :: r)

theorem items_rund : ∀ (its : List SItemTief) (R : List Token) (F : Nat),
    (∀ it ∈ its, ItemBein it ∧ ItemKopf it) → ItemsEnde R → 8 * (druckItems its).length + 39 ≤ F →
    parseItemsTief F (druckItems its ++ R) = .ok (its, R) := by
  intro its
  induction its with
  | nil =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rcases hR with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseItemsTief, druckItems, List.append_nil, List.nil_append]
  | cons it its ih =>
    intro R F h hR hF
    obtain ⟨hB, w, ts, hd, -, -⟩ := h it (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckItems, List.length_append] at hF ⊢
    have hl : 1 ≤ (druckItem it).length := by rw [hd]; simp only [List.length_cons, Nat.le_add_left]
    have hI := hB (druckItems its ++ R) F' (by simp only [fbI]; omega)
    have hR' := ih R F' (fun x hx => h x (List.mem_cons_of_mem _ hx)) hR (by omega)
    rw [List.append_assoc, hd]
    rw [hd] at hI
    simp only [List.cons_append] at hI ⊢
    simp only [parseItemsTief, hI, hR']

theorem item_use (p : List String) (hp : p ≠ []) : ItemBein (.useT p) := by
  intro rest F hF
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckItem (.useT p) ++ rest = .wort "use" :: (pfadToks p ++ .zeichen ";" :: rest) := by
    simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc]
  have hP := nimmPfad_pfad p (.zeichen ";" :: rest) hp
    (by intro r e; injection e with e1; injection e1 with e2; exact absurd e2 (by decide))
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_use]
  simp only [parseUseTief, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen]

/-- `= v ;` behind a type: the initialiser follow. -/
theorem typ_gleich (t : STyp) (ht : TypGut t) (X : List Token) (F : Nat) (hF : fbT t ≤ F) :
    parseTyp F (druckTyp t ++ .zeichen "=" :: X) = .ok (t, .zeichen "=" :: X) :=
  parse_druckTyp t ht _ F ⟨(by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
    (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ hF

theorem item_const (n : String) (hn : n ≠ "fn") (t : STyp) (v : SKonstWert) (ht : TypGut t)
    (hv : KonstGut v) :
    ItemBein (.constT n t v) := by
  intro rest F hF
  simp only [fbI, druckItem, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckItem (.constT n t v) ++ rest = .wort "const" :: nameTok n :: .zeichen ":" ::
      (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++ .zeichen ";" :: rest)) := by
    simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc]
  have hT := typ_gleich t ht (druckKonstWert v ++ .zeichen ";" :: rest) F' (by simp only [fbT]; omega)
  have hV := konst_rund v hv (.zeichen ";" :: rest) F' rfl rfl rfl (by simp only [fbK]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_const _ _ hn]
  simp only [parseKonstNach, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hV]

/-- The tail of a `static`: `[aligned e] [section "s"] [shared] ;`. -/
def globTailToks (al : Option SExpr) (s : Option String) (sh : Bool) : List Token :=
  (match al with
    | some e => [.wort "aligned"] ++ druckToks e
    | none => []) ++
  (match s with
    | some x => [.wort "section", .text x]
    | none => []) ++
  (if sh then [.wort "shared"] else []) ++ [.zeichen ";"]

theorem globTail_rund (al : Option SExpr) (s : Option String) (sh : Bool)
    (hal : ∀ e, al = some e → gut e = true) (rest : List Token) (F : Nat)
    (hF : 8 * (globTailToks al s sh).length + 40 ≤ F) :
    parseGlobTail F (globTailToks al s sh ++ rest) = .ok ((al, s, sh), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases al with
  | none =>
    cases s <;> cases sh <;>
      simp only [parseGlobTail, bind, Except.bind, globTailToks, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, pure, Except.pure, fordereZeichen, strEq_self, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, nimmTextTok]
  | some e =>
    have he := hal e rfl
    cases s with
    | none =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, fordereZeichen, strEq_self]
      | true =>
        have hO := ausdruck e he (.wort "shared" :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self]
    | some x =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc, hO, pure, Except.pure, nimmTextTok, fordereZeichen, strEq_self]
      | true =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .wort "shared" :: .zeichen ";" :: rest) F'
          rfl rfl rfl (by simp only [globTailToks, List.cons_append, List.nil_append, ↓reduceIte, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, nimmTextTok, fordereZeichen, strEq_self]

theorem globTail_ruhig (al : Option SExpr) (s : Option String) (sh : Bool) (rest : List Token) :
    ruhig (globTailToks al s sh ++ rest) = true ∧ ruhigSuff (globTailToks al s sh ++ rest) = true ∧
      ruhigGleit (globTailToks al s sh ++ rest) = true := by
  cases al <;> cases s <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.Parser
