module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem felder_rund : ∀ (fs : List SFeld) (R : List Token) (F : Nat), fs ≠ [] → (∀ fd ∈ fs, FeldGut fd) →
    8 * (druckFelder fs).length + 62 ≤ F →
    parseFeldFolge F (druckFelder fs ++ .zeichen "}" :: R) = .ok (fs, R) := by
  intro fs
  induction fs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons fd fs ih =>
    intro R F _ hg hF
    have hfd := hg fd (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases fs with
    | nil =>
      simp only [druckFelder] at hF ⊢
      have hP := feld_rund fd hfd (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp only [parseFeldFolge, hP, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons fd2 fs2 =>
      have hd : druckFelder (fd :: fd2 :: fs2) = druckFeld fd ++ .zeichen "," :: druckFelder (fd2 :: fs2) := by
        simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hP := feld_rund fd hfd (.zeichen "," :: (druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R = nameTok fd2.fname :: ts := by
        cases fs2 with
        | nil => simpa [druckFelder] using feldKopf fd2 (.zeichen "}" :: R)
        | cons x xs =>
          obtain ⟨ts, h⟩ := feldKopf fd2 (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
          exact ⟨ts, by simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
      simp only [List.append_assoc, List.cons_append] at hP ⊢
      rw [hts] at hP hR ⊢
      unfold parseFeldFolge
      simp only [hP, hR]
      rcases nameTok_cases fd2.fname with h | h <;> rw [h] <;> rfl

theorem feldListe_rund (fs : List SFeld) (hg : ∀ fd ∈ fs, FeldGut fd) (R : List Token) (F : Nat)
    (hF : 8 * (druckFelder fs).length + 63 ≤ F) :
    parseFeldListe F (.zeichen "{" :: (druckFelder fs ++ .zeichen "}" :: R)) = .ok (fs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases fs with
  | nil => simp only [parseFeldListe, fordereZeichen, strEq_self, ↓reduceIte, druckFelder, List.nil_append]
  | cons fd fs' =>
    have hFF := felder_rund (fd :: fs') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hg (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd :: fs') ++ .zeichen "}" :: R = nameTok fd.fname :: ts := by
      cases fs' with
      | nil => simpa [druckFelder] using feldKopf fd (.zeichen "}" :: R)
      | cons x xs =>
        obtain ⟨ts, h⟩ := feldKopf fd (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
        exact ⟨ts, by simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
    rw [hts] at hFF ⊢
    simp only [parseFeldListe, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hFF]

/-- An edge kind of a `tree`. -/
def KanteGut (k : String × String) : Prop :=
  k.1 = "parent" ∨ k.1 = "child" ∨ k.1 = "sibling"

theorem kante_rund (a b : String) (h : KanteGut (a, b)) (R : List Token) :
    parseKante (.wort a :: nameTok b :: R) = .ok ((a, b), R) := by
  rcases h with h | h | h <;> simp only at h <;> subst h <;> simp only [parseKante, strEq_self, Bool.true_or, ↓reduceIte, nimmName, nameText_nameTok, Bool.or_true]

theorem kanten_rund : ∀ (ks : List (String × String)) (R : List Token) (F : Nat), ks ≠ [] →
    (∀ k ∈ ks, KanteGut k) → ks.length ≤ F →
    parseKanten F (druckKanten ks ++ .zeichen "}" :: R) = .ok (ks, .zeichen "}" :: R) := by
  intro ks
  induction ks with
  | nil => intro _ _ h; exact absurd rfl h
  | cons k ks ih =>
    intro R F _ hg hF
    obtain ⟨a, b⟩ := k
    have hk := kante_rund a b (hg (a, b) (by simp only [List.mem_cons, true_or]))
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ks with
    | nil => simp only [parseKanten, druckKanten, List.cons_append, List.nil_append, hk, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons k2 ks2 =>
      obtain ⟨a2, b2⟩ := k2
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckKanten ((a2, b2) :: ks2) ++ .zeichen "}" :: R = .wort a2 :: ts := by
        cases ks2 <;> exact ⟨_, by simp only [druckKanten, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl⟩
      have hd : druckKanten ((a, b) :: (a2, b2) :: ks2) = [.wort a, nameTok b, .zeichen ","] ++
          druckKanten ((a2, b2) :: ks2) := by simp only [druckKanten, List.cons_append, List.nil_append]
      rw [hd]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hts] at hR ⊢
      unfold parseKanten
      simp only [hk, hR]

theorem baum_rund (ks : List (String × String)) (hne : ks ≠ []) (hg : ∀ k ∈ ks, KanteGut k)
    (R : List Token) (F : Nat) (hF : ks.length + 1 ≤ F) :
    parseBaum F (.zeichen "{" :: (druckKanten ks ++ .zeichen "}" :: R)) = .ok (ks, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hK := kanten_rund ks R F' hne hg (by omega)
  simp only [parseBaum, fordereZeichen, strEq_self, ↓reduceIte, hK]


/-- A printable group invariant has a printable predicate. -/
def InvGut (i : SGruppenInv) : Prop := PredGut i.pred

theorem gruppenInv_rund (i : SGruppenInv) (hi : InvGut i) (R : List Token) (F : Nat)
    (hF : 8 * (druckGruppenInv i).length + 60 ≤ F) :
    parseGruppenInv F (druckGruppenInv i ++ R) = .ok (i, R) := by
  obtain ⟨name, pred⟩ := i
  have hp : PredGut pred := hi
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckGruppenInv, List.length_append, List.length_cons, List.length_nil] at hF
  have hP := pred_voll pred hp (.zeichen ";" :: R)
    ⟨rfl, rfl, rfl,
      (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
    F' (by simp only [bP]; omega)
  simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc,
    parseGruppenInv, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok,
    parseInvRest, fordereZeichen, hP]

/-- A printable part of a table. -/
def TeilGut : STabTeil → Prop
  | .tConst _ t v => TypGut t ∧ KonstGut v
  | .tSlot fs => ∀ fd ∈ fs, FeldGut fd
  | .tInv i => InvGut i
  | .tOps ns => ns ≠ []
  | .tTree ks => ks ≠ [] ∧ ∀ k ∈ ks, KanteGut k
  | .tBusy _ => True

theorem tabTeile_ende (f : Nat) (R : List Token) :
    parseTabTeile (f + 1) (.zeichen "}" :: R) = .ok ([], .zeichen "}" :: R) := by
  simp only [parseTabTeile]

theorem tabTeil_rund (t : STabTeil) (ht : TeilGut t) (R X : List Token) (ps : List STabTeil) (f : Nat)
    (hR : parseTabTeile f R = .ok (ps, X)) (hf : 8 * (druckTabTeil t).length + 63 ≤ f) :
    parseTabTeile (f + 1) (druckTabTeil t ++ R) = .ok (t :: ps, X) := by
  cases t with
  | tConst n ty v =>
    obtain ⟨hty, hv⟩ := ht
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hT := typ_gleich ty hty (druckKonstWert v ++ .zeichen ";" :: R) f' (by simp only [fbT]; omega)
    have hV := konst_rund v hv (.zeichen ";" :: R) f' rfl rfl rfl (by simp only [fbK]; omega)
    have hK : parseKonstNach (f' + 1) (nameTok n :: .zeichen ":" :: (druckTyp ty ++ .zeichen "=" ::
        (druckKonstWert v ++ .zeichen ";" :: R))) = .ok (.constT n ty v, R) := by
      simp only [parseKonstNach, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hV]
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "const" "const" = true), ite_true, hK, hR]
  | tSlot fs =>
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hL := feldListe_rund fs ht R f (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "slot" "const" = false), (by decide : strEq "slot" "slot" = true),
      Bool.false_eq_true, ite_false, ite_true, hL, hR]
  | tInv i =>
    simp only [druckTabTeil] at hf
    have hI := gruppenInv_rund i ht R f (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckGruppenInv i = .wort "invariant" :: ts := ⟨_, rfl⟩
    simp only [druckTabTeil]
    rw [hts] at hI ⊢
    simp only [List.cons_append] at hI ⊢
    unfold parseTabTeile
    simp only [(by decide : strEq "invariant" "const" = false),
      (by decide : strEq "invariant" "slot" = false), (by decide : strEq "invariant" "invariant" = true),
      Bool.false_eq_true, ite_false, ite_true, hI, hR]
  | tOps ns =>
    have hlen : ns.length ≤ (druckNamen ns).length := by
      clear hf ht hR
      induction ns with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons n ns ih => cases ns with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
        | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hN := namen_rund ns (.zeichen ";" :: R) f ht (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "ops" "const" = false), (by decide : strEq "ops" "slot" = false),
      (by decide : strEq "ops" "invariant" = false), (by decide : strEq "ops" "ops" = true),
      Bool.false_eq_true, ite_false, ite_true, hN, fordereZeichen, strEq_self, hR]
  | tTree ks =>
    obtain ⟨hne, hg⟩ := ht
    have hlen : ks.length ≤ (druckKanten ks).length := by
      clear hf hne hg hR
      induction ks with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons k ks ih => cases ks with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckKanten, Nat.reduceAdd, Nat.reduceLeDiff]
        | cons k2 ks2 => simp only [List.length_cons, druckKanten, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hB := baum_rund ks hne hg R f (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "tree" "const" = false), (by decide : strEq "tree" "slot" = false),
      (by decide : strEq "tree" "invariant" = false), (by decide : strEq "tree" "ops" = false),
      (by decide : strEq "tree" "tree" = true), Bool.false_eq_true, ite_false, ite_true, hB, hR]
  | tBusy n =>
    simp only [druckTabTeil, List.cons_append, List.nil_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "occupied" "const" = false), (by decide : strEq "occupied" "slot" = false), (by decide : strEq "occupied" "invariant" = false), (by decide : strEq "occupied" "ops" = false), (by decide : strEq "occupied" "tree" = false), (by decide : strEq "occupied" "occupied" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, strEq_self, hR]


end Gabbro.Grammatik.Parser
