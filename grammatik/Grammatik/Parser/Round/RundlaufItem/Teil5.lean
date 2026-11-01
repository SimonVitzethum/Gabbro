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


/-- A printable group invariant: printable cost and predicate, a raw proof text without `:` and
    braces. -/
def InvGut (i : SGruppenInv) : Prop :=
  gut i.kosten = true ∧ PredGut i.pred ∧
    ∀ h, i.proof = some h → RohText (fun t => t = .zeichen ":" ∨ t = .zeichen "{" ∨ t = .zeichen "}") h

theorem gruppenInv_rund (i : SGruppenInv) (hi : InvGut i) (R : List Token) (F : Nat)
    (hF : 8 * (druckGruppenInv i).length + 60 ≤ F) :
    parseGruppenInv F (druckGruppenInv i ++ R) = .ok (i, R) := by
  obtain ⟨hk, hp, hpr⟩ := hi
  obtain ⟨name, kosten, online, proof, pred⟩ := i
  simp only at hk hp hpr ⊢
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add] at hF; omega⟩
  have hon : ∀ X, (Token.wort (if online then "online" else "offline") :: X) =
      .wort (if online then "online" else "offline") :: X := fun _ => rfl
  have hm : (strEq (if online then "online" else "offline") "online" ||
      strEq (if online then "online" else "offline") "offline") = true := by cases online <;> decide
  have hmo : strEq (if online then "online" else "offline") "online" = online := by cases online <;> decide
  have hoff : online = false → strEq (if online then "online" else "offline") "offline" = true := by
    intro h; subst h; decide
  cases proof with
  | none =>
    simp only [druckGruppenInv, List.length_append, List.length_cons, List.length_nil] at hF
    have hK := ausdruck kosten hk (.zeichen ")" :: .wort "runs" ::
      .wort (if online then "online" else "offline") :: .zeichen ":" :: (druckToks pred ++ .zeichen ";" :: R))
      (F' + 1) rfl rfl rfl (by omega)
    have hP := pred_voll pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [bP]; omega)
    simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseGruppenInv, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, nimmKostenO, nameText_ident, fordereZeichen, hK, hmo, Bool.or_eq_true, parseInvRest, hP, ite_eq_left_iff, not_or, Bool.not_eq_true, reduceCtorEq, imp_false, not_and, Bool.not_eq_false]
    all_goals exact hoff
  | some h =>
    obtain ⟨ts, rfl, hts⟩ := hpr _ rfl
    have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
    simp only [druckGruppenInv, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    have hK := ausdruck kosten hk (.zeichen ")" :: .wort "runs" ::
      .wort (if online then "online" else "offline") :: .wort "by" ::
        (ts ++ .zeichen ":" :: (druckToks pred ++ .zeichen ";" :: R)))
      (F' + 1) rfl rfl rfl (by omega)
    have hP := pred_voll pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [bP]; omega)
    have hN := nimmBisZeichen_roh ":" ts (druckToks pred ++ .zeichen ";" :: R)
      (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inr (Or.inl e)),
        fun e => (hts t ht).2 (Or.inr (Or.inr e)), fun e => (hts t ht).2 (Or.inl e)⟩)
    simp only [druckGruppenInv, hroh, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    simp only [parseGruppenInv, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, nimmKostenO, nameText_ident, fordereZeichen, hK, hmo, Bool.or_eq_true, parseInvRest, hN, hP, ite_eq_left_iff, not_or, Bool.not_eq_true, reduceCtorEq, imp_false, not_and, Bool.not_eq_false]
    all_goals exact hoff

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

theorem tabTeile_rund : ∀ (ps : List STabTeil) (R : List Token) (F : Nat), (∀ t ∈ ps, TeilGut t) →
    8 * (druckTabTeile ps).length + 64 ≤ F →
    parseTabTeile F (druckTabTeile ps ++ .zeichen "}" :: R) = .ok (ps, .zeichen "}" :: R) := by
  intro ps
  induction ps with
  | nil =>
    intro R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    exact tabTeile_ende F' R
  | cons t ps ih =>
    intro R F hg hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckTabTeile, List.length_append] at hF ⊢
    have h1 : 1 ≤ (druckTabTeil t).length := by cases t <;> simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_left, druckGruppenInv, Nat.reduceAdd, Nat.reduceLeDiff]
    have hR := ih R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    rw [List.append_assoc]
    exact tabTeil_rund t (hg t (by simp only [List.mem_cons, true_or])) _ _ ps F' hR (by omega)


/-! ### The table head -/

def cntToks : Option SExpr → List Token
  | some e => [.wort "count"] ++ druckToks e
  | none => []

def nameOptToks (w : String) : Option String → List Token
  | some b => [.wort w, nameTok b]
  | none => []

def shToks (sh : Bool) : List Token := if sh then [.wort "shared"] else []

theorem tabKopf_ende (f : Nat) (R : List Token) :
    parseTabellenKopf (f + 1) (.zeichen "{" :: R) = .ok ((none, none, none, none, false), .zeichen "{" :: R) := by
  simp only [parseTabellenKopf]

theorem tabKopf_shared (f : Nat) (R X : List Token) (c : Option SExpr) (v b o : Option String) (g : Bool)
    (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "shared" :: R) = .ok ((c, v, b, o, true), X) := by
  simp [parseTabellenKopf, h, strEq_self, (by decide : strEq "shared" "count" = false),
    (by decide : strEq "shared" "from" = false),
    (by decide : strEq "shared" "backed" = false), (by decide : strEq "shared" "owner" = false)]

theorem tabKopf_owner (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "owner" :: nameTok n :: R) = .ok ((c, v, b, some n, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "owner" "count" = false),
    (by decide : strEq "owner" "from" = false), (by decide : strEq "owner" "backed" = false)]

theorem tabKopf_backed (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "backed" :: nameTok n :: R) = .ok ((c, v, some n, o, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "backed" "count" = false),
    (by decide : strEq "backed" "from" = false)]

theorem tabKopf_from (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "from" :: nameTok n :: R) = .ok ((c, some n, b, o, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "from" "count" = false)]

theorem tabKopf_count (f : Nat) (e : SExpr) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (hO : parseOr f (druckToks e ++ R) = .ok (e, R))
    (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "count" :: (druckToks e ++ R)) = .ok ((some e, v, b, o, g), X) := by
  simp only [parseTabellenKopf, strEq_self, ↓reduceIte, hO, h]

theorem tabKopf_rund (cnt : Option SExpr) (von backed owner : Option String) (sh : Bool)
    (hc : ∀ e, cnt = some e → gut e = true) (R : List Token) (F : Nat)
    (hF : 8 * (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
      shToks sh).length + 40 ≤ F) :
    parseTabellenKopf F (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++
      nameOptToks "owner" owner ++ shToks sh ++ .zeichen "{" :: R) =
      .ok ((cnt, von, backed, owner, sh), .zeichen "{" :: R) := by
  have L1 : ∀ G, 2 ≤ G → parseTabellenKopf G (shToks sh ++ .zeichen "{" :: R) =
      .ok ((none, none, none, none, sh), .zeichen "{" :: R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases sh
    · simpa [shToks] using tabKopf_ende (G' + 1) R
    · simpa [shToks] using tabKopf_shared (G' + 1) _ _ none none none none false (tabKopf_ende G' R)
  have L2 : ∀ G, 3 ≤ G → parseTabellenKopf G (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R)) =
      .ok ((none, none, none, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases owner with
    | none => simpa [nameOptToks] using L1 G (by omega)
    | some o =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_owner G' o _ _ none none none none sh (L1 G' (by omega))
  have L3 : ∀ G, 4 ≤ G → parseTabellenKopf G (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
      (shToks sh ++ .zeichen "{" :: R))) = .ok ((none, none, backed, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases backed with
    | none => simpa [nameOptToks] using L2 G (by omega)
    | some b =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_backed G' b _ _ none none none owner sh (L2 G' (by omega))
  have L4 : ∀ G, 5 ≤ G → parseTabellenKopf G (nameOptToks "from" von ++ (nameOptToks "backed" backed ++
      (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R)))) =
      .ok ((none, von, backed, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases von with
    | none => simpa [nameOptToks] using L3 G (by omega)
    | some p =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_from G' p _ _ none none backed owner sh (L3 G' (by omega))
  simp only [List.append_assoc] at hF ⊢
  cases cnt with
  | none => simpa [cntToks] using L4 F (by simp only [cntToks, List.nil_append, List.length_append] at hF; omega)
  | some e =>
    have he := hc e rfl
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append] at hF; omega⟩
    have hrX : ruhig (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true ∧
        ruhigSuff (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true ∧
        ruhigGleit (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true := by
      cases von <;> cases backed <;> cases owner <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck e he _ F' hrX.1 hrX.2.1 hrX.2.2 (by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.reduceLeDiff] at hF; omega)
    have := tabKopf_count F' e _ _ none von backed owner sh hO (L4 F' (by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.reduceLeDiff] at hF; omega))
    simpa [cntToks] using this

theorem item_table (n : String) (von : Option String) (cnt : Option SExpr) (backed owner : Option String)
    (sh : Bool) (parts : List STabTeil) (hc : ∀ e, cnt = some e → gut e = true) (hp : ∀ t ∈ parts, TeilGut t) :
    ItemBein (.tableT n von cnt backed owner sh parts) := by
  intro rest F hF
  have hd : druckItem (.tableT n von cnt backed owner sh parts) ++ rest = .wort "table" :: nameTok n ::
      (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
        shToks sh ++ .zeichen "{" :: (druckTabTeile parts ++ .zeichen "}" :: rest)) := by
    cases cnt <;> cases von <;> cases backed <;> cases owner <;> cases sh <;>
      simp only [druckItem, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.append_assoc, cntToks, nameOptToks, shToks]
  have hlen : (druckItem (.tableT n von cnt backed owner sh parts)).length = 2 +
      (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
        shToks sh).length + 1 + (druckTabTeile parts).length + 1 := by
    cases cnt <;> cases von <;> cases backed <;> cases owner <;> cases sh <;>
      simp only [druckItem, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, cntToks, nameOptToks, shToks, Nat.add_zero, Nat.reduceAdd, Nat.add_right_cancel_iff, List.append_assoc] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hK := tabKopf_rund cnt von backed owner sh hc (druckTabTeile parts ++ .zeichen "}" :: rest) F' (by omega)
  have hT := tabTeile_rund parts rest F' hp (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_table]
  simp only [List.append_assoc] at hK
  simp only [parseTabellenTief, nimmWort, strEq_self, ↓reduceIte, List.append_assoc, nimmName, nameText_nameTok, hK, fordereZeichen, hT]


/-! ### `entry` -/

/-- What follows a register binding: `,` or `}`. -/
def BindEnde (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem regBind_rund (b : SRegBind) (R : List Token) (hR : BindEnde R) :
    parseRegBind (druckRegBind b ++ R) = .ok (b, R) := by
  cases b with
  | reg a =>
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      simp [druckRegBind, parseRegBind, nimmName, (by decide : strEq "," "=" = false), (by decide : strEq "," ":" = false), (by decide : strEq "}" "=" = false), (by decide : strEq "}" ":" = false)]
  | binds a c => simp only [parseRegBind, nimmName, druckRegBind, List.cons_append, List.nil_append, nameText_nameTok, strEq_self, Bool.true_or, ↓reduceIte]

theorem regBindFolge_rund : ∀ (bs : List SRegBind) (R : List Token) (F : Nat), bs ≠ [] → bs.length ≤ F →
    parseRegBindFolge F (druckRegBinds bs ++ .zeichen "}" :: R) = .ok (bs, R) := by
  intro bs
  induction bs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons b bs ih =>
    intro R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases bs with
    | nil =>
      have hB := regBind_rund b (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩)
      simp only [druckRegBinds]
      simp only [parseRegBindFolge, hB, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons c cs =>
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hd : druckRegBinds (b :: c :: cs) = druckRegBind b ++ .zeichen "," :: druckRegBinds (c :: cs) := by
        simp only [druckRegBinds, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd, List.append_assoc]
      have hB := regBind_rund b (.zeichen "," :: (druckRegBinds (c :: cs) ++ .zeichen "}" :: R)) (Or.inl ⟨_, rfl⟩)
      obtain ⟨a, ts, hts⟩ : ∃ a ts, druckRegBinds (c :: cs) ++ .zeichen "}" :: R = nameTok a :: ts := by
        cases c with
        | reg x => exact ⟨x, (druckRegBinds (.reg x :: cs) ++ .zeichen "}" :: R).tail,
            by cases cs <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
        | binds x y => exact ⟨x, (druckRegBinds (.binds x y :: cs) ++ .zeichen "}" :: R).tail,
            by cases cs <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
      try simp only [List.cons_append] at hB
      simp only [List.append_assoc, List.cons_append]
      rw [hts] at hB hR ⊢
      unfold parseRegBindFolge
      simp only [hB, hR]
      rcases nameTok_cases a with h | h <;> rw [h] <;> rfl

theorem regBindListe_rund (bs : List SRegBind) (R : List Token) (F : Nat) (hF : bs.length + 2 ≤ F) :
    parseRegBindListe F (.zeichen "{" :: (druckRegBinds bs ++ .zeichen "}" :: R)) = .ok (bs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases bs with
  | nil => simp only [parseRegBindListe, fordereZeichen, strEq_self, ↓reduceIte, druckRegBinds, List.nil_append]
  | cons b bs' =>
    have hR := regBindFolge_rund (b :: bs') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by omega)
    obtain ⟨a, ts, hts⟩ : ∃ a ts, druckRegBinds (b :: bs') ++ .zeichen "}" :: R = nameTok a :: ts := by
      cases b with
      | reg x => exact ⟨x, (druckRegBinds (.reg x :: bs') ++ .zeichen "}" :: R).tail,
          by cases bs' <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
      | binds x y => exact ⟨x, (druckRegBinds (.binds x y :: bs') ++ .zeichen "}" :: R).tail,
          by cases bs' <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
    rw [hts] at hR ⊢
    simp only [parseRegBindListe, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hR]

end Gabbro.Grammatik.Parser
