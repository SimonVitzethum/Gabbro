module

public import Grammatik.Parser.Round.RundlaufItem.Teil5a

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
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
