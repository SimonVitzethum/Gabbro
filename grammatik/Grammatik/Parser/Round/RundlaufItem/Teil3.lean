module

public import Grammatik.Parser.Round.RundlaufItem.Teil3a
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- The tokens of the starts, as `kommaToks` of each start's tokens. -/
theorem druckStarts_eq : ∀ (ps : List (List String × List SExpr)), (∀ p ∈ ps, PfadGut p.1) →
    druckStarts ps = kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) := by
  intro ps hps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
    cases ps with
    | nil => simp only [druckStarts, druckStart_eq p hp, List.map_cons, List.map_nil, kommaToks]
    | cons q qs =>
      simp only [List.map_cons] at ih' ⊢
      simp only [druckStarts, kommaToks, druckStart_eq p hp] at ih' ⊢
      rw [ih']

theorem startFolge_rund : ∀ (ps : List (List String × List SExpr)) (R : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, PfadGut p.1 ∧ ∀ x ∈ p.2, gut x = true) →
    ps.length + 6 * (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2)).length + 37 ≤ F →
    parsePfadFolge F (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R) =
      .ok (ps, R) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hF
    have hp := hg p (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons, List.map_cons] at hF; omega⟩
    cases ps with
    | nil =>
      have hP := nimmPfad_pfad p.1 (argToks p.2 ++ .zeichen "}" :: R) hp.1.1 (by
        intro r e
        unfold argToks at e; split at e <;> simp only [List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.cons_append, List.append_assoc] at e)
      have hA := argToks_rund p.2 hp.2 (.zeichen "}" :: R) F' (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by
        have := druckToksListe_le_argToks p.2
        simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil, kommaToks, List.length_append, Nat.reduceLeDiff] at hF; omega)
      simp only [List.map_cons, List.map_nil, kommaToks, List.append_assoc] at hP hA ⊢
      unfold parsePfadFolge
      simp only [hP]
      rw [hA]
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons q qs =>
      have hq := hg q (by simp only [List.mem_cons, true_or, or_true])
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append, List.length_append, Nat.reduceLeDiff] at hF ⊢; omega)
      obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks q.1 = nameTok a :: us := by
        match q.1, hq.1.1 with
        | [a], _ => exact ⟨a, [], rfl⟩
        | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
      have hk : kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) =
          nameTok a :: (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2)).tail := by
        cases qs <;> simp only [List.map_cons, hq1, List.cons_append, List.map_nil, kommaToks, List.tail_cons, List.append_assoc, List.nil_append]
      have hd : kommaToks ((p :: q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) = pfadToks p.1 ++
          (argToks p.2 ++ .zeichen "," :: kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2)) := by
        simp only [List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append]
      have hP := nimmPfad_pfad p.1 (argToks p.2 ++ .zeichen "," ::
        (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R)) hp.1.1 (by
          intro r e
          unfold argToks at e; split at e <;> simp only [List.isEmpty_iff, List.cons_append, List.nil_append, List.map_cons, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.append_assoc] at e)
      have hA := argToks_rund p.2 hp.2 (.zeichen "," ::
        (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R)) F'
        (by intro r e; simp only [List.map_cons, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by
          have := druckToksListe_le_argToks p.2
          rw [hd] at hF; simp only [List.length_cons, List.map_cons, List.length_append, Nat.reduceLeDiff] at hF; omega)
      rw [hd]
      simp only [List.append_assoc, List.cons_append] at hP hA ⊢
      unfold parsePfadFolge
      simp only [hP]
      rw [hA]
      rw [hk] at hR ⊢
      simp only [List.cons_append] at hR ⊢
      simp only [hR]
      rcases nameTok_cases a with h | h <;> rw [h] <;> rfl

theorem item_conc (ps : List (List String × List SExpr)) (hps : ∀ p ∈ ps, PfadGut p.1 ∧ ∀ x ∈ p.2, gut x = true) :
    ItemBein (.concT ps) := by
  intro rest F hF
  have hW := druckStarts_eq ps (fun p hp => (hps p hp).1)
  have hlen : ps.length ≤ (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2)).length := by
    clear hF hW
    induction ps with
    | nil => simp only [List.length_nil, List.map_nil, Nat.zero_le]
    | cons p ps ih =>
      have hp := hps p (by simp only [List.mem_cons, true_or])
      have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
      have h1 : 1 ≤ (pfadToks p.1).length := by
        match p.1, hp.1.1 with
        | [a], _ => simp only [pfadToks, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl]
        | a :: b :: cs, _ => simp only [pfadToks, List.cons_append, List.nil_append, List.length_cons, Nat.le_add_left]
      cases ps with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil, kommaToks, List.length_append, ge_iff_le]; omega
      | cons q qs => simp only [List.length_cons, List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append, List.length_append, ge_iff_le] at ih' ⊢; omega
  simp only [fbI, druckItem, hW, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckItem (.concT ps) ++ rest = .wort "concurrent" :: .zeichen "{" ::
      (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: .zeichen ";" :: rest) := by
    simp only [druckItem, hW, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_concurrent]
  cases ps with
  | nil => simp only [parseNebenTief, nimmWort, strEq_self, ↓reduceIte, List.map_nil, kommaToks, List.nil_append, parsePfadListe, fordereZeichen]
  | cons p ps' =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have hF' := startFolge_rund (p :: ps') (.zeichen ";" :: rest) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hps (by omega)
    obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks p.1 = nameTok a :: us := by
      match p.1, hp.1.1 with
      | [a], _ => exact ⟨a, [], rfl⟩
      | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
    have hk : kommaToks ((p :: ps').map fun p => pfadToks p.1 ++ argToks p.2) =
        nameTok a :: (kommaToks ((p :: ps').map fun p => pfadToks p.1 ++ argToks p.2)).tail := by
      cases ps' <;> simp only [List.map_cons, hq1, List.cons_append, List.map_nil, kommaToks, List.tail_cons, List.append_assoc, List.nil_append]
    rw [hk] at hF' ⊢
    simp only [List.cons_append, List.map_cons] at hF' ⊢
    simp only [parseNebenTief, nimmWort, strEq_self, ↓reduceIte, parsePfadListe, fordereZeichen, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hF']


theorem item_mod (segs : List String) (its : List SItemTief) (hs : PfadGut segs)
    (hits : ∀ it ∈ its, ItemBein it ∧ ItemKopf it) : ItemBein (.modT ("::".intercalate segs) its) := by
  intro rest F hF
  have hr := rohToks_pfad segs hs.1 hs.2
  have hd : druckItem (.modT ("::".intercalate segs) its) ++ rest = .wort "module" :: (pfadToks segs ++
      .zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) := by
    simp only [druckItem, hr, List.cons_append, List.nil_append, List.append_assoc]
  simp only [fbI, druckItem, hr, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hP := nimmPfad_pfad segs (.zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) hs.1
    (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
  have hI := items_rund its (.zeichen "}" :: rest) F' hits (Or.inr (Or.inl ⟨rest, rfl⟩)) (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_module]
  simp only [parseModulTief, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen, hI]

/-! ### `atomic` -/

theorem platzListe_rund (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token) (F : Nat)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ F) :
    parsePlatzListe F (.zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp only [parsePlatzListe, fordereZeichen, strEq_self, ↓reduceIte, druckPlaetze, List.nil_append]
  | cons p ps' =>
    rw [druckPlaetze_eq] at hF ⊢
    have hL := predListe_rund (p :: ps') (.zeichen "}" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hps
      ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
      (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    obtain ⟨t, ts, hd, -, -⟩ := druck_kopf_pred p (hps p (by simp only [List.mem_cons, true_or]))
    have hne : ∀ r, druckPredListe (p :: ps') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
      intro r e
      have : druckPredListe (p :: ps') = druckToks p ++ (druckPredListe (p :: ps')).drop (druckToks p).length := by
        cases ps' <;> simp only [druckPredListe, List.drop_length, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, List.drop_left']
      rw [this, hd] at e
      simp only [List.length_cons, List.cons_append, List.append_assoc, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      have := druck_kopf p (hps p (by simp only [List.mem_cons, true_or]))
      obtain ⟨t', ts', hd', hk'⟩ := this
      rw [hd] at hd'; injection hd' with e1; subst e1; simp only [KopfGut, String.reduceEq, or_self] at hk'
    simp only [parsePlatzListe, fordereZeichen, strEq_self, ite_true]
    simp only [hne, hL]
    simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, strEq_self, ↓reduceIte]

/-- The order words of an atomic. -/
def istOrdnung (o : String) : Bool :=
  strEq o "acquire" || strEq o "release" || strEq o "seq" || strEq o "relaxed"

/-- A printable `atomic` tail. -/
def AtomGut (pub : Option (List SExpr)) (ord : Option String) : Prop :=
  (∀ ps, pub = some ps → ∀ p ∈ ps, gut p = true) ∧ (∀ o, ord = some o → istOrdnung o = true)

def atomTail (pub : Option (List SExpr)) (ord : Option String) (obs : Option String) : List Token :=
  (match pub with
    | some [] => [.wort "publishes", .wort "nothing"]
    | some ps => [.wort "publishes", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}"]
    | none => []) ++
  (match ord with
    | some o => [.wort o]
    | none => []) ++
  (match obs with
    | some o => [.wort "observed", .wort "by", nameTok o]
    | none => []) ++ [.zeichen ";"]

theorem atomRest_ende (f : Nat) (acc : String × STyp × Option (List SExpr) × Option String × Option String)
    (R : List Token) : parseAtomarRest (f + 1) acc (.zeichen ";" :: R) = .ok (acc, R) := by
  simp only [parseAtomarRest, fordereZeichen, strEq_self, ↓reduceIte]

theorem atomRest_obs (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (o : String) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "observed" :: .wort "by" :: nameTok o :: R) =
      parseAtomarRest f (a, b, c, d, some o) R := by
  simp [parseAtomarRest, nimmWort, strEq_self, nimmName, (by decide : strEq "observed" "publishes" = false), (by decide : strEq "observed" "acquire" = false), (by decide : strEq "observed" "release" = false), (by decide : strEq "observed" "seq" = false), (by decide : strEq "observed" "relaxed" = false)]

theorem atomRest_ord (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (o : String) (ho : istOrdnung o = true) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort o :: R) = parseAtomarRest f (a, b, c, some o, e) R := by
  simp only [istOrdnung, Bool.or_eq_true, strEq_eq] at ho
  rcases ho with ((h | h) | h) | h <;> subst h
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "acquire" "publishes" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "release" "publishes" = false),
      (by decide : strEq "release" "acquire" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "seq" "publishes" = false),
      (by decide : strEq "seq" "acquire" = false), (by decide : strEq "seq" "release" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "relaxed" "publishes" = false),
      (by decide : strEq "relaxed" "acquire" = false), (by decide : strEq "relaxed" "release" = false),
      (by decide : strEq "relaxed" "seq" = false)]

theorem atomRest_nichts (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "publishes" :: .wort "nothing" :: R) =
      parseAtomarRest f (a, b, some [], d, e) R := by
  simp only [parseAtomarRest, strEq_self, ↓reduceIte]

theorem atomRest_liste (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ f) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "publishes" :: .zeichen "{" ::
      (druckPlaetze ps ++ .zeichen "}" :: R)) = parseAtomarRest f (a, b, some ps, d, e) R := by
  have hL := platzListe_rund ps hps R f hF
  simp only [parseAtomarRest, strEq_self, ↓reduceIte, hL]

end Gabbro.Grammatik.Parser
