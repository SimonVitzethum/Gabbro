module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem item_static (m : Bool) (n : String) (hn : n ≠ "mut") (t : STyp) (v : SKonstWert)
    (al : Option SExpr) (s : Option String) (sh : Bool) (ht : TypGut t) (hv : KonstGut v)
    (hal : ∀ e, al = some e → gut e = true) :
    ItemBein (.globT m n t v al s sh) := by
  intro rest F hF
  have hd : druckItem (.globT m n t v al s sh) ++ rest = .wort "static" :: ((if m then [.wort "mut"] else []) ++
      nameTok n :: .zeichen ":" :: (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++
        (globTailToks al s sh ++ rest)))) := by
    cases al <;> cases s <;> cases sh <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, Bool.false_eq_true, ↓reduceIte, globTailToks]
  have hlen : (druckItem (.globT m n t v al s sh)).length = 1 + (if m then 1 else 0) + 2 +
      (druckTyp t).length + 1 + (druckKonstWert v).length + (globTailToks al s sh).length := by
    cases m <;> cases al <;> cases s <;> cases sh <;> simp only [druckItem, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, globTailToks, Nat.add_right_cancel_iff] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  obtain ⟨h1, h2, h3⟩ := globTail_ruhig al s sh rest
  have hT := typ_gleich t ht (druckKonstWert v ++ (globTailToks al s sh ++ rest)) F'
    (by simp only [fbT]; split at hF <;> omega)
  have hV := konst_rund v hv (globTailToks al s sh ++ rest) F' h1 h2 h3
    (by simp only [fbK]; split at hF <;> omega)
  have hG := globTail_rund al s sh hal rest F' (by split at hF <;> omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_static]
  cases m
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    rcases nameTok_cases n with h | h <;> rw [h] <;>
      simp only [parseGlobTief, nimmWort, strEq_self, ↓reduceIte, strEq_ne hn, Bool.false_eq_true, parseGlobAfter, bind, Except.bind, nimmName, nameText_wort, fordereZeichen, hT, hV, hG, pure, Except.pure, nameText_ident]
  · simp only [parseGlobTief, nimmWort, strEq_self, ↓reduceIte, List.cons_append, List.nil_append, parseGlobAfter, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, hT, hV, hG, pure, Except.pure]


/-! ### Functions -/

theorem sigToks_kopf (s : FnSig) : ∃ ts, sigToks s = .wort "fn" :: ts := ⟨_, rfl⟩

/-- A function head read by the item reader, up to its body. -/
theorem item_fnkopf (sig : FnSig) (hs : SigGut sig) (R : List Token) (hR : KlauselEnde R) (F : Nat)
    (hF : 8 * (sigToks sig).length + 46 ≤ F) :
    ∃ G, F ≤ G + 4 ∧ parseItemTief F (druckFnSig sig ++ R) = parseFnRest G sig R := by
  obtain ⟨hart, -⟩ := id hs
  obtain ⟨ts, hts⟩ := sigToks_kopf sig
  rw [druckFnSig_eq]
  rcases hart with h | h | h
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    rw [h] at hS
    refine ⟨F', by omega, ?_⟩
    simp only [h, strEq_self, ite_true, List.nil_append]
    rw [hts, List.cons_append, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_fn,
      ← List.cons_append, ← hts, hS]
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    rw [h] at hS
    refine ⟨F', by omega, ?_⟩
    simp only [h, (by decide : strEq "const" "" = false), Bool.false_eq_true, ite_false,
      List.singleton_append]
    rw [hts] at hS ⊢
    simp only [List.cons_append] at hS ⊢
    rw [parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_constfn, hS]
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    have hne : strEq sig.art "" = false := by
      cases e : strEq sig.art ""
      · rfl
      · have := (strEq_eq _ _).mp e; rw [this] at h; exact absurd h (by decide)
    have hw1 : sig.art ≠ "when" := by intro e; rw [e] at h; exact absurd h (by decide)
    have hw2 : sig.art ≠ "pub" := by intro e; rw [e] at h; exact absurd h (by decide)
    refine ⟨F', by omega, ?_⟩
    simp only [hne, Bool.false_eq_true, ite_false, List.singleton_append]
    rw [hts] at hS ⊢
    simp only [List.cons_append] at hS ⊢
    rw [parseItemTief_wort _ _ _ hw1 hw2, parseItemKopf_art _ _ _ h, hS]

theorem druckFnSig_len (sig : FnSig) : (sigToks sig).length ≤ (druckFnSig sig).length := by
  rw [druckFnSig_eq]; simp only [List.length_append, Nat.le_add_left]

theorem item_fn (sig : FnSig) (b : SAnw) (hs : SigGut sig) (hb : BlockBein b) (hk : BlockKopf b) :
    ItemBein (.fnT sig b) := by
  intro rest F hF
  obtain ⟨us, hus⟩ := hk
  have hlen := druckFnSig_len sig
  have hbl : 1 ≤ (druckAnw b).length := by rw [hus]; simp only [List.length_cons, Nat.le_add_left]
  simp only [fbI, druckItem, List.length_append] at hF
  obtain ⟨G, hG, hI⟩ := item_fnkopf sig hs (druckAnw b ++ rest) (Or.inl ⟨us ++ rest, by rw [hus]; rfl⟩) F
    (by omega)
  have hB := hb rest (G - 1) (by simp only [fbA]; omega)
  simp only [druckItem, List.append_assoc]
  rw [hI]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hB
  rw [hus] at hB ⊢
  simp only [List.cons_append] at hB ⊢
  simp only [parseFnRest, hB]

theorem item_proto (sig : FnSig) (hs : SigGut sig) : ItemBein (.protoT sig) := by
  intro rest F hF
  have hlen := druckFnSig_len sig
  simp only [fbI, druckItem, List.length_append, List.length_singleton] at hF
  obtain ⟨G, hG, hI⟩ := item_fnkopf sig hs (.zeichen ";" :: rest) (Or.inr ⟨rest, rfl⟩) F (by omega)
  simp only [druckItem, List.append_assoc, List.singleton_append]
  rw [hI]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [parseFnRest]

/-! ### `reason`, `concurrent`, `module` -/

/-- A printable reason case: its number is printable. -/
def FallGut (c : String × SExpr × String) : Prop := gut c.2.1 = true ∧ c.1 ≠ "exhaustive"

theorem grundFaelle_rund : ∀ (cs : List (String × SExpr × String)) (ex : Bool) (R : List Token) (F : Nat),
    (∀ c ∈ cs, FallGut c) → 8 * (druckGrundFaelle cs).length + 42 ≤ F →
    parseGrundFaelle F (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++
      .zeichen "}" :: R)) = .ok ((cs, ex), R) := by
  intro cs
  induction cs with
  | nil =>
    intro ex R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ex <;> simp only [parseGrundFaelle, druckGrundFaelle, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, strEq_self, fordereZeichen]
  | cons c cs ih =>
    intro ex R F hg hF
    obtain ⟨n, num, t⟩ := c
    have hnum : gut num = true := (hg (n, num, t) (by simp only [List.mem_cons, true_or])).1
    have hx : strEq n "exhaustive" = false := by
      cases h : strEq n "exhaustive"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) (hg (n, num, t) (by simp only [List.mem_cons, true_or])).2
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckGrundFaelle, List.length_append, List.length_cons, List.length_nil] at hF
    have hR := ih ex R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hO := ausdruck num hnum (.text t :: .zeichen "," :: (druckGrundFaelle cs ++
      ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: R))) F'' rfl rfl rfl (by omega)
    simp only [druckGrundFaelle, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    unfold parseGrundFaelle
    rcases nameTok_cases n with h | h <;> rw [h] <;>
      simp only [hx, Bool.false_eq_true, ↓reduceIte, parseGrundFall, nimmName, nameText_wort, fordereZeichen, strEq_self, hO, nimmTextTok, hR, nameText_ident]

theorem item_why (n : String) (cs : List (String × SExpr × String)) (ex : Bool) (hg : ∀ c ∈ cs, FallGut c) :
    ItemBein (.whyT n cs ex) := by
  intro rest F hF
  have hd : druckItem (.whyT n cs ex) ++ rest = .wort "reason" :: nameTok n :: .zeichen "{" ::
      (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: rest)) := by
    cases ex <;> simp only [druckItem, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  have hlen : (druckGrundFaelle cs).length + 3 ≤ (druckItem (.whyT n cs ex)).length := by
    cases ex <;> simp only [druckItem, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_right, List.append_assoc, Nat.reduceAdd, Nat.add_le_add_iff_right] <;> omega
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hG := grundFaelle_rund cs ex rest F' hg (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_reason]
  simp only [parseGrundTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hG]

/-- A path printed as text: segments name-shaped. -/
def PfadGut (segs : List String) : Prop :=
  segs ≠ [] ∧ ∀ a ∈ segs, nameForm a = true

theorem druckWurzeln_pfade : ∀ (ps : List (List String)), (∀ p ∈ ps, PfadGut p) →
    druckWurzeln (ps.map (fun p => "::".intercalate p)) =
      kommaToks (ps.map pfadToks) := by
  intro ps hps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
    cases ps with
    | nil => simp only [List.map_cons, List.map_nil, druckWurzeln, rohToks_pfad p hp.1 hp.2, kommaToks]
    | cons q qs =>
      simp only [List.map_cons] at ih' ⊢
      simp only [druckWurzeln, kommaToks, rohToks_pfad p hp.1 hp.2] at ih' ⊢
      rw [ih']

/-- The arguments of a start as printed: in parentheses when there are any. -/
def argToks (as : List SExpr) : List Token :=
  if as.isEmpty then [] else [.zeichen "("] ++ druckToksListe as ++ [.zeichen ")"]

theorem druckStart_eq (p : List String × List SExpr) (hp : PfadGut p.1) :
    druckStart p = pfadToks p.1 ++ argToks p.2 := by
  simp only [druckStart, rohToks_pfad p.1 hp.1 hp.2, List.isEmpty_iff, List.cons_append, List.nil_append, argToks]

/-- After a path, the arguments read back (or none) and the follow `,`/`}` stays. -/
theorem argToks_rund (as : List SExpr) (has : ∀ x ∈ as, gut x = true) (R : List Token) (f : Nat)
    (hR : ∀ r, R ≠ .zeichen "(" :: r) (hF : 6 * (druckToksListe as).length + 36 ≤ f) :
    startArgs f (argToks as ++ R) = .ok (as, R) := by
  cases as with
  | nil =>
    simp only [argToks, List.isEmpty_nil, if_true, List.nil_append]
    unfold startArgs
    split
    · rename_i x; exact absurd rfl (hR x)
    · rfl
  | cons x xs =>
    simp only [argToks, List.isEmpty_cons, Bool.false_eq_true, if_false, List.append_assoc, List.cons_append,
      List.nil_append, startArgs]
    have := argsM (x :: xs) R f (fun y hy => ⟨legs_tok y (has y hy), has y hy⟩) hF
    simpa [List.append_assoc] using this

theorem druckToksListe_le_argToks : ∀ (as : List SExpr), (druckToksListe as).length ≤ (argToks as).length
  | [] => by simp only [druckToksListe, List.length_nil, argToks, List.isEmpty_nil, ↓reduceIte, Std.le_refl]
  | x :: xs => by simp only [argToks, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add]; omega


end Gabbro.Grammatik.Parser
