/-
  File:      Grammatik/Parser/Round/RundlaufProgramm.lean
  Subject:   Layer L2c: items read back -- `parseItemsTief`/`parseTopTief` of the item printer's tokens
             (`druckItem`, Print/Item.lean) return the items -- and the composition of all layers:
             `parseTopTief` of the lexed rendered text of printable items is `.ok items`.

  The class `ItemGut` (stated in full below) covers: `module` (a `::` path of name-shaped words, nested
  items), `use`, `const` (expression or nested array values), `static` (with
  `aligned`, `section`, `shared`), `table` (count/backed/owner/shared head; `const`, `slot` fields
  with bit position, `offset_into`, `where`, `reserved`, `by ops`; group invariants; `ops`; `tree`;
  `occupied`), `entry` (vector, `via`, `arch`, `ist`, `nested`, `per cpu`, saves, dispatch),
  `device` (parameters, space, `mirrors` and `reg` members with type, address, class and phases,
  fields, `requires` with `else`, `depends`), `fn` with its whole head (modifier, parameters,
  result, `or` channel, the clauses `requires`, `ensures`, `maintains`, `refines`, `effects`,
  `costs`, `decreases`, `payload`, `section`, `arch`, `advances`) and a block body or `;`, `lock`
  (with `held`, `shared held`, `masks`, `invariant`), `atomic` (with `publishes`, an order,
  `observed by`), `reason`, `concurrent`, `group` (members, invariants). Every expression is `gut`, every type `TypGut`, every
  body `AnwGut .block`, predicates (`requires`/`ensures`/`invariant`, place lists) ride
  `pred_druck`. The pieces are in `RundlaufItem` and `RundlaufGeraet`.

  Main statements: `rundlauf_items` (`parseItemsTief` before `}`, the end marker or nothing),
  `parseTopTief_druck` (the whole program reader, fuel `8 * length + 32`), and
  `rundlauf_programm` -- for printable items whose print is lexically clean,
  `parseTopTief` of `lex (renderText (druckItems its))` is `.ok its`.
-/
module
public import Grammatik.Parser.Round.RundlaufGeraet.Teil2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
@[expose] public section


namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### The printability class of items and the induction -/

/-- **The printability class of items** (see the header). -/
inductive ItemGut : SItemTief → Prop
  | modT (segs : List String) (its : List SItemTief) :
      PfadGut segs → (∀ it ∈ its, ItemGut it) → ItemGut (.modT ("::".intercalate segs) its)
  | useT (p : List String) : p ≠ [] → ItemGut (.useT p)
  | constT (n : String) (t : STyp) (v : SKonstWert) : n ≠ "fn" → TypGut t → KonstGut v →
      ItemGut (.constT n t v)
  | globT (m : Bool) (n : String) (t : STyp) (v : SKonstWert) (al : Option SExpr) (s : Option String)
      (sh : Bool) : n ≠ "mut" → TypGut t → KonstGut v → (∀ e, al = some e → gut e = true) →
      ItemGut (.globT m n t v al s sh)
  | fnT (sig : FnSig) (b : SAnw) : SigGut sig → AnwGut .block b → ItemGut (.fnT sig b)
  | protoT (sig : FnSig) : SigGut sig → ItemGut (.protoT sig)
  | lockT (n : String) (ps : List SExpr) (rk : SExpr) (h sh : Option SExpr) (m : Option String)
      (inv : Option SExpr) : (∀ p ∈ ps, gut p = true) → gut rk = true → (∀ e, h = some e → gut e = true) →
      (∀ e, sh = some e → gut e = true) → (∀ e, inv = some e → gut e = true) →
      ItemGut (.lockT n ps rk h sh m inv)
  | atomT (n : String) (t : STyp) (pub : Option (List SExpr)) (ord obs : Option String) :
      TypGut t → AtomGut pub ord → ItemGut (.atomT n t pub ord obs)
  | whyT (n : String) (cs : List (String × SExpr × String)) (ex : Bool) :
      (∀ c ∈ cs, FallGut c) → ItemGut (.whyT n cs ex)
  | concT (ps : List (List String × List SExpr)) : (∀ p ∈ ps, PfadGut p.1 ∧ ∀ x ∈ p.2, gut x = true) →
      ItemGut (.concT ps)
  | tableT (n : String) (von : Option String) (cnt : Option SExpr) (backed owner : Option String) (sh : Bool)
      (parts : List STabTeil) : (∀ e, cnt = some e → gut e = true) → (∀ t ∈ parts, TeilGut t) →
      ItemGut (.tableT n von cnt backed owner sh parts)
  | entryT (e : SEingang) : EingangGut e → ItemGut (.entryT e)
  | devT (n : String) (ps : List (String × STyp)) (sp : String) (ms : List SGerTeil) :
      GeraetGut ps ms → ItemGut (.devT n ps sp ms)
  | groupT (n : String) (ms : List String) (ivs : List SGruppenInv) :
      ms ≠ [] → (∀ i ∈ ivs, InvGut i) → ItemGut (.groupT n ms ivs)

theorem itemKopf_wort (it : SItemTief) (w : String) (h1 : w ≠ "when") (h2 : w ≠ "pub")
    (h : ∃ ts, druckItem it = .wort w :: ts) : ItemKopf it := by
  obtain ⟨ts, h⟩ := h; exact ⟨w, ts, h, h1, h2⟩

theorem fn_kopf (sig : FnSig) (hs : SigGut sig) (X : List Token) :
    ∃ w ts, druckFnSig sig ++ X = .wort w :: ts ∧ w ≠ "when" ∧ w ≠ "pub" := by
  obtain ⟨hart, -⟩ := hs
  obtain ⟨ts, hts⟩ := sigToks_kopf sig
  rw [druckFnSig_eq]
  rcases hart with h | h | h
  · refine ⟨"fn", ts ++ X, ?_, by decide, by decide⟩
    simp only [h, strEq_self, ↓reduceIte, hts, List.nil_append, List.cons_append]
  · refine ⟨"const", sigToks sig ++ X, ?_, by decide, by decide⟩
    simp [h, (by decide : strEq "const" "" = false)]
  · have hne : strEq sig.art "" = false := by
      cases e : strEq sig.art ""
      · rfl
      · have := (strEq_eq _ _).mp e; rw [this] at h; exact absurd h (by decide)
    refine ⟨sig.art, sigToks sig ++ X, ?_, ?_, ?_⟩
    · simp only [hne, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    · intro e; rw [e] at h; exact absurd h (by decide)
    · intro e; rw [e] at h; exact absurd h (by decide)

/-- **The induction over items.** -/
theorem item_bein : ∀ (it : SItemTief), ItemGut it → ItemBein it ∧ ItemKopf it := by
  intro it h
  induction h with
  | modT segs its hs _ ih =>
    exact ⟨item_mod segs its hs ih, itemKopf_wort _ "module" (by decide) (by decide) ⟨_, rfl⟩⟩
  | useT p hp => exact ⟨item_use p hp, itemKopf_wort _ "use" (by decide) (by decide) ⟨_, rfl⟩⟩
  | constT n t v hn ht hv =>
    exact ⟨item_const n hn t v ht hv, itemKopf_wort _ "const" (by decide) (by decide) ⟨_, rfl⟩⟩
  | globT m n t v al s sh hn ht hv hal =>
    exact ⟨item_static m n hn t v al s sh ht hv hal, itemKopf_wort _ "static" (by decide) (by decide) ⟨_, rfl⟩⟩
  | fnT sig b hs hb =>
    obtain ⟨hbb, hbk⟩ := bein_gut .block b hb
    refine ⟨item_fn sig b hs hbb hbk, ?_⟩
    obtain ⟨w, ts, hd, h1, h2⟩ := fn_kopf sig hs (druckAnw b)
    exact ⟨w, ts, by simpa [druckItem] using hd, h1, h2⟩
  | protoT sig hs =>
    refine ⟨item_proto sig hs, ?_⟩
    obtain ⟨w, ts, hd, h1, h2⟩ := fn_kopf sig hs [.zeichen ";"]
    exact ⟨w, ts, by simpa [druckItem] using hd, h1, h2⟩
  | lockT n ps rk h sh m inv hps hrk hh hs hi =>
    exact ⟨item_lock n ps rk h sh m inv hps hrk hh hs hi,
      itemKopf_wort _ "lock" (by decide) (by decide) ⟨_, rfl⟩⟩
  | atomT n t pub ord obs ht hg =>
    exact ⟨item_atom n t pub ord obs ht hg, itemKopf_wort _ "atomic" (by decide) (by decide) ⟨_, rfl⟩⟩
  | whyT n cs ex hg => exact ⟨item_why n cs ex hg, itemKopf_wort _ "reason" (by decide) (by decide) ⟨_, rfl⟩⟩
  | concT ps hps =>
    exact ⟨item_conc ps hps, itemKopf_wort _ "concurrent" (by decide) (by decide) ⟨_, rfl⟩⟩
  | tableT n von cnt backed owner sh parts hc hp =>
    exact ⟨item_table n von cnt backed owner sh parts hc hp,
      itemKopf_wort _ "table" (by decide) (by decide) ⟨_, rfl⟩⟩
  | entryT e he =>
    refine ⟨item_entry e he, itemKopf_wort _ "entry" (by decide) (by decide) ?_⟩
    simp only [druckItem, druckEingang_eq, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
  true_and, exists_eq']
  | devT n ps sp ms h =>
    refine ⟨item_dev n ps sp ms h, itemKopf_wort _ "device" (by decide) (by decide) ?_⟩
    rw [druckDev_eq]; exact ⟨_, rfl⟩
  | groupT n ms ivs hms hivs =>
    exact ⟨item_group n ms ivs hms hivs, itemKopf_wort _ "group" (by decide) (by decide) ⟨_, rfl⟩⟩

/-- **L2c: printable items read back** through `parseItemsTief`, before `}`, the end marker or
    nothing. -/
theorem rundlauf_items (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it) (R : List Token)
    (hR : ItemsEnde R) (F : Nat) (hF : 8 * (druckItems its).length + 39 ≤ F) :
    parseItemsTief F (druckItems its ++ R) = .ok (its, R) :=
  items_rund its R F (fun it hit => item_bein it (h it hit)) hR hF

/-- **The whole program reader** (`parseTopTief`, fuel `8 * length + 32`) returns every list of
    printable items. -/
theorem parseTopTief_druck (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it) :
    parseTopTief (druckItems its ++ [.ende]) = .ok its := by
  unfold parseTopTief
  rw [rundlauf_items its h [.ende] (Or.inr (Or.inr ⟨[], rfl⟩)) _
    (by simp only [List.length_append, List.length_singleton]; omega)]

/-- **The composition of all layers**: printable items whose print is lexically clean read back
    from their rendered source text -- lexer (L1), then the program reader (L2c over L2b over
    L2a). -/
theorem rundlauf_programm (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it)
    (ht : ∀ t ∈ druckItems its, TokGut t) :
    (match lex (renderText (druckItems its)) with
      | .ok toks => parseTopTief toks
      | .error _ => .error "lex") = .ok its := by
  rw [lex_render _ ht]
  exact parseTopTief_druck its h


end Gabbro.Grammatik.Parser
