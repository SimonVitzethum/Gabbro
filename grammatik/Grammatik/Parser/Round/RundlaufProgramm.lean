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
  `observed by`), `reason`, `concurrent`. Every expression is `gut`, every type `TypGut`, every
  body `AnwGut .block`, predicates (`requires`/`ensures`/`invariant`, place lists) ride
  `pred_druck`. The pieces are in `RundlaufItem` and `RundlaufGeraet`.

  Main statements: `rundlauf_items` (`parseItemsTief` before `}`, the end marker or nothing),
  `parseTopTief_druck` (the whole program reader, fuel `8 * length + 32`), and
  `rundlauf_programm` -- for printable items whose print is lexically clean,
  `parseTopTief` of `lex (renderText (druckItems its))` is `.ok its`.
-/
import Grammatik.Parser.Round.RundlaufGeraet

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
  | concT (ps : List (List String)) : (∀ p ∈ ps, PfadGut p) → ItemGut (.concT ps)
  | tableT (n : String) (cnt : Option SExpr) (backed owner : Option String) (sh : Bool)
      (parts : List STabTeil) : (∀ e, cnt = some e → gut e = true) → (∀ t ∈ parts, TeilGut t) →
      ItemGut (.tableT n cnt backed owner sh parts)
  | entryT (e : SEingang) : EingangGut e → ItemGut (.entryT e)
  | devT (n : String) (ps : List (String × STyp)) (sp : String) (ms : List SGerTeil) :
      GeraetGut ps ms → ItemGut (.devT n ps sp ms)

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
    simp [h, strEq_self, hts]
  · refine ⟨"const", sigToks sig ++ X, ?_, by decide, by decide⟩
    simp [h, (by decide : strEq "const" "" = false)]
  · have hne : strEq sig.art "" = false := by
      cases e : strEq sig.art ""
      · rfl
      · have := (strEq_eq _ _).mp e; rw [this] at h; exact absurd h (by decide)
    refine ⟨sig.art, sigToks sig ++ X, ?_, ?_, ?_⟩
    · simp [hne]
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
  | tableT n cnt backed owner sh parts hc hp =>
    exact ⟨item_table n cnt backed owner sh parts hc hp,
      itemKopf_wort _ "table" (by decide) (by decide) ⟨_, rfl⟩⟩
  | entryT e he =>
    refine ⟨item_entry e he, itemKopf_wort _ "entry" (by decide) (by decide) ?_⟩
    simp [druckItem, druckEingang_eq]
  | devT n ps sp ms h =>
    refine ⟨item_dev n ps sp ms h, itemKopf_wort _ "device" (by decide) (by decide) ?_⟩
    rw [druckDev_eq]; exact ⟨_, rfl⟩

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


/-! ### Witnesses -/

/-- A program with every covered item kind: `use`, `const` with an array value, `static mut ...
    shared`, a `lock` with `held`, an `atomic` with `publishes nothing` and an order, a `reason`, a
    `module` holding a function with a contract (`requires` with `forall`, `&&` and `exists`, `effects`, `costs`), a result type and
    a body, `concurrent` over a two-segment path, and a `table` with a count, `shared`, a slot field
    with `where` and `by ops`, `ops`, `tree`, `occupied` and a group invariant, and an `entry` with
    every optional clause. The static `max`, the parameter `x` and the table field `x` are table
    words: they print as `wort` and read back as names. -/
def zeugeProgramm : List SItemTief := [
  .useT ["io", "konsole"],
  .constT "N" (.atom "u32") (.rows [.one (.lit 1), .one (.lit 2)]),
  .globT true "max" (.atom "u64") (.one (.lit 0)) none none true,
  .lockT "L" [.variable "max"] (.lit 1) (some (.lit 10)) none none none,
  .atomT "flag" (.atom "bool") (some []) (some "release") none,
  .whyT "Fehler" [("Voll", .lit 1, "voll")] true,
  .modT ("::".intercalate ["kern"]) [
    .fnT { art := "", name := "erhoehe", params := [("x", .atom "u64")], res := some (.atom "u64"),
           fehler := none,
           klauseln := [.needs (.ext .all ["i", "slots"] [.variable "Knoten",
                          .bin "&&" (.bin "<" (.variable "x") (.lit 100))
                            (.ext .any ["t", "threads"] [.bin "==" (.variable "t") (.lit 1)])]),
                        .effs [.writes (.variable "max")], .cost (.lit 5)] }
      (.block [.set (.variable "max") "+=" (.variable "x")] (some (.ret (some (.variable "x")))))],
  .concT [["kern", "erhoehe"]],
  .tableT "Knoten" (some (.lit 64)) none none true [
    .tSlot [{ fname := "x", ftyp := .atom "u32", pos := none, bezug := none,
              wo := some (.bin "<" (.variable "x") (.lit 10)), reserviert := false, byOps := true }],
    .tOps ["einfuegen", "loeschen"],
    .tTree [("parent", "eltern")],
    .tBusy "belegt",
    .tInv { name := "klein", kosten := .lit 1, online := true, proof := none,
            pred := .bin "<" (.variable "n") (.lit 64) }],
  .entryT { name := "tick", vektor := some (.lit 32), via := some "idt", arch := "x86_64",
            regIn := [.binds "rdi" "arg", .reg "rsi"], regOut := [.reg "rax"],
            erhaelt := ["rbx"], kills := ["rcx"], stapel := "kstack", perCpu := true,
            ist := some (.lit 1), nest := some "never", dispatch := ["kern", "erhoehe"] }]

theorem zeugeProgramm_gut : ∀ it ∈ zeugeProgramm, ItemGut it := by
  have atom : ∀ a, typKopf a = false → TypGut (.atom a) := fun a h => by
    have := TypGut.kette (.atom a) [] (.atom a h) (by simp [TsGut]); simpa [applyTS] using this
  intro it hit
  simp only [zeugeProgramm, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .useT _ (by simp)
  · refine .constT _ _ _ (by decide) (atom _ (by decide)) (.rows _ ?_)
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact .one _ (by decide)
  · exact .globT _ _ _ _ _ _ _ (by decide) (atom _ (by decide)) (.one _ (by decide)) (by simp)
  · refine .lockT _ _ _ _ _ _ _ (by simp; decide) (by decide) ?_ (by simp) (by simp)
    intro e he; cases he; decide
  · exact .atomT _ _ _ _ _ (atom _ (by decide)) ⟨by intro ps h p hp; cases h; simp at hp,
      by intro o h; cases h; decide⟩
  · exact .whyT _ _ _ (by intro c hc; simp at hc; subst hc; exact ⟨show gut (.lit 1) = true by decide, by decide⟩)
  · refine .modT ["kern"] _ ⟨by simp, by intro a ha; simp at ha; subst ha; decide⟩ ?_
    intro it hit; simp at hit; subst hit
    refine .fnT _ _ ⟨Or.inl rfl, ?_, atom _ (by decide), ?_⟩ ?_
    · intro p hp; simp at hp; subst hp; exact atom _ (by decide)
    · intro k hk; simp at hk
      rcases hk with rfl | rfl | rfl
      · exact .quant .all "i" "slots" [] [.variable "Knoten"] _ (Or.inl rfl) (.ort _ _ (Or.inl rfl) (by decide))
          (.und _ _ (.expr _ (by decide))
            (.quant .any "t" "threads" [] [] _ (Or.inr rfl) .threads (.expr _ (by decide))))
      · intro e he; simp at he; subst he; show gut _ = true; decide
      · show gut _ = true; decide
    · refine .block _ _ ?_ (by show gut _ = true; decide) (by intro h; cases h)
      intro s hs; simp at hs; subst hs
      exact .set _ _ _ (by decide) (by decide) (by decide)
  · exact .concT _ (by
      intro p hp; simp at hp; subst hp
      exact ⟨by simp, by intro a ha; simp at ha; rcases ha with rfl | rfl <;> decide⟩)
  · refine .tableT _ _ _ _ _ _ (by intro e he; cases he; decide) ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · intro fd hfd; simp at hfd; subst hfd
      exact ⟨atom _ (by decide), by simp, by intro e he; cases he; decide⟩
    · show _ ≠ []; simp
    · exact ⟨by simp, by intro k hk; simp at hk; subst hk; exact Or.inl rfl⟩
    · trivial
    · exact ⟨by decide, .expr _ (by decide), by simp⟩
  · refine .entryT _ ⟨?_, ?_, Or.inr (Or.inl rfl), by simp⟩
    · intro v hv; cases hv; decide
    · intro x hx; cases hx; decide

/-- The witness program reads back through the whole program reader. -/
theorem zeugeProgramm_rund : parseTopTief (druckItems zeugeProgramm ++ [.ende]) = .ok zeugeProgramm :=
  parseTopTief_druck zeugeProgramm zeugeProgramm_gut

/-- The witness program from its rendered source text: lexer, then the program reader. -/
theorem zeugeProgramm_text :
    (match lex (renderText (druckItems zeugeProgramm)) with
      | .ok toks => parseTopTief toks
      | .error _ => .error "lex") = .ok zeugeProgramm :=
  rundlauf_programm zeugeProgramm zeugeProgramm_gut (tokGut_of_all _ (by decide))


/-- A device with a mirror and two registers -- a range type, an address, a class with its stages,
    bit fields, a precondition with its falsifier and carriers -- and a function over the device that
    reads a register (`let x = d.S;`), reads one with its falsifier (`let t = d.T else (e) { .. }`)
    and writes one (`d.C = x;`). -/
def zeugeGeraet : List SItemTief := [
  .whyT "G" [("Z", .lit 1, "z")] true,
  .devT "D" [("b", .atom "u64")] "mmio" [
    .copy (.variable "W") (.variable "R"),
    .reg { name := "S", rtyp := .range (.atom "u32") (.lit 0) (.lit 9) false, addr := .lit 0,
           klasse := "r", stage := [], felder := [], voraus := none, elseF := none, abhaengt := [] },
    .reg { name := "T", rtyp := .range (.atom "u32") (.lit 0) (.lit 9) false, addr := .lit 8,
           klasse := "rw", stage := ["in", "boot", ",", "x", "in", "live"],
           felder := [{ name := "en", pos := "0", klasse := some "w" }, { name := "st", pos := "lo", klasse := none }],
           voraus := some (.bin "<=" (.variable "T") (.lit 8)), elseF := some ("G", "Z"),
           abhaengt := [["Tab"], ["Tab", "x"]] }],
  .fnT { art := "", name := "f", params := [("d", .atom "D"), ("c", .atom "bool")],
         res := some (.range (.atom "u32") (.lit 0) (.lit 9) false), fehler := some "G", klauseln := [] }
    (.block [
      .bind false "x" none (.field (.variable "d") "S"),
      .bindElse "t" none (.field (.variable "d") "T") "e" (.block [] (some (.ret (some (.why "G" "Z"))))),
      .set (.field (.variable "d") "C") "=" (.variable "x")]
      (some (.ret (some (.variable "t")))))]

theorem zeugeGeraet_gut : ∀ it ∈ zeugeGeraet, ItemGut it := by
  have atom : ∀ a, typKopf a = false → TypGut (.atom a) := fun a h => by
    have := TypGut.kette (.atom a) [] (.atom a h) (by simp [TsGut]); simpa [applyTS] using this
  have rng : TypGut (.range (.atom "u32") (.lit 0) (.lit 9) false) :=
    TypGut.kette (.atom "u32") [.rng (.lit 0) (.lit 9) false] (.atom _ (by decide))
      (by intro lo hi x h; simp at h; obtain ⟨rfl, rfl, -⟩ := h; exact ⟨by decide, by decide⟩)
  intro it hit
  simp only [zeugeGeraet, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl
  · exact .whyT _ _ _ (by intro c hc; simp at hc; subst hc; exact ⟨show gut (.lit 1) = true by decide, by decide⟩)
  · refine .devT _ _ _ _ ⟨?_, ?_⟩
    · intro p hp; simp at hp; subst hp; exact atom _ (by decide)
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨rng, by intro _; decide, fun _ => rfl, Or.inl rfl, by simp, by simp, by simp, by simp⟩
      · refine ⟨rng, by intro _; decide, fun h => absurd h (by decide), ?_, ?_, ?_, by simp, ?_⟩
        · exact Or.inr ⟨"boot", _, rfl, by decide, .cons _ _ _ (by decide) (by decide) .nil⟩
        · intro fd hfd; simp at hfd
          rcases hfd with rfl | rfl
          · exact Or.inl ⟨0, rfl⟩
          · exact Or.inr (by decide)
        · intro p hp; cases hp; exact .expr _ (by decide)
        · intro c hc; simp at hc
          rcases hc with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
  · have leer : AnwGut .block (.block [] (some (.ret (some (.why "G" "Z"))))) :=
      .block [] _ (by simp) (show gut (.why "G" "Z") = true by decide) (by intro h; cases h)
    refine .fnT _ _ ⟨Or.inl rfl, ?_, rng, by simp⟩ ?_
    · intro p hp; simp at hp; rcases hp with rfl | rfl <;> exact atom _ (by decide)
    · refine .block _ _ ?_ (show gut (.variable "t") = true by decide) (by intro h; cases h)
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact .bind _ _ _ _ (by decide) trivial (by decide)
      · exact .bindElse _ _ _ _ _ (by decide) trivial (by decide) leer
      · exact .set _ _ _ (by decide) (by decide) (by decide)

/-- The device witness reads back through the whole program reader. -/
theorem zeugeGeraet_rund : parseTopTief (druckItems zeugeGeraet ++ [.ende]) = .ok zeugeGeraet :=
  parseTopTief_druck zeugeGeraet zeugeGeraet_gut

/-- The device witness from its rendered source text. -/
theorem zeugeGeraet_text :
    (match lex (renderText (druckItems zeugeGeraet)) with
      | .ok toks => parseTopTief toks
      | .error _ => .error "lex") = .ok zeugeGeraet :=
  rundlauf_programm zeugeGeraet zeugeGeraet_gut (tokGut_of_all _ (by decide))

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.item_dev
#print axioms Gabbro.Grammatik.Parser.zeugeGeraet_rund
#print axioms Gabbro.Grammatik.Parser.zeugeGeraet_text
#print axioms Gabbro.Grammatik.Parser.rundlauf_items
#print axioms Gabbro.Grammatik.Parser.parseTopTief_druck
#print axioms Gabbro.Grammatik.Parser.rundlauf_programm
#print axioms Gabbro.Grammatik.Parser.zeugeProgramm_rund
#print axioms Gabbro.Grammatik.Parser.zeugeProgramm_text

/-
  CUTS: what the item round trip does not cover yet, and why.

  * Item kinds not in `ItemGut`: `type`, `format`, `arena`, `state`, `assume`,
    `axiom`, `check`, `rcu`, `group`, `accumulates`, `walk`, `entrust`, `boot`, `syscall`,
    `target`, `translator`, `profile`, the spec/asm function bodies (`= pred ;`, `= asm {..} ;`) and
    the `when TESTBUILD` gate; slot bit positions as a `[hi:lo]` group. Each is one more constructor of `ItemGut` with its reader lemma in
    the pattern of `item_lock`/`item_atom` (a named recursive tail reader is a step lemma per
    clause; a `do` block is a case split over its optional clauses). Devices: see
    `RundlaufGeraet` (no `bank`, no `transition` members).
  * Clauses riding as reconstructed text (`by`, `retires`, `deadline`): the reader rebuilds a
    string from tokens (`druck e`, `nimmBisKopf`), the printer re-lexes it; excluded from
    `KlauselGut`.
  * Paths printed as text (`module`, `concurrent`) need name-shaped segments (`PfadGut`): the
    printer re-lexes the joined text.
  * Names print as `nameTok`, so the text-level theorem (`rundlauf_programm`) needs only
    name-shaped names. Names spelled like the word that opens a form where they stand are
    excluded: a `const` named `fn`, a `static` (without `mut`) named `mut`, a `reason` case named
    `exhaustive`, an effect `locks` place headed `shared`.
-/
