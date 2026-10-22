/-
  File:      Grammatik/Gen/Text/Gut.lean
  Subject:   DECIDED PRINTABILITY: Bool checks for the printability classes of the syntax round trip (`TypGut`,
             `PredGut`, `AnwGut`, `ItemGut`, ...), each with its soundness theorem, on the forms the delaborator emits.
             A check may refuse a printable form (it is narrower than the class); it never admits an unprintable one.
             The kernel evaluates a check on a concrete item list, so a printed program's `ItemGut` is one `decide`.
-/
import Grammatik.Gen.Text.AusText

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Parser

/-! ### Types, values, predicates -/

def typGutB : STyp → Bool
  | .atom a => !typKopf a
  | .range (.atom a) lo hi _ => !typKopf a && gut lo && gut hi
  | .ptr _ w t => nameForm w && typGutB t
  | .index _ _ => true
  | _ => false

theorem typGutB_sound (t : STyp) (h : typGutB t = true) : TypGut t := by
  match t, h with
  | .atom a, h =>
    have ha : typKopf a = false := by simpa [typGutB] using h
    have := TypGut.kette (.atom a) [] (.atom a ha) (by simp [TsGut])
    simpa [applyTS] using this
  | .range (.atom a) lo hi x, h =>
    simp only [typGutB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨ha, hlo⟩, hhi⟩ := h
    have := TypGut.kette (.atom a) [.rng lo hi x] (.atom a ha) (by
      intro l h' x' hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, TSuff.rng.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact ⟨hlo, hhi⟩)
    simpa [applyTS, tsStep] using this
  | .ptr r w t, h =>
    simp only [typGutB, Bool.and_eq_true] at h
    exact TypGut.ptr r w t h.1 (typGutB_sound t h.2)
  | .index o t, _ => exact TypGut.index o t

theorem typOptGutB_sound (t : Option STyp) (h : t.all typGutB = true) : TypOptGut t := by
  cases t with
  | none => trivial
  | some t => exact typGutB_sound t (by simpa using h)

/-- Printable predicates, with fuel for the nesting. -/
def predGutB : Nat → SExpr → Bool
  | 0, e => gut e
  | n + 1, e => gut e || match e with
    | .ext .all [_, d] [p, body] => (d == "slots") && gutPlatz p && predGutB n body
    | .ext .any [_, d] [p, body] => (d == "slots") && gutPlatz p && predGutB n body
    | .bin o l r => (o == "&&" || o == "||") && predGutB n l && predGutB n r
    | .un o x => (o == "!") && predGutB n x
    | .ext .imp [] [a, b] => predGutB n a && predGutB n b
    | _ => false

theorem predGutB_sound : ∀ (n : Nat) (e : SExpr), predGutB n e = true → PredGut e := by
  intro n
  induction n with
  | zero => intro e h; exact .expr e (by simpa [predGutB] using h)
  | succ n ih =>
    intro e h
    cases hg : gut e with
    | true => exact .expr e hg
    | false =>
      simp only [predGutB, hg, Bool.false_or] at h
      split at h
      · rename_i x d p body
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hp⟩, hb⟩ := h
        exact .quant .all x "slots" [] [p] body (Or.inl rfl) (.ort "slots" p (Or.inl rfl) hp) (ih body hb)
      · rename_i x d p body
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hp⟩, hb⟩ := h
        exact .quant .any x "slots" [] [p] body (Or.inr rfl) (.ort "slots" p (Or.inl rfl) hp) (ih body hb)
      · rename_i o l r
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨⟨ho | ho, hl⟩, hr⟩ := h
        · subst ho; exact .und l r (ih l hl) (ih r hr)
        · subst ho; exact .oder l r (ih l hl) (ih r hr)
      · rename_i o x
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hx⟩ := h
        exact .nicht x (ih x hx)
      · rename_i a b
        simp only [Bool.and_eq_true] at h
        exact .folgt a b (ih a h.1) (ih b h.2)
      · cases h

/-- A raw text the reader keeps between braces: it is the rendered text of its own tokens, all clean, no brace. -/
def rohZuB (p : String) : Bool :=
  let ts := rohToks p
  renderText ts == p && ts.all fun t => tokGutB t && t != .zeichen "{" && t != .zeichen "}"

theorem rohZuB_sound (p : String) (h : rohZuB p = true) : RohZu p := by
  simp only [rohZuB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨he, hall⟩ := h
  refine ⟨rohToks p, he.symm, fun t ht => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hall t ht
  exact ⟨tokGutB_gut t h1, fun e => by rcases e with e | e <;> simp_all⟩

def pubGutB (p : String) : Bool := p == "nothing" || (rohZuB p && p != "nothing")

theorem pubGutB_sound (p : String) (h : pubGutB p = true) : PubGut p := by
  simp only [pubGutB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨rohZuB_sound p h1, h2⟩

/-! ### Statements -/

def istEnderNicht (ss : List SAnw) : Bool := ss.getLast?.all fun s => !istEnder s

def endeOkB : Option SEnde → Bool
  | some (.ret (some x)) => gut x
  | _ => true

theorem endeOkB_sound (e : Option SEnde) (h : endeOkB e = true) : EndeOk e := by
  match e, h with
  | some (.ret (some x)), h => exact h
  | none, _ => trivial
  | some (.ret none), _ => trivial
  | some (.leave _), _ => trivial
  | some (.next _), _ => trivial

/-- Printable statements and blocks, with fuel for the nesting; `blk` asks for a block. -/
def anwGutB : Nat → Bool → SAnw → Bool
  | 0, _, _ => false
  | n + 1, true, .block ss e =>
    ss.all (anwGutB n false) && endeOkB e && (e.isSome || istEnderNicht ss)
  | _ + 1, true, _ => false
  | _ + 1, false, .bind _ x none e => x != "mut" && gut e
  | n + 1, false, .bindElse x none e _ b => x != "mut" && gut e && anwGutB n true b
  | _ + 1, false, .set z o w => gutPlatz z && istZuweis o && gut w
  | _ + 1, false, .call f xs => nameForm f && !istAnwWort f && gutListe xs
  | n + 1, false, .cond c t [] s => gut c && anwGutB n true t && s.all (anwGutB n true)
  | n + 1, false, .locks false o b => gutPlatz o && kopfName o != "shared" && anwGutB n true b
  | _ + 1, false, .emit z w p => gutPlatz z && gut w && pubGutB p
  | _ + 1, false, .await x q p => x != "mut" && gut q && rohZuB p
  | n + 1, false, .each _ none _ s _ r i body =>
    gut s && r == "" && i.all (predGutB 50) && anwGutB n true body
  | _ + 1, false, .ret none => true
  | _ + 1, false, .ret (some e) => gut e
  | _ + 1, false, _ => false

theorem rohTrav_leer : RohTrav "" := ⟨[], rfl, by simp⟩

theorem anwGutB_sound : ∀ (n : Nat) (b : Bool) (s : SAnw), anwGutB n b s = true →
    AnwGut (if b then .block else .anw) s := by
  intro n
  induction n with
  | zero => intro b s h; simp [anwGutB] at h
  | succ n ih =>
    intro b s h
    cases b with
    | true =>
      simp only [ite_true]
      match s, h with
      | .block ss e, h =>
        simp only [anwGutB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
        obtain ⟨⟨hss, he⟩, hend⟩ := h
        refine .block ss e (fun s hs => by simpa using ih false s (hss s hs)) (endeOkB_sound e he) ?_
        intro hn s hl
        rcases hend with h1 | h1
        · rw [hn] at h1; cases h1
        · simp only [istEnderNicht, hl, Option.all_some, Bool.not_eq_true'] at h1; exact h1
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      match s, h with
      | .bind m x none e, h =>
        simp only [anwGutB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        exact .bind m x none e h.1 trivial h.2
      | .bindElse x none e f b, h =>
        simp only [anwGutB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        exact .bindElse x none e f b h.1.1 trivial h.1.2 (by simpa using ih true b h.2)
      | .set z o w, h =>
        simp only [anwGutB, Bool.and_eq_true] at h
        exact .set z o w h.1.1 h.1.2 h.2
      | .call f xs, h =>
        simp only [anwGutB, Bool.and_eq_true, Bool.not_eq_true'] at h
        exact .call f xs h.1.1 h.1.2 h.2
      | .cond c t [] s, h =>
        simp only [anwGutB, Bool.and_eq_true] at h
        refine .cond c t [] s h.1.1 (by simpa using ih true t h.1.2) (by simp) ?_
        intro b hb; subst hb; simpa using ih true b (by simpa using h.2)
      | .locks false o b, h =>
        simp only [anwGutB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        exact .locks false o b h.1.1 (fun _ => h.1.2) (by simpa using ih true b h.2)
      | .emit z w p, h =>
        simp only [anwGutB, Bool.and_eq_true] at h
        exact .emit z w p h.1.1 h.1.2 (pubGutB_sound p h.2)
      | .await x q p, h =>
        simp only [anwGutB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        exact .await x q p h.1.1 h.1.2 (rohZuB_sound p h.2)
      | .each b none k s m r i body, h =>
        simp only [anwGutB, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hs, rfl⟩, hi⟩, hb⟩ := h
        refine .each b none k s m "" i body (by simp) hs rohTrav_leer ?_ (by simpa using ih true body hb)
        intro e he; subst he; exact predGutB_sound 50 e (by simpa using hi)
      | .ret none, _ => exact .retLeer
      | .ret (some e), h => exact .ret e (by simpa [anwGutB] using h)

/-! ### Items -/

def effGutB : SEffekt → Bool
  | .writes p => gut p
  | .locks sh p => gut p && (sh || match druckToks p with
    | .wort w :: _ => w != "shared"
    | _ => true)
  | _ => false

theorem effGutB_sound (e : SEffekt) (h : effGutB e = true) : EffGut e := by
  match e, h with
  | .writes p, h => exact h
  | .locks sh p, h =>
    simp only [effGutB, Bool.and_eq_true, Bool.or_eq_true] at h
    refine ⟨h.1, fun hs ts hd => ?_⟩
    subst hs
    rcases h.2 with h2 | h2
    · cases h2
    · rw [hd] at h2; simp at h2

def klauselGutB : SKlausel → Bool
  | .needs p => predGutB 50 p
  | .gives p => predGutB 50 p
  | .effs es => es.all effGutB
  | _ => false

theorem klauselGutB_sound (k : SKlausel) (h : klauselGutB k = true) : KlauselGut k := by
  match k, h with
  | .needs p, h => exact predGutB_sound 50 p h
  | .gives p, h => exact predGutB_sound 50 p h
  | .effs es, h =>
    intro e he
    exact effGutB_sound e (List.all_eq_true.1 h e he)

def sigGutB (s : FnSig) : Bool :=
  (s.art == "" || s.art == "const" || istMod s.art) && s.params.all (fun p => typGutB p.2) &&
    s.res.all typGutB && s.klauseln.all klauselGutB

theorem sigGutB_sound (s : FnSig) (h : sigGutB s = true) : SigGut s := by
  simp only [sigGutB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨ha, hp⟩, hr⟩, hk⟩ := h
  refine ⟨?_, fun p hm => typGutB_sound _ (hp p hm), typOptGutB_sound _ hr, fun k hm => klauselGutB_sound k (hk k hm)⟩
  rcases ha with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

def regGutB (r : SReg) : Bool :=
  typGutB r.rtyp && gut r.addr && r.klasse != "" && r.stage.isEmpty &&
    r.felder.isEmpty && r.voraus.all (predGutB 50) && (r.voraus.isSome || r.elseF.isNone) &&
    r.abhaengt.all (fun c => c.length == 1 || c.length == 2)

theorem regGutB_sound (r : SReg) (h : regGutB r = true) : RegGut r := by
  simp only [regGutB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.isEmpty_iff,
    List.all_eq_true, beq_iff_eq, Option.isSome_iff_exists, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ht, ha⟩, hk⟩, hs⟩, hf⟩, hv⟩, he⟩, hc⟩ := h
  refine ⟨typGutB_sound _ ht, ?_, fun e => absurd e hk, Or.inl hs, by simp [hf], ?_, ?_, fun c hm => hc c hm⟩
  · exact fun _ => ha
  · intro p hp
    rw [hp] at hv
    exact predGutB_sound 50 p (by simpa using hv)
  · intro hn
    rcases he with ⟨a, ha⟩ | he
    · rw [hn] at ha; cases ha
    · exact he

def gerGutB : SGerTeil → Bool
  | .copy a b => gut a && gut b
  | .reg r => regGutB r
  | _ => false

theorem gerGutB_sound (m : SGerTeil) (h : gerGutB m = true) : GerGut m := by
  match m, h with
  | .copy a b, h => simpa [gerGutB, GerGut] using h
  | .reg r, h => exact regGutB_sound r h

def invGutB (i : SGruppenInv) : Bool := gut i.kosten && predGutB 50 i.pred && i.proof.isNone

theorem invGutB_sound (i : SGruppenInv) (h : invGutB i = true) : InvGut i := by
  simp only [invGutB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1, predGutB_sound 50 _ h.1.2, fun x hx => by rw [h.2] at hx; cases hx⟩

def feldGutB (f : SFeld) : Bool := typGutB f.ftyp && f.pos.isNone && f.wo.isNone

def teilGutB : STabTeil → Bool
  | .tSlot fs => fs.all feldGutB
  | _ => false

theorem teilGutB_sound (t : STabTeil) (h : teilGutB t = true) : TeilGut t := by
  match t, h with
  | .tSlot fs, h =>
    intro f hf
    have := List.all_eq_true.1 h f hf
    simp only [feldGutB, Bool.and_eq_true, Option.isNone_iff_eq_none] at this
    exact ⟨typGutB_sound _ this.1.1, (fun p hp => by rw [this.1.2] at hp; cases hp),
      (fun e he => by rw [this.2] at he; cases he)⟩

/-- Printable items, with fuel for the nesting of modules. -/
def itemGutB : Nat → SItemTief → Bool
  | 0, _ => false
  | n + 1, .modT name its => nameForm name && its.all (itemGutB n)
  | _ + 1, .tableT _ cnt _ _ _ parts => cnt.all gut && parts.all teilGutB
  | _ + 1, .globT _ x t (.one v) al _ _ => x != "mut" && typGutB t && gut v && al.all gut
  | _ + 1, .atomT _ t pub ord _ => typGutB t && pub.all (·.all gut) && ord.all istOrdnung
  | _ + 1, .lockT _ ps rk h sh _ inv => ps.all gut && gut rk && h.all gut && sh.all gut && inv.all gut
  | _ + 1, .devT _ ps _ ms => ps.all (fun p => typGutB p.2) && ms.all gerGutB
  | _ + 1, .whyT _ cs _ => cs.all fun c => gut c.2.1 && c.1 != "exhaustive"
  | _ + 1, .groupT _ ms ivs => !ms.isEmpty && ivs.all invGutB
  | _ + 1, .fnT sig b => sigGutB sig && anwGutB 100 true b
  | _ + 1, .concT ps => ps.all fun p => !p.isEmpty && p.all nameForm
  | _ + 1, .entryT e => e.vektor.all gut && e.ist.all gut &&
      (e.nest.isNone || e.nest == some "never" || e.nest == some "masked") && !e.dispatch.isEmpty
  | _ + 1, _ => false

theorem itemGutB_sound : ∀ (n : Nat) (it : SItemTief), itemGutB n it = true → ItemGut it := by
  intro n
  induction n with
  | zero => intro it h; simp [itemGutB] at h
  | succ n ih =>
    intro it h
    match it, h with
    | .modT name its, h =>
      simp only [itemGutB, Bool.and_eq_true, List.all_eq_true] at h
      have := ItemGut.modT [name] its ⟨by simp, by simpa using h.1⟩ (fun it hm => ih it (h.2 it hm))
      simpa using this
    | .tableT x cnt b o sh parts, h =>
      simp only [itemGutB, Bool.and_eq_true, List.all_eq_true] at h
      refine .tableT x cnt b o sh parts ?_ (fun t ht => teilGutB_sound t (h.2 t ht))
      intro e he; subst he; simpa using h.1
    | .globT m x t (.one v) al s sh, h =>
      simp only [itemGutB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      refine .globT m x t (.one v) al s sh h.1.1.1 (typGutB_sound t h.1.1.2) (.one v h.1.2) ?_
      intro e he; subst he; simpa using h.2
    | .atomT x t pub ord obs, h =>
      simp only [itemGutB, Bool.and_eq_true] at h
      refine .atomT x t pub ord obs (typGutB_sound t h.1.1) ⟨?_, ?_⟩
      · intro ps hps p hp; subst hps; exact List.all_eq_true.1 (by simpa using h.1.2) p hp
      · intro o ho; subst ho; simpa using h.2
    | .lockT x ps rk hh sh m inv, h =>
      simp only [itemGutB, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨hps, hrk⟩, hh'⟩, hsh⟩, hinv⟩ := h
      refine .lockT x ps rk hh sh m inv hps hrk ?_ ?_ ?_
      · intro e he; subst he; simpa using hh'
      · intro e he; subst he; simpa using hsh
      · intro e he; subst he; simpa using hinv
    | .devT x ps sp ms, h =>
      simp only [itemGutB, Bool.and_eq_true, List.all_eq_true] at h
      exact .devT x ps sp ms ⟨fun p hp => typGutB_sound _ (h.1 p hp), fun m hm => gerGutB_sound m (h.2 m hm)⟩
    | .whyT x cs ex, h =>
      simp only [itemGutB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact .whyT x cs ex fun c hc => h c hc
    | .groupT x ms ivs, h =>
      simp only [itemGutB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at h
      exact .groupT x ms ivs h.1 fun i hi => invGutB_sound i (h.2 i hi)
    | .fnT sig b, h =>
      simp only [itemGutB, Bool.and_eq_true] at h
      exact .fnT sig b (sigGutB_sound sig h.1) (by simpa using anwGutB_sound 100 true b h.2)
    | .concT ps, h =>
      simp only [itemGutB, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at h
      exact .concT ps fun p hp => ⟨(h p hp).1, (h p hp).2⟩
    | .entryT e, h =>
      simp only [itemGutB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨⟨hv, hi⟩, hn⟩, hd⟩ := h
      refine .entryT e ⟨?_, ?_, ?_, hd⟩
      · intro v hv'; rw [hv'] at hv; simpa using hv
      · intro x hx; rw [hx] at hi; simpa using hi
      · rcases hn with (hn | hn) | hn
        · exact Or.inl hn
        · exact Or.inr (Or.inl hn)
        · exact Or.inr (Or.inr hn)

/-- **The printable item lists**, decided. -/
def itemsGutB (its : List SItemTief) : Bool :=
  its.all (itemGutB 100) && (druckItems its).all tokGutB

theorem itemsGutB_sound (its : List SItemTief) (h : itemsGutB its = true) :
    (∀ it ∈ its, ItemGut it) ∧ ∀ t ∈ druckItems its, TokGut t := by
  simp only [itemsGutB, Bool.and_eq_true] at h
  exact ⟨fun it hm => itemGutB_sound 100 it (List.all_eq_true.1 h.1 it hm), tokGut_of_all _ h.2⟩

/-- **The text reader on a decided-printable print is the item reader.** -/
theorem ausText_druckB (its : List SItemTief) (h : itemsGutB its = true) :
    ausText (renderText (druckItems its)) = ausItems its :=
  ausText_druck its (itemsGutB_sound its h).1 (itemsGutB_sound its h).2

end Gabbro.Grammatik.Gen.Text
