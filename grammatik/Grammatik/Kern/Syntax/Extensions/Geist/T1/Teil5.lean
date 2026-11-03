module

public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil4
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil4b
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil6

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

mutual

/-- Soundness for statements. Sub-body ghost-freedom comes from the sibling
    theorems of this `mutual` block. Every premise fires: `h`/`ho` fix the
    decision and the member. -/
theorem g001Stmt_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → (h : g001Stmt s = true) → (o : D.Tab ⊕ D.Glob) → (ho : o ∈ Extraktion.stmtOrte s) →
    ¬ istGeist (D := D) o
  | .assignSlot t f i e hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .ite c t e, zr_h, o, zr_ho =>
      g001Stmt_korrekt_ite (c := c) (t := t) (e := e) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_t := g001_korrekt t) (ih_g001_korrekt_e := g001_korrekt e)
  | .assignThru p t ht f i e hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .assignSlotRef r t ht ho f e hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .assignGlob g e hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .putBytes t f hf n i hlo hhi e hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .assignVar x e, zr_h, o, zr_ho =>
      g001Stmt_korrekt_assignVar (x := x) (e := e) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .shift t f hτ i von nach hn he hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_shift (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .call f args hp hr, zr_h, o, zr_ho =>
      g001Stmt_korrekt_call (f := f) (args := args) (hp := hp) (hr := hr) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .callInd p args hp hr, zr_h, o, zr_ho =>
      g001Stmt_korrekt_callInd (p := p) (args := args) (hp := hp) (hr := hr) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .callIndElse p args he hp hr err, zr_h, o, zr_ho =>
      g001Stmt_korrekt_callIndElse (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_err := g001End_korrekt err)
  | .axiomCall a args h hw hg hd hgd, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have h0 : (orteOk (D := D) args.orte) = true := h
      have ho' : o ∈ args.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .axiomCallElse _ a args _ hp hd hgd _ err, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have h0 : (orteOk (D := D) args.orte && g001End err) = true := h
      have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End err) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001End_korrekt err h1.2 o ho'
  | .regWrite r hk e, zr_h, o, zr_ho =>
      g001Stmt_korrekt_regWrite (r := r) (hk := hk) (e := e) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .publish g e payload hp hw hL, zr_h, o, zr_ho =>
      g001Stmt_korrekt_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .ret e hΛ, zr_h, o, zr_ho =>
      g001Stmt_korrekt_ret (e := e) (hΛ := hΛ) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .transition r hk m hm hl maske bits, zr_h, o, zr_ho =>
      g001Stmt_korrekt_transition (r := r) (hk := hk) (m := m) (hm := hm) (hl := hl) (maske := maske) (bits := bits) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .advances m a h hs, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .retires m s h a, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .retWhy r hΛ, zr_h, o, zr_ho =>
      g001Stmt_korrekt_retWhy (r := r) (hΛ := hΛ) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .leave h, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .next h, zr_h, o, zr_ho => by
      revert zr_h zr_ho
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .onOption opt p a, zr_h, o, zr_ho =>
      g001Stmt_korrekt_onOption (opt := opt) (p := p) (a := a) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_p := g001_korrekt p) (ih_g001_korrekt_a := g001_korrekt a)
  | .onTag v arms, zr_h, o, zr_ho =>
      g001Stmt_korrekt_onTag (v := v) (arms := arms) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001Arms_korrekt_arms := g001Arms_korrekt arms)
  | .onWhy r arms, zr_h, o, zr_ho =>
      g001Stmt_korrekt_onWhy (r := r) (arms := arms) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001Grund_korrekt_arms := g001Grund_korrekt arms)
  | .locks L hr body, zr_h, o, zr_ho =>
      g001Stmt_korrekt_locks (hr := hr) (body := body) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body)
  | .breaking i body, zr_h, o, zr_ho =>
      g001Stmt_korrekt_breaking (i := i) (body := body) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body)
  | .traverse t inv body, zr_h, o, zr_ho =>
      g001Stmt_korrekt_traverse (t := t) (inv := inv) (body := body) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body)
  | .consumeTraverse t member edge inv bound mass body, zr_h, o, zr_ho =>
      g001Stmt_korrekt_consumeTraverse (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body)
  | .retScoped e R, zr_h, o, zr_ho =>
      g001Stmt_korrekt_retScoped (e := e) (R := R) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .retWhyScoped r R, zr_h, o, zr_ho =>
      g001Stmt_korrekt_retWhyScoped (r := r) (R := R) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .retry n bis body ueber, zr_h, o, zr_ho =>
      g001Stmt_korrekt_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body) (ih_g001_korrekt_ueber := g001_korrekt ueber)
  | .forever a inv body, zr_h, o, zr_ho =>
      g001Stmt_korrekt_forever (a := a) (inv := inv) (body := body) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_body := g001_korrekt body)
/-- Soundness for blocks. The `htStmt` premise is statement soundness;
    `htEnd` is end-block soundness. Every premise fires: `h`/`ho` fix the
    decision and the member, `htStmt`/`htEnd` discharge the sub-body legs. -/
theorem g001_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → (h : g001 b = true) → (o : D.Tab ⊕ D.Glob) → (ho : o ∈ Extraktion.blockOrte b) →
    ¬ istGeist (D := D) o
  | .nil, zr_h, o, zr_ho =>
      g001_korrekt_nil (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .cons s rest, zr_h, o, zr_ho =>
      g001_korrekt_cons (s := s) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001Stmt_korrekt_s := g001Stmt_korrekt s) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bind e rest, zr_h, o, zr_ho =>
      g001_korrekt_bind (e := e) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bindCall f args he hp hr rest, zr_h, o, zr_ho =>
      g001_korrekt_bindCall (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bindCallInd p args he hp hr rest, zr_h, o, zr_ho =>
      g001_korrekt_bindCallInd (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bindCallIndElse p args he hp hr err rest, zr_h, o, zr_ho =>
      g001_korrekt_bindCallIndElse (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_err := g001End_korrekt err)
  | .bindCallElse f args he hp hr err rest, zr_h, o, zr_ho =>
      g001_korrekt_bindCallElse (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_err := g001End_korrekt err)
  | .bindAxiom a args he hw hg hd hgd rest, zr_h, o, zr_ho =>
      g001_korrekt_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, zr_h, o, zr_ho =>
      g001_korrekt_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_err := g001End_korrekt err)
  | .bindAxiomOpt e a args he hp hd hgd rest, zr_h, o, zr_ho =>
      g001_korrekt_bindAxiomOpt (zi_e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, zr_h, o, zr_ho =>
      g001_korrekt_bindAxiomOptElse (zi_e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_err := g001End_korrekt err)
  | .regRead r hk rest, zr_h, o, zr_ho =>
      g001_korrekt_regRead (r := r) (hk := hk) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .regReadElse r hk zusage sonst rest, zr_h, o, zr_ho =>
      g001_korrekt_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_sonst := g001End_korrekt sonst)
  | .awaits g payload hp hL hat rest, zr_h, o, zr_ho =>
      g001_korrekt_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .exchange g neu hw hL rest, zr_h, o, zr_ho =>
      g001_korrekt_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .narrow e lo' hi' sonst rest, zr_h, o, zr_ho =>
      g001_korrekt_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_sonst := g001End_korrekt sonst)
  | .narrowRequired e lo' hi' rest, zr_h, o, zr_ho =>
      g001_korrekt_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .check c sonst rest, zr_h, o, zr_ho =>
      g001_korrekt_check (c := c) (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_sonst := g001End_korrekt sonst)
  | .float op a b lo hi rest, zr_h, o, zr_ho =>
      g001_korrekt_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .floatLit q lo hi rest, zr_h, o, zr_ho =>
      g001_korrekt_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .floatOf e lo hi rest, zr_h, o, zr_ho =>
      g001_korrekt_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest)
  | .floatNarrow e lo hi sonst rest, zr_h, o, zr_ho =>
      g001_korrekt_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_rest := g001_korrekt rest) (ih_g001End_korrekt_sonst := g001End_korrekt sonst)
/-- Soundness for case arms. Every premise fires: `h`/`ho` fix the decision
    and the member, `htStmt`/`htEnd`/`htBlockSelf` discharge the legs. -/
theorem g001Arms_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → (h : g001Arms a = true) → (o : D.Tab ⊕ D.Glob) → (ho : o ∈ Extraktion.armsOrte a) →
    ¬ istGeist (D := D) o
  | .nil, zr_h, o, zr_ho =>
      g001Arms_korrekt_nil (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .cons b rest, zr_h, o, zr_ho =>
      g001Arms_korrekt_cons (b := b) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_b := g001_korrekt b) (ih_g001Arms_korrekt_rest := g001Arms_korrekt rest)
/-- Soundness for reason arms. Every premise fires: `h`/`ho` fix the
    decision and the member. -/
theorem g001Grund_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → (h : g001Grund a = true) → (o : D.Tab ⊕ D.Glob) → (ho : o ∈ Extraktion.grundArmsOrte a) →
    ¬ istGeist (D := D) o
  | .nil, zr_h, o, zr_ho =>
      g001Grund_korrekt_nil (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .cons b rest, zr_h, o, zr_ho =>
      g001Grund_korrekt_cons (b := b) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001_korrekt_b := g001_korrekt b) (ih_g001Grund_korrekt_rest := g001Grund_korrekt rest)
/-- The checker's decision is sound: a body with `g001End b = true` reads no
    ghost carrier. The `h` premise is the acceptance fact; `ho` fixes the
    footprint member inspected. -/
theorem g001End_korrekt {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → (h : g001End b = true) → (o : D.Tab ⊕ D.Glob) → (ho : o ∈ Extraktion.endblockOrte b) →
    ¬ istGeist (D := D) o
  | .ret e zz1, zr_h, o, zr_ho =>
      g001End_korrekt_ret (e := e) (zz1 := zz1) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .retWhy zz1 zz2, zr_h, o, zr_ho =>
      g001End_korrekt_retWhy (zz1 := zz1) (zz2 := zz2) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .retScoped e R, zr_h, o, zr_ho =>
      g001End_korrekt_retScoped (e := e) (R := R) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .retWhyScoped zz1 R, zr_h, o, zr_ho =>
      g001End_korrekt_retWhyScoped (zz1 := zz1) (R := R) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .leave zz1, zr_h, o, zr_ho =>
      g001End_korrekt_leave (zz1 := zz1) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .next zz1, zr_h, o, zr_ho =>
      g001End_korrekt_next (zz1 := zz1) (zr_h := zr_h) (o := o) (zr_ho := zr_ho)
  | .cons s rest, zr_h, o, zr_ho =>
      g001End_korrekt_cons (s := s) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001Stmt_korrekt_s := g001Stmt_korrekt s) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bind e rest, zr_h, o, zr_ho =>
      g001End_korrekt_bind (e := e) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindCall a args he zz1 zz2 rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindCall (a := a) (args := args) (he := he) (zz1 := zz1) (zz2 := zz2) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindCallElse f args he hp hr err rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindCallElse (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_err := g001End_korrekt err) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindAxiom a args he hw hg hd hgd rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_err := g001End_korrekt err) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindAxiomOpt e a args he hp hd hgd rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindAxiomOpt (zi_e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindAxiomOptElse (zi_e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_err := g001End_korrekt err) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .regRead r hk rest, zr_h, o, zr_ho =>
      g001End_korrekt_regRead (r := r) (hk := hk) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .regReadElse r hk zusage sonst rest, zr_h, o, zr_ho =>
      g001End_korrekt_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_sonst := g001End_korrekt sonst) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .awaits g payload hp hL hat rest, zr_h, o, zr_ho =>
      g001End_korrekt_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindCallInd p args he hp hr rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindCallInd (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .bindCallIndElse p args he hp hr err rest, zr_h, o, zr_ho =>
      g001End_korrekt_bindCallIndElse (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_err := g001End_korrekt err) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .narrow e lo' hi' sonst rest, zr_h, o, zr_ho =>
      g001End_korrekt_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_sonst := g001End_korrekt sonst) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .narrowRequired e lo' hi' rest, zr_h, o, zr_ho =>
      g001End_korrekt_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .exchange g neu hw hL rest, zr_h, o, zr_ho =>
      g001End_korrekt_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_rest := g001End_korrekt rest)
  | .ite c t e, zr_h, o, zr_ho =>
      g001End_korrekt_ite (c := c) (t := t) (e := e) (zr_h := zr_h) (o := o) (zr_ho := zr_ho) (ih_g001End_korrekt_e := g001End_korrekt e) (ih_g001End_korrekt_t := g001End_korrekt t)
end

end Gabbro.Grammatik.Geist
