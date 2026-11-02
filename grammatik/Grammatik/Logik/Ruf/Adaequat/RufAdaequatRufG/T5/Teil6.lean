module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5.Teil5

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimOk
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)
variable (hRuf : RufOk P O passes f A R C)
include hRuf

set_option linter.unusedSectionVars false in
mutual

theorem stmtOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C mr s →
    SimOkSR P O passes f fn stapel rho s0 A R s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs =>
      stmtOkR_ite (c := c) (t := t) (e := e) (hs := hs) (ih_blockOkR_t := blockOkR t) (ih_blockOkR_e := blockOkR e) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .onOption o p a, hs =>
      stmtOkR_onOption (o := o) (p := p) (a := a) (hs := hs) (ih_blockOkR_p := blockOkR p) (ih_blockOkR_a := blockOkR a) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, Λ₀, _, .onTag v arms, hs =>
      stmtOkR_onTag (v := v) (arms := arms) (hs := hs) (ih_armsOkR_arms := armsOkR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .onWhy r arms, hs =>
      stmtOkR_onWhy (r := r) (arms := arms) (hs := hs) (ih_grundOkR_arms := grundOkR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .call g args hp hr, hs =>
      stmtOkR_call (g := g) (args := args) (hp := hp) (hr := hr) (hs := hs) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .locks L hr body, hs =>
      stmtOkR_locks (hr := hr) (body := body) (hs := hs) (ih_blockOkR_body := blockOkR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .breaking i body, hs =>
      stmtOkR_breaking (i := i) (body := body) (hs := hs) (ih_blockOkR_body := blockOkR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .traverse t inv body, hs =>
      stmtOkR_traverse (t := t) (inv := inv) (body := body) (hs := hs) (ih_blockOkR_body := blockOkR body) (ih_blockAbbR_body := blockAbbR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .consumeTraverse .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retry n bis body ueber, hs =>
      stmtOkR_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (hs := hs) (ih_blockOkR_body := blockOkR body) (ih_blockOkR_ueber := blockOkR ueber) (ih_blockAbbR_body := blockAbbR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .forever a inv body, hs =>
      stmtOkR_forever (a := a) (inv := inv) (body := body) (hs := hs) (ih_blockOkR_body := blockOkR body) (ih_blockAbbR_body := blockAbbR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCallElse .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .ret .., _ => by
      intro log σ σ' ρ ρ' hex
      simp only [execStmt, reduceCtorEq] at hex
  | _, _, _, _, _, .retWhy .., _ => by
      intro log σ σ' ρ ρ' hex
      simp only [execStmt, reduceCtorEq] at hex
  | _, _, _, _, _, .retScoped .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retWhyScoped .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .leave .., _ => by
      intro log σ σ' ρ ρ' hex
      simp only [execStmt, reduceCtorEq] at hex
  | _, _, _, _, _, .next .., _ => by
      intro log σ σ' ρ ρ' hex
      simp only [execStmt, reduceCtorEq] at hex

theorem blockOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C mr b →
    SimOkBR P O passes f fn stapel rho s0 A R b
  | _, _, _, _, _, .nil, zzh1 =>
      blockOkR_nil (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .cons s rest, hb =>
      blockOkR_cons (s := s) (rest := rest) (hb := hb) (ih_stmtOkR_s := stmtOkR s) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bind e rest, hb =>
      blockOkR_bind (e := e) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bindCall g args he hp hr rest, hb =>
      blockOkR_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse g args he hp hr err rest, hb =>
      blockOkR_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOpt .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOptElse .., hb => by cases hb
  | _, _, _, _, _, .regRead r hk rest, hb =>
      blockOkR_regRead (r := r) (hk := hk) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .regReadElse r hk zusage sonst rest, hb =>
      blockOkR_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .awaits g payload hp hL hat rest, hb =>
      blockOkR_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb =>
      blockOkR_exchange (g := g) (neuE := neuE) (hw := hw) (hL := hL) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .narrow e lo' hi' sonst rest, hb =>
      blockOkR_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .narrowRequired _ _ _ _, hb => by cases hb
  | _, _, _, _, _, .check c sonst rest, hb =>
      blockOkR_check (c := c) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .float op a b lo hi rest, hb =>
      blockOkR_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatLit q lo hi rest, hb =>
      blockOkR_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatOf e lo hi rest, hb =>
      blockOkR_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatNarrow e lo hi sonst rest, hb =>
      blockOkR_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockOkR_rest := blockOkR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
theorem armsOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C mr arms → ∀ (v : Wert D (.sum cs)),
    SimOkBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsOkR rest ha.cons_inv.2 _

theorem grundOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C mr arms →
    ∀ (r : Fin n), SimOkBR P O passes f fn stapel rho s0 A R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundOkR rest ha.cons_inv.2 _


theorem stmtAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C mr s →
    SimAbbSR P O passes f fn stapel rho s0 A R s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs =>
      stmtAbbR_ite (c := c) (t := t) (e := e) (hs := hs) (ih_blockAbbR_t := blockAbbR t) (ih_blockAbbR_e := blockAbbR e) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .onOption o p a, hs =>
      stmtAbbR_onOption (o := o) (p := p) (a := a) (hs := hs) (ih_blockAbbR_p := blockAbbR p) (ih_blockAbbR_a := blockAbbR a) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, Λ₀, _, .onTag v arms, hs =>
      stmtAbbR_onTag (v := v) (arms := arms) (hs := hs) (ih_armsAbbR_arms := armsAbbR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .onWhy r arms, hs =>
      stmtAbbR_onWhy (r := r) (arms := arms) (hs := hs) (ih_grundAbbR_arms := grundAbbR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .call g args hp hr, zzh1 =>
      stmtAbbR_call (g := g) (args := args) (hp := hp) (hr := hr) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .locks L hr body, hs =>
      stmtAbbR_locks (hr := hr) (body := body) (hs := hs) (ih_blockAbbR_body := blockAbbR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .breaking i body, hs =>
      stmtAbbR_breaking (i := i) (body := body) (hs := hs) (ih_blockAbbR_body := blockAbbR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, l0, _, _, _, .traverse t inv body, zzh1 =>
      stmtAbbR_traverse (t := t) (inv := inv) (body := body) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .consumeTraverse .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retry n bis body ueber, hs =>
      stmtAbbR_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (hs := hs) (ih_blockOkR_body := blockOkR body) (ih_blockAbbR_body := blockAbbR body) (ih_blockAbbR_ueber := blockAbbR ueber) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, l0, _, _, _, .forever a inv body, zzh1 =>
      stmtAbbR_forever (a := a) (inv := inv) (body := body) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCallElse .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .ret .., _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp only [Ausgang.abb?, execStmt, reduceCtorEq] at hex
  | _, _, _, _, _, .retWhy .., _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp only [Ausgang.abb?, execStmt, reduceCtorEq] at hex
  | _, _, _, _, _, .retScoped .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retWhyScoped .., hs => by exact absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .leave h, zzh1 =>
      stmtAbbR_leave (h := h) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .next h, zzh1 =>
      stmtAbbR_next (h := h) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
theorem blockAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C mr b →
    SimAbbBR P O passes f fn stapel rho s0 A R b
  | _, _, _, _, _, .nil, _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp only [Ausgang.abb?, execBlock, reduceCtorEq] at hex
  | _, _, _, _, _, .cons s rest, hb =>
      blockAbbR_cons (s := s) (rest := rest) (hb := hb) (ih_stmtOkR_s := stmtOkR s) (ih_stmtAbbR_s := stmtAbbR s) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bind e rest, hb =>
      blockAbbR_bind (e := e) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bindCall g args he hp hr rest, hb =>
      blockAbbR_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by
      intro hl
      have h0 := hb.bindCallElse_inv.2.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOpt .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOptElse .., hb => by cases hb
  | _, _, _, _, _, .regRead r hk rest, hb =>
      blockAbbR_regRead (r := r) (hk := hk) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .regReadElse .., hb => by
      intro hl
      have h0 := hb.regLiesElse_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .awaits g payload hp hL hat rest, hb =>
      blockAbbR_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb =>
      blockAbbR_exchange (g := g) (neuE := neuE) (hw := hw) (hL := hL) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .narrow .., hb => by
      intro hl
      have h0 := hb.narrow_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .narrowRequired _ _ _ _, hb => by cases hb
  | _, _, _, _, _, .check .., hb => by
      intro hl
      have h0 := hb.pruefung_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .float op a b lo hi rest, hb =>
      blockAbbR_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatLit q lo hi rest, hb =>
      blockAbbR_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatOf e lo hi rest, hb =>
      blockAbbR_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockAbbR_rest := blockAbbR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (stapel := stapel) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (hRuf := hRuf)
  | _, _, _, _, _, .floatNarrow .., hb => by
      intro hl
      have h0 := hb.gleitNarrow_inv.2.2.2
      subst h0
      cases hl

theorem armsAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C mr arms → ∀ (v : Wert D (.sum cs)),
    SimAbbBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockAbbR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsAbbR rest ha.cons_inv.2 _

theorem grundAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C mr arms →
    ∀ (r : Fin n), SimAbbBR P O passes f fn stapel rho s0 A R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockAbbR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundAbbR rest ha.cons_inv.2 _


end

end SimOk

end Gabbro.Grammatik
