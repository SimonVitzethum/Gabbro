module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7.Teil3

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimRet
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (A : D.Lock → Prop)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop)
  (ziel : ErgVal D (D.erg fn) → RufRahmenG D) (zielG : Fin (D.gruende fn) → RufRahmenG D)
variable (hRuf : RufOk P O passes f A R C)
include hRuf

set_option linter.unusedSectionVars false in
theorem endRetR_retWhy 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hperm)
    (zzh1 : EndR A C (.retWhy r hperm : Endblock D (vertragVon D fn) l Γ Λ))
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.retWhy r hperm : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ _
  have hW := hZ.welt
  simp only [execEnd, EndAusgang.ende?, Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_rueckGrundP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe r hperm ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩

set_option linter.unusedSectionVars false in
theorem endRetR_cons 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (he : EndR A C (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_stmtRetR_s : StmtR A C true s → SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s)
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  obtain ⟨hs, hr, _⟩ := he.cons_inv
  rcases execEnd_cons_ende O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
  · exact endeConsRetR P O passes f fn caller rst rho s0 A R C ziel zielG hs (ih_stmtRetR_s hs)
      σ ρ E hpe h M rest hZ hΛ hA
  · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := endeConsOkR P O passes f fn (caller :: rst) rho s0 A R C
      hRuf hs (stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf s hs) σ σ1 ρ ρ1 h1 M
      rest hZ hΛ hA
    have hΛ1 := heldB_iff (s.held_iff) hΛ
    rw [← ho1] at hΛ1
    exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
      (ih_endRetR_rest hr _ _ _ _ hpe h2 M1 hZ1 hΛ1 (hA.lauf hl1))

set_option linter.unusedSectionVars false in
theorem endRetR_bind 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (he : EndR A C (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_endRetR_rest : EndR A C rest → SimRetER P O passes f fn caller rst rho s0 A R ziel zielG rest)
    : SimRetER P O passes f fn caller rst rho s0 A R ziel zielG (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D fn) l Γ Λ) :=
  by
  intro log σ ρ E hpe hex M hZ hΛ hA
  have hr := he.bind_inv
  have hW := hZ.welt
  simp only [execEnd] at hex
  rw [endEnde_schrumpf] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1
    e rest ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
    (ih_endRetR_rest hr _ _ _ _ hpe hex M1 hZ1 (heldB_lese _ hΛ)
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option linter.unusedSectionVars false in
theorem alsRetR_ret 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hperm)
    (zzh1 : EndR A C (.ret e hperm : Endblock D (vertragVon D fn) l Γ Λ))
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.ret e hperm : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ _
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock, execStmt, Ausgang.ende?,
    Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_dannRetP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe e hperm .nil k ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩

set_option linter.unusedSectionVars false in
theorem alsRetR_retWhy 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hperm)
    (zzh1 : EndR A C (.retWhy r hperm : Endblock D (vertragVon D fn) l Γ Λ))
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.retWhy r hperm : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ _
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock, execStmt, Ausgang.ende?,
    Option.some.injEq] at hex
  subst hex
  obtain ⟨M1, hs1, hG⟩ := w_dannRetGrundP (P := P) (O := O) (passes := passes) hZ.1
    caller rst rfl hpe r hperm .nil k ρ rfl hΛ.heldIn
  rw [hW] at hG
  exact ⟨M1, [], RufLaufG.einzeln hs1, hG, rfl⟩

set_option linter.unusedSectionVars false in
theorem alsRetR_cons 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (he : EndR A C (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_stmtRetR_s : StmtR A C true s → SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s)
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  obtain ⟨hs, hr, _⟩ := he.cons_inv
  rcases execBlock_cons_ende O passes R s _ hex with h | ⟨σ1, ρ1, h1, h2⟩
  · exact ih_stmtRetR_s hs _ _ _ _ hpe h M _ k hZ hΛ hA
  · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
      s hs _ _ _ _ _ h1 M _ k hZ hΛ hA
    have hΛ1 := heldB_iff (s.held_iff) hΛ
    rw [← ho1] at hΛ1
    exact gepoppt_laufR P O passes f fn rst rho s0 ziel zielG hl1 ho1
      (ih_alsRetR_rest hr _ _ _ _ hpe h2 M1 k hZ1 hΛ1 (hA.lauf hl1))

set_option linter.unusedSectionVars false in
theorem alsRetR_bind 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (he : EndR A C (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D fn) l Γ Λ))
    (ih_alsRetR_rest : EndR A C rest → SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG rest.alsBlock.2)
    : SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D fn) l Γ Λ).alsBlock.2 :=
  by
  intro log σ ρ E hpe hex M k hZ hΛ hA
  have hr := he.bind_inv
  have hW := hZ.welt
  simp only [Endblock.alsBlock, execBlock] at hex
  rw [ende_schrumpf] at hex
  obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
    e _ k ρ rfl
  rw [hW] at hZ1
  exact gepoppt_vorR P O passes f fn rst rho s0 ziel zielG hs1 (Erw.lese _ _ _).offen
    (ih_alsRetR_rest hr _ _ _ _ hpe hex M1 _ hZ1 (heldB_lese _ hΛ)
      (hA.lauf (RufLaufG.einzeln hs1)))

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
mutual

theorem stmtRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C true s →
    SimRetSR P O passes f fn caller rst rho s0 A R ziel zielG s
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignGlob g e hw hL)
  | _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.assignVar x e)
  | _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regWrite r hk e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.regWrite r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG
        (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel zielG (.retires m s h a)
  | _, _, _, _, .ite c t e, hs =>
      stmtRetR_ite (c := c) (t := t) (e := e) (hs := hs) (ih_blockRetR_t := blockRetR t) (ih_blockRetR_e := blockRetR e) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .onOption o p a, hs =>
      stmtRetR_onOption (o := o) (p := p) (a := a) (hs := hs) (ih_blockRetR_p := blockRetR p) (ih_blockRetR_a := blockRetR a) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, Λ₀, _, .onTag w arms, hs =>
      stmtRetR_onTag (w := w) (arms := arms) (hs := hs) (ih_armsRetR_arms := armsRetR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .onWhy r arms, hs =>
      stmtRetR_onWhy (r := r) (arms := arms) (hs := hs) (ih_grundRetR_arms := grundRetR arms) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .call g args hp hr, zzh1 =>
      stmtRetR_call (g := g) (args := args) (hp := hp) (hr := hr) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .locks L hr body, hs =>
      stmtRetR_locks (hr := hr) (body := body) (hs := hs) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .breaking i body, hs =>
      stmtRetR_breaking (i := i) (body := body) (hs := hs) (ih_blockRetR_body := blockRetR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .traverse t inv body, hs =>
      stmtRetR_traverse (t := t) (inv := inv) (body := body) (hs := hs) (ih_blockRetR_body := blockRetR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .retry n bis body ueber, hs =>
      stmtRetR_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (hs := hs) (ih_blockRetR_body := blockRetR body) (ih_blockRetR_ueber := blockRetR ueber) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .forever a inv body, hs =>
      stmtRetR_forever (a := a) (inv := inv) (body := body) (hs := hs) (ih_blockRetR_body := blockRetR body) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp only [Stmt.rArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, .ret e hperm, zzh1 =>
      stmtRetR_ret (e := e) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .retWhy r hperm, zzh1 =>
      stmtRetR_retWhy (r := r) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .leave .., _ => by
      intro log σ ρ E _ hex
      simp only [Ausgang.ende?, execStmt, reduceCtorEq] at hex
  | _, _, _, _, .next .., _ => by
      intro log σ ρ E _ hex
      simp only [Ausgang.ende?, execStmt, reduceCtorEq] at hex

theorem blockRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C true b →
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG b
  | _, _, _, _, .nil, _ => by
      intro log σ ρ E _ hex
      simp only [Ausgang.ende?, execBlock, reduceCtorEq] at hex
  | _, _, _, _, .cons s rest, hb =>
      blockRetR_cons (s := s) (rest := rest) (hb := hb) (ih_stmtRetR_s := stmtRetR s) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .bind e rest, hb =>
      blockRetR_bind (e := e) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .bindCall g args he hp hr rest, hb =>
      blockRetR_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse g args he hp hr err rest, hb =>
      blockRetR_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (ih_alsRetR_err := alsRetR err) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, .regRead r hk rest, hb =>
      blockRetR_regRead (r := r) (hk := hk) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .regReadElse r hk zusage sonst rest, hb =>
      blockRetR_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (ih_alsRetR_sonst := alsRetR sonst) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .awaits g payload hp hL hat rest, hb =>
      blockRetR_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, Λ₀, _, .exchange g neuE hw hL rest, hb =>
      blockRetR_exchange (g := g) (neuE := neuE) (hw := hw) (hL := hL) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .narrow e lo' hi' sonst rest, hb =>
      blockRetR_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (ih_alsRetR_sonst := alsRetR sonst) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .check c sonst rest, hb =>
      blockRetR_check (c := c) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (ih_alsRetR_sonst := alsRetR sonst) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .float op a b lo hi rest, hb =>
      blockRetR_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .floatLit q lo hi rest, hb =>
      blockRetR_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .floatOf e lo hi rest, hb =>
      blockRetR_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, _, .floatNarrow e lo hi sonst rest, hb =>
      blockRetR_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (hb := hb) (ih_blockRetR_rest := blockRetR rest) (ih_alsRetR_sonst := alsRetR sonst) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
theorem endRetR : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D fn) l Γ Λ), EndR A C eb →
    SimRetER P O passes f fn caller rst rho s0 A R ziel zielG eb
  | _, _, _, .ret e hperm, zzh1 =>
      endRetR_ret (e := e) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .retWhy r hperm, zzh1 =>
      endRetR_retWhy (r := r) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he =>
      endRetR_cons (s := s) (rest := rest) (he := he) (ih_stmtRetR_s := stmtRetR s) (ih_endRetR_rest := endRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .bind e rest, he =>
      endRetR_bind (e := e) (rest := rest) (he := he) (ih_endRetR_rest := endRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
/-- A covered end block run as a BLOCK (the residue of an `else` branch
    or of the reason block of `let … else`, `Endblock.alsBlock`) ends the
    frame on the machine as the end block does. -/
theorem alsRetR : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D fn) l Γ Λ), EndR A C eb →
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG eb.alsBlock.2
  | _, _, _, .ret e hperm, zzh1 =>
      alsRetR_ret (e := e) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .retWhy r hperm, zzh1 =>
      alsRetR_retWhy (r := r) (hperm := hperm) (zzh1 := zzh1) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he =>
      alsRetR_cons (s := s) (rest := rest) (he := he) (ih_stmtRetR_s := stmtRetR s) (ih_alsRetR_rest := alsRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
  | _, _, _, .bind e rest, he =>
      alsRetR_bind (e := e) (rest := rest) (he := he) (ih_alsRetR_rest := alsRetR rest) (P := P) (O := O) (passes := passes) (f := f) (fn := fn) (caller := caller) (rst := rst) (rho := rho) (s0 := s0) (A := A) (R := R) (C := C) (ziel := ziel) (zielG := zielG) (hRuf := hRuf)
theorem armsRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C true arms → ∀ (v : Wert D (.sum cs)),
    SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsRetR rest ha.cons_inv.2 _

theorem grundRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C true arms →
    ∀ (r : Fin n), SimRetBR P O passes f fn caller rst rho s0 A R ziel zielG (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundRetR rest ha.cons_inv.2 _

end

end SimRet

end Gabbro.Grammatik
