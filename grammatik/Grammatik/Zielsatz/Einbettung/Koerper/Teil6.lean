module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil7

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')
variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option maxHeartbeats 4000000 in
mutual

/-- **A statement beside its image.** -/
theorem sim_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') →
    E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') s)
      (execStmtHA S' O' U' A' passes R' (exS hS s))
  | .assignSlot t f i e hw hL =>
      sim_stmt_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .assignVar x e =>
      sim_stmt_assignVar (x := x) (e := e) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .assignThru p t ht f i e hw hL =>
      sim_stmt_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .assignThruOwn p t ht f i e m s ho he hg hw hL =>
      sim_stmt_assignThruOwn (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (m := m) (s := s) (ho := ho) (he := he) (hg := hg) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .assignSlotRef r t ht ho f e hw hL =>
      sim_stmt_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .assignGlob g e hw hL =>
      sim_stmt_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .putBytes t f hf n i hlo hhi e hw hL =>
      sim_stmt_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .shift t f hτ i von nach hn he hw hL =>
      sim_stmt_shift (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .ite c t e =>
      sim_stmt_ite (c := c) (t := t) (e := e) (ih_sim_block_e := sim_block e) (ih_sim_block_t := sim_block t) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .onOption (n := n) o p a =>
      sim_stmt_onOption (n := n) (o := o) (p := p) (a := a) (ih_sim_block_a := sim_block a) (ih_sim_block_p := sim_block p) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .onTag v arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE) v.orte
      let w' := eval (leseA A' σ' (Λ.map E.resE) (v.orte.map E.ortE)) (exE E v)
        (leseA A' σ' (Λ.map E.resE) (v.orte.map E.ortE)) ρ'
      have hv : E.valZ hZ _ w' = eval σ₁ v σ₁ ρ := E.valZ_vrel hZ _ (hev v ρ ρ' hρ)
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_arms arms w' M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        simpa only [hv] using hΦ2 Φ hP
      · simpa only [exS, execStmtHA, Einbettung.orte_exE] using hR
  | .onWhy r arms => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
        (r.orte)
      have hev0 := E.frei_alle hZ (@hev) hρ
      obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := sim_grund arms (eval σ₁ r σ₁ ρ) M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
        exact hΦ2 Φ hP
      · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref, valE_why]
        exact hR
  | .call f args hp hr =>
      sim_stmt_call (f := f) (args := args) (hp := hp) (hr := hr) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .callInd (n := n) p args hp hr =>
      sim_stmt_callInd (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .callIndElse (n := n) p args he hp hr err =>
      sim_stmt_callIndElse (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .locks L hr body =>
      sim_stmt_locks (hr := hr) (body := body) (ih_sim_block_body := sim_block body) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .breaking i body =>
      sim_stmt_breaking (i := i) (body := body) (ih_sim_block_body := sim_block body) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .traverse t inv body =>
      sim_stmt_traverse (t := t) (inv := inv) (body := body) (ih_sim_block_body := sim_block body) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .consumeTraverse t member edge inv bound mass body =>
      sim_stmt_consumeTraverse (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (ih_sim_block_body := sim_block body) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retry n bis body ueber =>
      sim_stmt_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (ih_sim_block_body := sim_block body) (ih_sim_block_ueber := sim_block ueber) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .forever a inv body =>
      sim_stmt_forever (a := a) (inv := inv) (body := body) (ih_sim_block_body := sim_block body) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .axiomCall a args h hw hg hd hgd =>
      sim_stmt_axiomCall (a := a) (args := args) (h := h) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .regWrite r hk e =>
      sim_stmt_regWrite (r := r) (hk := hk) (e := e) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .transition r hk m hm hl maske bits =>
      sim_stmt_transition (r := r) (hk := hk) (m := m) (hm := hm) (hl := hl) (maske := maske) (bits := bits) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .publish g e payload hp hw hL =>
      sim_stmt_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .advances m a h hs =>
      sim_stmt_advances (m := m) (a := a) (h := h) (hs := hs) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retires m s h a =>
      sim_stmt_retires (m := m) (s := s) (h := h) (a := a) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .ret e hΛ =>
      sim_stmt_ret (e := e) (hΛ := hΛ) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retScoped e R =>
      sim_stmt_retScoped (e := e) (R := R) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retWhy r hΛ =>
      sim_stmt_retWhy (r := r) (hΛ := hΛ) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retWhyScoped r R =>
      sim_stmt_retWhyScoped (r := r) (R := R) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .leave h =>
      sim_stmt_leave (h := h) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .next h =>
      sim_stmt_next (h := h) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
/-- **A block beside its image.** -/
theorem sim_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') →
    E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execBlockHA S' O' U' A' passes R' (exB hS b))
  | .nil => by
      intro M σ σ' ρ ρ' h hρ
      exact ⟨M, .ok σ ρ, teil_refl M, fun _ _ => rfl, h, hρ⟩
  | .cons s rest =>
      sim_block_cons (s := s) (rest := rest) (ih_sim_stmt_s := sim_stmt s) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bind e rest =>
      sim_block_bind (e := e) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCall (τ := τ) f args he hp hr rest =>
      sim_block_bindCall (τ := τ) (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest =>
      sim_block_bindCallInd (n := n) (τ := τ) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallIndElse (n := n) (τ := τ) p args he hp hr err rest =>
      sim_block_bindCallIndElse (n := n) (τ := τ) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallElse (τ := τ) f args he hp hr err rest =>
      sim_block_bindCallElse (τ := τ) (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest =>
      sim_block_bindAxiom (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest =>
      sim_block_bindAxiomElse (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .regRead r hk rest =>
      sim_block_regRead (r := r) (hk := hk) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .regReadElse r hk zusage sonst rest =>
      sim_block_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_sonst := sim_end sonst) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .awaits g payload hp hL hat rest =>
      sim_block_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .exchange g neu hw hL rest =>
      sim_block_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .narrow e lo' hi' sonst rest =>
      sim_block_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_sonst := sim_end sonst) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .narrowRequired e lo' hi' rest =>
      sim_block_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .check c sonst rest =>
      sim_block_check (c := c) (sonst := sonst) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_sonst := sim_end sonst) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .float op a b lo hi rest =>
      sim_block_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .floatLit q lo hi rest =>
      sim_block_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .floatOf e lo hi rest =>
      sim_block_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (ih_sim_block_rest := sim_block rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .floatNarrow e lo hi sonst rest =>
      sim_block_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (ih_sim_block_rest := sim_block rest) (ih_sim_end_sonst := sim_end sonst) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
/-- **An end block beside its image.** -/
theorem sim_end {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) →
    E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') b)
      (execEndHA S' O' U' A' passes R' (exEnd hS b))
  | .ret e hΛ =>
      sim_end_ret (e := e) (hΛ := hΛ) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retScoped e R =>
      sim_end_retScoped (e := e) (R := R) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retWhy r hΛ =>
      sim_end_retWhy (r := r) (hΛ := hΛ) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .retWhyScoped r R =>
      sim_end_retWhyScoped (r := r) (R := R) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .leave h =>
      sim_end_leave (h := h) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .next h =>
      sim_end_next (h := h) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .cons s rest =>
      sim_end_cons (s := s) (rest := rest) (ih_sim_stmt_s := sim_stmt s) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bind e rest =>
      sim_end_bind (e := e) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCall (τ := τ) f args he hp hr rest =>
      sim_end_bindCall (τ := τ) (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallInd (n := n) (τ := τ) p args he hp hr rest =>
      sim_end_bindCallInd (n := n) (τ := τ) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallIndElse (n := n) (τ := τ) p args he hp hr err rest =>
      sim_end_bindCallIndElse (n := n) (τ := τ) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (ih_sim_end_rest := sim_end rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindCallElse (τ := τ) f args he hp hr err rest =>
      sim_end_bindCallElse (τ := τ) (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (ih_sim_end_rest := sim_end rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindAxiom (τ := τ) a args he hw hg hd hgd rest =>
      sim_end_bindAxiom (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest =>
      sim_end_bindAxiomElse (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ih_sim_end_rest := sim_end rest) (ih_sim_end_err := sim_end err) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .regRead r hk rest =>
      sim_end_regRead (r := r) (hk := hk) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .regReadElse r hk zusage sonst rest =>
      sim_end_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (ih_sim_end_sonst := sim_end sonst) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .awaits g payload hp hL hat rest =>
      sim_end_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .exchange g neu hw hL rest =>
      sim_end_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .narrow e lo' hi' sonst rest =>
      sim_end_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (ih_sim_end_rest := sim_end rest) (ih_sim_end_sonst := sim_end sonst) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .narrowRequired e lo' hi' rest =>
      sim_end_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (ih_sim_end_rest := sim_end rest) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
  | .ite c t e =>
      sim_end_ite (c := c) (t := t) (e := e) (ih_sim_end_e := sim_end e) (ih_sim_end_t := sim_end t) (E := E) (hZ := hZ) (hS := hS) (pad := pad) (S := S) (T := T) (S' := S') (T' := T') (O' := O') (U' := U') (A' := A') (passes := passes) (R' := R') (hB := hB)
/-- **Arms beside their images.** -/
theorem sim_arms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ w' : Wert D' (E.tyE (.sum cs)),
    E.KoerperSim hZ (fun Φ => execArmsHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') a (E.valZ hZ (.sum cs) w'))
      (execArmsHA S' O' U' A' passes R' (exArms hS a) w')
  | .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | .cons (c := none) b _, ⟨⟨0, _⟩, nutz⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by
          simp only [valZ, Val.restrict, Val.restrictSum, execArmsHA, armEnv, Ausgang.schrumpfArm]
          exact hΦ Φ hP,
        by simp only [exArms, execArmsHA, armEnv, Ausgang.schrumpfArm]; exact hR⟩
  | .cons (c := some τ) b _, ⟨⟨0, _⟩, nutz⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ'
        (Env.cons (τ := τ) (E.valZ hZ τ nutz) ρ) (Env.cons (τ := E.tyE τ) nutz ρ') hM
        (E.envR_cons hZ hρ (E.valZ hZ τ nutz) nutz rfl (E.vrel_valZ hZ τ nutz))
      exact ⟨M₁, o.schrumpf, hs, fun Φ hP => by
          simp only [valZ, Val.restrict, Val.restrictSum, execArmsHA, armEnv, Ausgang.schrumpfArm]
          exact congrArg Ausgang.schrumpf (hΦ Φ hP),
        by simp only [exArms, execArmsHA, armEnv, Ausgang.schrumpfArm]
           exact E.ausRel_schrumpf hR⟩
  | .cons (c := none) _ rest, ⟨⟨i + 1, h⟩, nutz⟩ => by
      have ih := sim_arms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := ih M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by
          simpa only [valZ, Val.restrict, Val.restrictSum, execArmsHA] using hΦ Φ hP,
        by simpa only [exArms, execArmsHA] using hR⟩
  | .cons (c := some τ) _ rest, ⟨⟨i + 1, h⟩, nutz⟩ => by
      have ih := sim_arms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := ih M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by
          simpa only [valZ, Val.restrict, Val.restrictSum, execArmsHA] using hΦ Φ hP,
        by simpa only [exArms, execArmsHA] using hR⟩

/-- **Reason arms beside their images.** -/
theorem sim_grund {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ r : Fin n,
    E.KoerperSim hZ (fun Φ => execGrundHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') a r)
      (execGrundHA S' O' U' A' passes R' (exGArms hS a) r)
  | .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩ => by
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := sim_block b M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execGrundHA]; exact hΦ Φ hP,
        by simp only [exGArms, execGrundHA]; exact hR⟩
  | .cons _ rest, ⟨i + 1, h⟩ => by
      have := sim_grund rest ⟨i, Nat.lt_of_succ_lt_succ h⟩
      intro M σ σ' ρ ρ' hM hρ
      obtain ⟨M₁, o, hs, hΦ, hR⟩ := this M σ σ' ρ ρ' hM hρ
      exact ⟨M₁, o, hs, fun Φ hP => by simp only [execGrundHA]; exact hΦ Φ hP,
        by simp only [exGArms, execGrundHA]; exact hR⟩

end

end Sim

end Einbettung

end Gabbro.Grammatik.Einbettung
