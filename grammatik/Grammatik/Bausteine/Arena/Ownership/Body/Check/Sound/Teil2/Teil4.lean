module

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil1
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil3

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}
variable (hvoll : ∀ f, f ∈ fs)
include hvoll

mutual

theorem chkS_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (st : Stmt D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded → Supports (OS A I out k c st) (chkS A I fs out st k c)
  | _, _, _, _, .assignSlot t f i e hw hL, k, c, zzh1, hc =>
      chkS_sound_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .assignThru p t ht f i e hw hL, k, c, zzh1, hc =>
      chkS_sound_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .assignGlob g e hw hL, k, c, zzh1, hc =>
      chkS_sound_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL, k, c, zzh1, hc =>
      chkS_sound_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .assignVar x e, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => OS.assignVar x e h) (Context.assign_bounded hc x e)
  | _, _, _, _, .shift t f hτ i von nach hn he hw hL, k, c, zzh1, hc =>
      chkS_sound_shift (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .ite cond t e, k, c, hk, hc =>
      chkS_sound_ite (cond := cond) (t := t) (e := e) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_t := chkB_sound t) (ih_chkB_sound_e := chkB_sound e) (hvoll := hvoll)
  | _, _, _, _, .onOption o p a, k, c, hk, hc =>
      chkS_sound_onOption (o := o) (p := p) (a := a) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_p := chkB_sound p) (ih_chkB_sound_a := chkB_sound a) (hvoll := hvoll)
  | _, _, _, _, .onTag v arms, k, c, hk, hc =>
      chkS_sound_onTag (v := v) (arms := arms) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkArms_sound_arms := chkArms_sound arms) (hvoll := hvoll)
  | _, _, _, _, .onWhy r arms, k, c, hk, hc =>
      chkS_sound_onWhy (r := r) (arms := arms) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkGrund_sound_arms := chkGrund_sound arms) (hvoll := hvoll)
  | _, _, _, _, .call f args hp hr, k, c, zzh1, hc =>
      chkS_sound_call (f := f) (args := args) (hp := hp) (hr := hr) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .callInd p args hp hr, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true] at h
      exact OS.callInd p args hp hr _ _ (sigCompatB_sound hvoll h.1.2) h.1.1.1 h.1.1.2 h.2)
      (dropContextB_bounded (afterCall_bounded hc) _)
  | _, _, _, _, .locks L hr body, k, c, hk, hc => by
    simp only [chkS]
    exact supports_mono (fun z hz => OS.locks L hr body hz) (chkB_sound body k c hk hc)
  | _, _, _, _, .breaking i body, k, c, hk, hc => by
    simp only [chkS]
    exact supports_mono (fun z hz => OS.breaking i body hz) (chkB_sound body k c hk hc)
  | _, _, _, _, .traverse t inv body, k, c, hk, hc =>
      chkS_sound_traverse (t := t) (inv := inv) (body := body) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_body := chkB_sound body) (hvoll := hvoll)
  | _, _, _, _, .retry n bis body u, k, c, hk, hc =>
      chkS_sound_retry (n := n) (bis := bis) (body := body) (u := u) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_body := chkB_sound body) (ih_chkB_sound_u := chkB_sound u) (hvoll := hvoll)
  | _, _, _, _, .forever a inv body, k, c, hk, hc =>
      chkS_sound_forever (a := a) (inv := inv) (body := body) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_body := chkB_sound body) (hvoll := hvoll)
  | _, _, _, _, .axiomCall a args hres hw hg hd hgd, k, c, zzh1, hc =>
      chkS_sound_axiomCall (a := a) (args := args) (hres := hres) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .regWrite r hk' e, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => OS.regWrite r hk' e h) hc
  | _, _, _, _, .transition r hk' m hm hl maske bits, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.transition r hk' m hm hl maske bits, hc⟩
  | _, _, _, _, .publish g e payload hp hw hL, k, c, zzh1, hc =>
      chkS_sound_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
  | _, _, _, _, .advances m a h hs, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.advances m a h hs, hc⟩
  | _, _, _, _, .retires m st h a, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.retires m st h a, hc⟩
  | _, _, _, _, .ret e hΛ, k, c, _, _ => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.ret e hΛ h)
  | _, _, _, _, .retWhy r hΛ, k, c, _, _ => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.retWhy r hΛ h)
  | _, _, _, _, .leave hl, k, c, hk, hc => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.leave hl (exitsB_sound hk hc h))
  | _, _, _, _, .next hl, k, c, hk, hc => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.next hl (exitsB_sound hk hc h))
  | _, _, _, _, .assignSlotRef r t ht ho f e hw hL, k, c, zzh1, hc =>
      chkS_sound_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (k := k) (c := c) (zzh1 := zzh1) (hc := hc) (hvoll := hvoll)
theorem chkB_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded → Supports (OB A I out k c b) (chkB A I fs out b k c)
  | _, _, _, _, .nil, k, c, _, hc => by
    simp only [chkB]
    exact ⟨OB.nil, hc⟩
  | _, _, _, _, .cons s rest, k, c, hk, hc =>
      chkB_sound_cons (s := s) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkS_sound_s := chkS_sound s) (ih_chkB_sound_rest := chkB_sound rest) (ih_relB_sound_rest := relB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .bind e rest, k, c, hk, hc =>
      chkB_sound_bind (e := e) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .bindCall f args he hp hr rest, k, c, hk, hc =>
      chkB_sound_bindCall (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .bindCallInd p args he hp hr rest, k, c, hk, hc =>
      chkB_sound_bindCallInd (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .bindCallElse f args he hp hr err rest, k, c, hk, hc =>
      chkB_sound_bindCallElse (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_chkE_sound_err := chkE_sound err) (hvoll := hvoll)
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest, k, c, hk, hc =>
      chkB_sound_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, k, c, hk, hc =>
      chkB_sound_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_chkE_sound_err := chkE_sound err) (hvoll := hvoll)
  | _, _, _, _, .regRead r hk' rest, k, c, hk, hc =>
      chkB_sound_regRead (r := r) (hk' := hk') (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .regReadElse r hk' zusage sonst rest, k, c, hk, hc =>
      chkB_sound_regReadElse (r := r) (hk' := hk') (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_chkE_sound_sonst := chkE_sound sonst) (hvoll := hvoll)
  | _, _, _, _, .awaits g payload hp hL ha rest, k, c, hk, hc =>
      chkB_sound_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (ha := ha) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .exchange g neu hw hL rest, k, c, hk, hc =>
      chkB_sound_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, Γ, _, _, .narrow e lo' hi' voll rest, k, c, hk, hc =>
      chkB_sound_narrow (e := e) (lo' := lo') (hi' := hi') (voll := voll) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_ctr1B_sound_rest := ctr1B_sound rest) (ih_lst1B_sound_rest := lst1B_sound rest) (ih_chkE_sound_voll := chkE_sound voll) (hvoll := hvoll)
  | _, _, _, _, .check cond sonst rest, k, c, hk, hc =>
      chkB_sound_check (cond := cond) (sonst := sonst) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_chkE_sound_sonst := chkE_sound sonst) (hvoll := hvoll)
  | _, _, _, _, .float op a b lo hi rest, k, c, hk, hc =>
      chkB_sound_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .floatLit q lo hi rest, k, c, hk, hc =>
      chkB_sound_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .floatOf e lo hi rest, k, c, hk, hc =>
      chkB_sound_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (hvoll := hvoll)
  | _, _, _, _, .floatNarrow e lo hi sonst rest, k, c, hk, hc =>
      chkB_sound_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_rest := chkB_sound rest) (ih_chkE_sound_sonst := chkE_sound sonst) (hvoll := hvoll)
theorem relB_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwK : V.gschreibt g = true)
      (hLK : gdarf D g Λ) (rest' : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwK hLK) rest' ∧
      g = A.kopf ∧ exprVarPos e2 = some p ∧ OB A I out k c rest' x) (relB A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwK hLK =>
        simp only [relB]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          exact ⟨g, e2, hwK, hLK, rest1, rfl, h.1, h.2, hx⟩)
      | _ => simp only [relB]; trivial
    | .nil => by simp only [relB]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [relB]; trivial

theorem ctr2B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwG : V.gschreibt g = true)
      (hLG : gdarf D g Λ) (rest' : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwG hLG) rest' ∧
      g = A.zaehl ∧ exprSucc e2 = some p ∧ OB A I out k c rest' x) (ctr2B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwG hLG =>
        simp only [ctr2B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          exact ⟨g, e2, hwG, hLG, rest1, rfl, h.1, h.2, hx⟩)
      | _ => simp only [ctr2B]; trivial
    | .nil => by simp only [ctr2B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [ctr2B]; trivial

theorem ctr1B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest1 : Block D V l Γ Λ Λ'),
      rest = .cons (.assignSlot t f i ev hw hL) rest1 ∧ NotLink A t f ∧ checkExpression A c i = true ∧
      checkExpression A c ev = true ∧ storeCheck A c t i = true ∧
      ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwG : V.gschreibt g = true) (hLG : gdarf D g Λ)
        (rest2 : Block D V l Γ Λ Λ'), rest1 = .cons (.assignGlob g e2 hwG hLG) rest2 ∧
        g = A.zaehl ∧ exprSucc e2 = some p ∧ OB A I out k c rest2 x) (ctr1B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := ctr2B_sound rest1 k c p hk hc
      cases s with
      | assignSlot t f i ev hw hL =>
        simp only [ctr1B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨t, f, i, ev, hw, hL, rest1, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2, hx⟩)
      | _ => simp only [ctr1B]; trivial
    | .nil => by simp only [ctr1B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [ctr1B]; trivial

theorem lst2B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded →
    Supports (fun x => ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest' : Block D V l Γ Λ Λ'),
      rest = .cons (.assignSlot t f i ev hw hL) rest' ∧ NotLink A t f ∧ checkExpression A c i = true ∧
      checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ OB A I out k c rest' x) (lst2B A I fs out rest k c)
  | _, _, _, _, b, k, c, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignSlot t f i ev hw hL =>
        simp only [lst2B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨t, f, i, ev, hw, hL, rest1, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2, hx⟩)
      | _ => simp only [lst2B]; trivial
    | .nil => by simp only [lst2B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [lst2B]; trivial

theorem lst1B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwK : V.gschreibt g = true)
      (hLK : gdarf D g Λ) (rest1 : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwK hLK) rest1 ∧
      g = A.kopf ∧ exprSlotRead e2 = some ⟨A.tab, A.nxt, p⟩ ∧
      ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
        (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest2 : Block D V l Γ Λ Λ'),
        rest1 = .cons (.assignSlot t f i ev hw hL) rest2 ∧ NotLink A t f ∧ checkExpression A c i = true ∧
        checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ OB A I out k c rest2 x)
      (lst1B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := lst2B_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwK hLK =>
        simp only [lst1B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨g, e2, hwK, hLK, rest1, rfl, h.1, slotIsLink_sound h.2, hx⟩)
      | _ => simp only [lst1B]; trivial
    | .nil => by simp only [lst1B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [lst1B]; trivial

theorem chkE_sound : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) (k c : Context),
    k.bounded → c.bounded → chkE A I fs out eb k c = true → OE A I out k c eb
  | _, _, _, .ret e hΛ, k, c, _, _, h => by
    simp only [chkE] at h; exact OE.ret e hΛ h
  | _, _, _, .retWhy r hΛ, k, c, _, _, h => by
    simp only [chkE] at h; exact OE.retWhy r hΛ h
  | _, _, _, .leave hl, k, c, hk, hc, h => by
    simp only [chkE] at h; exact OE.leave hl (exitsB_sound hk hc h)
  | _, _, _, .next hl, k, c, hk, hc, h => by
    simp only [chkE] at h; exact OE.next hl (exitsB_sound hk hc h)
  | _, _, _, .cons s rest, k, c, hk, hc, h =>
      chkE_sound_cons (s := s) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkS_sound_s := chkS_sound s) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .bind e rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.bind e rest h.1 (chkE_sound rest k _ hk (Context.bindOrigin_bounded hc e) h.2)
  | _, _, _, .bindCall f args he hp hr rest, k, c, hk, hc, h =>
      chkE_sound_bindCall (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .bindCallElse f args he hp hr err rest, k, c, hk, hc, h =>
      chkE_sound_bindCallElse (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_err := chkE_sound err) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .bindAxiom a args he hw hg hd hgd rest, k, c, hk, hc, h =>
      chkE_sound_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, k, c, hk, hc, h =>
      chkE_sound_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_err := chkE_sound err) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .regRead r hk' rest, k, c, hk, hc, h => by
    simp only [chkE] at h
    exact OE.regRead r hk' rest (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h)
  | _, _, _, .regReadElse r hk' zusage sonst rest, k, c, hk, hc, h =>
      chkE_sound_regReadElse (r := r) (hk' := hk') (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_sonst := chkE_sound sonst) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .awaits g payload hp hL ha rest, k, c, hk, hc, h => by
    simp only [chkE] at h
    exact OE.awaits g payload hp hL ha rest (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h)
  | _, _, _, .bindCallInd p args he hp hr rest, k, c, hk, hc, h =>
      chkE_sound_bindCallInd (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (h := h) (ih_chkE_sound_rest := chkE_sound rest) (hvoll := hvoll)
  | _, _, _, .narrow .., _, _, _, _, h => by simp only [chkE, Bool.false_eq_true] at h
  | _, _, _, .exchange .., _, _, _, _, h => by simp only [chkE, Bool.false_eq_true] at h
  | _, _, _, .ite .., _, _, _, _, h => by simp only [chkE, Bool.false_eq_true] at h

theorem chkArms_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (k c : Context),
    k.bounded → c.bounded → Supports (OArms A I out k c arms) (chkArms A I fs out arms k c)
  | _, _, _, _, _, .nil, k, c, _, _ => by
    simp only [chkArms]
    exact fun x _ => OArms.nil
  | _, _, _, _, ca :: zz1, .cons b rest, k, c, hk, hc =>
      chkArms_sound_ca (ca := ca) (zz1 := zz1) (b := b) (rest := rest) (k := k) (c := c) (hk := hk) (hc := hc) (ih_chkB_sound_b := chkB_sound b) (ih_chkArms_sound_rest := chkArms_sound rest) (hvoll := hvoll)
theorem chkGrund_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (k c : Context),
    k.bounded → c.bounded → Supports (OGrund A I out k c arms) (chkGrund A I fs out arms k c)
  | _, _, _, _, _, .nil, k, c, _, _ => by
    simp only [chkGrund]
    exact fun x _ => OGrund.nil
  | _, _, _, _, _, .cons b rest, k, c, hk, hc => by
    simp only [chkGrund]
    exact supports_join (chkB_sound b k c hk hc) (chkGrund_sound rest k c hk hc)
      (fun x y z hx hy wx wy => OGrund.cons b rest hx wx (OGrund.weaken hy wy))

end

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
