/-
  File:      Grammatik/KorrespondenzAllg.lean
  Subject:   T2 PROPER: ONE decidable correspondence check for EVERY program
             whose emitted forms it covers, and its soundness down to the
             callee relation at every call depth (plan
             `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2, stage (a)).

  Before this file the correspondence certificate was checked in two ways,
  neither generic:
  * `certOk`/`certOkG` (Korrespondenz104.lean, Schlusssatz104.lean) compare
    the printed rows with 104's rows -- a check of ONE program;
  * `gbodyOk` (Korrespondenz.lean) decides shape and hygiene of general
    rows, but the link row <-> Gabbro statement is a PROOF (`REnd`) that a
    human writes per body.

  Here the link is DECIDED. `korrOk EL fnum c P fs` walks every body of
  `P` together with its printed rows and asks, statement by statement,
  whether the row is the emitted form of that statement: the slot store
  through a pointer or at a named table (`assignDurch`, `assignSlot`), the
  store to a local (`assignVar`), the direct call with its arguments
  (`call`), `let` (`bind`), the `(void)x;` of an unused parameter, and the
  return of an expression or nothing (`ret`, falling off a `void` body).
  Expressions: literals, locals, widenings, slot loads through a pointer or
  at a named table (`slot`, `durch`), table pointers (`ptrOf`). Every other
  form makes the Bool `false` -- a refusal, never an admission.

  THE SOUNDNESS (`korrOk_fnCorr`): a certificate that checks gives, for
  EVERY function and at EVERY call depth `n` and `forever` budget, the
  callee relation `FnCorr` between Gabbro's `rufAt P O passes n` and the
  C call `CallAt … (kProg c) n` of the unit the certificate elaborates
  to. Nothing is re-proved: each row is one existing T4 lemma
  (`scorr_assignDurch`, `scorr_assignVar`, `scorr_call`, `ecorr_slotVia`,
  `cCorr_ruf`, `cCorr_end`, …); the one new lemma is the argument passing
  of a call (`argsTo_of`), stated once for every argument list.

  THE LOCALS MAP is the EXPORTER'S: Gabbro variable `j` of a function is C
  local `vm[j]`, a pointer parameter is an ordinary variable whose value
  is the table's address (`ValCorr` at a pointer type). A callee's map
  must be exactly its C parameter list (`callMapOk`) -- the map the model
  of the source text has, not `refD`'s index-fixed map.
-/
import Grammatik.Korrespondenz
import Grammatik.CFormenDet

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. The certificate -/

/-- One emitted function as certificate data: its C parameters (local
    number and declared C type, in order), its address-taken locals, its
    body rows in emission order, and the locals map of its Gabbro body
    (`vm`: variable `j` lives in C local `vm[j]`; `pp`/`ks` as in
    `CEnvLay`, empty in the exporter's map). -/
structure KFun (D : Deklaration) where
  params : List (Nat × CTy)
  locals : List Nat
  rows : List GRow
  vm : List Nat
  pp : List (Nat × D.Tab)
  ks : List (Nat × Int)

/-- A certificate: the unit's functions by C function number. -/
abbrev KCert (D : Deklaration) := List (KFun D)

/-- The locals map of one certified function. -/
def KFun.lay (k : KFun D) {Γ : Ctx} : CEnvLay D Γ := ⟨k.vm, k.pp, k.ks⟩

/-- Elaboration of a body's rows: sequencing; a trailing return row is the
    `return` itself; falling off the end is `skip`. -/
def endCS : List GRow → CS
  | [] => .skip
  | r :: rs => match r, rs with
    | .ret cr, [] => .ret cr
    | r, rs => .seq (growRow r) (endCS rs)

/-- The C unit a certificate elaborates to: function `n` is row list `n`. -/
def kProg (c : KCert D) : CProg := fun n =>
  (c[n]?).map fun k => { params := k.params, locals := k.locals, body := endCS k.rows }

/-! ## 1. The decidable check -/

/-- Every variable of a context, with its type. -/
def varsOf : (Γ : Ctx) → List (Σ τ, Var Γ τ)
  | [] => []
  | τ :: Γ => ⟨τ, .hier⟩ :: (varsOf Γ).map fun p => ⟨p.1, .dort p.2⟩

/-- A type is a pointer to table `t`. -/
def istZeigerAuf (t : D.Tab) : Ty → Bool
  | .ptr n _ => decide (D.tabNr n = some t)
  | _ => false

section Pruefung

variable (EL : EmitLay D) {Γ : Ctx} (K : CEnvLay D Γ)

/-- A C expression that is the address of table `t`: the named object, a
    pointer parameter of the map (`pp`), or the C local of a Gabbro pointer
    variable to `t`. -/
def ptrOk : CX → D.Tab → Bool
  | .addr (.tab k), t => decide (k = EL.tnr t)
  | .var kp, t => decide ((kp, t) ∈ K.pp) ||
      (varsOf Γ).any fun p => decide (K.loc p.2 = kp) && istZeigerAuf t p.1
  | _, _ => false

/-- The address `b->slots[·].f` and the loaded C type are the emitter's for
    field `f` of table `t` (the layout numbers of `EL`), `t` not a ghost. -/
def slotOk (b : CX) (n ss off : Nat) (τc : CTy) (t : D.Tab) (f : D.Feld t) : Bool :=
  ptrOk EL K b t && decide (n = (EL.trec t).count) && decide (ss = (EL.trec t).ssize) &&
    decide (off = (EL.trec t).off (EL.fnr t f)) && decide (τc = EL.slotTy t f) && !(D.geist t)

/-- EXPRESSIONS: the C expression is the emitted form of the Gabbro one. -/
def exOk {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (c : CX) : Bool :=
  match e, c with
  | .lit n, c => match c with
    | .lit m => decide (m = n)
    | _ => false
  | .var x, c => match c with
    | .var k => decide (k = K.loc x)
    | _ => false
  | .weiter _ _ e, c => exOk e c
  | .slot t f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .durch _ t _ f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .ptrOf t _ _ _, c => ptrOk EL K c t
  | _, _ => false
termination_by structural e

/-- The arguments of a call against the callee's C parameters: each
    argument is the emitted form of the Gabbro one, and the declared C type
    holds its Gabbro type. -/
def argsOk {Λ : List (Res D)} : {τs : List Ty} → Args D Γ Λ τs → List CX → List (Nat × CTy) → Bool
  | _, .nil, cs, ps => cs.isEmpty && ps.isEmpty
  | _, .cons (τ := τ) e rest, cs, ps => match cs, ps with
    | ce :: cs, (_, τc) :: ps => exOk EL K e ce && declOk τ τc && argsOk rest cs ps
    | _, _ => false

/-- A callee's map is its C parameter list (the exporter's map). -/
def callMapOk (k : KFun D) : Bool :=
  decide (k.vm = k.params.map Prod.fst) && k.pp.isEmpty && k.ks.isEmpty &&
    decide (k.params.map Prod.fst).Nodup

/-- A `(void)x;` names the C local of some Gabbro variable. -/
def voidOk (x : Nat) : Bool := (varsOf Γ).any fun p => decide (K.loc p.2 = x)

/-- The answer of a `return`. -/
def ergOk {Λ : List (Res D)} : {e : Option Ty} → ErgExpr D Γ Λ e → Option (CTy × CX) → Bool
  | _, .keine, none => true
  | some τ, .wert e, some (τc, ce) => declOk τ τc && exOk EL K e ce
  | _, _, _ => false

end Pruefung

section Rumpf

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- STATEMENTS: the row is the emitted form of the statement. -/
def stOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ) :
    Stmt D V l Γ Λ Λ' → GRow → Bool
  | .assignDurch _ t _ f i e _ _, r => match r with
    | .storeSlot kp ci n ss off τc ce =>
        slotOk EL K (.var kp) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | .storeNamed tn ci n ss off τc ce =>
        slotOk EL K (.addr (.tab tn)) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | _ => false
  | .assignSlot t f i e _ _, r => match r with
    | .storeSlot kp ci n ss off τc ce =>
        slotOk EL K (.var kp) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | .storeNamed tn ci n ss off τc ce =>
        slotOk EL K (.addr (.tab tn)) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | _ => false
  | .assignVar (τ := τ) x e, r => match r with
    | .setVar k τc ce => K.okB && decide (k = K.loc x) && declOk τ τc && exOk EL K e ce
    | _ => false
  | .call g args _ _, r => match r with
    | .call fc cargs none => decide (fc = fnum g) &&
        (match c[fnum g]? with
          | some k => callMapOk k && argsOk EL K args cargs k.params
          | none => false)
    | _ => false
  | _, _ => false

/-- TERMINAL BLOCKS (a function body): row by row. `top` says the block is
    the whole body (a `void` body may fall off its end). -/
def enOk (top : Bool) {V : Vertrag D} {l : Bool} :
    List GRow → {Γ : Ctx} → {Λ : List (Res D)} → CEnvLay D Γ → Endblock D V l Γ Λ → Bool
  | [], _, _, _, b => match b with
    | .ret _ _ => top && decide (V.erg = none)
    | _ => false
  | r :: rs, _, _, K, b => match r with
    | .void x => voidOk K x && enOk top rs K b
    | .ret cr => rs.isEmpty && (match b with
        | .ret e _ => ergOk EL K e cr
        | _ => false)
    | .bindLet x τc ce => (match b with
        | .bind (τ := τ) e rest =>
            K.okB && K.freshB x && declOk τ τc && exOk EL K e ce && enOk top rs (K.push τ x) rest
        | _ => false)
    | r => (match b with
        | .cons s rest => stOk EL fnum c K s r && enOk top rs K rest
        | _ => false)

/-- **THE CHECK**: every function of `fs` has a certified C function (number
    `fnum f`), whose rows are the emitted form of its body under its map. -/
def korrOk (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => match c[fnum f]? with
    | some k => enOk EL fnum c true k.rows k.lay (P.rumpf f)
    | none => false

end Rumpf

/-! ## 2. Soundness, expression by expression -/

section Sound

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

theorem ptrOk_sound {cp : CX} {t : D.Tab} (h : ptrOk X.EL K cp t = true) : PtrTo X K cp t := by
  match cp, h with
  | .addr (.tab k), h =>
      have hk : k = X.EL.tnr t := of_decide_eq_true h
      subst hk
      exact ptrTo_named X K t
  | .var kp, h =>
      simp only [ptrOk, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ptrTo_param X K (of_decide_eq_true h)
      · obtain ⟨⟨τ, v⟩, -, hv⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true] at hv
        obtain ⟨hl, hz⟩ := hv
        have hl' : K.loc v = kp := of_decide_eq_true hl
        subst hl'
        cases τ with
        | ptr n rw => exact ptrTo_var X K v (of_decide_eq_true hz)
        | _ => simp [istZeigerAuf] at hz

theorem slotOk_sound {b : CX} {n ss off : Nat} {τc : CTy} {t : D.Tab} {f : D.Feld t}
    (h : slotOk X.EL K b n ss off τc t f = true) :
    PtrTo X K b t ∧ n = (X.EL.trec t).count ∧ ss = (X.EL.trec t).ssize ∧
      off = (X.EL.trec t).off (X.EL.fnr t f) ∧ τc = X.EL.slotTy t f ∧ D.geist t = false := by
  simp only [slotOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hp, hn⟩, hs⟩, ho⟩, hτ⟩, hg⟩ := h
  exact ⟨ptrOk_sound X K hp, of_decide_eq_true hn, of_decide_eq_true hs, of_decide_eq_true ho,
    of_decide_eq_true hτ, hg⟩

/-- A table pointer in C against Gabbro's `ptrOf`. -/
theorem ecorr_ptrOf {cp : CX} {t : D.Tab} {n : Nat} {ht : D.tabNr n = some t} {rw : Bool}
    (hp : PtrTo X K cp t) : ExprCorr X K cp (Expr.ptrOf (Λ := Λ) t n ht rw) := by
  intro σ st ρG ρC _ hr
  exact ⟨_, st, hp st ρG ρC hr, t, ht, rfl⟩

/-- **Soundness of the expression check.** -/
theorem exOk_lit {n : Int} {c : CX} (h : exOk X.EL K (Expr.lit (Γ := Γ) (Λ := Λ) n) c = true) :
    ExprCorr X K c (Expr.lit (Γ := Γ) (Λ := Λ) n) := by
  cases c with
  | lit m =>
      have hm : m = n := of_decide_eq_true h
      subst hm
      exact ecorr_lit X K m
  | _ => exact absurd h (by simp [exOk])

theorem exOk_var {τ : Ty} {x : Var Γ τ} {c : CX} (h : exOk X.EL K (Expr.var (Λ := Λ) x) c = true) :
    ExprCorr X K c (Expr.var (Λ := Λ) x) := by
  cases c with
  | var k =>
      have hk : k = K.loc x := of_decide_eq_true h
      subst hk
      exact ecorr_var X K x
  | _ => exact absurd h (by simp [exOk])

/-- The slot-load arm, given the index correspondence. -/
theorem exOk_ld {t : D.Tab} {f : D.Feld t} {e : Expr D Γ Λ (D.typ t f)}
    {i : Expr D Γ Λ (.index (D.count t))} {c : CX}
    (h : (match c with
      | .ld (.slotA b ci n ss off) τc => slotOk X.EL K b n ss off τc t f && exOk X.EL K i ci
      | _ => false) = true)
    (hev : ∀ (σ : World D) (ρG : Env D Γ), eval σ e σ ρG = σ.slots t (eval σ i σ ρG).n f)
    (ih : ∀ ci, exOk X.EL K i ci = true → ExprCorr X K ci i) : ExprCorr X K c e := by
  cases c with
  | ld p τc =>
      cases p with
      | slotA b ci n ss off =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hs, hi⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact ecorr_slotVia X K hp f hg (ih ci hi) hev
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_sound : ∀ {τ : Ty} (e : Expr D Γ Λ τ) (c : CX), exOk X.EL K e c = true →
    ExprCorr X K c e
  | _, .lit _, _, h => exOk_lit X K h
  | _, .var _, _, h => exOk_var X K h
  | _, .weiter h1 h2 e, c, h => ecorr_weiter X K h1 h2 (exOk_sound e c h)
  | _, .slot _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .durch _ _ _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .ptrOf _ _ _ _, _, h => ecorr_ptrOf X K (ptrOk_sound X K h)
  | _, .wahr, _, h => absurd h (by simp [exOk])
  | _, .falsch, _, h => absurd h (by simp [exOk])
  | _, .glob .., _, h => absurd h (by simp [exOk])
  | _, .fnref .., _, h => absurd h (by simp [exOk])
  | _, .altGlob .., _, h => absurd h (by simp [exOk])
  | _, .altSlot .., _, h => absurd h (by simp [exOk])
  | _, .add .., _, h => absurd h (by simp [exOk])
  | _, .sub .., _, h => absurd h (by simp [exOk])
  | _, .neg .., _, h => absurd h (by simp [exOk])
  | _, .mul .., _, h => absurd h (by simp [exOk])
  | _, .div .., _, h => absurd h (by simp [exOk])
  | _, .rem .., _, h => absurd h (by simp [exOk])
  | _, .sdiv .., _, h => absurd h (by simp [exOk])
  | _, .srem .., _, h => absurd h (by simp [exOk])
  | _, .leseBytes .., _, h => absurd h (by simp [exOk])
  | _, .band .., _, h => absurd h (by simp [exOk])
  | _, .bor .., _, h => absurd h (by simp [exOk])
  | _, .bxor .., _, h => absurd h (by simp [exOk])
  | _, .shl .., _, h => absurd h (by simp [exOk])
  | _, .shr .., _, h => absurd h (by simp [exOk])
  | _, .lt .., _, h => absurd h (by simp [exOk])
  | _, .le .., _, h => absurd h (by simp [exOk])
  | _, .eq .., _, h => absurd h (by simp [exOk])
  | _, .fllt .., _, h => absurd h (by simp [exOk])
  | _, .flle .., _, h => absurd h (by simp [exOk])
  | _, .und .., _, h => absurd h (by simp [exOk])
  | _, .oder .., _, h => absurd h (by simp [exOk])
  | _, .nicht .., _, h => absurd h (by simp [exOk])
  | _, .none .., _, h => absurd h (by simp [exOk])
  | _, .some .., _, h => absurd h (by simp [exOk])
  | _, .istSome .., _, h => absurd h (by simp [exOk])
  | _, .fall .., _, h => absurd h (by simp [exOk])
  | _, .grund .., _, h => absurd h (by simp [exOk])
  | _, .forallSlots .., _, h => absurd h (by simp [exOk])
  | _, .existsSlots .., _, h => absurd h (by simp [exOk])
  | _, .reaches .., _, h => absurd h (by simp [exOk])

/-- **Soundness of the answer check.** -/
theorem ergOk_sound : ∀ {e : Option Ty} (r : ErgExpr D Γ Λ e) (cr : Option (CTy × CX)),
    ergOk X.EL K r cr = true → ErgCorr X K r cr := by
  intro e r cr h
  cases r with
  | keine =>
      cases cr with
      | none => rfl
      | some _ => exact absurd h (by simp [ergOk])
  | wert e =>
      cases cr with
      | none => exact absurd h (by simp [ergOk])
      | some q =>
          obtain ⟨τc, ce⟩ := q
          simp only [ergOk, Bool.and_eq_true] at h
          exact ⟨τc, ce, rfl, exOk_sound X K e ce h.2, h.1⟩

/-- The value of an argument list under a map that IS the C parameter list:
    the locals relation of the bound parameters. -/
theorem argsOk_len : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → ps.length = τs.length
  | _, .nil, cs, ps, h => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      rw [h.2]; rfl
  | _, .cons _ rest, cs, ps, h => by
      match cs, ps, h with
      | _ :: cs, _ :: ps, h =>
          simp only [argsOk, Bool.and_eq_true] at h
          simp only [List.length_cons]
          rw [argsOk_len rest cs ps h.2]
      | [], _, h => simp [argsOk] at h
      | _ :: _, [], h => simp [argsOk] at h

/-- **THE ARGUMENT PASSING of a call, for every argument list**: arguments
    that are the emitted forms of Gabbro's, into C parameters that hold their
    types, establish the callee's locals relation under the map that is its
    parameter list. -/
theorem argsTo_of : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → (ps.map Prod.fst).Nodup →
    ArgsTo X K args cs ps ⟨ps.map Prod.fst, [], []⟩
  | _, .nil, cs, ps, h, _ => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hc, hp⟩ := h
      subst hc hp
      intro σ st ρG ρC _ _
      refine ⟨[], st, fun _ => .undef, rfl, SameML.refl st, rfl, ?_, ?_, ?_⟩
      · intro τ x; exact nomatch x
      · intro q hq; exact absurd hq List.not_mem_nil
      · intro q hq; exact absurd hq List.not_mem_nil
  | _, .cons (τ := τ) e rest, [], _, h, _ => by simp [argsOk] at h
  | _, .cons _ _, _ :: _, [], h, _ => by simp [argsOk] at h
  | _, .cons (τ := τ) e rest, ce :: cs, (x, τc) :: ps, h, hnd => by
      simp only [argsOk, Bool.and_eq_true] at h
      obtain ⟨⟨he, hd⟩, hrest⟩ := h
      have hnd' : (ps.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ ps.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hlen := argsOk_len X K rest cs ps hrest
      intro σ st ρG ρC hc hr
      obtain ⟨v, st1, h1, hv, hc1⟩ := (exOk_sound X K e ce he).run X K hc hr
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st ρC v st1 h1
      obtain ⟨vs, st2, ρ1, h2, hs2, hb, hrel⟩ :=
        argsTo_of rest cs ps hrest hnd' σ st1 ρG ρC hc1 hr
      refine ⟨v :: vs, st2, lokUpd ρ1 x v, ?_, hs1.trans hs2, ?_, ?_⟩
      · simp only [evArgs, h1, h2]
      · show (match convV τc v, bindParams ps vs with
          | some v', some ρ => some (lokUpd ρ x v')
          | _, _ => none) = _
        rw [convV_of_valCorr hv hd, hb]
      · refine ⟨?_, fun q hq => absurd hq List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
        intro τ' y
        cases y with
        | hier =>
            show ValCorr X.EL τ (eval σ e σ ρG) (lokUpd ρ1 x v x)
            simp only [lokUpd, if_pos]
            exact hv
        | dort y =>
            show ValCorr X.EL τ' ((evalArgs σ rest σ ρG).get y)
              (lokUpd ρ1 x v ((x :: ps.map Prod.fst).getD (y.idx + 1) 0))
            have hy : y.idx < (ps.map Prod.fst).length := by
              rw [List.length_map, hlen]; exact Var.idx_lt y
            have hne : (x :: ps.map Prod.fst).getD (y.idx + 1) 0 ≠ x := by
              intro heq
              apply hx
              rw [← heq]
              show (ps.map Prod.fst).getD y.idx 0 ∈ ps.map Prod.fst
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]
              exact List.getElem_mem _
            simp only [lokUpd]
            rw [if_neg hne]
            exact hrel.1 τ' y

end Sound

/-! ## 3. Soundness, statement by statement and body by body -/

section SoundS

variable (X : TVCtx D) (m : Nat) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- M2 through ANY pointer form (the named object, a parameter, a pointer
    variable) against Gabbro's store to the table (`assignSlot`). -/
theorem scorr_assignSlotVia {V : Vertrag D} {l : Bool} {cp : CX} {t : D.Tab}
    (hp : PtrTo X K cp t) (f : D.Feld t) (hgt : D.geist t = false)
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)} {ci ce : CX}
    (hw : V.schreibt t = true) (hL : darf D t Λ) (hi : ExprCorr X K ci i)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignSlot (l := l) t f i e hw hL)
      (.store (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
        ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) := by
  intro σ st ρG ρC hc hr _
  obtain ⟨st', hx, hc'⟩ := slotStore_exec X K hp f hgt hi he Λ
    ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ (i.orte ++ e.orte)) st) hr
  exact ⟨_, hx, st', ρC, rfl, hc', hr⟩

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- The callee relations the certificate's calls rest on: every certified
    function, at the context's call meanings. -/
def AlleRufe (X : TVCtx D) (fnum : D.Fn → Nat) (c : KCert D) : Prop :=
  ∀ (g : D.Fn) (k : KFun D), c[fnum g]? = some k →
    FnCorr X.EL X.R X.CR g (fnum g) k.params k.lay

/-- **Soundness of the statement check.** -/
theorem stOk_sound (hF : AlleRufe X fnum c) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (r : GRow), stOk X.EL fnum c K s r = true →
      StmtCorr X m K s (growRow r) := by
  intro s r h
  cases s with
  | assignDurch p t ht f i e hw hL =>
      cases r with
      | storeSlot kp ci n ss off τc ce =>
          simp only [stOk, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact scorr_assignDurch X K m ht hp f hg hw hL (exOk_sound X K i ci hi)
            (exOk_sound X K e ce he)
      | storeNamed tn ci n ss off τc ce =>
          simp only [stOk, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact scorr_assignDurch X K m ht hp f hg hw hL (exOk_sound X K i ci hi)
            (exOk_sound X K e ce he)
      | _ => exact absurd h (by simp [stOk])
  | assignSlot t f i e hw hL =>
      cases r with
      | storeSlot kp ci n ss off τc ce =>
          simp only [stOk, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact scorr_assignSlotVia X m K hp f hg hw hL (exOk_sound X K i ci hi)
            (exOk_sound X K e ce he)
      | storeNamed tn ci n ss off τc ce =>
          simp only [stOk, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact scorr_assignSlotVia X m K hp f hg hw hL (exOk_sound X K i ci hi)
            (exOk_sound X K e ce he)
      | _ => exact absurd h (by simp [stOk])
  | assignVar x e =>
      cases r with
      | setVar k τc ce =>
          simp only [stOk, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hK, hk⟩, hd⟩, he⟩ := h
          have hk' : k = K.loc x := of_decide_eq_true hk
          subst hk'
          exact scorr_assignVar X m K hK x (exOk_sound X K e ce he) hd
      | _ => exact absurd h (by simp [stOk])
  | call g args hp hr =>
      cases r with
      | call fc cargs dst =>
          cases dst with
          | some _ => exact absurd h (by simp [stOk])
          | none =>
              simp only [stOk, Bool.and_eq_true] at h
              obtain ⟨hfc, hk⟩ := h
              have hfc' : fc = fnum g := of_decide_eq_true hfc
              subst hfc'
              cases hc : c[fnum g]? with
              | none => rw [hc] at hk; exact absurd hk (by simp)
              | some k =>
                  rw [hc] at hk
                  simp only [Bool.and_eq_true] at hk
                  obtain ⟨hmap, ha⟩ := hk
                  simp only [callMapOk, Bool.and_eq_true, List.isEmpty_iff] at hmap
                  obtain ⟨⟨⟨hvm, hpp⟩, hks⟩, hnd⟩ := hmap
                  have hlay : (k.lay : CEnvLay D (D.params g)) = ⟨k.params.map Prod.fst, [], []⟩ := by
                    simp only [KFun.lay, of_decide_eq_true hvm, hpp, hks]
                  have hFk := hF g k hc
                  rw [hlay] at hFk
                  exact scorr_call X K m g args hp hr hFk
                    (argsTo_of X K args cargs k.params ha (of_decide_eq_true hnd))
      | _ => exact absurd h (by simp [stOk])
  | _ => exact absurd h (by simp [stOk])

/-- **Soundness of the body check**: the rows elaborate to C that the Gabbro
    body corresponds to (`EndCorr`). -/
theorem enOk_sound (hF : AlleRufe X fnum c) (top : Bool) {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk X.EL fnum c top rs K b = true → EndCorr X m top K b (endCS rs) := by
  intro rs
  induction rs with
  | nil =>
      intro Γ Λ K b h
      cases b with
      | ret r hΛ =>
          simp only [enOk, Bool.and_eq_true] at h
          exact EndCorr.retEnd hΛ h.1 (of_decide_eq_true h.2)
      | _ => exact absurd h (by simp [enOk])
  | cons r rs ih =>
      intro Γ Λ K b h
      cases r with
      | void x =>
          simp only [enOk, Bool.and_eq_true] at h
          obtain ⟨hv, hrest⟩ := h
          obtain ⟨⟨τ, v⟩, -, hl⟩ := List.any_eq_true.mp hv
          have hl' : K.loc v = x := of_decide_eq_true hl
          subst hl'
          exact EndCorr.pre (ecorr_var X K (Λ := Λ) v) (ih K b hrest)
      | ret cr =>
          simp only [enOk, Bool.and_eq_true, List.isEmpty_iff] at h
          obtain ⟨hnil, hb⟩ := h
          subst hnil
          cases b with
          | ret e hΛ => exact EndCorr.ret hΛ (ergOk_sound X K e cr hb)
          | _ => exact absurd hb (by simp)
      | bindLet x τc ce =>
          cases b with
          | bind e rest =>
              simp only [enOk, Bool.and_eq_true] at h
              obtain ⟨⟨⟨⟨hK, hf⟩, hd⟩, he⟩, hrest⟩ := h
              exact EndCorr.bind hK hf (exOk_sound X K e ce he) hd (ih _ rest hrest)
          | _ => exact absurd h (by simp [enOk])
      | _ =>
          cases b with
          | cons s rest =>
              simp only [enOk, Bool.and_eq_true] at h
              exact EndCorr.cons (stOk_sound X m K fnum c hF s _ h.1) (ih K rest h.2)
          | _ => exact absurd h (by simp [enOk])

end SoundS

/-! ## 4. Every call depth: the callee relation of every certified function -/

section Tiefe

theorem korrOk_fn {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (g : D.Fn) : ∃ k, c[fnum g]? = some k ∧ enOk EL fnum c true k.rows k.lay (P.rumpf g) = true := by
  have h := List.all_eq_true.mp hc g (hvoll g)
  cases hk : c[fnum g]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k => rw [hk] at h; exact ⟨k, rfl, h⟩

/-- **THE SOUNDNESS OF THE CHECK, AT EVERY DEPTH**: a certificate that
    checks gives, for every function, every call depth `n` and every budget,
    the callee relation between Gabbro's call `rufAt P O passes n` and the
    C call `CallAt … (kProg c) n` of the unit it elaborates to -- whatever
    the device oracle `orc` and the foreign-call meaning `XR`. -/
theorem korrOk_fnCorr {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (orc : DevOrc) (XR : CCallR) (O : Orakel D) (passes : Nat) :
    ∀ (n : Nat) (g : D.Fn) (k : KFun D), c[fnum g]? = some k →
      FnCorr EL (rufAt P O passes n) (CallAt EL.lay orc XR (kProg c) n) g (fnum g) k.params k.lay := by
  intro n
  induction n with
  | zero =>
      intro g k _ σ st ρG vs ρ0 _ _ _ hnf
      exact absurd hnf (by simp [rufAt, RufAusgang.istFehler])
  | succ n ih =>
      intro g k hk
      obtain ⟨k', hk', hok⟩ := korrOk_fn hvoll hc g
      rw [hk] at hk'
      cases hk'
      let X : TVCtx D := ⟨EL, orc, n + 1, CallAt EL.lay orc XR (kProg c) n, XR, O, passes,
        rufAt P O passes n⟩
      have hF : AlleRufe X fnum c := fun g' k'' hk'' => ih g' k'' hk''
      have hPr : kProg c (fnum g) = some { params := k.params, locals := k.locals, body := endCS k.rows } := by
        simp only [kProg, hk, Option.map_some]
      exact cCorr_ruf EL orc XR P O passes n (kProg c) g (fnum g) _ hPr k.lay 0
        (cCorr_end X 0 true (enOk_sound X 0 fnum c hF true k.rows k.lay (P.rumpf g) hok))

/-- **EVERY RUN**: under a checking certificate, from a C state related to
    the Gabbro world and C arguments related to the Gabbro arguments, when the
    Gabbro call at depth `n` ends in no model error, the C call has a run, and
    -- the C semantics being deterministic -- EVERY run of it ends related to
    the Gabbro outcome. -/
theorem korrOk_jeder_lauf {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional) (O : Orakel D) (passes n : Nat)
    (g : D.Fn) (k : KFun D) (hk : c[fnum g]? = some k) (σ : World D) (st : CSt)
    (ρG : Env D (D.params g)) (vs : List CVal) (ρ0 : CLok) (hw : corrW EL σ st)
    (hb : bindParams k.params vs = some ρ0) (hr : EnvRel EL k.lay ρG ρ0)
    (hnf : (rufAt P O passes n g σ ρG).istFehler = false) :
    (∃ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv) ∧
      ∀ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv →
        RufOut EL (rufAt P O passes n g σ ρG) st' rv := by
  obtain ⟨st1, rv1, hC1, hO1⟩ := korrOk_fnCorr hvoll hc orc XR O passes n g k hk σ st ρG vs ρ0 hw hb hr hnf
  refine ⟨⟨st1, rv1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional EL.lay orc XR hXR (kProg c) n (fnum g) st vs st1 rv1 st' rv hC1 hC
  subst e1
  subst e2
  exact hO1

end Tiefe

/-
CUTS -- what this file does not do, by name.
- COVERED FORMS: the statement and expression families listed in the header.
  Not covered (the Bool is `false`, a refusal): `if`/`else`, `traverse`,
  compound assignments (`+=` …), stores to globals, `let` of a call
  (`bindCall`), arithmetic and comparison expressions, `locks`, `forever`,
  device and foreign forms. Each has a T4 lemma already (`scorr_ite`,
  `scorr_traverse`, `scorr_plusGleich`, `scorr_assignGlob`, `bsem_bindCall`,
  `ecorr_add`, …); adding it here is one arm of `stOk`/`exOk` and one arm of
  its soundness proof. They were left out because no program the Lean parser
  admits today (sieve (a) of the chain count) contains them.
- A call's callee map must be its C parameter list (`callMapOk`): the
  exporter's map. The index-fixed `refD` maps (`ks`) of lanes 164/165 are
  not accepted at call sites; they still check as top-level maps.
- The Gabbro call is allowed to end in a model error (a failed `requires`,
  `ensures`, invariant, the call-depth bound `abstieg`, a hardware answer):
  the correspondence then claims nothing (`FnCorr` is conditional on
  `istFehler = false`). That the model's call ends without error is the
  model judgement's business (the goal theorem), not the certificate's.
-/

#print axioms Gabbro.Grammatik.ptrOk_sound
#print axioms Gabbro.Grammatik.exOk_sound
#print axioms Gabbro.Grammatik.argsTo_of
#print axioms Gabbro.Grammatik.stOk_sound
#print axioms Gabbro.Grammatik.enOk_sound
#print axioms Gabbro.Grammatik.korrOk_fnCorr
#print axioms Gabbro.Grammatik.korrOk_jeder_lauf

end Gabbro.Grammatik
