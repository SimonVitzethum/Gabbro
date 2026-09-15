/-
  File:      Grammatik/Schlusssatz104.lean
  Subject:   THE CLOSING THEOREM, STAGE (a), FOR `beispiele/104-referenz.gab`
             (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2 and
             §6): `schlusssatz_104`. Chain count 1.

  ONE program: `gP` over `gD` (`G104_referenz`), the program the LEAN PARSER
  produces from the source text (`Parser/Uebersetze.lean`). Before this
  file the chain talked about three programs -- `gP` (parser), `r4P` over
  `r4D` (goal theorem, hand translation) and `refP` over `refD` (C
  correspondence, the index-fixed one-parameter model) -- related by data
  agreement only. Every part is re-anchored at `gP` here:

  * section 1, parse: the source text lexes, parses, elaborates and lowers
    to `(gP, gFs)`; every stage a PROPOSITIONAL equation (the `Bool` pins
    `u104parse`/`u104elab` become `rfl` equations), `uebersetze104_ok`;
  * section 2, C: the emitted C bodies of `einzahlen` and `lies` (quoted in
    `CFormenZeuge.lean`) correspond to `gP`'s bodies (`liesG_fn`,
    `einG_fn`); the correspondence certificate carries the printer's rows
    and layout verbatim and `gP`'s locals map (`certG104`, `certOkG`,
    `corrCertG_sound`); from any related start the Gabbro call ends `ok`
    and EVERY C run ends related to it (`c104_einzahlen`, `c104_lies`);
  * section 3, model certificates: the Lean-side print of `gP`'s bodies IS
    the pasted printer output of `ZeugnisStmt104b.lean` (`print104_*`),
    and the Lean checker accepts it;
  * section 4, model judgement: every function of `gP` meets the
    per-function obligations of the goal theorem (`gP_koerperS`,
    `gP_invGutS`);
  * section 5, the machine: G starts EVERY thread in some function, and
    every function of `gD` holds `M` by signature, so no G theorem applies
    to a machine of `gP` alone (`gP_kein_ruhig`, `gP_kein_exklusiv`,
    proved). The runtime supplies the idle root: `gDB`/`gPB` = `gD`/`gP`
    plus exactly that root. `gPB`'s source part IS `gP` under a structural
    renaming (`gPB_ist_gP_umbenannt`, kernel-checked) and BEHAVES as `gP`
    through the same emitted C (`gPB_wie_gP_einzahlen`, `gPB_wie_gP_lies`);
    the goal theorem holds on the machine of `gPB` from every start memory,
    at every `forever` budget, for every start of the runtime's shape
    (`LaufzeitStart`, assumption A4 as a hypothesis), with the root
    function's `ensures` at its completion (`gPB_ziel`);
  * section 6, the theorem -- with A1 (+A2, A3) and A4 as HYPOTHESES
    (2026-09-14) --, its witnesses (rule 13) and its CUTS.
-/
import Grammatik.Parser.Uebersetze
import Grammatik.ZeugnisStmt104b
import Grammatik.Korrespondenz104
import Grammatik.CFormenDet
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtGanzZeuge
import Grammatik.ZeugnisIdent
import Grammatik.ZielOrtStart

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze
open G104_referenz (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies)

set_option maxRecDepth 100000

/-! ## 1. Parse: the source text to `(gP, gFs)` -/

/-- The source text of `beispiele/104-referenz.gab`, comment-free (the text
    `u104lex` pins; comments lex away) -- the pieces are in `Uebersetze.lean`
    (`srcZeilen104K`), and the text is *built from* them, so it is the same
    669 bytes it always was. Why pieces: O13, `Parser/Lexer.lean`. -/
def src104 : String := String.ofList srcQuelle104K

/-- THE LEAN TRANSLATION PIPELINE of the 104 fragment: lex, parse,
    elaborate, lower. Every stage is a Lean function; nothing Rust. -/
def uebersetze104 (s : String) : Except String (Programm G104_referenz.gD × List GFn) :=
  match lex s with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items =>
      match elabU items with
      | .error e => .error e
      | .ok u => lowerProg u

theorem s104_lex : lex src104 = .ok tt104 := u104lex

/-- The 104 pipeline from a source pinned as CHARACTERS, stage by stage --
    the local form of `uebersetzeAllg_von_zeichen` (Schlusssatz.lean), and
    for the same measured reason: unfolding `uebersetze104` at a CONCRETE
    source makes simplification whnf the discriminant `lex src104`, which
    runs Lean 4.33's UTF-8 decoder in the kernel (8,9 GB for this file,
    measured 2026-09-15). Here `l` is a variable, so there is nothing to
    decode. The conclusion is the same proposition either way. -/
theorem uebersetze104_von_zeichen {l : List Char} {toks : List Token}
    {items : List SItemTief} {u : UProg}
    (hl : lexL l = .ok toks)
    (hp : parseTopTief toks = .ok items)
    (he : elabU items = .ok u) :
    uebersetze104 (String.ofList l) = lowerProg u := by
  unfold uebersetze104
  rw [lex_ofList, hl]
  dsimp only
  rw [hp]
  dsimp only
  rw [he]

/-- Parsing, as an equation (the `Bool` pin `u104parse` made propositional). -/
theorem s104_parse : parseTopTief tt104 = .ok items104 := rfl

/-- Elaboration, as an equation (the `Bool` pin `u104elab` made propositional). -/
theorem s104_elab : elabU items104 = .ok uExp104 := rfl

/-- **PARSE FIDELITY**: the source text translates, in Lean, to the program
    `gP` with member list `gFs`. -/
theorem uebersetze104_ok : uebersetze104 src104 = .ok (G104_referenz.gP, G104_referenz.gFs) := by
  show uebersetze104 (String.ofList srcQuelle104K) = _
  rw [uebersetze104_von_zeichen u104lexL s104_parse s104_elab]
  exact u104lower

/-! ## 2. C: the emitted bodies correspond to `gP`'s bodies -/

/-- The emitter's layout of `gD`: `Konto` is table block 0, `stand` is
    field 0 of `Konto_slot` at `uint32_t`, no globals (the layout of
    `refEL`, over the parser's declaration). -/
def gEL104 : EmitLay G104_referenz.gD where
  lay := refLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => kontoLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun t => by cases t; rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun t f f' _ => by cases t; cases f; cases f'; rfl
  fnr_fits := fun t f => by cases t; cases f; rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- The oracle of `gD`: no axiom, register or global exists. -/
def gO104 : Orakel G104_referenz.gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- `lies` runs in frame 1, calling nothing. -/
def xLiesG : TVCtx G104_referenz.gD :=
  ⟨gEL104, tvOrc, 1, CallAt gEL104.lay tvOrc tvXR refCProg 0, tvXR, gO104, 0, rufAt G104_referenz.gP gO104 0 0⟩

/-- `einzahlen` runs in frame 2, its callees at depth 1. -/
def xEinG : TVCtx G104_referenz.gD :=
  ⟨gEL104, tvOrc, 2, CallAt gEL104.lay tvOrc tvXR refCProg 1, tvXR, gO104, 0, rufAt G104_referenz.gP gO104 0 1⟩

/-! ### 2.1 The correspondence certificate over `gP`

The rows (`(void)b;`, `k->slots[i].stand = 100;`, `lies(k, i);`,
`return k->slots[i].stand;`) and the layout are the emitter's, verbatim
from `printed104` (`certG104_rows`). The locals map is `gP`'s: `gP` HAS the
parameters `k`, `i`, `b`, so C locals 0, 1, 2 are Gabbro variables 0, 1, 2
(`vm`), and nothing is a pointer-only (`pp`) or model-fixed (`ks`) local.
`printed104`'s map (`vm = [2]`, `pp`, `ks = [(1, 0)]`) is the map for the
index-fixed model `refD`; its `ks` entry was the printer's `MODEL DATUM`. -/

/-- The certificate `certOkG` accepts: rows and layout as printed, the map
    of `gP`. -/
def certG104 : Cert104 :=
  { einRows := [CertRow.voidB 2, CertRow.store100 0 1, CertRow.callLies 0 1],
    liesRows := [CertRow.retLoad 0 1],
    lay := ⟨2, 4, 0⟩,
    vmEin := [0, 1, 2], ppEin := [], ksEin := [],
    vmLies := [0, 1], ppLies := [], ksLies := [] }

/-- The rows and the layout ARE the emitter's printed ones. -/
theorem certG104_rows : certG104.einRows = printed104.einRows ∧
    certG104.liesRows = printed104.liesRows ∧ certG104.lay = printed104.lay :=
  ⟨rfl, rfl, rfl⟩

/-- THE DECIDABLE CHECK of a certificate against `gP`: the rows and layout
    of the emitted C of 104, and `gP`'s locals map. -/
def certOkG (c : Cert104) : Bool :=
  decide (c.einRows = [.voidB 2, .store100 0 1, .callLies 0 1]) &&
  decide (c.liesRows = [.retLoad 0 1]) &&
  decide (c.lay = ⟨2, 4, 0⟩) &&
  decide (c.vmEin = [0, 1, 2]) && decide (c.ppEin = []) && decide (c.ksEin = []) &&
  decide (c.vmLies = [0, 1]) && decide (c.ppLies = []) && decide (c.ksLies = [])

theorem certG104_ok : certOkG certG104 = true := by decide

/-- The locals layout of a certificate, over `gD` (pointer entries name
    table `Konto`, the only table). -/
def kOfG {Γ : Ctx} (vm : List Nat) (pp : List (Nat × Unit)) (ks : List (Nat × Int)) :
    CEnvLay G104_referenz.gD Γ :=
  ⟨vm, pp.map (fun q => (q.1, GTab.Konto)), ks⟩

def kEinG : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_einzahlen) := kOfG [0, 1, 2] [] []

def kLiesG : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_lies) := kOfG [0, 1] [] []

/-! ### 2.2 `lies` -/

/-- `return k->slots[i].stand;` corresponds to `gP`'s `lies` body:
    `k` is C local 0 (Gabbro variable 0), `i` C local 1 (variable 1). -/
theorem liesG_end (m : Nat) : EndCorr xLiesG m true kLiesG (G104_referenz.gP.rumpf g_lies) cLiesBody := by
  have hi : ExprCorr xLiesG kLiesG (.var 1)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_lies) (Λ := gL_lies) (.dort .hier)) :=
    ecorr_var xLiesG kLiesG (.dort .hier)
  have hp : PtrTo xLiesG kLiesG (.var 0) GTab.Konto :=
    ptrTo_var xLiesG kLiesG (Γ := gCtx_lies) (.hier) rfl
  have he := ecorr_durch xLiesG kLiesG (Λ := gL_lies) (rw := false) (p := Expr.var .hier)
    rfl hp GKontoFeld.stand rfl gDarf_lies_Konto hi
  exact EndCorr.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- THE CALLEE RELATION of `lies` at depth 1. -/
theorem liesG_fn : FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 1) (CallAt gEL104.lay tvOrc tvXR refCProg 1)
    g_lies 1 cLies.params kLiesG :=
  cCorr_ruf gEL104 tvOrc tvXR G104_referenz.gP gO104 0 0 refCProg g_lies 1 cLies rfl kLiesG 0
    (cCorr_end xLiesG 0 true (liesG_end 0))

/-! ### 2.3 `einzahlen` -/

/-- `(void)b;` evaluates Gabbro's `b` (variable 2, C local 2). -/
theorem einG_void :
    ExprCorr xEinG kEinG (.var 2)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (.dort (.dort .hier))) :=
  ecorr_var xEinG kEinG (.dort (.dort .hier))

/-- `k->slots[i].stand = 100;` against `k.slots[i].stand = 100` through the
    `rw` pointer `k`. -/
theorem einG_write (m : Nat) :
    StmtCorr xEinG m kEinG
      (Stmt.assignDurch (V := vertragVon G104_referenz.gD g_einzahlen) (l := false) (Γ := gCtx_einzahlen)
        (Λ := gL_einzahlen) (.var .hier) GTab.Konto rfl GKontoFeld.stand (.var (.dort .hier))
        (.weiter (by decide) (by decide) (.lit 100)) (by decide) gDarf_einzahlen_Konto)
      (.store cStand cU32 (.lit 100)) := by
  have hi : ExprCorr xEinG kEinG (.var 1)
      (Expr.var (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (.dort .hier)) :=
    ecorr_var xEinG kEinG (.dort .hier)
  have he : ExprCorr xEinG kEinG (.lit 100)
      (Expr.weiter (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) (lo' := 0) (hi' := 100)
        (by decide) (by decide) (.lit 100)) :=
    ecorr_weiter xEinG kEinG _ _ (ecorr_lit xEinG kEinG 100)
  have hp : PtrTo xEinG kEinG (.var 0) GTab.Konto :=
    ptrTo_var xEinG kEinG (Γ := gCtx_einzahlen) (.hier) rfl
  exact scorr_assignDurch xEinG kEinG m rfl hp GKontoFeld.stand rfl _ _ hi he

/-- The arguments of `lies(k, i);`: C passes `k` (local 0) and `i`
    (local 1); Gabbro passes a read-only pointer to the same table and `i`.
    A pointer's C value is the table's address either way. -/
theorem einG_args : ArgsTo xEinG kEinG
    (Args.cons (Expr.ptrOf (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) GTab.Konto 0 rfl false)
      (Args.cons (Expr.var (.dort .hier)) .nil))
    [.var 0, .var 1] cLies.params kLiesG := by
  intro σ st ρG ρC _ hr
  have h0 := hr.1 _ (Var.hier (Γ := [.index 2, .int 0 10]) (τ := .ptr 0 true))
  have h1 := hr.1 _ (Var.dort (σ := .ptr 0 true) (Var.hier (Γ := [.int 0 10]) (τ := .index 2)))
  obtain ⟨t0, ht0, e0⟩ := h0
  have et : t0 = GTab.Konto := by cases t0; rfl
  subst et
  have e0' : ρC 0 = .ptr ⟨.tab 0, 0⟩ := e0
  have e1' : ρC 1 = .int (encW (.index 2) (ρG.get (.dort .hier))) := h1
  have hc1 : convV cU32 (ρC 1) = some (ρC 1) := by
    rw [e1']
    exact convV_of_valCorr (EL := gEL104) (τ := .index 2) (v := ρG.get (.dort .hier)) rfl rfl
  refine ⟨[ρC 0, ρC 1], st, lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0), ?_,
    SameML.refl st, ?_, ?_⟩
  · simp only [evArgs, ev, e0', e1']
  · show (match convV .ptr (ρC 0), bindParams [(1, cU32)] [ρC 1] with
      | some v', some ρ => some (lokUpd ρ 0 v')
      | _, _ => none) = _
    have hb1 : bindParams [(1, cU32)] [ρC 1] = some (lokUpd (fun _ => .undef) 1 (ρC 1)) := by
      show (match convV cU32 (ρC 1), bindParams [] [] with
        | some v', some ρ => some (lokUpd ρ 1 v')
        | _, _ => none) = _
      rw [hc1]
      rfl
    rw [hb1, e0']
    rfl
  · refine ⟨?_, fun q hq => absurd hq (by simp [kLiesG, kOfG]),
      fun q hq => absurd hq (by simp [kLiesG, kOfG])⟩
    intro τ x
    cases x with
    | hier =>
        refine ⟨GTab.Konto, rfl, ?_⟩
        show lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 0 = _
        simp only [lokUpd, if_pos]
        exact e0'
    | dort y =>
        cases y with
        | hier =>
            show ValCorr gEL104 (.index 2) _ (lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 1)
            simp only [lokUpd]
            rw [e1']
            rfl
        | dort z => exact nomatch z

/-- `lies(k, i);` against `gP`'s call of `lies`. -/
theorem einG_call (m : Nat) :
    StmtCorr xEinG m kEinG
      (Stmt.call (V := vertragVon G104_referenz.gD g_einzahlen) (l := false) (Γ := gCtx_einzahlen) g_lies
        (Args.cons (Expr.ptrOf (D := G104_referenz.gD) (Γ := gCtx_einzahlen) (Λ := gL_einzahlen) GTab.Konto 0 rfl false)
          (Args.cons (Expr.var (.dort .hier)) .nil))
        gHp_einzahlen_lies rfl)
      (.call 1 [.var 0, .var 1] none) :=
  scorr_call xEinG kEinG m g_lies _ gHp_einzahlen_lies rfl liesG_fn einG_args

/-- THE BODY of `einzahlen` against the emitted body. -/
theorem einG_end (m : Nat) : EndCorr xEinG m true kEinG (G104_referenz.gP.rumpf g_einzahlen) cEinBody :=
  EndCorr.pre einG_void
    (EndCorr.cons (einG_write m) (EndCorr.cons (einG_call m) (EndCorr.retEnd (by rfl) rfl rfl)))

/-- THE CALLEE RELATION of `einzahlen` at depth 2. -/
theorem einG_fn : FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 2) (CallAt gEL104.lay tvOrc tvXR refCProg 2)
    g_einzahlen 0 cEin.params kEinG :=
  cCorr_ruf gEL104 tvOrc tvXR G104_referenz.gP gO104 0 1 refCProg g_einzahlen 0 cEin rfl kEinG 0
    (cCorr_end xEinG 0 true (einG_end 0))


/-! ### 2.4 The certificate is load-bearing -/

/-- The C unit a certificate elaborates to: `einzahlen` is function 0,
    `lies` function 1, bodies from the rows (parameters and locals as the
    emitter declares them). -/
def progOf (c : Cert104) : CProg
  | 0 => some { cEin with body := einCS c }
  | 1 => some { cLies with body := liesCS c }
  | _ => none

/-- A valid certificate elaborates to the EMITTED unit (the quoted C of
    `CFormenZeuge.lean`). -/
theorem progOf_ok (c : Cert104) (h : certOkG c = true) : progOf c = refCProg := by
  unfold certOkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, hL⟩, hLay⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hE' := of_decide_eq_true hE
  have hL' := of_decide_eq_true hL
  have hLay' := of_decide_eq_true hLay
  have e1 : einCS c = cEinBody := by unfold einCS; rw [hE', hLay']; rfl
  have e2 : liesCS c = cLiesBody := by unfold liesCS; rw [hL', hLay']; rfl
  funext n
  match n with
  | 0 => simp only [progOf, e1]; rfl
  | 1 => simp only [progOf, e2]; rfl
  | _ + 2 => rfl

/-- A valid certificate's locals maps ARE `gP`'s. -/
theorem kOf_ok (c : Cert104) (h : certOkG c = true) :
    (kOfG c.vmEin c.ppEin c.ksEin : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) =
      kEinG ∧
    (kOfG c.vmLies c.ppLies c.ksLies : CEnvLay G104_referenz.gD (G104_referenz.gD.params g_lies)) =
      kLiesG := by
  unfold certOkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hVmE⟩, hPpE⟩, hKsE⟩, hVmL⟩, hPpL⟩, hKsL⟩ := h
  rw [of_decide_eq_true hVmE, of_decide_eq_true hPpE, of_decide_eq_true hKsE,
    of_decide_eq_true hVmL, of_decide_eq_true hPpL, of_decide_eq_true hKsL]
  exact ⟨rfl, rfl⟩

/-- **THE SOUNDNESS OF THE CORRESPONDENCE CERTIFICATE over `gP`**: a valid
    certificate gives the callee relations of both functions of `gP`,
    against the unit the certificate elaborates to, under the certificate's
    locals maps. -/
theorem corrCertG_sound (c : Cert104) (h : certOkG c = true) :
    FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 1) (CallAt gEL104.lay tvOrc tvXR (progOf c) 1)
      g_lies 1 cLies.params (kOfG c.vmLies c.ppLies c.ksLies) ∧
    FnCorr gEL104 (rufAt G104_referenz.gP gO104 0 2) (CallAt gEL104.lay tvOrc tvXR (progOf c) 2)
      g_einzahlen 0 cEin.params (kOfG c.vmEin c.ppEin c.ksEin) := by
  rw [progOf_ok c h, (kOf_ok c h).1, (kOf_ok c h).2]
  exact ⟨liesG_fn, einG_fn⟩

/-! ### 2.5 Every run: the sequential model's answer and the C runs -/

/-- `lies` on `gP`, from ANY world and arguments, at any depth: the call
    ends `ok` (requires, ensures and invariants all checked by `rufAt`),
    and the answer world has the caller's slots. -/
theorem rufLies_ok (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ∃ σ' v, rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok σ' v ∧ σ'.slots = σ.slots := by
  have h := rufAt_ok_of_gates G104_referenz.gP gO104 0 n g_lies σ ρ _ rfl rfl _ _ rfl _ rfl
    (by show wahr? (decide (_ = _)) = true; exact decide_eq_true rfl) _ rfl rfl
  exact ⟨_, _, h, rfl⟩

/-- The answer world of `lies` (chosen; its slots are the caller's). -/
noncomputable def liesW (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) : World G104_referenz.gD :=
  Classical.choose (rufLies_ok n σ ρ)

theorem liesW_spec (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ∃ v, rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok (liesW n σ ρ) v ∧
      (liesW n σ ρ).slots = σ.slots :=
  Classical.choose_spec (rufLies_ok n σ ρ)

/-- The answer value of `lies` (chosen). -/
noncomputable def liesV (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    ErgVal G104_referenz.gD (G104_referenz.gD.erg g_lies) :=
  Classical.choose (liesW_spec n σ ρ)

theorem liesAt (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    rufAt G104_referenz.gP gO104 0 (n + 1) g_lies σ ρ = .ok (liesW n σ ρ) (liesV n σ ρ) :=
  (Classical.choose_spec (liesW_spec n σ ρ)).1

theorem liesW_slots (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) :
    (liesW n σ ρ).slots = σ.slots :=
  (Classical.choose_spec (liesW_spec n σ ρ)).2

/-- `einzahlen`'s body under `rufAt` handlers: it returns, with the slot
    `k.slots[i].stand` at `100`. -/
theorem einBody (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) :
    ∃ σ1, execEnd (V := vertragVon G104_referenz.gD g_einzahlen) gO104 0
      (rufAt G104_referenz.gP gO104 0 (n + 1)) (G104_referenz.gP.rumpf g_einzahlen) σ ρ =
      .zurueck σ1 () ∧ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 := by
  show ∃ σ1, execEnd _ _ _ G104_referenz.gBody_einzahlen σ ρ = _ ∧ _
  simp only [G104_referenz.gBody_einzahlen, execEnd, execStmt, liesAt]
  refine ⟨_, rfl, ?_⟩
  show ((liesW n _ _).slots GTab.Konto _ GKontoFeld.stand).n = 100
  rw [liesW_slots]
  exact (congrArg (fun z : Zahl 0 100 => z.n)
    (storeSlot_hit (D := G104_referenz.gD) _ GTab.Konto _ GKontoFeld.stand _)).trans rfl

/-- `einzahlen` on `gP`, from ANY world and arguments, at depth `n + 2`:
    the call ends `ok` -- its `ensures old(stand) <= stand` and `lies`'s
    `ensures result == stand` both checked by `rufAt` on the way. -/
theorem rufEin_ok (n : Nat) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) :
    ∃ σ', rufAt G104_referenz.gP gO104 0 (n + 2) g_einzahlen σ ρ = .ok σ' () := by
  obtain ⟨σ1, hb, h100⟩ := einBody n
    (σ.lese (Signatur.anfang G104_referenz.gD (G104_referenz.gD.signatur g_einzahlen))
      (G104_referenz.gP.requires g_einzahlen).orte) ρ
  refine ⟨_, rufAt_ok_of_gates G104_referenz.gP gO104 0 (n + 1) g_einzahlen σ ρ _ rfl rfl _ ()
    hb _ rfl ?_ _ rfl rfl⟩
  show wahr? (decide (_ ≤ _)) = true
  apply decide_eq_true
  show _ ≤ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n
  rw [h100]
  exact (Zahl.le_hi _)

/-- No foreign call in this unit: its (empty) meaning is functional. -/
theorem tvXR_funktional : tvXR.Funktional := fun _ _ _ _ _ _ _ h _ => h.elim

/-- **EVERY RUN OF THE EMITTED C OF `einzahlen`** (depth 2, calling `lies`
    at depth 1), from a state related to ANY Gabbro world, with arguments
    related to ANY Gabbro arguments: the Gabbro call `rufAt gP … einzahlen`
    ends `ok` in a world `σ'`; the C call has a run; and EVERY C run ends in
    a state related to `σ'`, returning nothing. -/
theorem c104_einzahlen (c : Cert104) (hc : certOkG c = true) (σ : World G104_referenz.gD)
    (st : CSt) (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
    (vs : List CVal) (ρ0 : CLok) (hw : corrW gEL104 σ st)
    (hb : bindParams cEin.params vs = some ρ0)
    (hr : EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0) :
    ∃ σ', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
      (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' none) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' rv →
        corrW gEL104 σ' st' ∧ rv = none := by
  obtain ⟨σ', hR⟩ := rufEin_ok 0 σ ρG
  have hF := (corrCertG_sound c hc).2
  obtain ⟨st1, rv1, hC1, hO1⟩ := hF σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  rw [hR] at hO1
  obtain ⟨hc1, hret1⟩ := hO1
  have hrv1 : rv1 = none := hret1
  subst hrv1
  refine ⟨σ', hR, ⟨st1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional (progOf c) 2
    0 st vs st1 none st' rv hC1 hC
  subst e1
  exact ⟨hc1, e2.symm⟩

/-- **EVERY RUN OF THE EMITTED C OF `lies`** (depth 1): the Gabbro call ends
    `ok` with answer `v`; the C call has a run; every C run ends related and
    returns the encoding of `v`. -/
theorem c104_lies (c : Cert104) (hc : certOkG c = true) (σ : World G104_referenz.gD)
    (st : CSt) (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
    (vs : List CVal) (ρ0 : CLok) (hw : corrW gEL104 σ st)
    (hb : bindParams cLies.params vs = some ρ0)
    (hr : EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0) :
    ∃ σ' v, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
      (∃ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv →
        corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv := by
  obtain ⟨σ', v, hR, -⟩ := rufLies_ok 0 σ ρG
  have hF := (corrCertG_sound c hc).1
  obtain ⟨st1, rv1, hC1, hO1⟩ := hF σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  rw [hR] at hO1
  refine ⟨σ', v, hR, ⟨st1, rv1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional (progOf c) 1
    1 st vs st1 rv1 st' rv hC1 hC
  subst e1
  subst e2
  exact hO1


/-! ## 3. Model certificates: they are the print of `gP`'s bodies -/

section Druck
variable {D : Deklaration} {V : Vertrag D} {l : Bool}

/-- Print of a statement of the 104 shapes, in front of the print of the
    rest: the pointer write (`cons2 assignDurch`, pointer and proofs
    forgotten, index and value printed) and the call (`consCall`, the
    argument count and the `RufPasst` carried). Every other statement: none. -/
def printStmt104 {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → CertEnd104 D V → Option (CertEnd104 D V)
  | .assignDurch (n := n) _ t _ f i e _ _, r =>
    (printInt i).bind fun ci => (printInt e).bind fun ce =>
      some (.cons2 (.assignDurch t f n true ci ce) Λ' r)
  | .call f _ hp _, r => some (.consCall f (D.params f).length Λ hp r)
  | _, _ => none

/-- Print of a return value: none (`ret`) or a read through a pointer
    (`retDurch`, the pointer forgotten, the table number and index
    printed). Every other value: none. -/
def printRet104 {Γ : Ctx} {Λ : List (Res D)} : {e : Option Ty} → ErgExpr D Γ Λ e →
    Option (CertEnd104 D V)
  | _, .keine => some (.lift2 (.liftE .ret))
  | _, .wert (.durch (n := n) _ t _ f i _) => (printInt i).map (CertEnd104.retDurch t f n)
  | _, .wert _ => none

/-- THE LEAN-SIDE PRINT of a body, in the `CertEnd104` layer. -/
def printEnd104 {Γ : Ctx} : {Λ : List (Res D)} → Endblock D V l Γ Λ → Option (CertEnd104 D V)
  | _, .cons s rest => (printEnd104 rest).bind (printStmt104 s)
  | _, .ret e _ => printRet104 e
  | _, _ => none

end Druck

/-- **The pasted statement certificate of `einzahlen` IS the print of the
    parsed program's body** (term identity on the Lean side, for this body). -/
theorem print104_einzahlen :
    printEnd104 (G104_referenz.gP.rumpf g_einzahlen) = some cert104_einzahlen := rfl

theorem print104_lies :
    printEnd104 (G104_referenz.gP.rumpf g_lies) = some cert104_lies := rfl

theorem cert104_einzahlen_ok : certEnd104Ok G104_referenz.gD
    (vertragVon G104_referenz.gD g_einzahlen) false gCtx_einzahlen gL_einzahlen
    cert104_einzahlen = true := by decide

theorem cert104_lies_ok : certEnd104Ok G104_referenz.gD
    (vertragVon G104_referenz.gD g_lies) false gCtx_lies gL_lies cert104_lies = true := by decide


/-! ## 4. The model judgement on `gP` -/

/-- A call of a `requires true` function through the gate never fails the
    gate when the handler blames nobody (over `gD`). -/
theorem g_call_tor {V : Vertrag G104_referenz.gD} {l : Bool} {Γ : Ctx}
    {Λ : List (Res G104_referenz.gD)} (O : Orakel G104_referenz.gD) (passes : Nat)
    (R : ∀ f : G104_referenz.gD.Fn, World G104_referenz.gD → Env G104_referenz.gD
      (G104_referenz.gD.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : G104_referenz.gD.Fn) (args : Args G104_referenz.gD Γ Λ (G104_referenz.gD.params g))
    (hp : RufPasst G104_referenz.gD V (G104_referenz.gD.signatur g) Λ)
    (hr : G104_referenz.gD.gruende g = 0) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD Γ) (g' : G104_referenz.gD.Fn) :
    execStmt O passes (torRuf G104_referenz.gP R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf G104_referenz.gP R g σ1 ρ1 = R g σ1 ρ1 :=
    fun _ _ => if_pos (by cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | grund σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

/-- `lies` meets its obligation: the returned value is the slot. -/
theorem gP_koerper_lies : KoerperGutV G104_referenz.gP 0 g_lies := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : G104_referenz.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun

/-- **`einzahlen` of the parsed program meets the obligation against
    declared frames**: the write sets the slot to `100`, `lies` declares no
    write (every frame-respecting answer keeps the slots), so
    `old(stand) <= stand` is `old(stand) <= 100`, true by the range. -/
theorem gP_einzahlen_R : KoerperGutR G104_referenz.gP 0 g_einzahlen := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 g_lies _ _ σ2 w hRv).1.1 GTab.Konto rfl
      simp only [execStmt] at h1
      cases h1
      show decide ((σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.dort .hier)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := G104_referenz.gD) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : G104_referenz.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact g_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem gFs_voll : ∀ g : G104_referenz.gD.Fn, g ∈ G104_referenz.gFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem gP_logikFrei : programmLogikFrei G104_referenz.gP G104_referenz.gFs = true := by decide

/-- **THE MODEL JUDGEMENT on the parsed program**: every function meets the
    per-function obligation of the goal theorem (`KoerperGutS`, over the
    empty lock-invariant family and the trivial axiom ensures -- the
    declaration has no axiom). -/
theorem gP_koerperS : ∀ f : G104_referenz.gD.Fn,
    KoerperGutS G104_referenz.gP 0 (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  fun f => koerperGutS_leer ⟨koerperGutRQ_of_R _ (match f with
    | .einzahlen => gP_einzahlen_R
    | .lies => koerperGutR_of_V gP_koerper_lies),
    programmLogikFrei_ok gFs_voll gP_logikFrei 0 _ f⟩

theorem gP_invGutS : ∀ f : G104_referenz.gD.Fn,
    InvGutS G104_referenz.gP 0 (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  invGutS_leer rfl

/-- No body of the parsed program contains a `forever` loop. -/
theorem gP_ohneEwig : ohneEwigB G104_referenz.gP G104_referenz.gFs = true := by decide

/-- **The model judgement at EVERY `forever` budget** (`Durchgaenge.lean`):
    the goal statements demand the obligation at every budget. -/
theorem gP_koerperS_alle : ∀ (passes : Nat) (f : G104_referenz.gD.Fn),
    KoerperGutS G104_referenz.gP passes (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  koerperGutS_alle gFs_voll gP_ohneEwig gP_koerperS

theorem gP_invGutS_alle : ∀ (passes : Nat) (f : G104_referenz.gD.Fn),
    InvGutS G104_referenz.gP passes (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  fun _ => invGutS_leer rfl

/-- **The call semantics of the parsed program does not depend on the
    budget**: every statement of part 4 at budget `0` holds at every
    budget. -/
theorem gP_rufAt_passes : ∀ (passes k : Nat) (f : G104_referenz.gD.Fn) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params f)),
    rufAt G104_referenz.gP gO104 passes k f σ ρ = rufAt G104_referenz.gP gO104 0 k f σ ρ :=
  fun passes => rufAt_passes gO104 (ohneEwigB_ok gFs_voll gP_ohneEwig) passes 0


/-! ## 5. The machine -/

/-! ### 5.1 The finding: no G machine of `gP` alone has one active thread -/

/-- No function of the parsed program is an idle root (`ruhig`): both hold
    `M` by signature and touch `Konto`. -/
theorem gP_kein_ruhig : ∀ f : G104_referenz.gD.Fn, ruhig G104_referenz.gP f = false := by
  intro f; cases f <;> decide

/-- **No start assignment of `gP` is exclusive**: G starts EVERY thread in
    some function, and every function of `gD` holds `M` by signature, so
    threads 0 and 1 both start holding `M`. Neither `ziel_ort_einfaden`
    (idle roots) nor `ziel_ort_sperre`/`_inv` (`StartExklusiv`) applies to
    a machine of `gP` alone: the start of the other threads is runtime
    data, not source text. -/
theorem gP_kein_exklusiv (init : Faden → Σ f : G104_referenz.gD.Fn,
    Env G104_referenz.gD (G104_referenz.gD.params f)) : ¬ StartExklusiv init := by
  intro h
  have hM : ∀ f : G104_referenz.gD.Fn, GLock.M ∈ G104_referenz.gD.haelt f := by
    intro f; cases f <;> exact List.mem_singleton.mpr rfl
  exact h 0 1 (by decide) GLock.M (hM _) (hM _)

/-! ### 5.2 The runtime's idle root: `gDB`, `gPB` -/

/-- The idle root's signature: no parameter, no result, no lock, no write. -/
def sigRuhe : Signatur GTab Empty GLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- **`gD` plus the idle root**: every carrier, lock, table, field, global,
    axiom and register IS `gD`'s (the fields are `gD`'s own); the functions
    are `some f` for `gD`'s `f` (same signature number) and `none`, the
    idle root (signature number 2, unused by `gD`: `gD` has no function
    pointer). -/
abbrev gDB : Deklaration :=
  { G104_referenz.gD with
    Fn := Option GFn
    sig := fun | some f => G104_referenz.gD.sig f | none => 2
    sigNr := fun | 2 => sigRuhe | n => G104_referenz.gD.sigNr n
    eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
    rzusage := fun r => nomatch r
    invarianten_gehalten := fun _ i => nomatch i }

abbrev gbL : List (Res gDB) := [Res.held (D := gDB) GLock.M]

theorem gbDarf : darf gDB GTab.Konto gbL := by unfold darf; decide

theorem gbHp : RufPasst gDB (vertragVon gDB (some GFn.einzahlen)) (gDB.signatur (some GFn.lies))
    gbL where
  hw := fun t => by cases t <;> decide
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (fun L => by cases L <;> decide)
  hx := RufPasst.hx_von (fun L => by cases L <;> decide)

def gbEns_einzahlen : Expr gDB (ErgCtx (gDB.params (some GFn.einzahlen)) (gDB.erg (some GFn.einzahlen)))
    (vertragVon gDB (some GFn.einzahlen)).ende .bool :=
  (.le (Expr.altSlot (D := gDB) GTab.Konto GKontoFeld.stand ((.var (.dort .hier))) gbDarf)
    (Expr.durch (D := gDB) (.var .hier) GTab.Konto rfl GKontoFeld.stand ((.var (.dort .hier))) gbDarf))

def gbEns_lies : Expr gDB (ErgCtx (gDB.params (some GFn.lies)) (gDB.erg (some GFn.lies)))
    (vertragVon gDB (some GFn.lies)).ende .bool :=
  (.eq (.var .hier) (Expr.durch (D := gDB) (.var (.dort .hier)) GTab.Konto rfl GKontoFeld.stand
    ((.var (.dort (.dort .hier)))) gbDarf))

def gbBody_einzahlen : Endblock gDB (vertragVon gDB (some GFn.einzahlen)) false
    (gDB.params (some GFn.einzahlen)) gbL :=
  (.cons (.assignDurch (.var .hier) GTab.Konto rfl GKontoFeld.stand ((.var (.dort .hier)))
    (.weiter (by decide) (by decide) (.lit 100)) (by decide) gbDarf)
    (.cons (.call (some GFn.lies) (.cons (.ptrOf GTab.Konto 0 rfl false) (.cons (.var (.dort .hier)) .nil))
      gbHp rfl) (.ret .keine (List.Perm.refl _))))

def gbBody_lies : Endblock gDB (vertragVon gDB (some GFn.lies)) false
    (gDB.params (some GFn.lies)) gbL :=
  (.ret (.wert (Expr.durch (D := gDB) (.var .hier) GTab.Konto rfl GKontoFeld.stand
    ((.var (.dort .hier))) gbDarf)) (List.Perm.refl _))

def gbBody_ruhe : Endblock gDB (vertragVon gDB none) false (gDB.params none) [] :=
  .ret .keine List.Perm.nil

/-- **The program the machine runs**: `gP`'s contracts and bodies on
    `some f` (section 5.3 proves them the renamings of the parser's), the
    idle root on `none`. -/
def gPB : Programm gDB where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | some .einzahlen => gbEns_einzahlen
    | some .lies => gbEns_lies
    | none => .wahr
  rumpf
    | some .einzahlen => gbBody_einzahlen
    | some .lies => gbBody_lies
    | none => gbBody_ruhe

def gbFs : List gDB.Fn := [some GFn.einzahlen, some GFn.lies, none]

theorem gbFs_voll : ∀ g : gDB.Fn, g ∈ gbFs := by
  intro g
  rcases g with _ | g
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · cases g
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem gPB_fragment : programmImFragmentG gPB gbFs = true := by decide

theorem gPB_logikFrei : programmLogikFrei gPB gbFs = true := by decide

theorem gPB_ruhig : ruhig gPB none = true := by decide


/-! ### 5.3 `gPB`'s source part IS the parsed program, renamed

`renE`/`renArgs`/`renErg`/`renS`/`renEnd` rename a term over `gD` to the same
term over `gDB`: every constructor to the same-named constructor, every
table, field, lock, index and literal to itself, a function `f` to `some f`;
proofs are transported (`darf_rm`, `rufPasst_rm`, `perm_rm`), never
re-invented. The renaming is PARTIAL: it covers the constructors of the
104 fragment (and a few more) and answers `none` elsewhere, so an equation
`ren x = some y` is a kernel-checked statement that `y` is `x` renamed. -/

/-- A resource of `gD` as a resource of `gDB` (same lock, same mark). -/
def rm : Res G104_referenz.gD → Res gDB
  | .held L => .held L
  | .marke m s => .marke m s

theorem rm_von (w : GLock ⊕ (Empty × Nat)) : rm (Res.von G104_referenz.gD w) = Res.von gDB w := by
  rcases w with L | ⟨m, s⟩
  · rfl
  · exact m.elim

theorem darf_rm {t : GTab} {Λ : List (Res G104_referenz.gD)} (h : darf G104_referenz.gD t Λ) :
    darf gDB t (Λ.map rm) := by
  intro w hw
  rw [← rm_von]
  exact List.mem_map_of_mem (h w hw)

/-- A contract of `gD` as a contract of `gDB` (field by field). -/
def vm (V : Vertrag G104_referenz.gD) : Vertrag gDB :=
  ⟨V.schreibt, V.gschreibt, V.erg, V.gruende, V.haelt, V.produziert, V.boden⟩

theorem ende_rm (V : Vertrag G104_referenz.gD) : (vm V).ende = V.ende.map rm := by
  have hp : V.produziert = [] := by
    cases h : V.produziert with
    | nil => rfl
    | cons x _ => exact x.1.elim
  simp [Vertrag.ende, vm, hp, rm]

theorem perm_rm {V : Vertrag G104_referenz.gD} {Λ : List (Res G104_referenz.gD)}
    (h : Λ.Perm V.ende) : (Λ.map rm).Perm (vm V).ende := by
  rw [ende_rm]
  exact h.map rm

theorem konsumiert_leer (S : Signatur GTab Empty GLock Empty) : S.konsumiert = [] := by
  cases h : S.konsumiert with
  | nil => rfl
  | cons x _ => exact x.1.elim

theorem produziert_leer (S : Signatur GTab Empty GLock Empty) : S.produziert = [] := by
  cases h : S.produziert with
  | nil => rfl
  | cons x _ => exact x.1.elim

theorem held_rm_mem {L : GLock} {Λ : List (Res G104_referenz.gD)}
    (h : Res.held (D := gDB) L ∈ Λ.map rm) : Res.held (D := G104_referenz.gD) L ∈ Λ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  cases x with
  | held L' => cases e; exact hx
  | marke m s => exact m.elim

theorem rufPasst_rm {V : Vertrag G104_referenz.gD} {S : Signatur GTab Empty GLock Empty}
    {Λ : List (Res G104_referenz.gD)} (h : RufPasst G104_referenz.gD V S Λ) :
    RufPasst gDB (vm V) S (Λ.map rm) where
  hw := h.hw
  hg := h.hg
  hk := ⟨[], by rw [konsumiert_leer]; exact List.Perm.refl [], List.nil_sublist _⟩
  hh := fun L hL => List.mem_map_of_mem (f := rm) (h.hh L hL)
  hx := fun L hL hn => h.hx L (held_rm_mem hL) hn
  hb := h.hb

theorem params_some (f : GFn) : gDB.params (some f) = G104_referenz.gD.params f := by
  cases f <;> rfl

theorem signatur_some (f : GFn) : gDB.signatur (some f) = G104_referenz.gD.signatur f := by
  cases f <;> rfl

theorem nach_rm (f : GFn) (Λ : List (Res G104_referenz.gD)) :
    (nach G104_referenz.gD f Λ).map rm = nach gDB (some f) (Λ.map rm) := by
  cases f <;> simp [nach, nachSig, Deklaration.signatur, gSig_einzahlen, gSig_lies]

/-- Expressions. -/
def renE : {Γ : Ctx} → {Λ : List (Res G104_referenz.gD)} → {τ : Ty} →
    Expr G104_referenz.gD Γ Λ τ → Option (Expr gDB Γ (Λ.map rm) τ)
  | _, _, _, .lit n => some (.lit n)
  | _, _, _, .wahr => some .wahr
  | _, _, _, .falsch => some .falsch
  | _, _, _, .var x => some (.var x)
  | _, _, _, .slot t f i hL => (renE i).map fun i' => Expr.slot (D := gDB) t f i' (darf_rm hL)
  | _, _, _, .durch p t ht f i hL =>
    (renE p).bind fun p' => (renE i).map fun i' => Expr.durch (D := gDB) p' t ht f i' (darf_rm hL)
  | _, _, _, .ptrOf t n ht rw => some (Expr.ptrOf (D := gDB) t n ht rw)
  | _, _, _, .altSlot t f i hL => (renE i).map fun i' => Expr.altSlot (D := gDB) t f i' (darf_rm hL)
  | _, _, _, .weiter h1 h2 e => (renE e).map (.weiter h1 h2)
  | _, _, _, .add a b => (renE a).bind fun a' => (renE b).map (.add a')
  | _, _, _, .sub a b => (renE a).bind fun a' => (renE b).map (.sub a')
  | _, _, _, .lt a b => (renE a).bind fun a' => (renE b).map (.lt a')
  | _, _, _, .le a b => (renE a).bind fun a' => (renE b).map (.le a')
  | _, _, _, .eq a b => (renE a).bind fun a' => (renE b).map (.eq a')
  | _, _, _, .und a b => (renE a).bind fun a' => (renE b).map (.und a')
  | _, _, _, .oder a b => (renE a).bind fun a' => (renE b).map (.oder a')
  | _, _, _, .nicht a => (renE a).map .nicht
  | _, _, _, _ => none

/-- Argument lists. -/
def renArgs : {Γ : Ctx} → {Λ : List (Res G104_referenz.gD)} → {τs : List Ty} →
    Args G104_referenz.gD Γ Λ τs → Option (Args gDB Γ (Λ.map rm) τs)
  | _, _, _, .nil => some .nil
  | _, _, _, .cons e rest => (renE e).bind fun e' => (renArgs rest).map (.cons e')

/-- Return values. -/
def renErg {Γ : Ctx} {Λ : List (Res G104_referenz.gD)} : {e : Option Ty} →
    ErgExpr G104_referenz.gD Γ Λ e → Option (ErgExpr gDB Γ (Λ.map rm) e)
  | _, .keine => some .keine
  | _, .wert e => (renE e).map .wert

section Ren
variable {V : Vertrag G104_referenz.gD} {l : Bool}

/-- Statements: the table writes and the direct call (`f` to `some f`, the
    argument list, the transported `RufPasst`; the resource index moves along
    `nach_rm`). Every other statement: none. -/
def renS {Γ : Ctx} {Λ Λ' : List (Res G104_referenz.gD)} :
    Stmt G104_referenz.gD V l Γ Λ Λ' → Option (Stmt gDB (vm V) l Γ (Λ.map rm) (Λ'.map rm))
  | .assignSlot t f i e hw hL =>
    (renE i).bind fun i' => (renE e).map fun e' => Stmt.assignSlot (V := vm V) t f i' e' hw (darf_rm hL)
  | .assignDurch p t ht f i e hw hL =>
    (renE p).bind fun p' => (renE i).bind fun i' => (renE e).map fun e' =>
      Stmt.assignDurch (V := vm V) p' t ht f i' e' hw (darf_rm hL)
  | .call f args hp hr =>
    (renArgs args).map fun a =>
      (nach_rm f Λ) ▸ Stmt.call (V := vm V) (l := l) (some f) ((params_some f).symm ▸ a)
        ((signatur_some f).symm ▸ rufPasst_rm hp) (by cases f <;> exact hr)
  | _ => none

/-- Terminal blocks. -/
def renEnd {Γ : Ctx} : {Λ : List (Res G104_referenz.gD)} →
    Endblock G104_referenz.gD V l Γ Λ → Option (Endblock gDB (vm V) l Γ (Λ.map rm))
  | _, .ret e hΛ => (renErg e).map fun e' => .ret e' (perm_rm hΛ)
  | _, .retGrund r hΛ => some (.retGrund r (perm_rm hΛ))
  | _, .leave h => some (.leave h)
  | _, .next h => some (.next h)
  | _, .cons s rest => (renS s).bind fun s' => (renEnd rest).map (.cons s')
  | _, .bind e rest => (renE e).bind fun e' => (renEnd rest).map (.bind e')

end Ren

theorem ren_rumpf_einzahlen :
    renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) := rfl

theorem ren_rumpf_lies :
    renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) := rfl

theorem ren_ensures_einzahlen :
    renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) := rfl

theorem ren_ensures_lies :
    renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) := rfl

theorem ren_requires_einzahlen :
    renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) := rfl

theorem ren_requires_lies :
    renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) := rfl

/-- **`gPB`'s source part IS the parsed program `gP`, renamed**: every
    body, `ensures` and `requires` of `gPB` at `some f` is the renaming of
    `gP`'s at `f` (kernel-checked, `rfl`); `gPB` adds exactly the idle root
    `none`, which holds no lock, touches nothing and returns. -/
theorem gPB_ist_gP_umbenannt :
    renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) ∧
    renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) ∧
    renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) ∧
    renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) ∧
    renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) ∧
    renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) ∧
    ruhig gPB none = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩


/-! ### 5.4 The goal theorem for the machine of `gPB` -/

theorem gb_call_tor {V : Vertrag gDB} {l : Bool} {Γ : Ctx}
    {Λ : List (Res gDB)} (O : Orakel gDB) (passes : Nat)
    (R : ∀ f : gDB.Fn, World gDB → Env gDB (gDB.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : gDB.Fn) (args : Args gDB Γ Λ (gDB.params g))
    (hp : RufPasst gDB V (gDB.signatur g) Λ)
    (hr : gDB.gruende g = 0) (σ : World gDB) (ρ : Env gDB Γ) (g' : gDB.Fn) :
    execStmt O passes (torRuf gPB R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf gPB R g σ1 ρ1 = R g σ1 ρ1 :=
    fun _ _ => if_pos (by rcases g with _ | g; rfl; cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | grund σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

theorem gPB_koerper_lies : KoerperGutV gPB 0 (some GFn.lies) := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : gPB.rumpf (some GFn.lies) = gbBody_lies := rfl
    rw [hr] at hrun
    simp only [gbBody_lies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : gPB.rumpf (some GFn.lies) = gbBody_lies := rfl
    rw [hr] at hrun
    simp only [gbBody_lies, execEnd] at hrun
    cases hrun

theorem gPB_koerper_ruhe : KoerperGutV gPB 0 none := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : gPB.rumpf none = gbBody_ruhe := rfl
  rw [hr] at hrun
  simp only [gbBody_ruhe, execEnd] at hrun
  cases hrun

theorem gPB_einzahlen_R : KoerperGutR gPB 0 (some GFn.einzahlen) := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : gPB.rumpf (some GFn.einzahlen) = gbBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 (some GFn.lies) _ _ σ2 w hRv).1.1 GTab.Konto rfl
      simp only [execStmt] at h1
      cases h1
      show decide ((σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.dort .hier)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := gDB) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : gPB.rumpf (some GFn.einzahlen) = gbBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact gb_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem gPB_koerperS : ∀ f : gDB.Fn,
    KoerperGutS gPB 0 (axWahr gDB) (SperrInv.leer gDB) f :=
  fun f => koerperGutS_leer ⟨koerperGutRQ_of_R _ (match f with
    | some .einzahlen => gPB_einzahlen_R
    | some .lies => koerperGutR_of_V gPB_koerper_lies
    | none => koerperGutR_of_V gPB_koerper_ruhe),
    programmLogikFrei_ok gbFs_voll gPB_logikFrei 0 _ f⟩

/-- The oracle of `gDB`: no axiom, register or global exists. -/
def gOB : Orakel gDB where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem gOB_gut : GutO gOB := fun a => nomatch a

theorem gOB_lokal : RegLokal gOB := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- **The runtime's start**: thread 0 runs the source function `f` on the
    arguments `ρ` (whatever the driver calls), every other thread idles. -/
def bootInit (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    Faden → Σ g : gDB.Fn, Env gDB (gDB.params g) :=
  fun t => if t = 0 then ⟨some f, ρ⟩ else ⟨none, .nil⟩

theorem bootInit_ruhig (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    ∀ u, u ≠ 0 → ruhig gPB (bootInit f ρ u).1 = true := by
  intro u hu
  unfold bootInit
  rw [if_neg hu]
  exact gPB_ruhig

theorem bootInit_start (sp : Speicher gDB) (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    StartGut gPB sp (bootInit f ρ) := by
  intro t
  unfold bootInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]; rfl

theorem gPB_ohneEwig : ohneEwigB gPB gbFs = true := by decide

theorem gPB_koerperS_alle : ∀ (passes : Nat) (f : gDB.Fn),
    KoerperGutS gPB passes (axWahr gDB) (SperrInv.leer gDB) f :=
  koerperGutS_alle gbFs_voll gPB_ohneEwig gPB_koerperS

theorem gPB_rufAt_passes : ∀ (passes k : Nat) (f : gDB.Fn) (σ : World gDB)
    (ρ : Env gDB (gDB.params f)), rufAt gPB gOB passes k f σ ρ = rufAt gPB gOB 0 k f σ ρ :=
  fun passes => rufAt_passes gOB (ohneEwigB_ok gbFs_voll gPB_ohneEwig) passes 0

/-- No function of `gDB` declares a reason. -/
theorem gDB_ohneGrund (g : gDB.Fn) : gDB.gruende g = 0 := by
  rcases g with _ | f
  · rfl
  · cases f <;> rfl

/-- **A4 AS A LEAN PROPOSITION: the runtime's start.** Every thread but `0`
    idles in the runtime's root `none`; thread `0` runs whatever the driver
    calls (a source function on its arguments -- or nothing). -/
def LaufzeitStart (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) : Prop :=
  ∀ u, u ≠ 0 → init u = ⟨none, .nil⟩

theorem bootInit_laufzeit (f : GFn) (ρ : Env gDB (gDB.params (some f))) :
    LaufzeitStart (bootInit f ρ) := by
  intro u hu
  unfold bootInit
  rw [if_neg hu]

/-- **THE GOAL THEOREM ON THE MACHINE OF `gPB`** -- for EVERY start that
    has the runtime's shape (A4, `LaufzeitStart`), from EVERY start memory,
    at EVERY `forever` budget: on every reachable machine the contracts
    hold at every logged event, the (empty) lock invariants hold, no thread
    is stuck at a `logik` check, the progress conjunct holds, every owed
    invariant holds at every logged return, and -- new -- at a finished
    thread `0` the root function's `ensures` holds (`StartEndeG`), and it
    finished at a value return (`KeinStartGrundG`). `ziel_ort_einfaden_ende`. -/
theorem gPB_ziel (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) (hA4 : LaufzeitStart init) :
    ∀ (sp : Speicher gDB) (passes : Nat) (M : RufMaschineG gDB),
      RufErreichbarG gPB gOB passes (RufStartG gPB sp init) M →
      ((VertragAmOrtG gPB M ∧ SperrInvG (SperrInv.leer gDB) M ∧ KeinLogikHaltG gOB passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG gPB gOB passes M t M') ∧
      InvAmOrtG gPB M) ∧ StartEndeG gPB M ∧ KeinStartGrundG M :=
  fun sp => ziel_ort_einfaden_ende gPB gOB (axWahr gDB) (SperrInv.leer gDB) gbFs sp init
    gOB_gut gOB_lokal (axVertragO_wahr gOB) axEnsLokal_wahr sperrInvOk_leer gbFs_voll gPB_fragment
    (fun u hu => by rw [hA4 u hu]; exact gPB_ruhig) gPB_koerperS_alle (fun _ => rfl) (fun _ => rfl)
    (fun _ => invGutS_leer rfl) (fun _ => gDB_ohneGrund _)


/-! ### 5.5 `gPB` behaves as `gP`: both against the same emitted C

The renaming of 5.3 is syntactic. Its semantic content, for the two source
functions: the C correspondence of `gPB`'s bodies against the SAME emitted
unit (a copy of section 2 over `gDB`), and then, from worlds related to one
C state, both Gabbro calls end `ok` and agree -- every C run relates to both
(`gPB_wie_gP_einzahlen`, `gPB_wie_gP_lies`). -/

def kEinB : CEnvLay gDB (gDB.params (some GFn.einzahlen)) := ⟨[0, 1, 2], [], []⟩

def kLiesB : CEnvLay gDB (gDB.params (some GFn.lies)) := ⟨[0, 1], [], []⟩

/-- The emitter's layout over `gDB` -- the same layout as `gEL104`
    (the carriers are `gD`'s). -/
def gEBL : EmitLay gDB where
  lay := refLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => kontoLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun t => by cases t; rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun t f f' _ => by cases t; cases f; cases f'; rfl
  fnr_fits := fun t f => by cases t; cases f; rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- `lies` runs in frame 1, calling nothing. -/
def xLiesB : TVCtx gDB :=
  ⟨gEBL, tvOrc, 1, CallAt gEBL.lay tvOrc tvXR refCProg 0, tvXR, gOB, 0, rufAt gPB gOB 0 0⟩

/-- `einzahlen` runs in frame 2, its callees at depth 1. -/
def xEinB : TVCtx gDB :=
  ⟨gEBL, tvOrc, 2, CallAt gEBL.lay tvOrc tvXR refCProg 1, tvXR, gOB, 0, rufAt gPB gOB 0 1⟩

/-! #### 5.5.1 `lies` of `gPB` against the emitted `lies` -/

/-- `return k->slots[i].stand;` corresponds to `gPB`'s `lies` body:
    `k` is C local 0 (Gabbro variable 0), `i` C local 1 (variable 1). -/
theorem liesB_end (m : Nat) : EndCorr xLiesB m true kLiesB (gPB.rumpf (some GFn.lies)) cLiesBody := by
  have hi : ExprCorr xLiesB kLiesB (.var 1)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.lies))) (Λ := gbL) (.dort .hier)) :=
    ecorr_var xLiesB kLiesB (.dort .hier)
  have hp : PtrTo xLiesB kLiesB (.var 0) GTab.Konto :=
    ptrTo_var xLiesB kLiesB (Γ := (gDB.params (some GFn.lies))) (.hier) rfl
  have he := ecorr_durch xLiesB kLiesB (Λ := gbL) (rw := false) (p := Expr.var .hier)
    rfl hp GKontoFeld.stand rfl gbDarf hi
  exact EndCorr.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- THE CALLEE RELATION of `lies` at depth 1. -/
theorem liesB_fn : FnCorr gEBL (rufAt gPB gOB 0 1) (CallAt gEBL.lay tvOrc tvXR refCProg 1)
    (some GFn.lies) 1 cLies.params kLiesB :=
  cCorr_ruf gEBL tvOrc tvXR gPB gOB 0 0 refCProg (some GFn.lies) 1 cLies rfl kLiesB 0
    (cCorr_end xLiesB 0 true (liesB_end 0))

/-! #### 5.5.2 `einzahlen` of `gPB` against the emitted `einzahlen` -/

/-- `(void)b;` evaluates Gabbro's `b` (variable 2, C local 2). -/
theorem einB_void :
    ExprCorr xEinB kEinB (.var 2)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (.dort (.dort .hier))) :=
  ecorr_var xEinB kEinB (.dort (.dort .hier))

/-- `k->slots[i].stand = 100;` against `k.slots[i].stand = 100` through the
    `rw` pointer `k`. -/
theorem einB_write (m : Nat) :
    StmtCorr xEinB m kEinB
      (Stmt.assignDurch (V := vertragVon gDB (some GFn.einzahlen)) (l := false) (Γ := (gDB.params (some GFn.einzahlen)))
        (Λ := gbL) (.var .hier) GTab.Konto rfl GKontoFeld.stand (.var (.dort .hier))
        (.weiter (by decide) (by decide) (.lit 100)) (by decide) gbDarf)
      (.store cStand cU32 (.lit 100)) := by
  have hi : ExprCorr xEinB kEinB (.var 1)
      (Expr.var (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (.dort .hier)) :=
    ecorr_var xEinB kEinB (.dort .hier)
  have he : ExprCorr xEinB kEinB (.lit 100)
      (Expr.weiter (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) (lo' := 0) (hi' := 100)
        (by decide) (by decide) (.lit 100)) :=
    ecorr_weiter xEinB kEinB _ _ (ecorr_lit xEinB kEinB 100)
  have hp : PtrTo xEinB kEinB (.var 0) GTab.Konto :=
    ptrTo_var xEinB kEinB (Γ := (gDB.params (some GFn.einzahlen))) (.hier) rfl
  exact scorr_assignDurch xEinB kEinB m rfl hp GKontoFeld.stand rfl _ _ hi he

/-- The arguments of `lies(k, i);`: C passes `k` (local 0) and `i`
    (local 1); Gabbro passes a read-only pointer to the same table and `i`.
    A pointer's C value is the table's address either way. -/
theorem einB_args : ArgsTo xEinB kEinB
    (Args.cons (Expr.ptrOf (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) GTab.Konto 0 rfl false)
      (Args.cons (Expr.var (.dort .hier)) .nil))
    [.var 0, .var 1] cLies.params kLiesB := by
  intro σ st ρG ρC _ hr
  have h0 := hr.1 _ (Var.hier (Γ := [.index 2, .int 0 10]) (τ := .ptr 0 true))
  have h1 := hr.1 _ (Var.dort (σ := .ptr 0 true) (Var.hier (Γ := [.int 0 10]) (τ := .index 2)))
  obtain ⟨t0, ht0, e0⟩ := h0
  have et : t0 = GTab.Konto := by cases t0; rfl
  subst et
  have e0' : ρC 0 = .ptr ⟨.tab 0, 0⟩ := e0
  have e1' : ρC 1 = .int (encW (.index 2) (ρG.get (.dort .hier))) := h1
  have hc1 : convV cU32 (ρC 1) = some (ρC 1) := by
    rw [e1']
    exact convV_of_valCorr (EL := gEBL) (τ := .index 2) (v := ρG.get (.dort .hier)) rfl rfl
  refine ⟨[ρC 0, ρC 1], st, lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0), ?_,
    SameML.refl st, ?_, ?_⟩
  · simp only [evArgs, ev, e0', e1']
  · show (match convV .ptr (ρC 0), bindParams [(1, cU32)] [ρC 1] with
      | some v', some ρ => some (lokUpd ρ 0 v')
      | _, _ => none) = _
    have hb1 : bindParams [(1, cU32)] [ρC 1] = some (lokUpd (fun _ => .undef) 1 (ρC 1)) := by
      show (match convV cU32 (ρC 1), bindParams [] [] with
        | some v', some ρ => some (lokUpd ρ 1 v')
        | _, _ => none) = _
      rw [hc1]
      rfl
    rw [hb1, e0']
    rfl
  · refine ⟨?_, fun q hq => absurd hq (by simp [kLiesB]),
      fun q hq => absurd hq (by simp [kLiesB])⟩
    intro τ x
    cases x with
    | hier =>
        refine ⟨GTab.Konto, rfl, ?_⟩
        show lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 0 = _
        simp only [lokUpd, if_pos]
        exact e0'
    | dort y =>
        cases y with
        | hier =>
            show ValCorr gEBL (.index 2) _ (lokUpd (lokUpd (fun _ => .undef) 1 (ρC 1)) 0 (ρC 0) 1)
            simp only [lokUpd]
            rw [e1']
            rfl
        | dort z => exact nomatch z

/-- `lies(k, i);` against `gPB`'s call of `lies`. -/
theorem einB_call (m : Nat) :
    StmtCorr xEinB m kEinB
      (Stmt.call (V := vertragVon gDB (some GFn.einzahlen)) (l := false) (Γ := (gDB.params (some GFn.einzahlen))) (some GFn.lies)
        (Args.cons (Expr.ptrOf (D := gDB) (Γ := (gDB.params (some GFn.einzahlen))) (Λ := gbL) GTab.Konto 0 rfl false)
          (Args.cons (Expr.var (.dort .hier)) .nil))
        gbHp rfl)
      (.call 1 [.var 0, .var 1] none) :=
  scorr_call xEinB kEinB m (some GFn.lies) _ gbHp rfl liesB_fn einB_args

/-- THE BODY of `einzahlen` against the emitted body. -/
theorem einB_end (m : Nat) : EndCorr xEinB m true kEinB (gPB.rumpf (some GFn.einzahlen)) cEinBody :=
  EndCorr.pre einB_void
    (EndCorr.cons (einB_write m) (EndCorr.cons (einB_call m) (EndCorr.retEnd (by rfl) rfl rfl)))

/-- THE CALLEE RELATION of `einzahlen` at depth 2. -/
theorem einB_fn : FnCorr gEBL (rufAt gPB gOB 0 2) (CallAt gEBL.lay tvOrc tvXR refCProg 2)
    (some GFn.einzahlen) 0 cEin.params kEinB :=
  cCorr_ruf gEBL tvOrc tvXR gPB gOB 0 1 refCProg (some GFn.einzahlen) 0 cEin rfl kEinB 0
    (cCorr_end xEinB 0 true (einB_end 0))

/-- `lies` on `gPB`, from ANY world and arguments, at any depth: the call
    ends `ok` (requires, ensures and invariants all checked by `rufAt`),
    and the answer world has the caller's slots. -/
theorem rufLiesB_ok (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ∃ σ' v, rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok σ' v ∧ σ'.slots = σ.slots := by
  have h := rufAt_ok_of_gates gPB gOB 0 n (some GFn.lies) σ ρ _ rfl rfl _ _ rfl _ rfl
    (by show wahr? (decide (_ = _)) = true; exact decide_eq_true rfl) _ rfl rfl
  exact ⟨_, _, h, rfl⟩

/-- The answer world of `lies` (chosen; its slots are the caller's). -/
noncomputable def liesWB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) : World gDB :=
  Classical.choose (rufLiesB_ok n σ ρ)

theorem liesWB_spec (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ∃ v, rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok (liesWB n σ ρ) v ∧
      (liesWB n σ ρ).slots = σ.slots :=
  Classical.choose_spec (rufLiesB_ok n σ ρ)

/-- The answer value of `lies` (chosen). -/
noncomputable def liesVB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    ErgVal gDB (gDB.erg (some GFn.lies)) :=
  Classical.choose (liesWB_spec n σ ρ)

theorem liesAtB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    rufAt gPB gOB 0 (n + 1) (some GFn.lies) σ ρ = .ok (liesWB n σ ρ) (liesVB n σ ρ) :=
  (Classical.choose_spec (liesWB_spec n σ ρ)).1

theorem liesWB_slots (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.lies))) :
    (liesWB n σ ρ).slots = σ.slots :=
  (Classical.choose_spec (liesWB_spec n σ ρ)).2

/-- `einzahlen`'s body under `rufAt` handlers: it returns, with the slot
    `k.slots[i].stand` at `100`. -/
theorem einBodyB (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.einzahlen))) :
    ∃ σ1, execEnd (V := vertragVon gDB (some GFn.einzahlen)) gOB 0
      (rufAt gPB gOB 0 (n + 1)) (gPB.rumpf (some GFn.einzahlen)) σ ρ =
      .zurueck σ1 () ∧ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n = 100 := by
  show ∃ σ1, execEnd _ _ _ gbBody_einzahlen σ ρ = _ ∧ _
  simp only [gbBody_einzahlen, execEnd, execStmt, liesAtB]
  refine ⟨_, rfl, ?_⟩
  show ((liesWB n _ _).slots GTab.Konto _ GKontoFeld.stand).n = 100
  rw [liesWB_slots]
  exact (congrArg (fun z : Zahl 0 100 => z.n)
    (storeSlot_hit (D := gDB) _ GTab.Konto _ GKontoFeld.stand _)).trans rfl

/-- `einzahlen` on `gPB`, from ANY world and arguments, at depth `n + 2`:
    the call ends `ok` -- its `ensures old(stand) <= stand` and `lies`'s
    `ensures result == stand` both checked by `rufAt` on the way. -/
theorem rufEinB_ok (n : Nat) (σ : World gDB)
    (ρ : Env gDB (gDB.params (some GFn.einzahlen))) :
    ∃ σ', rufAt gPB gOB 0 (n + 2) (some GFn.einzahlen) σ ρ = .ok σ' () := by
  obtain ⟨σ1, hb, h100⟩ := einBodyB n
    (σ.lese (Signatur.anfang gDB (gDB.signatur (some GFn.einzahlen)))
      (gPB.requires (some GFn.einzahlen)).orte) ρ
  refine ⟨_, rufAt_ok_of_gates gPB gOB 0 (n + 1) (some GFn.einzahlen) σ ρ _ rfl rfl _ ()
    hb _ rfl ?_ _ rfl rfl⟩
  show wahr? (decide (_ ≤ _)) = true
  apply decide_eq_true
  show _ ≤ (σ1.slots GTab.Konto (ρ.get (.dort .hier)).n GKontoFeld.stand).n
  rw [h100]
  exact (Zahl.le_hi _)

/-- A cell of `Konto` under both layouts: the same C cell holds the
    encoded slot of both related worlds, so the slots agree. -/
theorem slots_gleich {σ : World G104_referenz.gD} {σB : World gDB} {st : CSt}
    (h : corrW gEL104 σ st) (hB : corrW gEBL σB st) (k : Int) (h0 : 0 ≤ k) (h1 : k < 2) :
    (σ.slots GTab.Konto k GKontoFeld.stand).n = (σB.slots GTab.Konto k GKontoFeld.stand).n := by
  have e := (h.1 GTab.Konto rfl).2 k GKontoFeld.stand h0 h1
  have eB := (hB.1 GTab.Konto rfl).2 k GKontoFeld.stand h0 h1
  have := e.symm.trans eB
  injection this

/-- **`gPB`'s `einzahlen` behaves as `gP`'s**: from worlds related to the
    same C state and arguments related to the same C locals, both Gabbro
    calls end `ok`, and their memories agree slot by slot -- through the
    emitted C, whose every run relates to both (`callAt_funktional`). -/
theorem gPB_wie_gP_einzahlen (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
    (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
    (ρB : Env gDB (gDB.params (some GFn.einzahlen))) (vs : List CVal) (ρ0 : CLok)
    (hw : corrW gEL104 σ st) (hwB : corrW gEBL σB st) (hb : bindParams cEin.params vs = some ρ0)
    (hr : EnvRel gEL104 kEinG ρG ρ0) (hrB : EnvRel gEBL kEinB ρB ρ0) :
    ∃ σ' σB', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
      rufAt gPB gOB 0 2 (some GFn.einzahlen) σB ρB = .ok σB' () ∧
      ∀ k : Int, 0 ≤ k → k < 2 →
        (σ'.slots GTab.Konto k GKontoFeld.stand).n = (σB'.slots GTab.Konto k GKontoFeld.stand).n := by
  obtain ⟨σ', hR⟩ := rufEin_ok 0 σ ρG
  obtain ⟨σB', hRB⟩ := rufEinB_ok 0 σB ρB
  obtain ⟨st1, rv1, hC1, hO1⟩ := einG_fn σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  obtain ⟨st2, rv2, hC2, hO2⟩ := einB_fn σB st ρB vs ρ0 hwB hb hrB (by rw [hRB]; rfl)
  rw [hR] at hO1
  rw [hRB] at hO2
  obtain ⟨e1, -⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional refCProg 2
    0 st vs st1 rv1 st2 rv2 hC1 hC2
  subst e1
  exact ⟨σ', σB', hR, hRB, fun k h0 h1 => slots_gleich hO1.1 hO2.1 k h0 h1⟩

/-- **`gPB`'s `lies` behaves as `gP`'s**: both calls end `ok` with the SAME
    answer and slot-equal memories. -/
theorem gPB_wie_gP_lies (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
    (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
    (ρB : Env gDB (gDB.params (some GFn.lies))) (vs : List CVal) (ρ0 : CLok)
    (hw : corrW gEL104 σ st) (hwB : corrW gEBL σB st) (hb : bindParams cLies.params vs = some ρ0)
    (hr : EnvRel gEL104 kLiesG ρG ρ0) (hrB : EnvRel gEBL kLiesB ρB ρ0) :
    ∃ σ' v σB' vB, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
      rufAt gPB gOB 0 1 (some GFn.lies) σB ρB = .ok σB' vB ∧
      (show Zahl 0 100 from v).n = (show Zahl 0 100 from vB).n ∧
      ∀ k : Int, 0 ≤ k → k < 2 →
        (σ'.slots GTab.Konto k GKontoFeld.stand).n = (σB'.slots GTab.Konto k GKontoFeld.stand).n := by
  obtain ⟨σ', v, hR, -⟩ := rufLies_ok 0 σ ρG
  obtain ⟨σB', vB, hRB, -⟩ := rufLiesB_ok 0 σB ρB
  obtain ⟨st1, rv1, hC1, hO1⟩ := liesG_fn σ st ρG vs ρ0 hw hb hr (by rw [hR]; rfl)
  obtain ⟨st2, rv2, hC2, hO2⟩ := liesB_fn σB st ρB vs ρ0 hwB hb hrB (by rw [hRB]; rfl)
  rw [hR] at hO1
  rw [hRB] at hO2
  obtain ⟨e1, e2⟩ := callAt_funktional gEL104.lay tvOrc tvXR tvXR_funktional refCProg 1
    1 st vs st1 rv1 st2 rv2 hC1 hC2
  subst e1
  subst e2
  obtain ⟨c1, hc1, hv1⟩ := hO1.2
  obtain ⟨c2, hc2, hv2⟩ := hO2.2
  rw [hc1] at hc2
  cases hc2
  have := hv1.symm.trans hv2
  injection this with hvv
  exact ⟨σ', v, σB', vB, hR, hRB, hvv, fun k h0 h1 => slots_gleich hO1.1 hO2.1 k h0 h1⟩

/-! ## 6. THE CLOSING THEOREM, stage (a) -/

/-- **`schlusssatz_104` -- the closing theorem, stage (a), for
    `beispiele/104-referenz.gab`.** About ONE program, the `gP` the Lean
    parser produces. PREMISES: the correspondence certificate checks
    (`certOkG c = true`, by `decide` on the printed one), and the named
    assumptions that ARE Lean propositions (CUTS names the rest):

    * `hA1ein`/`hA1lies` -- A1 with A2 and A3, as a hypothesis: every run of
      the compiled `einzahlen`/`lies` (`binEin`/`binLies`, the behaviour of
      the binary, a parameter) is a run of the C semantics of the emitted
      unit `refCProg` at the emitter's layout `gEL104.lay`, at the depth the
      call tree needs;
    * `hA4` -- A4: the runtime's start (`LaufzeitStart init`: every thread
      but `0` idles in the runtime's root).

    CONCLUSIONS:
    1. PARSE FIDELITY: the source text translates to `(gP, gFs)`;
    2. MODEL CERTIFICATES: the printed statement certificates ARE the print
       of `gP`'s two bodies, and the Lean checker accepts them;
    3. MODEL JUDGEMENT: `gP` passes the fragment and footprint checks, every
       function meets the per-function obligations at EVERY `forever`
       budget, and its call semantics does not depend on the budget;
    4. EVERY C RUN: the certificate elaborates to the emitted C unit; for
       each function, from a C state related to ANY Gabbro world and C
       arguments related to ANY Gabbro arguments, the Gabbro call ends `ok`
       (every contract on the way checked), the C call has a run, and EVERY
       run of it ends related to the Gabbro result;
    5. THE MACHINE: the program the machine runs, `gPB`, is `gP` renamed
       plus the runtime's idle root, and on every reachable machine -- from
       every start memory, at every budget, from the start `init` -- the
       conclusion of the goal theorem holds, including the root function's
       `ensures` at its completion (`StartEndeG`, `KeinStartGrundG`);
    6. EVERY RUN OF THE BINARY (under `hA1ein`/`hA1lies`): from related
       starts it ends related to the Gabbro result, which is the same at
       every budget. -/
theorem schlusssatz_104 (c : Cert104) (hc : certOkG c = true)
    (binEin : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1ein : ∀ st vs st' rv, binEin st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv)
    (binLies : CSt → List CVal → CSt → Option CVal → Prop)
    (hA1lies : ∀ st vs st' rv, binLies st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv)
    (init : Faden → Σ g : gDB.Fn, Env gDB (gDB.params g)) (hA4 : LaufzeitStart init) :
    -- 1. parse fidelity
    uebersetze104 src104 = .ok (G104_referenz.gP, G104_referenz.gFs) ∧
    -- 2. model certificates
    (printEnd104 (G104_referenz.gP.rumpf g_einzahlen) = some cert104_einzahlen ∧
      certEnd104Ok G104_referenz.gD (vertragVon G104_referenz.gD g_einzahlen) false
        gCtx_einzahlen gL_einzahlen cert104_einzahlen = true ∧
      printEnd104 (G104_referenz.gP.rumpf g_lies) = some cert104_lies ∧
      certEnd104Ok G104_referenz.gD (vertragVon G104_referenz.gD g_lies) false
        gCtx_lies gL_lies cert104_lies = true) ∧
    -- 3. model judgement, at every budget
    (programmImFragmentG G104_referenz.gP G104_referenz.gFs = true ∧
      fussOrtGB G104_referenz.gP G104_referenz.gFs = true ∧
      (∀ (passes : Nat) (f : G104_referenz.gD.Fn), KoerperGutS G104_referenz.gP passes
        (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f) ∧
      (∀ (passes : Nat) (f : G104_referenz.gD.Fn), InvGutS G104_referenz.gP passes
        (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f) ∧
      (∀ (passes k : Nat) (f : G104_referenz.gD.Fn) (σ : World G104_referenz.gD)
        (ρ : Env G104_referenz.gD (G104_referenz.gD.params f)),
        rufAt G104_referenz.gP gO104 passes k f σ ρ = rufAt G104_referenz.gP gO104 0 k f σ ρ)) ∧
    -- 4. every C run
    (progOf c = refCProg ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0 →
        ∃ σ', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
          (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' none) ∧
          ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 2 0 st vs st' rv →
            corrW gEL104 σ' st' ∧ rv = none) ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0 →
        ∃ σ' v, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
          (∃ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv) ∧
          ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf c) 1 1 st vs st' rv →
            corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv)) ∧
    -- 5. the machine
    ((renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) ∧
      renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) ∧
      renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) ∧
      renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) ∧
      renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) ∧
      renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) ∧
      ruhig gPB none = true) ∧
      -- `gPB`'s source functions behave as `gP`'s, through the same emitted C
      (∀ (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen))
        (ρB : Env gDB (gDB.params (some GFn.einzahlen))) (vs : List CVal) (ρ0 : CLok),
        corrW gEL104 σ st → corrW gEBL σB st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 kEinG ρG ρ0 → EnvRel gEBL kEinB ρB ρ0 →
        ∃ σ' σB', rufAt G104_referenz.gP gO104 0 2 g_einzahlen σ ρG = .ok σ' () ∧
          rufAt gPB gOB 0 2 (some GFn.einzahlen) σB ρB = .ok σB' () ∧
          ∀ k : Int, 0 ≤ k → k < 2 → (σ'.slots GTab.Konto k GKontoFeld.stand).n =
            (σB'.slots GTab.Konto k GKontoFeld.stand).n) ∧
      (∀ (σ : World G104_referenz.gD) (σB : World gDB) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies))
        (ρB : Env gDB (gDB.params (some GFn.lies))) (vs : List CVal) (ρ0 : CLok),
        corrW gEL104 σ st → corrW gEBL σB st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 kLiesG ρG ρ0 → EnvRel gEBL kLiesB ρB ρ0 →
        ∃ σ' v σB' vB, rufAt G104_referenz.gP gO104 0 1 g_lies σ ρG = .ok σ' v ∧
          rufAt gPB gOB 0 1 (some GFn.lies) σB ρB = .ok σB' vB ∧
          (show Zahl 0 100 from v).n = (show Zahl 0 100 from vB).n ∧
          ∀ k : Int, 0 ≤ k → k < 2 → (σ'.slots GTab.Konto k GKontoFeld.stand).n =
            (σB'.slots GTab.Konto k GKontoFeld.stand).n) ∧
      (∀ (passes k : Nat) (f : gDB.Fn) (σ : World gDB) (ρ : Env gDB (gDB.params f)),
        rufAt gPB gOB passes k f σ ρ = rufAt gPB gOB 0 k f σ ρ) ∧
      ∀ (sp : Speicher gDB) (passes : Nat) (M : RufMaschineG gDB),
        RufErreichbarG gPB gOB passes (RufStartG gPB sp init) M →
          ((VertragAmOrtG gPB M ∧ SperrInvG (SperrInv.leer gDB) M ∧ KeinLogikHaltG gOB passes M ∧
            ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
              AnPruefungG M t → ∃ M', RufSchrittG gPB gOB passes M t M') ∧
          InvAmOrtG gPB M) ∧ StartEndeG gPB M ∧ KeinStartGrundG M) ∧
    -- 6. every run of the binary
    ((∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cEin.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmEin c.ppEin c.ksEin) ρG ρ0 →
        ∃ σ', (∀ passes : Nat, rufAt G104_referenz.gP gO104 passes 2 g_einzahlen σ ρG = .ok σ' ()) ∧
          ∀ st' rv, binEin st vs st' rv → corrW gEL104 σ' st' ∧ rv = none) ∧
      (∀ (σ : World G104_referenz.gD) (st : CSt)
        (ρG : Env G104_referenz.gD (G104_referenz.gD.params g_lies)) (vs : List CVal)
        (ρ0 : CLok), corrW gEL104 σ st → bindParams cLies.params vs = some ρ0 →
        EnvRel gEL104 (kOfG c.vmLies c.ppLies c.ksLies) ρG ρ0 →
        ∃ σ' v, (∀ passes : Nat, rufAt G104_referenz.gP gO104 passes 1 g_lies σ ρG = .ok σ' v) ∧
          ∀ st' rv, binLies st vs st' rv →
            corrW gEL104 σ' st' ∧ RetCorr gEL104 (G104_referenz.gD.erg g_lies) v rv)) := by
  refine ⟨uebersetze104_ok,
    ⟨print104_einzahlen, cert104_einzahlen_ok, print104_lies, cert104_lies_ok⟩,
    ⟨export104_fragment, export104_fuss, gP_koerperS_alle, gP_invGutS_alle, gP_rufAt_passes⟩,
    ⟨progOf_ok c hc, fun σ st ρG vs ρ0 hw hb hr => c104_einzahlen c hc σ st ρG vs ρ0 hw hb hr,
      fun σ st ρG vs ρ0 hw hb hr => c104_lies c hc σ st ρG vs ρ0 hw hb hr⟩,
    ⟨gPB_ist_gP_umbenannt, gPB_wie_gP_einzahlen, gPB_wie_gP_lies, gPB_rufAt_passes,
      gPB_ziel init hA4⟩, ?_, ?_⟩
  · intro σ st ρG vs ρ0 hw hb hr
    obtain ⟨σ', hR, _, hall⟩ := c104_einzahlen c hc σ st ρG vs ρ0 hw hb hr
    refine ⟨σ', fun passes => (gP_rufAt_passes passes 2 _ σ ρG).trans hR, fun st' rv hbin => ?_⟩
    exact hall st' rv (by rw [progOf_ok c hc]; exact hA1ein _ _ _ _ hbin)
  · intro σ st ρG vs ρ0 hw hb hr
    obtain ⟨σ', v, hR, _, hall⟩ := c104_lies c hc σ st ρG vs ρ0 hw hb hr
    refine ⟨σ', v, fun passes => (gP_rufAt_passes passes 1 _ σ ρG).trans hR, fun st' rv hbin => ?_⟩
    exact hall st' rv (by rw [progOf_ok c hc]; exact hA1lies _ _ _ _ hbin)

/-- The premise holds for the certificate as printed (rows and layout from
    `printed104`, `certG104_rows`), by `decide`; it elaborates to the emitted
    unit. `schlusssatz_104 certG104 certG104_ok` is the closed chain. -/
theorem schlusssatz_104_praemisse :
    certOkG certG104 = true ∧ certG104.einRows = printed104.einRows ∧
      certG104.liesRows = printed104.liesRows ∧ certG104.lay = printed104.lay ∧
      progOf certG104 = refCProg :=
  ⟨certG104_ok, certG104_rows.1, certG104_rows.2.1, certG104_rows.2.2, progOf_ok _ certG104_ok⟩


/-! ### 6.1 Witnesses (rule 13): the premises are jointly satisfiable, on runs that move memory -/

/-- The zero world of `gD`: both slots `0`, empty trace. -/
def gWelt0 : World G104_referenz.gD :=
  ⟨fun t _ f => (match t, f with | .Konto, .stand => ⟨0, by decide, by decide⟩),
    (fun g => nomatch g), []⟩

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def gRho7 : Env G104_referenz.gD (G104_referenz.gD.params g_einzahlen) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

theorem gW0_corr : corrW gEL104 gWelt0 refSt0 := by
  refine ⟨?_, fun g => nomatch g⟩
  intro t _
  cases t
  refine ⟨rfl, ?_⟩
  intro k f hk0 hk
  cases f
  have hk2 : k < 2 := hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with e | e <;> subst e <;> rfl

theorem gRho7_env : EnvRel gEL104 (kOfG certG104.vmEin certG104.ppEin certG104.ksEin) gRho7
    (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩)) := by
  refine ⟨?_, fun q hq => absurd hq (by simp [certG104, kOfG]),
    fun q hq => absurd hq (by simp [certG104, kOfG])⟩
  intro τ x
  cases x with
  | hier => exact ⟨GTab.Konto, rfl, rfl⟩
  | dort y =>
      cases y with
      | hier => rfl
      | dort z =>
          cases z with
          | hier => rfl
          | dort w => exact nomatch w

/-- **WITNESS, part 4**: `einzahlen(k, 0, 7)` from the zero state -- the
    premises of part 4 hold jointly; by the theorem the Gabbro call ends
    `ok` and EVERY C run ends related to it; the slot moved `0 -> 100` in
    the Gabbro world and in the C cell. -/
theorem schlusssatz_104_zeuge :
    ∃ σ' : World G104_referenz.gD,
      rufAt G104_referenz.gP gO104 0 2 g_einzahlen gWelt0 gRho7 = .ok σ' () ∧
      (gWelt0.slots GTab.Konto 0 GKontoFeld.stand).n = 0 ∧
      (σ'.slots GTab.Konto 0 GKontoFeld.stand).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧
      (∃ st', CallAt gEL104.lay tvOrc tvXR (progOf certG104) 2 0 refSt0 einArgs st' none) ∧
      ∀ st' rv, CallAt gEL104.lay tvOrc tvXR (progOf certG104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 ∧ rv = none := by
  obtain ⟨σ', hR, hex, hall⟩ := (schlusssatz_104 certG104 certG104_ok _ (fun _ _ _ _ h => h) _ (fun _ _ _ _ h => h)
    (fun _ => ⟨none, .nil⟩) (fun _ _ => rfl)).2.2.2.1.2.1 gWelt0 refSt0 gRho7
    einArgs _ gW0_corr rfl gRho7_env
  have hR' : rufAt G104_referenz.gP gO104 0 2 g_einzahlen gWelt0 gRho7 = .ok _ () := rfl
  rw [hR'] at hR
  cases hR
  refine ⟨_, hR', rfl, rfl, rfl, hex, fun st' rv hC => ?_⟩
  obtain ⟨hc, hrv⟩ := hall st' rv hC
  exact ⟨(hc.1 GTab.Konto rfl).2 0 GKontoFeld.stand (by decide) (by decide), hrv⟩


/-! ### 6.2 A reached machine of `gPB` -/

/-- The zero start memory of `gDB`. -/
def gbSp0 : Speicher gDB :=
  ⟨fun t _ f => (match t, f with | .Konto, .stand => ⟨0, by decide, by decide⟩), (fun g => nomatch g)⟩

/-- `einzahlen(k, 0, 7)` on the machine. -/
def gbRho7 : Env gDB (gDB.params (some GFn.einzahlen)) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

theorem gbHoff {M : RufMaschineG gDB} {f : Faden} {z : RufFadenG gDB} {x : List GLock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

theorem gbHg {s : List (Ereignis gDB)} (h : offen s = [GLock.M]) : HeldGenau gbL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

/-- **WITNESS, part 5**: a reached machine of `gPB` (thread 0 runs
    `einzahlen(k, 0, 7)`, three steps: the write, the call of `lies`, its
    return): memory `0 -> 100`, the return of `lies` is logged, and its
    `ensures result == k.slots[i].stand` holds there BY THE THEOREM. -/
theorem schlusssatz_104_maschine_zeuge :
    ∃ M : RufMaschineG gDB,
      RufErreichbarG gPB gOB 0 (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)) M ∧
      (gbSp0.slots GTab.Konto 0 GKontoFeld.stand).n = 0 ∧
      (M.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100 ∧
      ∃ (rho : Env gDB (gDB.params (some GFn.lies))) (v : ErgVal gDB (gDB.erg (some GFn.lies)))
        (s0 s1 : World gDB),
        RufEreignisF.rueck (some GFn.lies) rho v s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck gPB (some GFn.lies) s0 s1 rho v ∧
        -- the root `einzahlen` has finished (empty stack, head at its `return`):
        -- its `ensures` holds at its completion, BY THE THEOREM (`StartEndeG`)
        (M.faeden 0).stapel = [] ∧
        ∃ w : World gDB, EnsAmRueck gPB (some GFn.einzahlen) (gbSp0.welt []) w gbRho7 () := by
  have h00 : (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)).faeden 0 =
      ⟨[], ⟨some GFn.einzahlen, gbRho7, gbSp0.welt [],
        ⟨false, gDB.params (some GFn.einzahlen), gbL, gbRho7, .ende gbBody_einzahlen⟩⟩,
        startSpur (some GFn.einzahlen),
        [RufEreignisF.eintritt (some GFn.einzahlen) gbRho7 (gbSp0.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)).faeden 0).spur =
      [GLock.M] := rfl
  -- 1: the write through the pointer
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := gPB) (O := gOB) (passes := 0) h00 _ _ _
    rfl rfl (gbHg hoff0).heldIn _ _ rfl ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff1 : offen (M1.faeden 0).spur = [GLock.M] := by
    rw [hZ1.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff0)
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: call `lies`
  obtain ⟨M2, s2, hZ2⟩ := w_rufEnde (P := gPB) (O := gOB) (passes := 0) e1 (some GFn.lies) _ gbHp rfl
    _ _ rfl (gbHg (gbHoff e1 hoff1)).heldIn
  have hoff2 : offen (M2.faeden 0).spur = [GLock.M] := by
    rw [hZ2.spur, (Erw.lese _ _ _).offen]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: `lies` returns
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := gPB) (O := gOB) (passes := 0) e2 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (gbHg (gbHoff e2 hoff2)).heldIn
  have hr3 : RufErreichbarG gPB gOB 0 (RufStartG gPB gbSp0 (bootInit GFn.einzahlen gbRho7)) M3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3
  have hsp : (M3.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100 := by
    rw [hG3.2]
    show (M2.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100
    rw [hZ2.2]
    show (M1.speicher.slots GTab.Konto 0 GKontoFeld.stand).n = 100
    rw [hZ1.2]
    rfl
  have hlog := congrArg RufFadenG.log hG3.1
  have hex : ∃ (rho : Env gDB (gDB.params (some GFn.lies)))
      (v : ErgVal gDB (gDB.erg (some GFn.lies))) (w0 w1 : World gDB),
      RufEreignisF.rueck (D := gDB) (some GFn.lies) rho v w0 w1 ∈ (M3.faeden 0).log := by
    rw [hlog]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  obtain ⟨rho, v, w0, w1, hm⟩ := hex
  have hens := ((gPB_ziel (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _) gbSp0 0 M3
    hr3).1.1.1 0 _ hm).2 (some GFn.lies) rho v w0 w1 rfl
  have hSE := (gPB_ziel (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _) gbSp0 0 M3 hr3).2.1 0
  have h3 := hG3.1
  rw [h3] at hSE
  have hroot := (hSE rfl _ _ _ _ _ .keine rfl ⟨_, Or.inl rfl⟩).1
  exact ⟨M3, hr3, rfl, hsp, rho, v, w0, w1, hm, hens, by rw [h3], _, hroot⟩

/-- **The premises of `schlusssatz_104` are jointly satisfiable** (rule
    13): the printed certificate, the C semantics itself as the binary's
    behaviour (the hypotheses A1 hold with equality), and the runtime's
    start `bootInit` (A4) -- the start of the reached machine above. -/
theorem schlusssatz_104_praemissen :
    certOkG certG104 = true ∧
    (∀ st vs st' rv, CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 2 0 st vs st' rv) ∧
    (∀ st vs st' rv, CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv →
      CallAt gEL104.lay tvOrc tvXR refCProg 1 1 st vs st' rv) ∧
    LaufzeitStart (bootInit GFn.einzahlen gbRho7) :=
  ⟨certG104_ok, fun _ _ _ _ h => h, fun _ _ _ _ h => h, bootInit_laufzeit _ _⟩

example := schlusssatz_104 certG104 certG104_ok _ (fun _ _ _ _ h => h) _ (fun _ _ _ _ h => h)
  (bootInit GFn.einzahlen gbRho7) (bootInit_laufzeit _ _)


/-! ## CUTS

  THE PREMISES of `schlusssatz_104` (since 2026-09-14 the named
  assumptions that ARE Lean propositions are hypotheses of the theorem):

  * `hc : certOkG c = true` -- the correspondence certificate checks.
    Discharged for the printed rows by `decide` (`schlusssatz_104_praemisse`).
  * `hA1ein`/`hA1lies` -- A1 with A2 and A3 as ONE Lean hypothesis per
    function: every run of the binary's `einzahlen`/`lies` (`binEin`,
    `binLies`: the behaviour of the compiled code, parameters of the
    theorem) is a run of `CallAt gEL104.lay tvOrc tvXR refCProg` -- the C
    semantics of `CSemantik`/`CSpeicher`/`CFormen*`, applied to the emitted
    unit as the CS term `refCProg`, at the emitter's layout, at the call
    depth the call tree needs (2 for `einzahlen`, 1 for `lies`). Part 6
    then states EVERY run of the binary; part 4 stays a statement about the
    C semantics.
  * `hA4 : LaufzeitStart init` -- A4, fully a Lean proposition: every
    thread but `0` idles in the runtime's root `none`. Part 5 holds for
    EVERY such start (`bootInit` is one: `bootInit_laufzeit`).
  * No hardware or oracle premise: `gD` declares no axiom, register,
    device, global or `awaits` (`gO104`/`gOB` are forced by empty types,
    `GutO`/`RegLokal` proved), and the emitted unit makes no device access
    and no foreign call (`tvOrc`, `tvXR`; `tvXR_funktional`).
  * Jointly satisfiable: `schlusssatz_104_praemissen` (the C semantics
    itself as the binary's behaviour, `bootInit`), and the `example`.

  WHAT STAYS OUTSIDE LEAN -- the parts of A1-A5 that are no Lean
  proposition, precisely:

  A1. That `binEin`/`binLies` ARE the behaviour of the binary a C compiler
      produced from the emitted file -- i.e. that the compiler implements
      the C semantics of the model. A statement about a program outside
      Lean (the compiler); the theorem is conditional on it through the
      hypotheses, not by construction. Also outside: that the depth-2/1
      runs are all runs (no monotonicity lemma for `CallAt` in its fuel).
  A2. That the emitted TEXT means `refCProg`. `refCProg`/`cEinBody`/
      `cLiesBody` are a hand transcription of the quoted emitter output
      (`CFormenZeuge.lean`, `Korrespondenz104.lean`; byte identity of the
      quote with `gabbro emit` measured 2026-09-13, not proved); the
      certificate rows elaborate to them (`progOf_ok`) and are the Rust
      printer's rows (`certG104_rows`). WHAT WOULD REPLACE IT: a C parser
      in Lean for the emitter's subset, `parseC : String → Option CProg`,
      the emitted text pinned as a `String`, and `parseC text = some
      refCProg` by `decide`. A2 would then shrink to "the compiler's front
      end reads the subset as `parseC` does" -- a part of A1.
  A3. That the compiler lays out `Konto` as `kontoLay` (2 records of 4
      bytes, `stand` at offset 0, `uint32_t`; `kontoLay_werte`). It is in
      the A1 hypothesis (`gEL104.lay`); the emitted `_Static_assert` pins
      (`CFormenM` M11) are checked BY THE COMPILER, so A3 reduces to A1 +
      A2 plus one missing Lean lemma: the C semantics depends on a
      `RecLay` only through the pinned numbers (fields `< nf`).
  A4. That the real runtime starts the program in a `LaufzeitStart` shape
      (the C driver that makes the call is not emitted). The shape itself
      is the hypothesis `hA4`.
  A5. The Lean kernel, and the DEFINITIONS a human must read (plan §3):
      machine G, `rufAt`/`execEnd`, `KoerperGutS`, `VertragAmOrtG`, the C
      semantics, `corrW`/`EnvRel`. Not a proposition.

  THE `forever` BUDGET: `gP` and `gPB` contain no `forever` loop; the
  obligations (part 3) are stated at EVERY budget (`koerperGutS_alle`),
  the call semantics is budget-independent (`gP_rufAt_passes`,
  `gPB_rufAt_passes`: every `rufAt … 0 …` of parts 4-6 holds at every
  budget), and part 5 holds on the machines of every budget.

  JOINTS -- what is closed and how:

  J1. P identity. CLOSED for the parser's `gP`: parse (1), model
      certificates (2), model judgement (3) and the C correspondence (4)
      are all about `gP` itself; `r4P`/`refP` are no longer in the chain.
      The machine (5) needs `gPB` = `gP` plus the idle root, related to `gP`
      by a proved translation: syntactically (`gPB_ist_gP_umbenannt`, the
      renaming `renEnd`/`renE` applied to `gP`'s bodies and contracts gives
      `gPB`'s, by `rfl`) and semantically for both source functions
      (`gPB_wie_gP_*`: same memory effect and answer, through the emitted C).
  J2. Model certificates are FOR `gP`: `print104_*` (the Lean print of
      `gP`'s bodies is the pasted printer output), accepted by `decide`.
  J3. The C correspondence is about `gP`'s bodies (`liesG_end`, `einG_end`)
      and the emitted text (A2); the certificate is load-bearing
      (`progOf_ok`, `kOf_ok`, `corrCertG_sound`).
  J4. Single-threaded completeness: `ziel_ort_einfaden` (no footprint or
      exclusivity premise) for the machine; every C run by
      `callAt_funktional` (`exec_det`).

  NOT PROVED (named):

  - The source text is the comment-free one-line form `u104lex` pins; the
    real file with comments is lane 162's.
  - The certificate's MAP (`vm`/`pp`/`ks`) is `gP`'s and is NOT what
    `corrlean.rs` prints today: the printer prints `refD`'s map (`vm = [2]`,
    the `MODEL DATUM` index `ks = [(1, 0)]`). Its rows and layout are the
    printer's. Moving the printer to the exporter's map is Rust work (no
    `cargo` in this lane).
  - `renE`/`renEnd` are PARTIAL (the 104 fragment and some more; `none`
    elsewhere) and their semantic preservation is not proved in general;
    the semantic bridge is proved for 104's two functions only, and only
    for starts related to one C state.
  - Part 4 relates C runs to `rufAt` (the sequential semantics), part 5
    states the goal theorem on machine G of `gPB`; that G with one active
    thread agrees with `rufAt` is the adequacy chain (`rufG_adaequat_ruf`),
    not re-instantiated here. (Part 5 now carries the root's `ensures` at
    its completion -- `StartEndeG`, witnessed on a reached machine in
    `schlusssatz_104_maschine_zeuge` -- so the root's contract is no longer
    carried by part 4 alone.)
  - The C statements are at the depth the call tree needs (`einzahlen` at 2,
    `lies` at 1); deeper `CallAt` fuel is not stated (no monotonicity lemma).
  - `corrW` relates memory, not traces: Gabbro's lock trace and C's
    observation list are not related (CSpeicher CUTS).
  - Stage (b): concurrency (DRF-SC, lock primitives, thread creation) is
    not addressed; `gP_kein_exklusiv` shows a two-active-thread start of
    this program is refused by the model anyway (every function holds `M`).
  - Widening beyond 104: everything keyed to `gD`: the lowering
    (`lowerProg`), `certOkG` (fixed rows), `printEnd104` (the 104 shapes),
    the renaming target `gDB`, the per-program `rufAt` computations
    (`rufEin_ok`) that stand in for a general "obligations imply `rufAt` ok"
    theorem, and the copied C correspondence of 5.5.
-/

#print axioms Gabbro.Grammatik.uebersetze104_ok
#print axioms Gabbro.Grammatik.corrCertG_sound
#print axioms Gabbro.Grammatik.c104_einzahlen
#print axioms Gabbro.Grammatik.c104_lies
#print axioms Gabbro.Grammatik.print104_einzahlen
#print axioms Gabbro.Grammatik.print104_lies
#print axioms Gabbro.Grammatik.gP_koerperS
#print axioms Gabbro.Grammatik.gP_kein_ruhig
#print axioms Gabbro.Grammatik.gP_kein_exklusiv
#print axioms Gabbro.Grammatik.gPB_ist_gP_umbenannt
#print axioms Gabbro.Grammatik.gPB_ziel
#print axioms Gabbro.Grammatik.gPB_wie_gP_einzahlen
#print axioms Gabbro.Grammatik.gPB_wie_gP_lies
#print axioms Gabbro.Grammatik.schlusssatz_104
#print axioms Gabbro.Grammatik.schlusssatz_104_praemisse
#print axioms Gabbro.Grammatik.schlusssatz_104_zeuge
#print axioms Gabbro.Grammatik.schlusssatz_104_maschine_zeuge
#print axioms Gabbro.Grammatik.schlusssatz_104_praemissen
#print axioms Gabbro.Grammatik.gP_rufAt_passes

end Gabbro.Grammatik
